#!/usr/bin/env python3
"""Archive exact external Tex2Lean exports; never run Lean or write native state."""
import argparse
import gzip
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import tarfile

TARGETS = {
    "thm-main": "thm:main",
    "thm-attainable-count": "thm:attainable-count",
    "lem-splitting": "lem:splitting",
}
# Reviewed producer for the refreshed exports after the helper relocation.
# Main was exported with this source; the remaining exports must use it too.
EXPORT_HELPERS = {
    "lem:splitting": "b538eb1777398a1736f49c34e4a3c66a6ef93de0c7b319c8a42b88bf04039a09",
    "thm:main": "b538eb1777398a1736f49c34e4a3c66a6ef93de0c7b319c8a42b88bf04039a09",
    "thm:attainable-count": "b538eb1777398a1736f49c34e4a3c66a6ef93de0c7b319c8a42b88bf04039a09",
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def safe_name(name):
    require(isinstance(name, str) and name and "\\" not in name and "\x00" not in name,
            "invalid archive path")
    p = PurePosixPath(name)
    require(not p.is_absolute() and all(x not in (".", "..", "") for x in p.parts),
            f"unsafe archive path: {name}")
    require(str(p) == name, f"noncanonical archive path: {name}")
    return name


def validate_contents(contents):
    require("EXPORT.json" in contents, "missing EXPORT.json")
    report = json.loads(contents["EXPORT.json"])
    require(report.get("schema") == "antichain.native-target-export/1", "wrong export schema")
    expected = {"EXPORT.json"}
    for item in report["files"]:
        name = safe_name(item["path"])
        require(name not in expected, f"duplicate exported path: {name}")
        expected.add(name)
        require(name in contents, f"missing exported file: {name}")
        data = contents[name]
        require(len(data) == item["bytes"], f"size mismatch: {name}")
        require(sha(data) == item["rawSHA256"], f"raw SHA256 mismatch: {name}")
    require(set(contents) == expected, "archive has unlisted files")
    review = report.get("handoffLimitationsReview")
    unknowns = report["observedHandoff"]["unknowns"]
    if unknowns or review:
        require(bool(unknowns) and isinstance(review, dict),
                "nonempty native unknowns require the preserved limitations review")
        require(sha(review["rawText"].encode("utf-8")) == review["rawSHA256"],
                "limitations review raw SHA256 mismatch")
        details = json.loads(review["rawText"])
        require(details["unknowns"] == unknowns, "limitations review changed native unknowns")
        require(details["targetLabel"] == report["targetLabel"], "limitations review target mismatch")
        require(details["targetId"] == report["head"]["targetId"], "limitations review target ID mismatch")
        require(details["certifiedSnapshotDigest"] == report["head"]["certifiedSnapshotDigest"],
                "limitations review certificate mismatch")
        require(details["sourceFingerprint"] == report["certificate"]["sourceFingerprint"],
                "limitations review source mismatch")
        slug = next(k for k, v in TARGETS.items() if v == report["targetLabel"])
        handoff = contents[f".blueprint/handoff/{slug}/handoff.json"]
        require(sha(handoff) == details["handoffRawSHA256"], "limitations review handoff mismatch")
        require(isinstance(review["purpose"], str) and review["purpose"].strip(),
                "limitations review purpose is absent")
    return report


def read_export(directory):
    directory = directory.resolve(strict=True)
    contents = {}
    for file in directory.rglob("*"):
        require(not file.is_symlink(), f"symlink refused: {file}")
        if file.is_dir():
            continue
        require(file.is_file(), f"nonregular input refused: {file}")
        name = safe_name(file.relative_to(directory).as_posix())
        contents[name] = file.read_bytes()
    return contents, validate_contents(contents)


def read_archive(file, expected_sha=None):
    archive = file.read_bytes()
    if expected_sha is not None:
        require(sha(archive) == expected_sha, f"archive SHA256 mismatch: {file.name}")
    contents = {}
    with tarfile.open(fileobj=io.BytesIO(archive), mode="r:gz") as tar:
        for member in tar:
            name = safe_name(member.name)
            require(member.isfile(), f"nonregular archive member refused: {name}")
            require(name not in contents, f"duplicate archive member: {name}")
            contents[name] = tar.extractfile(member).read()
    return contents, validate_contents(contents)


def summary(report, contents, archive_name, archive_hash):
    provenance = "Codex assistant review under user-authorized formalization; no human review asserted"
    bindings = []
    for binding in report["bindings"]:
        require(binding.get("semanticReviewProvenance", "").startswith(provenance),
                "cannot replace unrecognized review provenance with an assistant statement")
        bindings.append({key: binding[key] for key in (
            "declaration", "bindingId", "receiptDigest", "semanticApprovalDecisionId")})
        bindings[-1]["semanticReviewProvenance"] = provenance
    result = {
        "schema": "antichain.native-export-archive-summary/1",
        "purpose": "Exact-byte package of an independently checked native export; not a new certificate or verdict",
        "archive": archive_name,
        "archiveSHA256": archive_hash,
        "exportManifestSHA256": sha(contents["EXPORT.json"]),
        "exportHelperSHA256": EXPORT_HELPERS[report["targetLabel"]],
        "exportedAtUTC": report["exportedAtUTC"],
        "targetLabel": report["targetLabel"],
        "head": report["head"],
        "certificate": report["certificate"],
        "observedHandoff": report["observedHandoff"],
        "bindings": bindings,
        "fullReviewProvenance": "Preserved verbatim in the archive's original EXPORT.json and native decision records",
        "excludedMetadata": report["excludedMetadata"],
        "leanSourceSnapshot": report["leanSourceSnapshot"],
        "archiveFileCount": len(contents),
        "uncompressedBytes": sum(map(len, contents.values())),
        "validation": "Archive SHA256 and each original path, byte count, and raw SHA256 agree with EXPORT.json",
        "limitations": report["limitations"],
    }
    if "handoffLimitationsReview" in report:
        review = report["handoffLimitationsReview"]
        result["handoffLimitationsReview"] = {
            "rawSHA256": review["rawSHA256"],
            "purpose": review["purpose"],
            "fullReview": "Preserved verbatim in the archive's original EXPORT.json",
        }
    return result


def pack_one(source, output, slug):
    contents, report = read_export(source)
    require(report["targetLabel"] == TARGETS[slug], "unexpected target in export directory")
    archive = output / f"{slug}.tar.gz"
    require(not archive.exists(), f"refusing overwrite: {archive}")
    # Normalize only tar/gzip container metadata. Native file bytes stay exact.
    with archive.open("xb") as raw:
        with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as gz:
            with tarfile.open(fileobj=gz, mode="w", format=tarfile.PAX_FORMAT) as tar:
                for name, data in sorted(contents.items()):
                    info = tarfile.TarInfo(name)
                    info.size, info.mode, info.mtime = len(data), 0o644, 0
                    tar.addfile(info, io.BytesIO(data))
    archive_hash = sha(archive.read_bytes())
    copied, copied_report = read_archive(archive, archive_hash)
    require(copied == contents, "archive changed source bytes")
    current, _ = read_export(source)
    require(current == contents, "source export changed while packaging")
    result = summary(copied_report, copied, archive.name, archive_hash)
    summary_path = output / f"{slug}.summary.json"
    with summary_path.open("x") as f:
        json.dump(result, f, indent=2, ensure_ascii=False)
        f.write("\n")
    return {
        "targetLabel": report["targetLabel"],
        "archive": archive.name,
        "archiveSHA256": archive_hash,
        "summary": summary_path.name,
        "summarySHA256": sha(summary_path.read_bytes()),
        "generation": report["head"]["generation"],
        "sourceFingerprint": report["certificate"]["sourceFingerprint"],
    }


def pack(root, output):
    require(not output.exists(), "output directory already exists; use a fresh external path")
    for slug in TARGETS:
        require((root / slug / "EXPORT.json").is_file(), f"export not ready: {slug}")
    # Parent must review final source/head agreement before this packaging step.
    reports = [read_export(root / slug)[1] for slug in TARGETS]
    source_fingerprints = {r["certificate"]["sourceFingerprint"] for r in reports}
    require(len(source_fingerprints) == 1, "the three exports pin different Lean sources")
    output.mkdir()
    entries = [pack_one(root / slug, output, slug) for slug in TARGETS]
    index = {
        "schema": "antichain.selected-native-archives/1",
        "purpose": "Preserved exports for three selected native runs, independent of complete 18-result Lean coverage",
        "sourceFingerprint": source_fingerprints.pop(),
        "exports": entries,
        "exportHelpers": EXPORT_HELPERS,
        "mappingHistory": "The complete immutable history remains at .tex2lean/mapping in the repository",
        "validationScope": "Exact archive/export bytes and shared recorded source fingerprint; no compiler or native validator is run",
    }
    (output / "index.json").write_text(json.dumps(index, indent=2) + "\n")
    (output / "SHA256SUMS").write_text("".join(f"{e['archiveSHA256']}  {e['archive']}\n" for e in entries))
    return check(output)


def check(directory):
    index = json.loads((directory / "index.json").read_text())
    require(index.get("schema") == "antichain.selected-native-archives/1", "wrong index schema")
    require(index.get("exportHelpers") == EXPORT_HELPERS, "export helper provenance differs")
    require(len(index["exports"]) == len(TARGETS), "expected exactly three selected exports")
    seen = set()
    for entry in index["exports"]:
        require(entry["targetLabel"] in TARGETS.values() and entry["targetLabel"] not in seen, "wrong/duplicate target")
        seen.add(entry["targetLabel"])
        archive = directory / safe_name(entry["archive"])
        contents, report = read_archive(archive, entry["archiveSHA256"])
        require(report["targetLabel"] == entry["targetLabel"], "target differs from index")
        require(report["certificate"]["sourceFingerprint"] == index["sourceFingerprint"] == entry["sourceFingerprint"], "source fingerprint differs")
        require(report["head"]["generation"] == entry["generation"], "generation differs")
        summary_path = directory / safe_name(entry["summary"])
        require(sha(summary_path.read_bytes()) == entry["summarySHA256"], "summary SHA256 differs")
        require(json.loads(summary_path.read_text()) == summary(report, contents, archive.name, entry["archiveSHA256"]), "summary differs from original export")
    expected_sums = "".join(f"{e['archiveSHA256']}  {e['archive']}\n" for e in index["exports"])
    require((directory / "SHA256SUMS").read_text() == expected_sums, "SHA256SUMS differs from index")
    return {"archiveChecks": "passed", "targets": sorted(seen), "sourceFingerprint": index["sourceFingerprint"],
            "nativeCertificationRun": False, "compilerRun": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("pack")
    p.add_argument("--root", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p = sub.add_parser("check")
    p.add_argument("directory", type=Path)
    args = parser.parse_args()
    try:
        result = pack(args.root, args.out) if args.command == "pack" else check(args.directory)
        print(json.dumps(result, indent=2))
    except (ValueError, OSError, KeyError, json.JSONDecodeError, tarfile.TarError) as error:
        parser.exit(1, f"ARCHIVE CHECK REFUSED: {error}\n")
