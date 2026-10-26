#!/usr/bin/env python3
"""Extract and narrowly patch this task's installed Tex2Lean CLI bundle.

Only the destination directory is written. The installed executable, project,
settings, and workflow state are not modified. The nine exact replacements
fail closed if the installed source differs from the reviewed version.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import shlex

parser = argparse.ArgumentParser()
parser.add_argument("--installed", type=Path, default=Path.home() / ".local/bin/tex2lean")
parser.add_argument("--output", type=Path, required=True, help="Separate build directory; do not commit its generated bundle")
parser.add_argument("--node", type=Path, default=Path.home() / ".cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin/node")
args = parser.parse_args()
blob = args.installed.read_bytes()
anchor = b"function uhe(e,t,n)"
assert blob.count(anchor) == 1, "Expected exactly one reviewed audit collector"
at = blob.index(anchor)
begin = blob.rfind(b"\x00", 0, at) + 1
end = blob.index(b"\x00", at)
original = blob[begin:end].decode("utf-8")
assert original.startswith('#!/usr/bin/env node\n"use strict";'), "Unexpected bundle start"
assert original.endswith('MY(OY.resolve(__dirname,".."));\n'), "Unexpected bundle entrypoint"

patches = [
    (
        "Keep generated Meta.Audit imports inside the selected project library",
        '.filter(r=>!r.startsWith(`${n}.Meta`)&&!r.startsWith(`${n}Test`)&&r!==n).sort()',
        '.filter(r=>r.startsWith(`${n}.`)&&!r.startsWith(`${n}.Meta`)&&!r.startsWith(`${n}Test`)&&r!==n).sort()',
    ),
    (
        "Forward configured effort to the structured Codex provider",
        'new sv({path:e.codexCliPath,model:e.codexModel,timeoutMs:e.cliTimeoutSeconds*1e3})',
        'new sv({path:e.codexCliPath,model:e.codexModel,effort:e.anthropicEffort,timeoutMs:e.cliTimeoutSeconds*1e3})',
    ),
    (
        "Emit structured request/config effort using the existing Codex effort mapping",
        'a&&s.push("--model",a);let d=0,l="",c=await Bc(',
        'a&&s.push("--model",a);const effort=ete(t.effort??this.opts.effort);effort&&s.push("-c",`model_reasoning_effort="${effort}"`);let d=0,l="",c=await Bc(',
    ),
    (
        "Use configured effort when an interactive/proof worker has no tier override",
        'o=r?ete(n?.effort):void 0;',
        'o=r?ete(n?.effort??t.anthropicEffort):void 0;',
    ),
    (
        "Include private project constants in ModelClosure namespace classification",
        '      let acc := if (\\`${e}).isPrefixOf c then acc.insert c else acc',
        '      let acc := if (\\`${e}).isPrefixOf (Lean.privateToUserName c) then acc.insert c else acc',
    ),
    (
        "Limit concurrent Lean diagnostic processes to two, preserving all checks",
        'await vQ(d,4,async y=>{',
        'await vQ(d,2,async y=>{',
    ),
    (
        "Traverse project inductive constructors so structure field constraints enter ModelClosure",
        '        let next := ci.type.getUsedConstants.toList\n'
        '          ++ (match ci.value? with | some v => v.getUsedConstants.toList | none => [])\n',
        '        let next := ci.type.getUsedConstants.toList\n'
        '          ++ (match ci.value? with | some v => v.getUsedConstants.toList | none => [])\n'
        '          ++ (match ci with\n'
        '              | .inductInfo iv =>\n'
        '                if (\\`${e}).isPrefixOf (Lean.privateToUserName c) then iv.ctors else []\n'
        '              | _ => [])\n',
    ),
    (
        "Retain registered capstone claims when regenerating Meta at a planning boundary",
        'headlines:r.filter(c=>c.trim())',
        'headlines:[...new Set([...(await k8(e,t)),...r])].filter(c=>c.trim())',
    ),
    (
        "Exclude only known transient helper basenames at the Lean project root from source inventory",
        'else s.endsWith(".lean")&&n.push(x(o,s))',
        'else s.endsWith(".lean")&&!(o===e&&/^\\.tex2lean-(?:(?:inspection|axioms|public-refutation|refutation|interfaces|interface-values)-[0-9a-f]{32}|side)\\.lean$/.test(s))&&n.push(x(o,s))',
    ),
]
expected_source_sha256 = "ae68bb68d8b7d1333660add1a39474e007d43136b8ddab923850594ff79bc99d"
assert hashlib.sha256(original.encode()).hexdigest() == expected_source_sha256, "Installed bundle differs from the reviewed Tex2Lean 1.0.2 build"
patched = original
for label, before, after in patches:
    assert patched.count(before) == 1, f"Anchor mismatch: {label}"
    patched = patched.replace(before, after, 1)

# These complete check-generating functions remain byte-identical.
check_sections = [
    ("CostSeal permissions", "function kX(e)", "function ZA(e)"),
    ("CostSeal checker", "function ZA(e)", "function OD("),
    ("Meta phase regeneration", "async function qD(", "async function iC("),
    ("Audit template", "function XA(e,t,n)", "var ph="),
    ("Proof-fact source fingerprint checks", "async function cr(", "var Fl,"),
]
unchanged_checks = {}
for label, start, end_marker in check_sections:
    old_begin = original.index(start)
    old_end = original.index(end_marker, old_begin)
    new_begin = patched.index(start)
    new_end = patched.index(end_marker, new_begin)
    old_section = original[old_begin:old_end]
    assert old_section == patched[new_begin:new_end], f"Mathematical check changed: {label}"
    unchanged_checks[label] = hashlib.sha256(old_section.encode()).hexdigest()

# ModelClosure is strengthened by exactly the fifth and seventh replacements.
# Preserve each internal constant name for environment lookup and module checks;
# normalize only its namespace classification. Expand constructors only for
# project inductives, so their field constraints are checked too.
closure_start = "function BD(e)"
closure_end = "async function qD("
old_begin = original.index(closure_start)
new_begin = patched.index(closure_start)
old_closure = original[old_begin:original.index(closure_end, old_begin)]
new_closure = patched[new_begin:patched.index(closure_end, new_begin)]
expected_closure = old_closure
for patch_index in (4, 6):
    _, closure_before, closure_after = patches[patch_index]
    assert expected_closure.count(closure_before) == 1, "ModelClosure anchor mismatch"
    expected_closure = expected_closure.replace(closure_before, closure_after, 1)
assert new_closure == expected_closure, "Unexpected ModelClosure change"
strengthened_checks = {
    "ModelClosure and statement-side checker": {
        "original_sha256": hashlib.sha256(old_closure.encode()).hexdigest(),
        "patched_sha256": hashlib.sha256(new_closure.encode()).hexdigest(),
        "changes": [patches[index][0] for index in (4, 6)],
    },
}

# The diagnostic scheduler changes only its concurrency argument, not its
# file selection, checks, cancellation, cache, or result processing.
diagnostics_start = "async function $C("
diagnostics_end = "function bQ("
old_begin = original.index(diagnostics_start)
new_begin = patched.index(diagnostics_start)
old_diagnostics = original[old_begin:original.index(diagnostics_end, old_begin)]
new_diagnostics = patched[new_begin:patched.index(diagnostics_end, new_begin)]
_, diagnostics_before, diagnostics_after = patches[5]
assert old_diagnostics.count(diagnostics_before) == 1, "Diagnostics concurrency anchor mismatch"
assert new_diagnostics == old_diagnostics.replace(diagnostics_before, diagnostics_after, 1), "Unexpected diagnostic check change"
resource_tuning = {
    "Lean diagnostics": {
        "original_sha256": hashlib.sha256(old_diagnostics.encode()).hexdigest(),
        "patched_sha256": hashlib.sha256(new_diagnostics.encode()).hexdigest(),
        "original_concurrency": 4,
        "patched_concurrency": 2,
    },
}

# Only exact tool-generated helper names at the project root leave inventory.
# All other collection logic and the independent snapshot checks stay intact.
inventory_start = "async function Vc("
inventory_end = "function FQ("
old_begin = original.index(inventory_start)
new_begin = patched.index(inventory_start)
old_inventory = original[old_begin:original.index(inventory_end, old_begin)]
new_inventory = patched[new_begin:patched.index(inventory_end, new_begin)]
_, inventory_before, inventory_after = patches[8]
assert old_inventory.count(inventory_before) == 1, "Inventory filter anchor mismatch"
assert new_inventory == old_inventory.replace(inventory_before, inventory_after, 1), "Unexpected inventory change"
source_inventory = {
    "original_sha256": hashlib.sha256(old_inventory.encode()).hexdigest(),
    "patched_sha256": hashlib.sha256(new_inventory.encode()).hexdigest(),
    "change": patches[8][0],
}

out = args.output.resolve()
assert out != args.installed.parent.resolve(), "Do not write beside the installed CLI"
out.mkdir(parents=True, exist_ok=True)
(out / "out").mkdir(exist_ok=True)
(out / "original.cjs").write_text(original)
(out / "out/cli.cjs").write_text(patched)
(out / "compatibility.patch").write_text("".join(difflib.unified_diff(
    original.splitlines(keepends=True), patched.splitlines(keepends=True),
    fromfile="original.cjs", tofile="out/cli.cjs",
)))
(out / "changes.json").write_text(json.dumps([
    {"purpose": label, "before": before, "after": after}
    for label, before, after in patches
], indent=2) + "\n")
manifest = {
    "installed": str(args.installed.resolve()),
    "installed_sha256": hashlib.sha256(blob).hexdigest(),
    "bundle_range": [begin, end],
    "original_bundle_sha256": hashlib.sha256(original.encode()).hexdigest(),
    "patched_bundle_sha256": hashlib.sha256(patched.encode()).hexdigest(),
    "node": str(args.node.resolve()),
    "patches": [label for label, _, _ in patches],
    "unchanged_check_sha256": unchanged_checks,
    "strengthened_check_sha256": strengthened_checks,
    "resource_tuning": resource_tuning,
    "source_inventory": source_inventory,
}
(out / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
wrapper = '#!/bin/sh\nexec ' + shlex.quote(str(args.node.resolve())) + ' ' + shlex.quote(str(out / "out/cli.cjs")) + ' "$@"\n'
(out / "tex2lean").write_text(wrapper)
(out / "tex2lean").chmod(0o755)
print(json.dumps(manifest, indent=2))
