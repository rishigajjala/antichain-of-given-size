#!/usr/bin/env node
'use strict';
// Read-only consistency/export helper. This does not run Tex2Lean or Lean,
// alter native status, authenticate reviewers, or replace the native validator.
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');

// Reviewed against G0/Au/Pt/Cu/Tu/K0/V0 in the unchanged native bundle.
function canonical(value, omitted = new Set(), location = '$') {
  if (value === null || typeof value === 'boolean') return value;
  if (typeof value === 'string') return value.normalize('NFC').replace(/\r\n?/g, '\n');
  if (typeof value === 'number') {
    if (!Number.isFinite(value)) throw new TypeError(`non-finite number at ${location}`);
    return Object.is(value, -0) ? 0 : value;
  }
  if (Array.isArray(value)) return value.map((v, i) => canonical(v, omitted, `${location}[${i}]`));
  if (typeof value !== 'object' || value === undefined) throw new TypeError(`unsupported canonical value at ${location}`);
  const result = {};
  for (const key of Object.keys(value).sort()) {
    if (!omitted.has(key) && value[key] !== undefined) result[key] = canonical(value[key], omitted, `${location}.${key}`);
  }
  return result;
}
const rawHash = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const digest = (domain, value, omitted = []) => 'sha256-' + rawHash(
  'tex2lean.canonical-json/1\0' + domain + '\0' + JSON.stringify(canonical(value, new Set(omitted))));
const tuple = b => JSON.stringify(['declaration', 'role', 'file', 'module'].map(k => b[k]));
// Native retired records remain in the archived ledger. Stale/proposed records
// remain active and must still satisfy every existing verified/receipt guard.
const currentBindings = ledger => ledger.bindings.filter(b => !['rejected', 'superseded'].includes(b.status));
const exactSet = (actual, expected, message) => {
  assert.equal(new Set(actual).size, actual.length, `${message}: duplicates`);
  assert.deepEqual([...actual].sort(), [...expected].sort(), message);
};
const specs = {
  'thm:main': {
    id: 'target:6d290646-6ef6-4d8e-8d05-9ae814b12874',
    blueprint: '.blueprint/thm-main-5e5f26eaeb/blueprint.json',
    handoff: '.blueprint/handoff/thm-main', mathematicalClaims: 7, excluded: []
  },
  'thm:attainable-count': {
    id: 'target:dba29c12-9eef-4c73-a091-1ac777e05e5f',
    blueprint: '.blueprint/thm-attainable-count-04ffa9e627/blueprint.json',
    handoff: '.blueprint/handoff/thm-attainable-count', mathematicalClaims: 11,
    excluded: ['claim-version:2a429de2-108f-4b45-8210-c126cc2c6a95', 'claim-version:e7fd79a7-be6d-4b9b-847a-18cdb0de891f']
  },
  'lem:splitting': {
    id: 'target:b340dafe-e1c4-4bdd-a7a9-e888e9282117',
    blueprint: '.blueprint/lem-splitting-2934d3ab00/blueprint.json',
    handoff: '.blueprint/handoff/lem-splitting', mathematicalClaims: 1, excluded: []
  }
};

function environment(repoArg) {
  const repo = fs.realpathSync(repoArg);
  const files = new Map();
  function read(relative) {
    const name = path.resolve(repo, relative);
    assert(name.startsWith(repo + path.sep), 'input escapes repository');
    assert.equal(fs.realpathSync(name), name, 'symlinked export input refused');
    const bytes = fs.readFileSync(name);
    if (files.has(relative)) assert(bytes.equals(files.get(relative)), `input changed: ${relative}`);
    else files.set(relative, bytes);
    return bytes;
  }
  const json = relative => JSON.parse(read(relative).toString('utf8'));
  const mapped = (directory, id) => {
    assert(/^sha256-[0-9a-f]{64}$/.test(id), 'content-addressed ID expected');
    return json(`.tex2lean/mapping/${directory}/${encodeURIComponent(id)}.json`);
  };
  function stable() {
    for (const [relative, bytes] of files) assert(fs.readFileSync(path.join(repo, relative)).equals(bytes), `input changed: ${relative}`);
  }
  return {repo, files, read, json, mapped, stable};
}

// Same file selection/order/relative-path hashing as the reviewed native Vc/na.
function currentLeanSources(repo) {
  const files = [];
  function walk(directory) {
    for (const item of fs.readdirSync(directory, {withFileTypes: true})) {
      const file = path.join(directory, item.name);
      if (fs.lstatSync(file).isSymbolicLink()) continue;
      if (item.isDirectory()) {
        if (item.name.startsWith('.') || ['build', 'scratch'].includes(item.name)) continue;
        walk(file);
      } else if (item.name.endsWith('.lean') && !(directory === repo &&
        /^\.tex2lean-(?:(?:inspection|axioms|public-refutation|refutation|interfaces|interface-values)-[0-9a-f]{32}|side)\.lean$/.test(item.name))) files.push(file);
    }
  }
  walk(repo);
  files.sort((a, b) => a.localeCompare(b));
  const hash = crypto.createHash('sha256');
  const inputs = files.map(file => {
    const relative = path.relative(repo, file).replace(/\\/g, '/');
    const bytes = fs.readFileSync(file);
    hash.update(relative).update('\0').update(bytes.toString('utf8')).update('\0');
    return {path: relative, bytes: bytes.length, sha256: rawHash(bytes)};
  });
  return {fingerprint: 'sha256:' + hash.digest('hex'), inputs};
}


// Packaging review only: native findings, unknowns and lifecycle flags are never changed.
function checkHandoffFindings(handoff) {
  assert.equal(handoff.correspondence.headline.verdict, 'formalized');
  assert.deepEqual(handoff.correspondence.headline.mismatches, [], 'native headline mismatches remain');
  assert(Array.isArray(handoff.correspondence.auditSurface), 'native audit surface is absent');
  for (const finding of handoff.correspondence.auditSurface) {
    assert.equal(finding.severity, 'note', 'native blocking audit-surface finding');
    assert(['agrees', 'stronger', 'not-in-paper'].includes(finding.verdict), 'native audit-surface mismatch');
  }
  function noBlockers(value) {
    if (!value || typeof value !== 'object') return;
    assert(value.severity !== 'blocking', 'native blocking finding remains');
    for (const nested of Object.values(value)) noBlockers(nested);
  }
  noBlockers(handoff);
  assert(Array.isArray(handoff.claimProgress?.rows), 'native claim progress is absent');
  for (const row of handoff.claimProgress.rows.filter(x => x.coverage === 'mapped')) {
    assert.equal(row.proof, 'proved', 'mapped mathematical claim is not proved');
    assert.equal(row.proofSnapshot, 'certified');
    assert.deepEqual(row.conditions, []); assert.deepEqual(row.nearestBlockers, []);
  }
  assert(['pass', 'pass-with-note'].includes(handoff.assumptions.verdict));
  assert.equal(handoff.assumptions.axiomProfile.verified, true);
  assert(['pass', 'pass-with-note', 'not-applicable'].includes(handoff.probability.verdict), 'native probability gate is unresolved');
}
function reviewHandoffLimitations(e, handoff, label, head, certificate, reviewPath) {
  assert(Array.isArray(handoff.unknowns));
  if (!reviewPath) { assert.deepEqual(handoff.unknowns, [], 'nonempty native unknowns require an exact limitations review'); return undefined; }
  assert(handoff.unknowns.length > 0, 'limitations review supplied for a handoff without unknowns');
  assert(path.isAbsolute(reviewPath), 'limitations review must use an absolute path');
  const bytes = fs.readFileSync(reviewPath), rawText = bytes.toString('utf8');
  assert(Buffer.from(rawText, 'utf8').equals(bytes), 'review must be UTF-8');
  const review = JSON.parse(rawText);
  exactSet(Object.keys(review), ['schema','targetLabel','targetId','certifiedSnapshotDigest','sourceFingerprint','handoffRawSHA256','unknowns','reviewer','provenance','noNativeVerdictOverride','assessment','items'], 'limitations review fields');
  assert.equal(review.schema, 'antichain.handoff-evidence-limitations-review/1');
  assert.equal(review.targetLabel, label); assert.equal(review.targetId, head.targetId);
  assert.equal(review.certifiedSnapshotDigest, head.certifiedSnapshotDigest);
  assert.equal(review.sourceFingerprint, certificate.sourceFingerprint);
  assert.equal(review.handoffRawSHA256, rawHash(e.read(specs[label].handoff + '/handoff.json')), 'reviewed handoff changed');
  assert.deepEqual(review.unknowns, handoff.unknowns, 'review must preserve every exact native unknown');
  assert.deepEqual(handoff.correspondence.unresolved, handoff.unknowns, 'unreviewed native correspondence uncertainty remains');
  assert.equal(review.reviewer, 'Codex assistant');
  assert.equal(review.provenance, 'Assistant assessment for faithful evidence packaging; no human review or new proof certification asserted');
  assert.equal(review.noNativeVerdictOverride, true);
  assert(typeof review.assessment === 'string' && review.assessment.trim());
  assert(Array.isArray(review.items));
  exactSet(review.items.map(x => x.unknownIndex), handoff.unknowns.map((_, i) => i), 'review every unknown exactly once');
  for (const item of review.items) {
    exactSet(Object.keys(item), ['unknownIndex','classification','assessment','citations'], 'limitation item fields');
    assert(['read-only-verification', 'empty-output-log'].includes(item.classification), 'only verification-evidence limitations are supported');
    assert(typeof item.assessment === 'string' && item.assessment.trim());
    assert(Array.isArray(item.citations) && item.citations.length > 0, 'limitation assessment needs cited evidence');
    for (const citation of item.citations) {
      exactSet(Object.keys(citation), ['path','rawSHA256','description'], 'citation fields');
      assert(typeof citation.description === 'string' && citation.description.trim());
      assert(typeof citation.path === 'string' && !path.isAbsolute(citation.path) && !citation.path.split(/[\\/]/).includes('..'), 'citation must be project-relative');
      assert.equal(rawHash(e.read(citation.path)), citation.rawSHA256, 'cited evidence changed');
    }
  }
  const originalStable = e.stable;
  e.stable = () => { originalStable(); assert(fs.readFileSync(reviewPath).equals(bytes), 'limitations review changed before export'); };
  return {rawSHA256: rawHash(bytes), rawText,
    purpose: 'Preserve the observed native report with explicitly reviewed verification limitations; no unknown or native verdict is cleared.'};
}

function inspectTarget(repoArg, label, {handoffLimitationsPath} = {}) {
  const spec = specs[label]; assert(spec, 'choose one of the three reviewed targets');
  const e = environment(repoArg), {json, mapped, read} = e;
  const head = json(`.tex2lean/mapping/targets/${encodeURIComponent(spec.id)}/head.json`);
  assert.equal(head.targetId, spec.id);
  assert(head.certifiedSnapshotDigest, 'no native certified snapshot: do not export as finished');
  const ledger = mapped('objects', head.ledgerDigest);
  const certificate = mapped('snapshots', head.certifiedSnapshotDigest);
  const evidence = mapped('lean-evidence', certificate.leanEvidenceSnapshotDigest);
  const graph = json('.tex2lean/proof-graph.json');
  assert.equal(digest('paper-proof-ledger/1', ledger), head.ledgerDigest);
  assert.equal(digest('certified-mapping-snapshot/1', certificate, ['created']), head.certifiedSnapshotDigest);
  assert.equal(digest('lean-evidence-snapshot/1', evidence), certificate.leanEvidenceSnapshotDigest);
  assert.equal(digest('proof-graph/6', graph), certificate.graphDigest, 'shared graph no longer matches this certificate; refresh target before export');
  assert.equal(certificate.targetId, spec.id);
  assert.equal(certificate.ledgerDigest, head.ledgerDigest);
  assert.equal(certificate.targetVersionId, ledger.target.activeVersionId);
  assert.equal(certificate.created.by, 'proof-graph-reconciliation');
  assert.equal(graph.target.key, 'label:' + label);
  assert.equal(graph.mappingDigest, head.ledgerDigest);
  const sources = currentLeanSources(e.repo);
  for (const key of ['sourceFingerprint', 'buildFingerprint', 'dependencyFingerprint']) {
    assert.equal(certificate[key], sources.fingerprint, `${key}: sources changed after certification`);
    assert.equal(evidence[key], sources.fingerprint);
    assert.equal(graph[key], sources.fingerprint);
  }
  assert.equal(evidence.toolchainDigest, digest('lean-toolchain/1', read('lean-toolchain').toString('utf8')));
  const blueprint = json(spec.blueprint), bundle = blueprint.bundle;
  assert(!blueprint.inProgress, 'blueprint is still in progress');
  assert.equal(bundle.target.label, label);
  assert.equal(blueprint.paperProofMapping.targetId, spec.id);
  const packet = {origin: bundle.origin, files: bundle.files, macros: bundle.macros,
    theoremEnvironments: bundle.theoremEnvironments,
    target: {body: bundle.target.body, start: bundle.target.start, end: bundle.target.end, environment: bundle.target.environment}};
  assert.equal(digest('paper-packet/1', packet), certificate.paperPacketDigest);
  const paperFiles = new Map(bundle.files.map(f => [f, read(f).toString('utf8')]));
  assert(paperFiles.get(bundle.target.start.file).includes(bundle.target.body), 'paper target changed');
  for (const macro of bundle.macros || []) assert(paperFiles.get(macro.source.file)?.includes(macro.declaration), 'paper macro changed');
  const receipt = ledger.claimSetReceipts.find(r => r.id === ledger.activeClaimSetReceiptId);
  const inventory = ledger.surfaceInventories.find(i => i.id === ledger.activeSurfaceInventoryId);
  assert.equal(receipt.targetVersionId, certificate.targetVersionId);
  assert.equal(receipt.paperPacketDigest, certificate.paperPacketDigest);
  assert.equal(inventory.targetVersionId, certificate.targetVersionId);
  exactSet(receipt.claimVersionIds, ledger.claims.map(c => {assert.equal(c.role, 'reportable'); return c.activeVersionId;}), 'claim receipt membership');
  const formal = ledger.plans.filter(p => p.disposition === 'formalize');
  const excluded = ledger.plans.filter(p => p.disposition === 'exclude');
  assert.equal(formal.length, spec.mathematicalClaims);
  assert.equal(ledger.plans.length, formal.length + excluded.length);
  exactSet(excluded.map(p => p.claimVersionId), spec.excluded, 'only the two reviewed counting metadata exclusions are allowed');
  assert.equal(ledger.claims.length, formal.length + excluded.length);
  const obligationIds = formal.map(p => {assert.equal(p.requirements.allOf.length, 1); assert.equal(p.requirements.allOf[0].anyOf.length, 1); return p.requirements.allOf[0].anyOf[0];});
  const activeBindings = currentBindings(ledger);
  assert.equal(new Set(ledger.bindings.map(b => b.id)).size, ledger.bindings.length, 'duplicate historical binding ID');
  exactSet(activeBindings.map(b => b.obligationId), obligationIds, 'one active binding per mathematical obligation');
  exactSet(inventory.declarations.map(tuple), activeBindings.map(tuple), 'exact selected inventory');
  assert.equal(evidence.interfaceReceipts.length, activeBindings.length);
  const bindingRecords = [];
  for (const binding of activeBindings) {
    assert.equal(binding.status, 'verified');
    assert.equal(binding.leanEvidenceSnapshotId, certificate.leanEvidenceSnapshotDigest);
    const r = evidence.interfaceReceipts.find(x => x.bindingId === binding.id);
    assert(r); assert.equal(r.declaration, binding.declaration); assert.deepEqual(r.receipt, binding.receipt);
    assert.equal(digest('lean-interface-receipt/1', r.receipt), r.receiptDigest);
    assert.equal(r.receipt.toolchainDigest, evidence.toolchainDigest);
    assert(ledger.appliedDecisionIds.includes(binding.semanticApprovalDecisionId));
    assert(ledger.appliedDecisionIds.includes(binding.verifiedByDecisionId));
    const approval = mapped('decisions', binding.semanticApprovalDecisionId);
    assert.equal(approval.id, binding.semanticApprovalDecisionId); assert.equal(approval.kind, 'put-binding');
    assert.equal(approval.actor, 'author'); assert.equal(approval.binding.id, binding.id);
    assert.equal(approval.binding.declaration, binding.declaration); assert.equal(approval.binding.obligationId, binding.obligationId);
    const decision = mapped('decisions', binding.verifiedByDecisionId);
    const publication = mapped('publications', binding.verifiedByDecisionId);
    assert.equal(decision.actor, 'validator'); assert.equal(decision.mode, 'automatic'); assert.equal(decision.kind, 'put-binding');
    assert.deepEqual(decision.binding, binding); assert.equal(publication.decisionId, decision.id);
    assert.equal(publication.baseLedgerDigest, decision.baseLedgerDigest);
    for (const key of ['baseLedgerDigest', 'resultingLedgerDigest']) assert.equal(digest('paper-proof-ledger/1', mapped('objects', publication[key])), publication[key]);
    bindingRecords.push({declaration: binding.declaration, bindingId: binding.id, receiptDigest: r.receiptDigest,
      semanticApprovalDecisionId: binding.semanticApprovalDecisionId, semanticReviewProvenance: approval.provenance,
      verifiedByDecisionId: binding.verifiedByDecisionId, verificationProvenance: decision.provenance});
  }
  const handoff = json(spec.handoff + '/handoff.json');
  read(spec.handoff + '/HANDOFF.md');
  assert.equal(handoff.target.label, label); assert.equal(handoff.target.body, bundle.target.body);
  assert(Date.parse(handoff.generatedAt) >= Date.parse(certificate.created.at), 'handoff predates certificate');
  checkHandoffFindings(handoff);
  const handoffLimitationsReview = reviewHandoffLimitations(e, handoff, label, head, certificate, handoffLimitationsPath);
  const progress = handoff.claimProgress; assert(progress, 'handoff lacks certified claim progress');
  exactSet(progress.rows.map(r => r.claimVersionId), receipt.claimVersionIds, 'handoff receipt membership');
  for (const p of formal) {
    const row = progress.rows.find(r => r.claimVersionId === p.claimVersionId);
    assert.equal(row.coverage, 'mapped'); assert.equal(row.proofSnapshot, 'certified'); assert.equal(row.proof, 'proved');
    assert.deepEqual(row.conditions, []); assert.deepEqual(row.nearestBlockers, []);
    const binding = activeBindings.find(b => b.obligationId === p.requirements.allOf[0].anyOf[0]);
    assert.deepEqual(row.declarations, [binding.declaration]);
  }
  for (const p of excluded) {
    const row = progress.rows.find(r => r.claimVersionId === p.claimVersionId);
    assert.equal(row.coverage, 'excluded'); assert.equal(row.proof, 'not-applicable'); assert.equal(row.proofSnapshot, 'none');
    assert(!('requirements' in p)); assert(p.reason && p.evidenceIds.length);
    for (const id of p.evidenceIds) assert(ledger.evidence.some(item => item.id === id));
  }
  // Do not turn counting's truthful false aggregate flags into true.
  assert.equal(progress.complete, excluded.length === 0);
  assert.equal(progress.whollyProved, excluded.length === 0);
  for (const file of ['formalize.json', 'lakefile.toml', 'lake-manifest.json', 'AGENTS.md', 'scripts/capstones.txt', 'paper/SHA256SUMS']) read(file);
  e.stable(); assert.deepEqual(currentLeanSources(e.repo), sources, 'source inventory changed during export inspection');
  return {environment: e, report: {schema: 'antichain.native-target-export/1', exportedAtUTC: new Date().toISOString(),
    purpose: 'Exact-byte preservation and independent consistency checks; not native certification or a new proof verdict',
    targetLabel: label, head, certificate, observedHandoff: {generatedAt: handoff.generatedAt,
      headline: handoff.correspondence.headline.verdict, assumptions: handoff.assumptions.verdict,
      probability: handoff.probability.verdict, unknowns: handoff.unknowns,
      complete: progress.complete, whollyProved: progress.whollyProved,
      proofCounts: progress.proofCounts, coverageCounts: progress.coverageCounts},
    ...(handoffLimitationsReview ? {handoffLimitationsReview} : {}),
    bindings: bindingRecords, excludedMetadata: excluded.map(p => ({...p, text: ledger.claimVersions.find(v => v.id === p.claimVersionId)?.text})),
    leanSourceSnapshot: sources, nativeDigestChecks: ['ledger', 'certificate (created omitted)', 'lean evidence', 'complete graph', 'paper packet', 'interface receipts', 'toolchain', 'verification publication predecessor/successor ledgers'],
    limitations: ['Does not run the compiler or native validator.', 'Does not authenticate the author role as human review.',
      'Selected paper/configuration bytes and all Lean source hashes are preserved; pair this export with the matching Git source tree. External dependency binaries are not independently hashed.',
      'Full immutable mapping history must also be exported once after all selected runs.']}};
}

function writeExport(e, report, output, extraStabilityCheck = () => {}) {
  const parent = fs.realpathSync(path.dirname(path.resolve(output)));
  const destination = path.join(parent, path.basename(output));
  assert(destination !== e.repo && !destination.startsWith(e.repo + path.sep), 'output must be outside the repository');
  assert(!fs.existsSync(destination), 'refusing to overwrite an earlier export');
  const stable = () => {
    e.stable();
    if (report.leanSourceSnapshot) assert.deepEqual(currentLeanSources(e.repo), report.leanSourceSnapshot, 'Lean source inventory changed after inspection');
    extraStabilityCheck();
  };
  stable(); fs.mkdirSync(destination);
  const files = [];
  for (const [relative, bytes] of e.files) {
    const file = path.join(destination, relative); fs.mkdirSync(path.dirname(file), {recursive: true});
    fs.writeFileSync(file, bytes, {flag: 'wx'});
    assert(fs.readFileSync(file).equals(bytes), 'copied bytes differ');
    files.push({path: relative, bytes: bytes.length, rawSHA256: rawHash(bytes)});
  }
  // A failed race check leaves copies for inspection, but no completed export manifest.
  stable();
  fs.writeFileSync(path.join(destination, 'EXPORT.json'), JSON.stringify({...report, files}, null, 2) + '\n', {flag: 'wx'});
  return {output: destination, fileCount: files.length, bytes: files.reduce((n, f) => n + f.bytes, 0), manifestSHA256: rawHash(fs.readFileSync(path.join(destination, 'EXPORT.json')))};
}

function exportHistory(repoArg, output) {
  const e = environment(repoArg), root = '.tex2lean/mapping';
  function paths() {
    const result = [];
    function walk(relative) {
      for (const item of fs.readdirSync(path.join(e.repo, relative), {withFileTypes: true})) {
        const child = path.join(relative, item.name); assert(!fs.lstatSync(path.join(e.repo, child)).isSymbolicLink(), 'symlinked mapping artifact');
        if (item.isDirectory()) walk(child); else result.push(child);
      }
    }
    walk(root); return result.sort();
  }
  const before = paths();
  assert(!before.some(f => f.startsWith(root + '/locks/')), 'mapping lease/lock exists; wait until all workers are idle');
  for (const file of before) e.read(file);
  e.stable(); assert.deepEqual(paths(), before, 'mapping inventory changed');
  return writeExport(e, {schema: 'antichain.native-mapping-history-export/1', exportedAtUTC: new Date().toISOString(),
    purpose: 'All immutable native mapping records preserved byte-for-byte; no decisions or statuses synthesized',
    validation: 'Raw-byte inventory and before/after equality; target certificate checks are in the separate target exports'}, output,
    () => assert.deepEqual(paths(), before, 'mapping inventory changed during copying'));
}

if (require.main === module) {
  try {
    const [mode, ...args] = process.argv.slice(2), options = {};
    for (let i = 0; i < args.length; i += 2) {assert(args[i]?.startsWith('--') && args[i + 1], 'expected --key value'); options[args[i].slice(2)] = args[i + 1];}
    assert(options.repo, '--repo is required');
    if (mode === 'target' || mode === 'check-target') {
      assert(options.label, '--label is required'); const checked = inspectTarget(options.repo, options.label, {handoffLimitationsPath: options['handoff-limitations']});
      if (mode === 'check-target') console.log(JSON.stringify({consistencyChecks: 'passed', ...checked.report}, null, 2));
      else {assert(options.out, '--out is required'); console.log(JSON.stringify(writeExport(checked.environment, checked.report, options.out), null, 2));}
    } else if (mode === 'history') {assert(!options['handoff-limitations'], 'limitations review applies only to a target'); assert(options.out, '--out is required'); console.log(JSON.stringify(exportHistory(options.repo, options.out), null, 2));}
    else throw new Error('use target, check-target, or history');
  } catch (error) {console.error('EXPORT REFUSED: ' + error.message); process.exitCode = 1;}
}
module.exports = {canonical, digest, rawHash, specs, currentBindings, currentLeanSources, inspectTarget, writeExport, exportHistory, checkHandoffFindings, reviewHandoffLimitations};
