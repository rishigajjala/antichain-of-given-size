// Test the actual patched helpers/provider in isolated VM contexts.
// No CLI bootstrap, Codex child, network, project state, or real FS operations.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
assert(process.argv[2], 'Usage: node test_compat.cjs /path/to/output/out/cli.cjs');
const source = fs.readFileSync(process.argv[2], 'utf8');
function between(start, end) {
  const at = source.indexOf(start);
  assert(at >= 0, start);
  const stop = source.indexOf(end, at + start.length);
  assert(stop > at, end);
  return source.slice(at, stop);
}
const context = vm.createContext({
  hn: (root, file) => file,
  rm: (_kind, fallback) => fallback,
});
vm.runInContext(between('function uhe(e,t,n)', 'function _6('), context);
vm.runInContext(between('function nk(e,t,n)', 'function _h('), context);
vm.runInContext(between('function BD(e)', 'async function qD('), context);
const closureSource = context.BD('AntichainOfGivenSize');
assert(closureSource.includes('(`AntichainOfGivenSize).isPrefixOf (Lean.privateToUserName c) then acc.insert c else acc'));
assert(!closureSource.includes('(`AntichainOfGivenSize).isPrefixOf c then acc.insert c else acc'));
assert(closureSource.includes('let seen := seen.insert c'));
assert(closureSource.includes('match env.find? c with'));
assert(closureSource.includes('moduleOf env c'));
assert(closureSource.includes([
  '        let next := ci.type.getUsedConstants.toList',
  '          ++ (match ci.value? with | some v => v.getUsedConstants.toList | none => [])',
  '          ++ (match ci with',
  '              | .inductInfo iv =>',
  '                if (`AntichainOfGivenSize).isPrefixOf (Lean.privateToUserName c) then iv.ctors else []',
  '              | _ => [])',
  '        closureAux env seen (next ++ rest) acc',
].join('\n')));
const modules = context.uhe({}, [
  'AntichainOfGivenSize/Model/Theorem.lean',
  'AntichainOfGivenSize/Paper/Results.lean',
  'AntichainOfGivenSize/Analysis/AttainableCountProof.lean',
  'AntichainOfGivenSize/Meta/Audit.lean',
  'AntichainOfGivenSizeTest/CostSealBreaches.lean',
  'AntichainOfGivenSizeExtra/Unrelated.lean',
  'scripts/CheckAxioms.lean', 'scripts/CheckPaperStatements.lean',
  'AntichainOfGivenSize.lean',
], 'AntichainOfGivenSize');
assert.deepEqual(Array.from(modules), [
  'AntichainOfGivenSize.Analysis.AttainableCountProof',
  'AntichainOfGivenSize.Model.Theorem',
  'AntichainOfGivenSize.Paper.Results',
]);
const cfg = {codexModel: 'gpt-6-astra', anthropicEffort: 'high'};
assert.deepEqual(Array.from(context.nk('codex', cfg)), [
  '--model', 'gpt-6-astra', '-c', 'model_reasoning_effort="high"',
]);
assert.deepEqual(Array.from(context.nk('codex', cfg, {model:'gpt-6-sol', effort:'low'})), [
  '--model', 'gpt-6-sol', '-c', 'model_reasoning_effort="low"',
]);
assert.deepEqual(Array.from(context.nk('codex', cfg, {model:'gpt-6-astra'})), [
  '--model', 'gpt-6-astra', '-c', 'model_reasoning_effort="high"',
]);

const inspectedFiles = [];
let diagnosticsRunning = 0;
let diagnosticsPeak = 0;
const diagnosticsContext = vm.createContext({
  x: () => ({fsPath:'/isolated-test'}),
  yv: require('node:crypto'), Hc: new Map(), Cr: /theorem/, g: () => {},
  mh: async (_root, file) => {
    inspectedFiles.push(file);
    diagnosticsPeak = Math.max(diagnosticsPeak, ++diagnosticsRunning);
    await new Promise(resolve => setImmediate(resolve));
    diagnosticsRunning--;
    return {succeeded:true, sorry:[], diagnostics:[]};
  },
});
vm.runInContext(between('async function $C(', 'function kQ('), diagnosticsContext);
async function checkDiagnostics() {
  const files = ['A.lean', 'B.lean', 'C.lean', 'D.lean', 'E.lean'];
  const modules = [...files, 'notes.txt'].map(file => ({
    file, module:file.split('.')[0], digest:'test', imports:[],
  }));
  const result = await diagnosticsContext.$C({}, '.', {modules, statements:[], flags:[]});
  assert.equal(diagnosticsPeak, 2);
  assert.deepEqual(inspectedFiles.sort(), files);
  assert.equal(result.leanDiagnostics.complete, true);
  assert.deepEqual(Array.from(result.leanDiagnostics.certifiedFiles), files);
  assert.equal(result.leanDiagnostics.failedFiles.length, 0);
}

const planningCalls = [];
const planningWorkspace = {fsPath:'/isolated-workspace'};
const planningConfig = {leanProjectPath:'lean'};
const planningContext = vm.createContext({
  x: () => ({fsPath:'/isolated-workspace/lean'}),
  Vc: async () => ({complete:true, files:[
    'AntichainOfGivenSize/Model/Theorem.lean',
    'AntichainOfGivenSize/Paper/Results.lean',
  ]}),
  uhe: context.uhe,
  k8: async (workspace, config) => {
    assert.equal(workspace, planningWorkspace);
    assert.equal(config, planningConfig);
    return ['AntichainOfGivenSize.previousClaim', 'AntichainOfGivenSize.membership'];
  },
  qD: async (_root, library, options) => {
    planningCalls.push({library, options});
    return {rewritten:[], edited:[]};
  },
  hn: (_root, file) => file, lv: async () => {}, g: () => {}, W: () => {},
});
vm.runInContext(between('async function IS(', 'async function B6('), planningContext);
async function checkPlanningClaims() {
  await planningContext.IS(planningWorkspace, planningConfig, 'AntichainOfGivenSize', [
    'AntichainOfGivenSize.currentClaim', 'AntichainOfGivenSize.previousClaim', '',
  ]);
  assert.equal(planningCalls.length, 1);
  assert.equal(planningCalls[0].library, 'AntichainOfGivenSize');
  assert.deepEqual(Array.from(planningCalls[0].options.headlines), [
    'AntichainOfGivenSize.previousClaim', 'AntichainOfGivenSize.membership',
    'AntichainOfGivenSize.currentClaim',
  ]);
  assert.deepEqual(Array.from(planningCalls[0].options.modules), [
    'AntichainOfGivenSize.Model.Theorem', 'AntichainOfGivenSize.Paper.Results',
  ]);
}

const helperId = 'de1e0b617cc84f0db5e40c47848da14f';
const helperFamilies = ['inspection', 'axioms', 'public-refutation', 'refutation', 'interfaces', 'interface-values'];
const reservedNames = helperFamilies.map(family => `.tex2lean-${family}-${helperId}.lean`)
  .concat('.tex2lean-side.lean');
const authoredNames = [
  'Paper.lean', '.author.lean', '.tex2lean-inspection-handwritten.lean',
  `.tex2lean-unknown-${helperId}.lean`, `.tex2lean-inspection-${helperId}.lean.backup.lean`,
];
const inventoryTree = new Map([
  ['/mock-project', [
    ...reservedNames.concat(authoredNames).map(name => [name, 'file']),
    ['AntichainOfGivenSize', 'directory'], ['notes.txt', 'file'],
  ]],
  ['/mock-project/AntichainOfGivenSize', [
    ['Theorem.lean', 'file'], ['Model', 'directory'],
    [reservedNames[0], 'file'],
  ]],
  ['/mock-project/AntichainOfGivenSize/Model', [['Definitions.lean', 'file']]],
]);
const inventoryContext = vm.createContext({
  fg:'scratch',
  x:(root, name) => ({fsPath:root.fsPath + '/' + name}),
  A:{
    list:async root => {
      assert(inventoryTree.has(root.fsPath), `Unexpected directory: ${root.fsPath}`);
      return inventoryTree.get(root.fsPath);
    },
    stat:async () => ({symlink:false}),
  },
});
vm.runInContext(between('async function Vc(', 'function FQ('), inventoryContext);
async function checkInventory() {
  const result = await inventoryContext.Vc({fsPath:'/mock-project'});
  assert.equal(result.complete, true);
  const kept = Array.from(result.files, file => file.fsPath).sort();
  assert.deepEqual(kept, [
    ...authoredNames.map(name => '/mock-project/' + name),
    '/mock-project/AntichainOfGivenSize/Theorem.lean',
    '/mock-project/AntichainOfGivenSize/Model/Definitions.lean',
    '/mock-project/AntichainOfGivenSize/' + reservedNames[0],
  ].sort());
  for (const name of reservedNames) assert(!kept.includes('/mock-project/' + name));
}

const handoffRequests = [];
const handoffContext = vm.createContext({
  x:(root, name) => ({fsPath:root.fsPath + '/' + name}),
  A:{
    list:async root => {
      if (root.fsPath.endsWith('/missing')) throw new Error('not found');
      if (root.fsPath.endsWith('/empty')) return [];
      return [['axioms.txt', 'file'], ['paper-statements.txt', 'file']];
    },
    read:async file => Buffer.from(file.fsPath.endsWith('axioms.txt') ? 'Recorded axiom output' : ''),
  },
  HG:() => 'ORIGINAL_SHARED_AUDIT_PROMPT', mde:() => '\nCAPTURED_AXIOM_OUTPUT',
  g:() => {}, GG:() => 'correspondence request', KG:() => 'assumption request',
  VG:() => 'probability request', dd:() => [], BG:{}, qG:{}, zG:{},
  St:() => ({model:'gpt-6-astra', effort:'high'}), fde:() => [],
  It:async (_context, label, request) => {
    handoffRequests.push({label, request});
    if (label === 'Final audit writer') return {narrative:'Preserved reader findings.'};
    return {reader:label, verdict:'unknown'};
  },
});
vm.runInContext(between('async function compatHandoffSourceAccess(', 'function fde('), handoffContext);
async function checkHandoffEvidence() {
  const workspace = {fsPath:'/absolute/repo'};
  const project = {fsPath:'/absolute/repo/lean'};
  const paper = {fsPath:'/absolute/repo/paper/main.tex'};
  const verification = {fsPath:'/absolute/repo/.blueprint/verification'};
  const sourceAccess = await handoffContext.compatHandoffSourceAccess(workspace, project, paper, verification);
  assert(sourceAccess.includes('/absolute/repo/.blueprint/verification/axioms.txt'));
  assert(sourceAccess.includes('/absolute/repo/.blueprint/verification/paper-statements.txt (empty; not evidence of a successful check)'));
  assert(!sourceAccess.includes('/verification/build.txt'));
  const missing = await handoffContext.compatHandoffSourceAccess(workspace, project, paper, {fsPath:'/absolute/repo/missing'});
  assert(missing.includes('could not be listed'));
  assert(!missing.includes('axioms.txt'));
  const empty = await handoffContext.compatHandoffSourceAccess(workspace, project, paper, {fsPath:'/absolute/repo/empty'});
  assert(empty.includes('No verification files or subdirectories were found'));
  const result = await handoffContext.YG({
    sourceAccess, provider:{id:'codex-cli'}, providerLabel:'test provider',
    playbook:{}, bundle:{target:{label:'test-target'}}, inventory:[],
    evidence:{projectPath:'.'}, progress:{report:() => {}},
  });
  assert.equal(handoffRequests.length, 4);
  for (const {request} of handoffRequests.slice(0, 3)) {
    assert(request.system.startsWith('ORIGINAL_SHARED_AUDIT_PROMPT\nCAPTURED_AXIOM_OUTPUT'));
    for (const uri of [workspace, project, paper, verification]) assert(request.system.includes(uri.fsPath));
    assert(request.system.includes('temporary directory'));
    assert(request.system.includes('Read the complete relevant source files'));
    assert(request.system.includes('Use read-only filesystem inspection'));
    assert(request.system.includes('recorded commands, exit status, and source version'));
    assert(request.system.includes('empty; not evidence of a successful check'));
  }
  assert.equal(new Set(handoffRequests.slice(0, 3).map(call => call.request.system)).size, 1);
  assert.equal(result.correspondence.verdict, 'unknown');
  assert.equal(result.assumptions.verdict, 'unknown');
  assert.equal(result.probability.verdict, 'unknown');
  assert(handoffRequests[3].request.system.includes('Do not redo their work or change their verdicts.'));
  assert.equal(result.narrative, 'Preserved reader findings.');
}

const launches = [];
const providerContext = vm.createContext({
  rl: (_kind, command) => ({command, source:'test'}), il: () => true, g: () => {},
  dl: {mkdtemp: async () => '/isolated-test', writeFile: async () => {}, rm: async () => {}},
  av: path, kD: {tmpdir: () => '/tmp'}, oX: x => x, rv: x => x,
  Bc: async options => {launches.push(options); return {code:0, stderr:'', stdout:''};},
  iX: async () => '{"ok":true}', gi: JSON.parse, fD: x => x,
  Io: class extends Error {},
});
vm.runInContext(between('function ete(e)', 'function _h('), providerContext);
// The last brace belongs to the bundle's lazy-initializer wrapper, not the class.
vm.runInContext('var ' + between('sv=class{constructor(t)', ');function RD(').slice(0, -1), providerContext);
async function checkProvider(request, expectedModel, expectedEffort) {
  const p = new providerContext.sv({path:'/no-spawn', model:'gpt-6-astra', effort:'high', timeoutMs:0});
  await p.completeJson({system:'', user:'', schemaName:'test', schema:{}, ...request});
  const args = launches.at(-1).args;
  assert.equal(args[args.indexOf('--model')+1], expectedModel);
  assert.equal(args[args.indexOf('-c')+1], `model_reasoning_effort="${expectedEffort}"`);
  assert(args.includes('--output-schema'));
  assert(args.includes('--sandbox'));
  assert(args.includes('read-only'));
}
(async () => {
  await checkDiagnostics();
  await checkPlanningClaims();
  await checkInventory();
  await checkHandoffEvidence();
  await checkProvider({}, 'gpt-6-astra', 'high');
  await checkProvider({model:'gpt-6-sol', effort:'medium'}, 'gpt-6-sol', 'medium');
  await checkProvider({model:'gpt-6-astra', effort:'high'}, 'gpt-6-astra', 'high');
  console.log('PASS: library-only audit imports; configured/tier worker effort; structured request/config effort; models preserved; ModelClosure classifies private names and expands only project inductive constructors without changing lookup keys; all diagnostic files checked with peak concurrency two; planning retains registered and current claims without duplicates; inventory excludes only exact known root helper names and retains authored/nested Lean files; all three handoff gates receive absolute read-only source access and honest log inventory, with unknown verdicts preserved. No Lean or workflow started.');
})().catch(error => {console.error(error); process.exitCode = 1;});
