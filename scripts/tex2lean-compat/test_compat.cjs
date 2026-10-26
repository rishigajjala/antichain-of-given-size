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
vm.runInContext(between('function yX(', 'function vX('), context);
vm.runInContext(between('function vX(', 'function kX('), context);
vm.runInContext(between('function XA(e,t,n)', 'var ph='), context);
vm.runInContext(between('function TX(', 'function EX('), context);
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

const theoremClaims = ['AntichainOfGivenSize.firstClaim', 'AntichainOfGivenSize.secondClaim'];
const theoremSource = [
  'namespace AntichainOfGivenSize',
  'theorem firstClaim : True := trivial',
  'theorem secondClaim : True := trivial',
  'end AntichainOfGivenSize',
  '#print axioms AntichainOfGivenSize.firstClaim',
  '#print axioms AntichainOfGivenSize.secondClaim',
].join('\n');
const repairedTheorem = context.pg(theoremSource, 'AntichainOfGivenSize', 'AntichainOfGivenSize/Model/Theorem.lean', theoremClaims);
assert(!repairedTheorem.includes('#surplusIn'));
for (const claim of theoremClaims) {
  assert(repairedTheorem.includes('#modelClosureOfType ' + claim));
  assert(repairedTheorem.includes('#print axioms ' + claim));
}
assert.equal(context.pg(repairedTheorem, 'AntichainOfGivenSize', 'AntichainOfGivenSize/Model/Theorem.lean', theoremClaims), repairedTheorem);
assert.deepEqual(Array.from(context.yX('AntichainOfGivenSize', 'AntichainOfGivenSize/Model/Program.lean')), [
  '#programSeal AntichainOfGivenSize.Program', '#executableModule AntichainOfGivenSize.Model.Program',
]);
const globalAudit = context.XA('AntichainOfGivenSize', [
  'AntichainOfGivenSize.Model.Theorem', 'AntichainOfGivenSize.Paper.Results',
], theoremClaims);
assert(globalAudit.includes('#surplusIn AntichainOfGivenSize.Model from ' + theoremClaims.join(' ')));
assert(globalAudit.includes('import AntichainOfGivenSize.Paper.Results'));
assert.equal((globalAudit.match(/#surplusIn/g) ?? []).length, 1);
assert(context.TX('AntichainOfGivenSize').includes('import AntichainOfGivenSize.Meta.Audit'));
const sealContext = vm.createContext({p3:6, Lhe:['programSeal', 'executableModule', 'surplusIn']});
vm.runInContext(between('function Whe(', 'function Uhe('), sealContext);
assert.equal(sealContext.Whe({files:['AntichainOfGivenSize/Model/Theorem.lean'], sealCommands:['programSeal', 'executableModule', 'surplusIn']}).ok, true);
assert.equal(sealContext.Whe({files:['AntichainOfGivenSize/Model/Theorem.lean'], sealCommands:['programSeal', 'executableModule']}).ok, false);

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
    planningCalls.push({library, options, audit:context.XA(library, options.modules, options.headlines)});
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
  assert(planningCalls[0].audit.includes('#surplusIn AntichainOfGivenSize.Model from AntichainOfGivenSize.previousClaim AntichainOfGivenSize.membership AntichainOfGivenSize.currentClaim'));
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

function recoveryHarness() {
  const files = new Map(), dirs = new Set(['/']), removed = [], hooks = {};
  const uri = value => ({fsPath:value});
  const missing = file => Object.assign(new Error(`missing ${file}`), {code:'ENOENT'});
  function mkdir(dir) {
    for (let p = dir; !dirs.has(p); p = path.posix.dirname(p)) dirs.add(p);
  }
  function put(file, bytes) { mkdir(path.posix.dirname(file)); files.set(file, Buffer.from(bytes)); }
  const A = {
    async list(dir) {
      await hooks.list?.(dir.fsPath);
      if (!dirs.has(dir.fsPath)) throw missing(dir.fsPath);
      const children = new Map();
      for (const [items, kind] of [[dirs,'directory'], [files.keys(),'file']])
        for (const file of items) if (file !== dir.fsPath && path.posix.dirname(file) === dir.fsPath)
          children.set(path.posix.basename(file), kind);
      return [...children].sort(([a],[b]) => a.localeCompare(b));
    },
    async stat(file) {
      await hooks.stat?.(file.fsPath);
      if (!dirs.has(file.fsPath) && !files.has(file.fsPath)) throw missing(file.fsPath);
      return {symlink:false};
    },
    async read(file) {
      await hooks.read?.(file.fsPath);
      if (!files.has(file.fsPath)) throw missing(file.fsPath);
      return files.get(file.fsPath);
    },
    async write(file, bytes) { put(file.fsPath, bytes); },
    async mkdirp(dir) { mkdir(dir.fsPath); },
    async remove(file) {
      await hooks.remove?.(file.fsPath);
      if (!files.has(file.fsPath)) throw missing(file.fsPath);
      files.delete(file.fsPath); removed.push(file.fsPath);
    },
  };
  const ctx = vm.createContext({
    A, Buffer, Uint8Array, TextDecoder, hi:path.posix, fg:'scratch',
    x:(base,...parts) => uri(path.posix.resolve(base.fsPath,...parts)),
    my:'tex2lean.surface-transaction/1', g:()=>{}, W:()=>{}, du:async()=>{},
    Br:async(file, record) => {
      await hooks.beforeJournalWrite?.(file.fsPath,record);
      put(file.fsPath, JSON.stringify(record));
      await hooks.afterJournalWrite?.(file.fsPath,record);
    },
  });
  vm.runInContext(between('var compatLiveTransactions =', 'function LW('), ctx);
  vm.runInContext(between('async function Vk(', 'var my,'), ctx);
  return {ctx, files, dirs, removed, hooks, put, mkdir, uri};
}
const recoveryRoot = {fsPath:'/repo'};
const recoveryConfig = {leanProjectPath:'.', outputDirectory:'.blueprint'};
function writeOrphan(h, name, snapshot, extra={}) {
  const file = `/repo/.blueprint/transactions/${name}.json`;
  h.put(file, JSON.stringify({schema:'tex2lean.surface-transaction/1', id:name,
    targetKey:'test', state:'open', files:Object.fromEntries(Object.entries(snapshot)
      .map(([key,value]) => [key,Buffer.from(value).toString('base64')])), ...extra}));
  return file;
}
async function checkRecoverySafety() {
  // A descendant ENOENT is not evidence that the root directory was missing.
  {
    const h = recoveryHarness(); h.put('/repo/Main.lean','original');
    h.hooks.read = async file => { if (file === '/repo/Main.lean') { h.files.delete(file); throw Object.assign(new Error('snapshot race'),{code:'ENOENT'}); } };
    await assert.rejects(h.ctx.rf(recoveryRoot,recoveryConfig,'main'), /snapshot race/);
    assert.equal(h.ctx.compatLiveTransactions.size,0);
    assert(![...h.files.keys()].some(file => file.includes('/transactions/')));
    assert.equal(h.removed.length,0);
  }
  // Exclude only native atomic-write files and the configured journal directory.
  {
    const h = recoveryHarness(); h.put('/repo/Main.lean','original');
    h.put('/repo/.blueprint/checkpoint.json.writing-1793045405104-dda99cf590902','temporary');
    h.put('/repo/.blueprint/checkpoint.json.writing-handwritten','authored');
    h.put('/repo/.blueprint/checkpoint.json','stable');
    h.put('/repo/custom-output/transactions/old.json','old journal');
    h.hooks.stat = async file => { if (/\.writing-1793/.test(file)) throw new Error('temporary must not be inspected'); };
    const tx = await h.ctx.rf(recoveryRoot,{...recoveryConfig,outputDirectory:'custom-output'},'main');
    assert(tx.before.files.has('.blueprint/checkpoint.json'));
    assert(tx.before.files.has('.blueprint/checkpoint.json.writing-handwritten'));
    assert(![...tx.before.files.keys()].some(file => /\.writing-1793|custom-output\/transactions/.test(file)));
    await h.ctx.of(tx); assert.equal(h.ctx.compatLiveTransactions.size,0);
  }
  // Reject the reproduced legacy empty journal before any project mutation.
  {
    const h = recoveryHarness(); h.put('/repo/Main.lean','keep');
    const bad = writeOrphan(h,'bad',{});
    await assert.rejects(h.ctx.af(recoveryRoot,recoveryConfig), /empty unscoped/);
    assert.equal(h.files.get('/repo/Main.lean').toString(),'keep');
    assert(h.files.has(bad)); assert.equal(h.removed.length,0);
    await assert.rejects(h.ctx.nf(recoveryRoot,{files:new Map()}), /empty unscoped/);
  }
  // Valid scoped empty snapshots still remove newly created scoped files only.
  {
    const h = recoveryHarness(); h.put('/repo/Main.lean','keep'); h.put('/repo/New.lean','new');
    await h.ctx._W(recoveryRoot,{files:new Map(),scope:['New.lean']});
    assert(!h.files.has('/repo/New.lean')); assert(h.files.has('/repo/Main.lean'));
  }
  // Valid missing/empty baselines are explicit and survive prepare + reload.
  for (const initiallyMissing of [true,false]) {
    const h = recoveryHarness(); if (!initiallyMissing) h.mkdir('/repo');
    const tx = await h.ctx.rf(recoveryRoot,recoveryConfig,'new-project');
    assert.equal(tx.before.emptySnapshotReason, initiallyMissing?'project-missing':'project-empty');
    await h.ctx.Vk(tx);
    const saved = JSON.parse(h.files.get(tx.journal.fsPath));
    assert.equal(saved.emptySnapshotReason,tx.before.emptySnapshotReason);
    h.put('/repo/New.lean','new');
    h.ctx.compatLiveTransactions.clear(); // Simulate a fresh process after interruption.
    assert.equal(await h.ctx.af(recoveryRoot,recoveryConfig),1);
    assert(!h.files.has('/repo/New.lean')); assert(!h.files.has(tx.journal.fsPath));
  }
  // An active journal is protected even while its atomic publication is awaited.
  {
    const h = recoveryHarness(); h.put('/repo/Main.lean','original');
    let sawPublication = false;
    h.hooks.afterJournalWrite = async (_file,record) => {
      if (record.state !== 'open') return;
      sawPublication = true;
      assert.equal(h.ctx.compatLiveTransactions.size,1);
      assert.equal(await h.ctx.af(recoveryRoot,recoveryConfig),0);
    };
    const tx = await h.ctx.rf(recoveryRoot,recoveryConfig,'main');
    assert(sawPublication); h.put('/repo/Main.lean','changed');
    assert.equal(await h.ctx.af(recoveryRoot,recoveryConfig),0);
    assert.equal(h.files.get('/repo/Main.lean').toString(),'changed');
    await h.ctx.Vt(tx);
    assert.equal(h.files.get('/repo/Main.lean').toString(),'original');
    assert.equal(h.ctx.compatLiveTransactions.size,0);
  }
  // Preserve ordinary rollback, and serialize two recovery callers and a new open.
  {
    const h = recoveryHarness(); h.put('/repo/Main.lean','changed'); h.put('/repo/New.lean','new');
    const journal = writeOrphan(h,'old',{'Main.lean':'original','Deleted.lean':'restored'});
    let release; const gate = new Promise(resolve => {release=resolve;});
    let entered; const started = new Promise(resolve => {entered=resolve;});
    let reads = 0;
    h.hooks.read = async file => { if (file === journal) {reads++; entered(); await gate;} };
    const a = h.ctx.af(recoveryRoot,recoveryConfig); await started;
    const b = h.ctx.af(recoveryRoot,recoveryConfig);
    const opening = h.ctx.rf(recoveryRoot,recoveryConfig,'next');
    assert.equal(h.ctx.compatLiveTransactions.size,0);
    release(); assert.equal(await a,1); assert.equal(await b,1);
    const tx = await opening;
    assert.equal(reads,1);
    assert.equal(Buffer.from(tx.before.files.get('Main.lean')).toString(),'original');
    assert(tx.before.files.has('Deleted.lean')); assert(!tx.before.files.has('New.lean'));
    await h.ctx.of(tx);
  }
  // A legacy snapshot cannot resurrect transaction journals or atomic temporaries.
  {
    const h = recoveryHarness(); h.put('/repo/Main.lean','changed');
    writeOrphan(h,'legacy',{'Main.lean':'original',
      '.blueprint/transactions/resurrected.json':'not a source file',
      '.blueprint/checkpoint.json.writing-1793045405104-dda99cf590902':'temporary'});
    assert.equal(await h.ctx.af(recoveryRoot,recoveryConfig),1);
    assert.equal(h.files.get('/repo/Main.lean').toString(),'original');
    assert(![...h.files.keys()].some(file => /resurrected|\.writing-/.test(file)));
  }
  // An ambiguous journal publication failure stays protected until process exit.
  {
    const h = recoveryHarness(); h.put('/repo/Main.lean','keep');
    h.hooks.afterJournalWrite = async()=>{throw new Error('publication interrupted');};
    await assert.rejects(h.ctx.rf(recoveryRoot,recoveryConfig,'main'), /publication interrupted/);
    assert.equal(h.ctx.compatLiveTransactions.size,1);
    assert.equal(await h.ctx.af(recoveryRoot,recoveryConfig),0);
    assert.equal(h.files.get('/repo/Main.lean').toString(),'keep');
  }
  // Only deletion ENOENT is harmless; other failures retain the live journal.
  {
    const h = recoveryHarness(); h.put('/repo/Main.lean','original');
    const tx = await h.ctx.rf(recoveryRoot,recoveryConfig,'main'); h.put('/repo/New.lean','new');
    h.hooks.remove = async file => { if (file === '/repo/New.lean') {
      h.files.delete(file); throw Object.assign(new Error('already gone'),{code:'ENOENT'});
    }};
    await h.ctx.Vt(tx); assert(!h.files.has('/repo/New.lean'));
    const tx2 = await h.ctx.rf(recoveryRoot,recoveryConfig,'main2'); h.put('/repo/New.lean','new');
    h.hooks.remove = async file => { if (file === '/repo/New.lean') throw Object.assign(new Error('denied'),{code:'EACCES'}); };
    await assert.rejects(h.ctx.Vt(tx2), /denied/);
    assert(h.ctx.compatLiveTransactions.has(tx2.journal.fsPath));
    assert(h.files.has(tx2.journal.fsPath));
  }
  // Busy checkpoint refresh must not even call recovery or scan checkpoints.
  {
    let noted = 0, cleared = 0;
    const busy = vm.createContext({Ft:()=>recoveryRoot,go:()=>1,
      me:()=>{throw new Error('must return before configuration/recovery');},
      W:()=>{throw new Error('unexpected refresh failure');}});
    vm.runInContext(between('async function Pf(', 'async function '),busy);
    await busy.Pf({setResumable:()=>{cleared++;},noteCheckpointsRead:()=>{noted++;}});
    assert.equal(cleared,1); assert.equal(noted,1);
  }
  // A journal can remain live between worker shutdown and the planning commit.
  {
    let noted = 0, cleared = 0;
    const busy = vm.createContext({Ft:()=>recoveryRoot,go:()=>0,me:()=>recoveryConfig,
      x:()=>recoveryRoot,compatHasLiveTransaction:()=>true,
      af:()=>{throw new Error('live transaction must not enter recovery');},
      W:()=>{throw new Error('unexpected refresh failure');}});
    vm.runInContext(between('async function Pf(', 'async function '),busy);
    await busy.Pf({setResumable:()=>{cleared++;},noteCheckpointsRead:()=>{noted++;}});
    assert.equal(cleared,1); assert.equal(noted,1);
  }
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
  await checkRecoverySafety();
  await checkProvider({}, 'gpt-6-astra', 'high');
  await checkProvider({model:'gpt-6-sol', effort:'medium'}, 'gpt-6-sol', 'medium');
  await checkProvider({model:'gpt-6-astra', effort:'high'}, 'gpt-6-astra', 'high');
  console.log('PASS: library-only audit imports; configured/tier worker effort; structured request/config effort; models preserved; ModelClosure classifies private names and expands only project inductive constructors without changing lookup keys; all diagnostic files checked with peak concurrency two; planning retains registered and current claims without duplicates; inventory excludes only exact known root helper names and retains authored/nested Lean files; all three handoff gates receive absolute read-only source access and honest log inventory, with unknown verdicts preserved; per-file closure/axiom checks retained and global surplus checking remains mandatory over all registered/current claims; recovery rejects nested snapshot failures and unverified empty journals, excludes native temporary/journal paths, protects live transactions, serializes recovery/open, and preserves valid rollback and error handling. No Lean or workflow started.');
})().catch(error => {console.error(error); process.exitCode = 1;});
