'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const vm = require('node:vm');
const crypto = require('node:crypto');
const {patchLifecycleUi} = require('./lifecycle-ui.cjs');
assert(process.argv.length === 3, 'Usage: node test-lifecycle-ui.cjs /path/to/v8/out/cli.cjs');
const source = fs.readFileSync(process.argv[2], 'utf8');
const patched = patchLifecycleUi(source);
const copy = x => JSON.parse(JSON.stringify(x));
function between(s, start, end) {
  const a = s.indexOf(start), b = s.indexOf(end, a + start.length);
  assert(a >= 0 && b > a, `missing native region: ${start}`); return s.slice(a, b);
}
const strict = 'ae&&ae.targetId===_.targetId&&ae.ledgerDigest===z.head.ledgerDigest&&ae.graphDigest===Pt("proof-graph/6",T)&&ae.sourceFingerprint===T.sourceFingerprint&&ae.buildFingerprint===T.buildFingerprint&&ae.dependencyFingerprint===T.dependencyFingerprint';
assert(source.includes(strict) && patched.source.includes(strict), 'strict certificate predicate unchanged');
const untouched = [
  ['native-certification', 'ai=async(F,G=Q', '},qe='],
  ['native-graph-construction', 'function zT(', 'function '],
  ['native-claim-progress', 'function mue(', 'var hue,'],
  ['native-ledger-validation-store', 'function KJ(', 'function XJ('],
  ['native-interface-certifier', 'async function o4(', 'function '],
  ['native-model-closure', 'function BD(', 'async function qD('],
  ['native-cost-seal', 'function ZA(', 'function XA(']
];
const unchanged = {};
for (const [name,start,end] of untouched) {
  const before = between(source,start,end), after = between(patched.source,start,end);
  assert.equal(after,before,name); unchanged[name] = crypto.createHash('sha256').update(before).digest('hex');
}
assert.throws(() => patchLifecycleUi(patched.source), /anchor mismatch/);
assert.throws(() => patchLifecycleUi(source.replace('async answerIfAsked(n){', 'async answerIfAsked(changed){')), /anchor mismatch/);

function baseContext(text) {
  const context = vm.createContext({J2:crypto,Wse:'tex2lean.canonical-json/1',g:()=>{},W:()=>{}});
  vm.runInContext(between(text,'function G0(', 'function Cu('),context);
  if(text.includes('function compatRetainGraphTimestamp('))
    vm.runInContext(between(text,'function compatRetainGraphTimestamp(', 'async function gd('),context);
  return context;
}
async function testChoices() {
  const context = baseContext(patched.source);
  const request = between(patched.source, 'requestChoice(t){', 'answerUnattended(t){');
  const answer = between(patched.source, 'async answerIfAsked(n){', 'unanswerable;async answerFor(');
  vm.runInContext('globalThis.Harness=class {'+request+answer+'}',context);
  const harness = new context.Harness(); let asks=0,settlements=0,resolve;
  Object.assign(harness,{answerUnattended:()=>undefined,queued:fn=>fn(),waitOnUser:()=>{},post:()=>{},reveal:()=>{},out:{},
    answerFor:()=>{asks++;return new Promise(r=>{resolve=r;});},
    settleChoice:value=>{settlements++;harness.pendingChoice(value);}});
  const first = harness.requestChoice({id:'statementChanged',actions:['stop','keep']});
  const firstSequence=harness.choice.compatChoiceRequestSequence;
  const pending=harness.answerIfAsked({choice:{...harness.choice}});
  await harness.answerIfAsked({choice:{...harness.choice}});
  assert.equal(asks,1,'repeated cloned UI snapshots do not double-answer');
  resolve({id:'keep'}); await pending; await first;
  await harness.answerIfAsked({});
  const second=harness.requestChoice({id:'statementChanged',actions:['stop','keep']});
  assert.notEqual(harness.choice.compatChoiceRequestSequence,firstSequence);
  assert.equal(harness.choice.id,'statementChanged','public ID unchanged');
  const pending2=harness.answerIfAsked({choice:{...harness.choice}});
  await harness.answerIfAsked({choice:{...harness.choice}});assert.equal(asks,2);
  resolve({id:'stop'});await pending2;await second;assert.equal(settlements,2);
}

function fixture() {
  const graph={schema:'tex2lean.proof-graph/6',slug:'main',updatedAt:'2026-10-27T00:00:00Z',
    sourceFingerprint:'source-A',buildFingerprint:'source-A',dependencyFingerprint:'source-A',dependencySource:'lean-environment',
    elaboratedAt:'2026-10-27T00:00:00Z',rootModule:'Lib.Model.Theorem',reachableModules:['Lib.Model.Theorem'],
    target:{key:'label:main',paperDigest:'paper-A'},nodes:[{id:'n',kind:'lean',declaration:'Lib.main',status:'proved'}],edges:[],
    feedback:[{at:'2026-10-26T00:00:00Z'}],attempts:[],recoveries:[],mappingDigest:'ledger-A'};
  const ledger={target:{id:'target-A',activeVersionId:'version-A'},claims:[{id:'c',role:'reportable',activeVersionId:'cv'}],
    claimVersions:[{id:'cv',text:'The exact mathematical conclusion',anchor:{file:'paper.tex'}}],
    plans:[{claimVersionId:'cv',disposition:'formalize',requirements:{allOf:[{anyOf:['o']}]}}],
    obligations:[{id:'o'}],bindings:[{id:'b',obligationId:'o',declaration:'Lib.main',status:'verified'}]};
  return {graph,ledger};
}
function projectionContext(text,graph,ledger) {
  const ctx=baseContext(text);let state;
  Object.assign(ctx,{Q:{},a:{data:{}},Z:new Map([[graph.sourceFingerprint,graph]]),le:false,Ge:{digest:'ledger-A'},
    Rt:s=>typeof s==='string'&&s.length>0,sn:F=>({evidence:F,scope:{rootModule:graph.rootModule,modules:graph.reachableModules}}),
    n:{mapping:()=>({targetId:'target-A'}),decomposition:()=>undefined},
    zT:()=>({...copy(graph),updatedAt:'2026-10-27T00:00:01Z'}),ve:g=>g,
    At:1,e:{setProofState:s=>{state=s;}},Se:()=>({graphProofState:()=>{}}),
    XJ:keys=>Object.fromEntries(keys.map(k=>[k,0])),
    hue:['mapped','unmapped','pending-review','unsupported','disputed','excluded','stale'],
    fue:['proved','proved-conditional','candidate-closed','assembled','implemented','open','blocked','assumed-instead','refuted','not-applicable','unknown']});
  vm.runInContext(between(text,'function Xg(', 'async function '),ctx);
  vm.runInContext(between(text,'function mue(', 'var hue,'),ctx);
  vm.runInContext('globalThis.dn='+between(text,'dn=(F,G=Q','},Ct=').slice(3)+'};',ctx);
  vm.runInContext('globalThis.Ct='+between(text,'Ct=(F,G,T=!1)',',Lt=').slice(3)+';',ctx);
  vm.runInContext('globalThis.Lt='+between(text,'Lt=async(F,G,T,N)','},oe=').slice(3)+'};',ctx);
  const snapshot={targetId:'target-A',targetVersionId:'version-A',ledgerDigest:'ledger-A',graphDigest:ctx.Pt('proof-graph/6',graph),
    sourceFingerprint:graph.sourceFingerprint,buildFingerprint:graph.buildFingerprint,dependencyFingerprint:graph.dependencyFingerprint};
  const current={head:{ledgerDigest:'ledger-A',certifiedSnapshotDigest:'snapshot-A'},ledger};
  ctx.it={readCurrent:async()=>current,readCertifiedSnapshot:async()=>snapshot,publishDecision:()=>{throw Error('unexpected ledger write');}};
  return {ctx,current,snapshot,state:()=>state};
}
async function testProjection() {
  const {graph,ledger}=fixture(),evidence={complete:true,sourceFingerprint:'source-A',statements:[],modules:[]};
  const old=projectionContext(source,graph,ledger),next=projectionContext(patched.source,graph,ledger);
  await old.ctx.Lt({targetKey:'label:main'},evidence,old.ctx.dn(evidence),1);
  assert.equal(old.state().claimProgress.rows[0].proof,'candidate-closed','actual old path reproduces defect');
  const derived=next.ctx.dn(evidence);
  assert.equal(derived,graph,'actual dn reuses exact graph when only display timestamp differs');
  await next.ctx.Lt({targetKey:'label:main'},evidence,derived,1);
  assert.equal(next.state().claimProgress.rows[0].proof,'proved');
  assert.equal(next.state().claimProgress.rows[0].proofSnapshot,'certified');
  assert.equal(next.state().claimProgress.complete,true);
  assert.equal(next.state().compatClaimProgressCertificate.snapshotDigest,'snapshot-A');
  for(const [label,mutate] of [
    ['node',x=>x.nodes[0].declaration='Lib.other'],['status',x=>x.nodes[0].status='open'],
    ['edge',x=>x.edges.push({from:'n',to:'x'})],['source',x=>x.sourceFingerprint='source-B'],
    ['build',x=>x.buildFingerprint='source-B'],['dependency',x=>x.dependencyFingerprint='source-B'],
    ['ledger',x=>x.mappingDigest='ledger-B'],['target',x=>x.target.key='label:count'],
    ['paper',x=>x.target.paperDigest='paper-B'],['nested timestamp',x=>x.feedback[0].at='other'],
    ['elaboration time',x=>x.elaboratedAt='other'],['module closure',x=>x.reachableModules.push('Lib.Other')],
    ['unknown future field',x=>x.futureField='new']]) {
    const fresh=copy(graph);fresh.updatedAt='later';mutate(fresh);
    assert.equal(next.ctx.compatRetainGraphTimestamp(graph,fresh),fresh,`${label} must not reuse graph`);
    const test=projectionContext(patched.source,graph,ledger);
    await test.ctx.Lt({targetKey:'label:main'},evidence,fresh,1);
    assert.notEqual(test.state().claimProgress.rows[0].proof,'proved',`${label} must not certify`);
    assert.equal(test.state().compatClaimProgressCertificate,undefined);
  }
  const noCertificate=projectionContext(patched.source,graph,ledger);delete noCertificate.current.head.certifiedSnapshotDigest;
  await noCertificate.ctx.Lt({targetKey:'label:main'},evidence,graph,1);
  assert.equal(noCertificate.state().claimProgress.rows[0].proof,'candidate-closed');
  const proposed=projectionContext(patched.source,graph,{...ledger,bindings:[{...ledger.bindings[0],status:'proposed'}]});
  await proposed.ctx.Lt({targetKey:'label:main'},evidence,graph,1);
  assert.notEqual(proposed.state().claimProgress.rows[0].proof,'proved','certificate display cannot bypass verified-binding requirement');
  return {next,graph,evidence};
}
async function testHandoff() {
  const {next,graph,evidence}=await testProjection(),ctx=next.ctx;
  let sessionState=next.state(),current=next.current,snapshot=next.snapshot,persisted=graph,fresh={complete:true,sourceFingerprint:'source-A'},reads=0;
  const session={getProofState:()=>sessionState},target={key:'label:main',paperDigest:'paper-A'};
  Object.assign(ctx,{Oe:t=>t.key,Yt:t=>t.paperDigest,
    wd:class {async readCurrent(){reads++;return current;}async readCertifiedSnapshot(){return snapshot;}},
    ts:async()=>persisted,na:async()=>fresh});
  const call=()=>ctx.compatMatchingHandoffProgress(session,{}, {leanProjectPath:'.'},target,evidence);
  assert.equal(await call(),sessionState.claimProgress,'matching immediate handoff retains native progress');
  const savedState=sessionState;
  sessionState={...savedState,targetKey:'label:count'};const before=reads;
  assert.equal(await call(),undefined);assert.equal(reads,before,'other target is rejected before any evidence read');
  sessionState={...savedState,compatClaimProgressCertificate:undefined};assert.equal(await call(),undefined,'standalone unbound state omitted');
  sessionState=savedState;
  for(const [label,change,restore] of [
    ['head drift',()=>current={...next.current,head:{...next.current.head,ledgerDigest:'ledger-B'}},()=>current=next.current],
    ['snapshot drift',()=>current={...next.current,head:{...next.current.head,certifiedSnapshotDigest:'snapshot-B'}},()=>current=next.current],
    ['target version',()=>snapshot={...next.snapshot,targetVersionId:'version-B'},()=>snapshot=next.snapshot],
    ['graph change',()=>persisted={...graph,updatedAt:'later'},()=>persisted=graph],
    ['missing graph',()=>persisted=undefined,()=>persisted=graph],
    ['source changed during readers',()=>fresh={complete:true,sourceFingerprint:'source-B'},()=>fresh={complete:true,sourceFingerprint:'source-A'}],
    ['incomplete scan',()=>fresh={complete:false,sourceFingerprint:'source-A'},()=>fresh={complete:true,sourceFingerprint:'source-A'}]
  ]) {change();assert.equal(await call(),undefined,label);restore();}
  ctx.na=async()=>{sessionState={...savedState};return fresh;};assert.equal(await call(),undefined,'changed session state not substituted');
  sessionState=savedState;ctx.na=async()=>{current={...next.current,head:{...next.current.head,ledgerDigest:'ledger-B'}};return fresh;};
  assert.equal(await call(),undefined,'head change during source scan rejected');current=next.current;
  ctx.na=async()=>{persisted={...graph,updatedAt:'after-first-read'};return fresh;};
  assert.equal(await call(),undefined,'graph change during source scan rejected');persisted=graph;
  ctx.na=async()=>{persisted=undefined;return fresh;};
  assert.equal(await call(),undefined,'graph dirtied during source scan rejected');persisted=graph;
  ctx.na=async()=>{throw Error('source read failed');};assert.equal(await call(),undefined,'read failure safely omits');
}
async function main(){
  await testChoices();await testHandoff();
  console.log(JSON.stringify({ok:true,before:patched.before,after:patched.after,unchanged,
    tests:['actual requestChoice/answerIfAsked: repeated same-ID requests and duplicate renders',
      'actual dn/Lt/native QJ: old candidate-closed reproduction and certified projection',
      'all semantic/source/ledger/nested timestamp changes reject reuse; absent certificate and unverified bindings stay unproved',
      'matching-target handoff guard; wrong target/head/source/graph/session and read errors omit safely'],
    cliExecuted:false,compilerExecuted:false,ledgerWrites:false},null,2));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
