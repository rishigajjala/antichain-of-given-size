'use strict';
const assert=require('node:assert/strict');
const fs=require('node:fs');
assert(process.argv.length === 3 && process.argv[2], 'Usage: node test-integration.cjs /path/to/v8/out/cli.cjs');
const vm=require('node:vm');
const path=require('node:path');
const crypto=require('node:crypto');
const {patch}=require('./patch.cjs');
const {parseRequest,withStrictNativeLease,executeNativeReview}=require('./native-host.cjs');
const source=fs.readFileSync(process.argv[2],'utf8');
const built=patch(source);
function between(s,start,end) {const a=s.indexOf(start),b=s.indexOf(end,a+start.length);assert(a>=0&&b>a,start);return s.slice(a,b);}
const plain=x=>JSON.parse(JSON.stringify(x));
const sha=x=>'sha256-'+crypto.createHash('sha256').update(x).digest('hex');
function receiptContext(s) {
  const files=new Map(),commands=[];
  const rows=[['Project.claim','Expr(ClaimType)',['Project.Spec'],['Project.Spec']],
    ['Project.Spec','Expr(Prop)',[],['Project.Hidden']],['Project.Hidden','Expr(Nat)',[],[]]];
  const ctx=vm.createContext({require,Buffer,TextEncoder,TextDecoder,process,
    J2:crypto,Wse:'tex2lean.canonical-json/1',r4:crypto,i4:/^[\p{L}_][\p{L}\p{N}_']*(?:\.[\p{L}_][\p{L}\p{N}_']*)*$/u,t4:256*1024*1024,
    x:(root,f)=>root+'/'+f,
    A:{write:async(p,b)=>files.set(p,Buffer.from(b)),read:async p=>files.get(p),
      stat:async p=>({size:files.get(p).length}),remove:async p=>files.delete(p)},
    qt:async (request,root)=>{
      commands.push(request);assert.equal(request.command,'lake');assert.deepEqual(Array.from(request.args.slice(0,2)),['env','lean']);
      const input=files.get(root+'/'+request.args[2]).toString();
      const output=input.match(/IO\.FS\.writeFile "([^"]+)"/)[1];
      const value=request.args[2].includes('interface-values')?
        {leanVersion:'fixture-version',rows:[['Project.Spec','Expr(SpecBody)'],['Project.Hidden','Expr(HiddenBody)']]}:
        {leanVersion:'fixture-version',rows:ctx.rows};
      files.set(root+'/'+output,Buffer.from(JSON.stringify(value)));return {code:0};
    }});
  ctx.rows=rows;
  vm.runInContext(between(source,'function G0(','var J2,'),ctx);
  vm.runInContext(fs.readFileSync(path.join(__dirname,'cli-helpers.js'),'utf8'),ctx);
  vm.runInContext(between(s,'function Sue(','var r4,'),ctx);
  return {ctx,files,commands};
}
async function testReceipts() {
  const old=receiptContext(source),next=receiptContext(built.source);
  const bindings=[{id:'binding',declaration:'Project.claim'}];
  const evidence={sourceFingerprint:'actual-source-hash',statements:[{name:'Project.claim',file:'Project/Model.lean',header:'theorem claim : Spec'}]};
  const opts={toolchainDigest:'pinned-toolchain',optionsDigest:'pinned-options'};
  const a=await old.ctx.o4('/virtual',['Project.Model'],bindings,evidence,opts);
  const b=await next.ctx.o4('/virtual',['Project.Model'],bindings,evidence,opts);
  assert.deepEqual(plain(b),plain(a),'default native interface receipts must be byte-equivalent data');
  const r=await next.ctx.o4('/virtual',['Project.Model'],bindings,evidence,{...opts,includeReviewMaterial:true});
  const {reviewMaterial,...same}=plain(r);assert.deepEqual(same,plain(a));
  assert.equal(reviewMaterial[0].elaboratedType,'Expr(ClaimType)');
  assert.deepEqual(reviewMaterial[0].semanticDefinitions.map(x=>x.declaration),['Project.Hidden','Project.Spec']);
  assert(reviewMaterial[0].semanticDefinitions.every(x=>x.elaboratedValue.startsWith('Expr(')));
  assert.deepEqual(reviewMaterial[0].semanticDefinitions.map(x=>({declaration:x.declaration,valueDigest:x.valueDigest})),
    plain(a.interfaceReceipts[0].receipt.semanticRootDigests));
  assert.equal(next.files.size,0,'all native temporary probe files cleaned up');
  next.ctx.rows.push(['Project.Hidden','ambiguous duplicate',[],[]]);
  await assert.rejects(()=>next.ctx.o4('/virtual',['Project.Model'],bindings,evidence,{...opts,includeReviewMaterial:true}),/ambiguous duplicate/);
  assert.equal(next.files.size,0);
}
function wrapper(s) {
  const a=s.indexOf('let n=(r,i)=>{Rx.set(r,async(...o)=>{');
  const b=s.indexOf(';return n("formalize.changeStatement"',a);
  assert(a>=0&&b>a);return s.slice(a,b)+';globalThis.register=n;';
}
async function testActualWrapper() {
  let reconciles=0,handled=0,errors=0;
  const ctx=vm.createContext({Rx:new Map(),Ef:()=>{},_M:new Set(['formalize.reviewLedger','formalize.remapStatements']),
    Ae:{batchState:'idle',mode:{permits:()=>undefined}},g:()=>{},q:async()=>{},Bl:()=>{},
    Jfe:new Set(),Vfe:new Set(['formalize.reviewLedger','formalize.remapStatements']),
    AK:async()=>{errors++;},Oi:async()=>{reconciles++;},t:{},compatLedgerReviewActive:false});
  vm.runInContext(wrapper(built.source),ctx);
  ctx.register('formalize.reviewLedger',async()=>{handled++;});
  await ctx.Rx.get('formalize.reviewLedger')();assert.equal(handled,1);assert.equal(reconciles,0);
  ctx.register('formalize.reviewLedger',async()=>{throw Error('failure');});
  await ctx.Rx.get('formalize.reviewLedger')();assert.equal(errors,1);assert.equal(reconciles,0);
  ctx.register('formalize.remapStatements',async()=>{handled++;});
  await ctx.Rx.get('formalize.remapStatements')();assert.equal(reconciles,1,'ordinary command refresh retained');
  ctx.register('formalize.reviewLedger',async()=>{handled++;});
  ctx.Ae.batchState='working';await ctx.Rx.get('formalize.reviewLedger')();assert.equal(handled,2,'batch entry guard retained');
  ctx.Ae.batchState='idle';ctx.Ae.mode.permits=()=>({reason:'already-working'});
  await ctx.Rx.get('formalize.reviewLedger')();assert.equal(handled,2,'mode entry guard retained');
  ctx.Ae.mode.permits=()=>undefined;ctx.compatLedgerReviewActive=true;
  await assert.rejects(()=>ctx.Rx.get('formalize.remapStatements')(),/finish the ledger review/);
  assert.equal(reconciles,1);
  // The original native wrapper would have reconciled the review command too.
  const legacy=vm.createContext({...Object.fromEntries(Object.entries(ctx)),compatLedgerReviewActive:false,Rx:new Map()});
  vm.runInContext(wrapper(source),legacy);legacy.register('formalize.reviewLedger',async()=>{});
  await legacy.Rx.get('formalize.reviewLedger')();assert.equal(reconciles,2);
}
class MemoryFS {
  constructor(){this.files=new Map();this.directories=new Set(['/','/virtual']);}
  async mkdir(p){this.directories.add(p);}
  async readFile(p,encoding){if(!this.files.has(p))throw Object.assign(Error('missing'),{code:'ENOENT'});const b=Buffer.from(this.files.get(p));return encoding?b.toString():b;}
  async writeFile(p,data){this.files.set(p,Buffer.from(data));}
  async open(p,flag){assert.equal(flag,'wx');if(this.files.has(p))throw Object.assign(Error('lease exists'),{code:'EEXIST'});this.files.set(p,Buffer.alloc(0));return {writeFile:x=>this.writeFile(p,x),close:async()=>{}};}
  async unlink(p){if(!this.files.delete(p))throw Object.assign(Error('missing'),{code:'ENOENT'});}
  async realpath(p){return p;}
}
function leaseFixture(){
  const fs=new MemoryFS();let controls=0,releases=0;
  const d={go:()=>controls,isBatchWorking:()=>false,hasLiveTransaction:()=>false,hasRecoveryInFlight:()=>false,
    newControl:()=>{controls++;return {token:{},dispose:()=>{controls--;}};},leaseFile:()=>'/virtual/run/lease.json',
    makeLease:what=>({schema:'tex2lean.lease/1',machine:'fixture',pid:1,what,takenAt:'fixed',seenAt:'fixed'}),
    assertNoJournalFiles:async()=>{},hasProcessLease:()=>false,
    newHeldLease:(value,write,remove)=>({refresh:()=>write(JSON.stringify(value)),release:async()=>{releases++;await remove();}})};
  return {fs,d,controls:()=>controls,releases:()=>releases};
}
async function testLeaseAndAuthority() {
  let f=leaseFixture();let ran=false;
  await withStrictNativeLease(f.d,f.fs,async lease=>{ran=true;assert.equal(f.controls(),1);await lease.assertOwner();await lease.refresh();});
  assert(ran);assert.equal(f.controls(),0);assert.equal(f.releases(),1);assert.equal(f.fs.files.size,0);
  for(const contents of ['not JSON',JSON.stringify({schema:'unknown'}),JSON.stringify({schema:'tex2lean.lease/1',pid:99})]){
    f=leaseFixture();f.fs.files.set(f.d.leaseFile(),Buffer.from(contents));
    await assert.rejects(()=>withStrictNativeLease(f.d,f.fs,async()=>{throw Error('must not enter');}),/lease exists/);
    assert.equal(f.controls(),0);assert.equal((await f.fs.readFile(f.d.leaseFile(),'utf8')),contents);
  }
  for(const key of ['isBatchWorking','hasLiveTransaction','hasRecoveryInFlight']){
    f=leaseFixture();f.d[key]=()=>true;
    await assert.rejects(()=>withStrictNativeLease(f.d,f.fs,async()=>{}),/active/);assert.equal(f.controls(),0);
  }
  f=leaseFixture();f.d.hasProcessLease=()=>true;
  await assert.rejects(()=>withStrictNativeLease(f.d,f.fs,async()=>{}),/holds the native lease/);assert.equal(f.controls(),0);
  f=leaseFixture();
  await assert.rejects(()=>withStrictNativeLease(f.d,f.fs,async()=>{throw Error('inspection failed');}),/inspection failed/);
  assert.equal(f.controls(),0);assert.equal(f.fs.files.size,0);
  // A replacement lease is never removed on cleanup, even if another operation changes ownership.
  f=leaseFixture();
  await assert.rejects(()=>withStrictNativeLease(f.d,f.fs,async()=>{
    f.fs.files.set(f.d.leaseFile(),Buffer.from(JSON.stringify({schema:'tex2lean.lease/1',pid:55})));
  }),/lease ownership changed/);
  assert(f.fs.files.has(f.d.leaseFile()));assert.equal(f.controls(),0);
  const auth=Buffer.from(JSON.stringify({userRequest:'the authorized request'}));
  const request={inspect:true,authority:'/virtual/authority.json',declarations:['Project.claim']};
  f=leaseFixture();f.fs.files.set('/virtual/authority.json',auth);
  await assert.rejects(()=>executeNativeReview(request,{authorityRecordDigest:''},{fs:f.fs}),/no trusted authority/);
  await assert.rejects(()=>executeNativeReview(request,{authorityRecordDigest:sha('different authority')},{fs:f.fs}),/separately reviewed host pin/);
  // Changing the authority and matching any manifest cannot affect the independently compiled pin.
  f.fs.files.set('/virtual/authority.json',Buffer.from(JSON.stringify({userRequest:'invented replacement'})));
  await assert.rejects(()=>executeNativeReview(request,{authorityRecordDigest:sha(auth)},{fs:f.fs}),/separately reviewed host pin/);
  assert.throws(()=>parseRequest({inspect:true,authority:'/a',declarations:['P.x'],apply:true}),/inspection cannot apply/);
  assert.throws(()=>parseRequest({manifest:'/m',authority:'/a',apply:'true'}),/boolean/);
  assert.throws(()=>parseRequest({manifest:'/m',authority:'/a',verified:true}),/unknown request/);
}
async function testInspectionFlow() {
  const f=leaseFixture(),native=receiptContext(built.source),root='/virtual/project';
  const put=(file,text)=>f.fs.files.set(root+'/'+file,Buffer.from(text));
  const bundle={origin:'latex',files:['paper.tex'],macros:[],theoremEnvironments:['theorem'],target:{
    body:'Exact mathematical claim.',start:{file:'paper.tex',line:1},end:{file:'paper.tex',line:1},environment:'theorem'}};
  const packet=native.ctx.Pt('paper-packet/1',{origin:bundle.origin,files:bundle.files,macros:bundle.macros,
    theoremEnvironments:bundle.theoremEnvironments,target:{body:bundle.target.body,start:bundle.target.start,end:bundle.target.end,environment:bundle.target.environment}});
  put('paper.tex',bundle.target.body);put('Project/Model.lean','def Spec : Prop := True\ntheorem claim : Spec := trivial');
  put('lean-toolchain','leanprover/lean4:v4.32.0\n');
  put('.blueprint/blueprint.json',JSON.stringify({bundle,paperProofMapping:{targetId:'target'},filePlan:{capstone:'Project.claim'}}));
  const authority={schema:'tex2lean.delegated-authority-record/1',scope:'formalization-and-correspondence-review',
    recordedBy:'Codex assistant',noHumanSemanticReviewAsserted:true,userRequest:'The user authorized faithful formalization.',
    projectRoot:root,blueprint:'.blueprint/blueprint.json',targetIds:['target']};
  const bytes=Buffer.from(JSON.stringify(authority));f.fs.files.set('/virtual/authority.json',bytes);
  const evidence={complete:true,sourceFingerprint:'source-v1',leanProofFactsFingerprint:'source-v1',leanDiagnostics:{complete:true},
    statements:[{name:'Project.claim',file:'Project/Model.lean',header:'theorem claim : Spec'}],
    modules:[{module:'Project.Model',file:'Project/Model.lean',imports:[]}]};
  let certifies=0,clears=0,publications=0;
  const d={...f.d,authorityRecordDigest:sha(bytes),rootPath:()=>root,projectPath:()=>root,
    Pt:native.ctx.Pt,Sf:native.ctx.Sf,
    newStore:()=>({readCurrent:async()=>({head:{ledgerDigest:'ledger-v1'},ledger:{target:{id:'target',activeVersionId:'tv'},
      targetVersions:[{id:'tv',paperPacketDigest:packet}]}}),publishDecision:async()=>{publications++;}}),
    scan:async()=>plain(evidence),clearProjectEvidenceCaches:()=>{clears++;},
    certify:async()=>{assert.equal(clears,1);certifies++;return plain(evidence);},
    scope:()=>({modules:['Project.Model'],files:['Project/Model.lean']}),
    inspectInterfaces:(modules,bindings,ev,opts)=>native.ctx.o4('/probe',modules,bindings,ev,opts)};
  const result=await executeNativeReview({inspect:true,authority:'/virtual/authority.json',declarations:['Project.claim']},d,{fs:f.fs});
  assert.equal(result.mode,'inspect');assert.equal(certifies,1);assert.equal(clears,1);assert.equal(publications,0);
  assert.equal(result.declarations['Project.claim'].elaboratedType,'Expr(ClaimType)');
  assert(result.elaboratedDefinitionBodies[0].semanticDefinitions.some(x=>x.elaboratedValue==='Expr(HiddenBody)'));
  assert.equal(result.sourceBodies['Project/Model.lean'].text,'def Spec : Prop := True\ntheorem claim : Spec := trivial');
  assert.equal(result.pins.paperPacket,packet);assert.equal(f.controls(),0);assert(!f.fs.files.has(f.d.leaseFile()));
  // Inputs changing during the native inspection are rejected before producing review evidence.
  d.certify=async()=>{put('paper.tex','Changed source');return plain(evidence);};
  await assert.rejects(()=>executeNativeReview({inspect:true,authority:'/virtual/authority.json',declarations:['Project.claim']},d,{fs:f.fs}),/target body changed/);
  assert.equal(publications,0);assert.equal(f.controls(),0);
}
function testUnchangedAndCache() {
  assert.equal(between(source,'function KJ(','function XJ('),between(built.source,'function KJ(','function XJ('),
    'native replay, validation and store unchanged');
  const marker='for(let Zt of un.ledger.bindings){let nt=nr.get(Zt.id);',suffix='un=await it.readCurrent(Ge.ledger.target.id)??un}';
  const loop=s=>s.slice(s.indexOf(marker),s.indexOf(suffix,s.indexOf(marker))+suffix.length);
  assert.equal(loop(source),loop(built.source),'native validator loop unchanged');
  const ctx=vm.createContext({});vm.runInContext(fs.readFileSync(path.join(__dirname,'cli-helpers.js'),'utf8'),ctx);
  const f=new Map([['/project:abc',1],['/project:xyz',2],['/project-other:abc',3]]);
  const h=new Map([['/project\0A.lean\0digest',1],['/project-other\0A.lean\0digest',2]]);
  ctx.compatClearReviewCaches('/project',f,h);
  assert.deepEqual([...f.keys()],['/project-other:abc']);assert.deepEqual([...h.keys()],['/project-other\0A.lean\0digest']);
  const pinned=patch(source,{authorityDigest:sha('reviewed authority')});
  assert(pinned.source.includes('var compatLedgerReviewAuthorityDigest = '+JSON.stringify(sha('reviewed authority'))+';'));
}
(async()=>{
  testUnchangedAndCache();await testReceipts();await testActualWrapper();await testLeaseAndAuthority();await testInspectionFlow();
  console.log(JSON.stringify({ok:true,candidateBundleSha256:built.after,
    tests:['actual native o4 ordinary receipt equivalence and optional type/body extraction',
      'actual T8 wrapper success/failure skip only review reconciliation; entry guards unchanged',
      'strict exclusive lease rejects live/stale/malformed/existing leases; cleanup preserves replacement owner',
      'independent authority pin mismatch, including changed authority plus self-consistent manifest',
      'targeted Fl/Hc cache invalidation; other projects preserved',
      'positive inspection flow exports exact types/bodies and complete source files without publication',
      'native validator/store/replay unchanged; inspect cannot apply'],
    runtimeExecuted:false,compilerExecuted:false,repositoryChanged:false},null,2));
})().catch(e=>{console.error(e);process.exitCode=1;});
