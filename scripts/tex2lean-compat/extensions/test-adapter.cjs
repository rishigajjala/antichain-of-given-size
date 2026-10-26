'use strict';
const assert=require('node:assert/strict');
const fs=require('node:fs');
assert(process.argv.length === 3 && process.argv[2], 'Usage: node test-adapter.cjs /path/to/v8/out/cli.cjs');
const path=require('node:path');
const vm=require('node:vm');
const {runReview,PROVENANCE,NONMATHEMATICAL}=require('./adapter.cjs');
const {extractValidatorLoop}=require('./validator-loop.cjs');
const bundle=process.argv[2];
const source=fs.readFileSync(bundle,'utf8'); // Read only; never evaluate the CLI bootstrap.
const clone=x=>JSON.parse(JSON.stringify(x));
function between(start,end) {
  const a=source.indexOf(start),b=source.indexOf(end,a+start.length);
  assert(a>=0 && b>a,`${start} ... ${end}`);return source.slice(a,b);
}
function nativeHarness() {
  const files=new Map();
  const missing=()=>Object.assign(new Error('missing'),{code:'ENOENT'});
  const ctx=vm.createContext({require,process,TextEncoder,Map,Set,Date,JSON,Buffer,
    P:fn=>{let done=false;return()=>{if(!done){done=true;fn();}}},ge:()=>{},oa:()=>{},ka:()=>{},
    J2:require('node:crypto'),Wse:'tex2lean.canonical-json/1',
    x:(...xs)=>path.posix.join(...xs),
    kt:async p=>{if(!files.has(p)) throw missing();return files.get(p)},
    Qf:async p=>files.has(p),Br:async(p,value)=>{files.set(p,JSON.stringify(value));},
    A:{mkdirp:async()=>{},write:async(p,b)=>files.set(p,Buffer.from(b).toString()),
      move:async(a,b)=>{if(files.has(b))throw Error('already locked');if(!files.has(a))throw missing();files.set(b,files.get(a));files.delete(a);},
      remove:async p=>{if(!files.delete(p))throw missing();},
      list:async p=>[...files.keys()].filter(f=>path.posix.dirname(f)===p).map(f=>[path.posix.basename(f),'file'])}});
  vm.runInContext(between('function G0(', 'var J2,'),ctx);
  // Exact bundled immutable replay, validation, and wd publication implementation.
  vm.runInContext(between('function KJ(', 'function XJ('),ctx);
  vm.runInContext('hS();',ctx);
  const store=new ctx.wd('/mock-project','.');
  return {ctx,store,files};
}
function fixture(ctx) {
  const P=ctx.Pt,meta=[...NONMATHEMATICAL.keys()];
  const pins={paperPacket:P('fixture','paper'),leanSources:P('fixture','lean'),
    configuration:P('fixture','config'),toolchain:P('fixture','toolchain')};
  const texts=['First exact mathematical assertion.','Second exact mathematical assertion.',...meta];
  const ledger={schema:'tex2lean.paper-proof-ledger/1',ledgerId:'ledger',paper:{id:'paper'},
    target:{id:'target',paperId:'paper',activeVersionId:'target-v1'},
    activeClaimSetReceiptId:'claim-set',activeSurfaceInventoryId:'surface',
    targetVersions:[{id:'target-v1',targetId:'target',paperPacketDigest:pins.paperPacket,status:'active'}],
    claims:texts.map((_,i)=>({id:`claim${i}`,targetId:'target',activeVersionId:`cv${i}`,role:'reportable'})),
    claimVersions:texts.map((text,i)=>({id:`cv${i}`,claimId:`claim${i}`,targetVersionId:'target-v1',text,
      normalizedTextDigest:ctx.J0(text),kind:'correctness',status:'active'})),
    plans:texts.map((_,i)=>({claimVersionId:`cv${i}`,disposition:'formalize',
      requirements:{allOf:[{anyOf:[`ob${i}`]}]},evidenceIds:[],reason:'original'})),
    obligations:texts.map((text,i)=>({id:`ob${i}`,kind:'headline',summary:text,status:'planned'})),
    bindings:[],leanRelations:[],claimSetReceipts:[{id:'claim-set',targetVersionId:'target-v1',
      paperPacketDigest:pins.paperPacket,claimVersionIds:texts.map((_,i)=>`cv${i}`),readerProvenance:'fixture'}],
    evidence:[],surfaceInventories:[{id:'surface',targetVersionId:'target-v1',source:'fixture',
      declarations:[0,1].map(i=>({declaration:`Project.claim${i}`,role:'headline',file:'Project/Model.lean',module:'Project.Model'}))}],
    appliedDecisionIds:[]};
  const files={};
  const file=(name,text,kind)=>{files[name]={text,kind,digest:P('file',text)};};
  file('paper/main.tex','Theorem: exact claims.\nCorollary: a separate probabilistic statement.','paper');
  file('.blueprint/BLUEPRINT.md',meta.join('\n'),'metadata');
  file('Project/PriorProof.lean','theorem previous_endpoint : True := trivial','lean');
  file('docs/current-paper.md','The old proof used a larger clustered encoding.','documentation');
  const q=(name,from,to)=>({file:name,from,to,text:files[name].text.split('\n').slice(from-1,to).join('\n'),fileDigest:files[name].digest});
  const definitions=[{declaration:'Project.Model',elaboratedType:'Type',valueDigest:P('definition','exact body')}];
  const declarations=Object.fromEntries([0,1].map(i=>[`Project.claim${i}`,{
    file:'Project/Model.lean',module:'Project.Model',elaboratedType:`ExactProposition${i}`,
    semanticDefinitions:definitions,inCertifiedModuleClosure:true}]));
  const snapshot={complete:true,diagnosticsComplete:true,pins,interfaceEvidenceSourceFingerprint:pins.leanSources,
    leanProofFactsFingerprint:pins.leanSources,buildFingerprint:pins.leanSources,
    idle:{workers:0,liveTransactions:0,otherLease:false,workflowRunning:false},files,declarations};
  const manifest={schema:'tex2lean.delegated-ledger-review/1',targetId:'target',baseLedgerDigest:ctx.Cu(ledger),pins:clone(pins),
    review:{authority:'user-delegated-author',authorizationDigest:P('authorization','explicit user task'),provenance:PROVENANCE},
    bindings:[0,1].map(i=>({claimVersionId:`cv${i}`,obligationId:`ob${i}`,declaration:`Project.claim${i}`,
      file:'Project/Model.lean',module:'Project.Model',elaboratedType:`ExactProposition${i}`,
      semanticDefinitions:definitions,sourceQuote:q('paper/main.tex',1,1),reason:'Reviewed exact domains and both directions of the semantic correspondence.'})),
    exclusions:[{claimVersionId:'cv2',exactClaimText:meta[0],category:'implementation-provenance',
      metadataQuote:q('.blueprint/BLUEPRINT.md',1,1),sourceQuotes:[q('Project/PriorProof.lean',1,1),q('docs/current-paper.md',1,1)],
      reason:'This is an instruction to preserve proof provenance, not a separate mathematical assertion.'},
    {claimVersionId:'cv3',exactClaimText:meta[1],category:'scope-metadata',metadataQuote:q('.blueprint/BLUEPRINT.md',2,2),
      sourceQuotes:[q('paper/main.tex',1,1),q('paper/main.tex',2,2)],reason:'This separates theorem scope from the subsequent corollary.'}]};
  return {ledger,snapshot,manifest};
}
async function setup() {
  const native=nativeHarness();const f=fixture(native.ctx);await native.store.publishGenesis(f.ledger);
  let writes=0,leases=0;
  const rawPublish=native.store.publishDecision.bind(native.store);
  native.store.publishDecision=async d=>{writes++;return rawPublish(d)};
  const host={native:native.ctx,store:native.store,authorizedUserRequestDigest:f.manifest.review.authorizationDigest,
    captureSnapshot:async()=>clone(f.snapshot),withIdleLease:async fn=>{leases++;return fn();}};
  return {...native,...f,host,getWrites:()=>writes,getLeases:()=>leases};
}
async function rejected(change,pattern) {
  const f=await setup();change(f);
  await assert.rejects(()=>runReview(f.manifest,f.host,{apply:true}),pattern);
  assert.equal(f.getWrites(),0,'negative control must fail before publication');
}
async function testAdapter() {
  const f=await setup();const before=JSON.stringify([...f.files]);
  const dry=await runReview(f.manifest,f.host);
  assert.equal(dry.mode,'dry-run');assert.equal(dry.publications.length,0);
  assert.equal(f.getWrites(),0);assert.equal(f.getLeases(),0);assert.equal(JSON.stringify([...f.files]),before);
  const applied=await runReview(f.manifest,f.host,{apply:true});
  assert.equal(applied.publications.length,10);assert.equal(f.getLeases(),1);
  const after=await f.store.readCurrent('target');
  assert.equal(after.ledger.claims.length,4);assert.equal(after.ledger.claimSetReceipts[0].claimVersionIds.length,4);
  assert(after.ledger.bindings.every(b=>b.status==='proposed' && b.semanticApprovalDecisionId));
  assert(after.ledger.plans.slice(0,2).every(p=>p.disposition==='formalize'));
  assert(after.ledger.plans.filter(p=>p.disposition==='exclude').length===2);
  assert.equal(f.ctx.Vy(after.ledger).length,0);
  const decisions=[...f.files].filter(([p])=>p.includes('/decisions/')).map(([,v])=>JSON.parse(v));
  assert(decisions.every(d=>['put-evidence','put-binding','set-disposition'].includes(d.kind)));
  assert(decisions.every(d=>d.actor==='author' && d.mode==='automatic' && d.provenance.startsWith(PROVENANCE)));
  assert(decisions.every(d=>!d.binding || d.binding.status==='proposed'));
  assert.equal(new Set(decisions.map(d=>d.baseLedgerDigest)).size,10,'fresh head at every native publication');
  const approvals=decisions.filter(d=>d.binding?.semanticApprovalDecisionId);
  assert(approvals.every(d=>d.binding.semanticApprovalDecisionId===d.id));
  // Native automatic semantic approval still refuses a non-author actor; no unchecked approval branch used.
  const g=await setup(),current=await g.store.readCurrent('target');
  const d={id:'bad',ledgerId:'ledger',baseLedgerDigest:current.head.ledgerDigest,actor:'planner',mode:'automatic',
    provenance:'invalid',kind:'put-binding',binding:{id:'b',obligationId:'ob0',declaration:'Project.claim0',
      file:'Project/Model.lean',module:'Project.Model',role:'headline',status:'proposed',semanticApprovalDecisionId:'bad'}};
  await assert.rejects(()=>g.store.publishDecision(d),/requires a reviewed proposal/);
  await rejected(f=>f.manifest.bindings[0].status='verified',/forbidden field status/);
  await rejected(f=>f.manifest.exclusions[0].exactClaimText=f.ledger.claimVersions[0].text,/claim text changed/);
  await rejected(f=>{f.manifest.exclusions[0].claimVersionId='cv0';f.manifest.exclusions[0].exactClaimText=f.ledger.claimVersions[0].text;f.manifest.bindings=[];},/only the two exact/);
  await rejected(f=>f.manifest.bindings[0].elaboratedType='True',/type changed/);
  await rejected(f=>f.manifest.bindings[0].semanticDefinitions=[],/omits or changes/);
  await rejected(f=>f.manifest.bindings[0].sourceQuote.text='not the source',/quote is not exact/);
  await rejected(f=>f.snapshot.complete=false,/complete source snapshot/);
  await rejected(f=>f.snapshot.diagnosticsComplete=false,/complete source snapshot/);
  for(const pin of ['paperPacket','leanSources','configuration','toolchain'])
    await rejected(f=>f.snapshot.pins[pin]='changed',/changed|pinned source snapshot/);
  await rejected(f=>f.snapshot.interfaceEvidenceSourceFingerprint='old',/interfaces do not belong/);
  await rejected(f=>f.manifest.review.authorizationDigest='invented',/trusted user authorization/);
  await rejected(f=>f.manifest.review.provenance='human reviewed',/Expected values/);
  for(const field of ['workers','liveTransactions','otherLease','workflowRunning'])
    await rejected(f=>f.snapshot.idle[field]=field==='workers'||field==='liveTransactions'?1:true,/busy or held/);
  await rejected(f=>f.manifest.baseLedgerDigest='old',/ledger head changed/);
  // Pins are rechecked between every native publication; already written history is retained.
  const mid=await setup();
  const publishMid=mid.store.publishDecision.bind(mid.store);
  mid.store.publishDecision=async d=>{const result=await publishMid(d);mid.snapshot.pins.leanSources='changed';return result;};
  await assert.rejects(()=>runReview(mid.manifest,mid.host,{apply:true}),/changed|pinned source snapshot/);
  assert.equal(mid.getWrites(),1);
  assert.equal((await mid.store.readCurrent('target')).ledger.bindings.length,0);
  // A new outside ledger writer after the lease is acquired is rejected before any adapter publication.
  const race=await setup();race.host.withIdleLease=async fn=>{
    const cur=await race.store.readCurrent('target');
    await race.store.publishDecision({id:'outside',ledgerId:'ledger',baseLedgerDigest:cur.head.ledgerDigest,
      actor:'author',mode:'automatic',provenance:'outside',kind:'put-evidence',evidence:(()=>{
        const e={kind:'source-reading',anchors:[]};e.id=race.ctx.Sf(e);return e;})()});
    return fn();
  };
  await assert.rejects(()=>runReview(race.manifest,race.host,{apply:true}),/ledger head changed/);
  assert.equal(race.getWrites(),1,'only simulated outside publication exists');
  return f;
}
function compileLoop(ctx,loop) {
  vm.runInContext(`async function runNativeLoop(it,targetId,Fi,jn,ot){
    let Ge={ledger:{target:{id:targetId}}},un=await it.readCurrent(targetId);
    let nr=new Map(Fi.interfaceReceipts.map(row=>[row.bindingId,row]));
    ${loop}
    return it.readCurrent(targetId);
  }`,ctx);
  return ctx.runNativeLoop;
}
async function makeApproved() {
  const f=await setup();await runReview(f.manifest,f.host,{apply:true});
  const current=await f.store.readCurrent('target');
  const Fi={schema:'tex2lean.lean-evidence/1',sourceFingerprint:f.snapshot.pins.leanSources,
    buildFingerprint:f.snapshot.pins.leanSources,dependencyFingerprint:f.snapshot.pins.leanSources,
    toolchainDigest:f.snapshot.pins.toolchain,relationEvidence:[],interfaceReceipts:current.ledger.bindings.map(b=>{
      const receipt={sourceSignatureDigest:f.ctx.Pt('sig',b.declaration),elaboratedTypeDigest:f.ctx.Pt('type',b.declaration),
        semanticRootPolicyId:'project-type-closure/1',semanticRootDigests:[],leanVersion:'fixture',
        toolchainDigest:f.snapshot.pins.toolchain,optionsDigest:f.ctx.Pt('options',{})};
      return {bindingId:b.id,declaration:b.declaration,receiptDigest:f.ctx.Tu(receipt),receipt};})};
  return {...f,Fi,jn:await f.store.writeLeanEvidence(Fi)};
}
async function testValidator() {
  const {loop:original,digest}=extractValidatorLoop(source);
  const mutant=original.replace('un=await it.readCurrent(Ge.ledger.target.id)??un}', '}');
  assert.notEqual(mutant,original);
  const broken=await makeApproved();
  await assert.rejects(()=>compileLoop(broken.ctx,mutant)(broken.store,'target',broken.Fi,broken.jn,
    {sourceFingerprint:broken.snapshot.pins.leanSources}),/stale mapping publication base/);
  const one=await broken.store.readCurrent('target');assert.equal(one.ledger.bindings.filter(b=>b.status==='verified').length,1);
  const fixed=await makeApproved();
  const run=compileLoop(fixed.ctx,original);
  const verified=await run(fixed.store,'target',fixed.Fi,fixed.jn,{sourceFingerprint:fixed.snapshot.pins.leanSources});
  assert(verified.ledger.bindings.every(b=>b.status==='verified'));
  assert.equal(fixed.ctx.Vy(verified.ledger,{leanEvidence:new Map([[fixed.jn,fixed.Fi]]),requireCertifiedSurface:true}).length,0);
  // Re-running the unchanged validator is idempotent, not a new proof-status update.
  const count=fixed.getWrites();await run(fixed.store,'target',fixed.Fi,fixed.jn,{sourceFingerprint:fixed.snapshot.pins.leanSources});
  assert.equal(fixed.getWrites(),count);
  // Refresh both bindings under one newer certified source snapshot.
  const newer=clone(fixed.Fi);newer.sourceFingerprint=newer.buildFingerprint=newer.dependencyFingerprint=fixed.ctx.Pt('fixture','new sources');
  const newerId=await fixed.store.writeLeanEvidence(newer);
  const refreshed=await run(fixed.store,'target',newer,newerId,{sourceFingerprint:newer.sourceFingerprint});
  assert(refreshed.ledger.bindings.every(b=>b.leanEvidenceSnapshotId===newerId));
  // Changed interface receipts stale both bindings, preserving the existing rejection logic.
  const changed=clone(newer);for(const row of changed.interfaceReceipts){row.receipt.elaboratedTypeDigest='changed';row.receiptDigest=fixed.ctx.Tu(row.receipt);}
  const changedId=await fixed.store.writeLeanEvidence(changed);
  const stale=await run(fixed.store,'target',changed,changedId,{sourceFingerprint:changed.sourceFingerprint});
  assert(stale.ledger.bindings.every(b=>b.status==='stale'));
  // The deliberately broken mutant wrote an orphan immutable decision. Native publication
  // correctly refuses silently changing its base; this is not a failure of the real loop.
  await assert.rejects(()=>compileLoop(broken.ctx,original)(broken.store,'target',broken.Fi,broken.jn,
    {sourceFingerprint:broken.snapshot.pins.leanSources}),/reused with different content/);
  return {unchangedNativeLoopDigest:digest,patchRequired:false,negativeControl:'removing the native per-iteration refresh reproduces a stale-head failure'};
}
(async()=>{
  await testAdapter();const hashes=await testValidator();
  console.log(JSON.stringify({ok:true,tests:'native replay/publication, dry-run, provenance-only exclusions, strict pins, authority, concurrency, and unchanged real validator verify/refresh/stale and negative-control regression',validator:hashes},null,2));
})().catch(e=>{console.error(e);process.exitCode=1;});
