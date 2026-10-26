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
async function setupReplacement(oldDeclaration='Project.oldClaim') {
  const f=await setup(),current=await f.store.readCurrent('target');
  const old={id:'old-unapproved-binding',obligationId:'ob0',declaration:oldDeclaration,
    file:'Project/Old.lean',module:'Project.Old',role:'headline',status:'proposed'};
  const seed={id:'original-proposal',ledgerId:'ledger',baseLedgerDigest:current.head.ledgerDigest,
    actor:'planner',mode:'automatic',provenance:'original planner proposal',kind:'put-binding',binding:old};
  await f.store.publishDecision(seed);
  f.manifest.baseLedgerDigest=(await f.store.readCurrent('target')).head.ledgerDigest;
  f.manifest.bindings[0].replaceUnapprovedProposal={expectedBinding:clone(old),
    expectedBindingDigest:f.ctx.Pt('delegated-binding-proposal/1',old),
    reason:'The original unapproved whole-capstone guess is replaced by the exact reviewed component theorem.'};
  return {...f,old,seed};
}
async function rejectReplacement(change,pattern,externalWrites=0) {
  const f=await setupReplacement();await change(f);const before=f.getWrites();
  await assert.rejects(()=>runReview(f.manifest,f.host,{apply:true}),pattern);
  assert.equal(f.getWrites(),before+externalWrites,'rejected replacement must publish nothing beyond the simulated outside writer');
}
async function testReplacement() {
  const f=await setupReplacement(),before=JSON.stringify([...f.files]),writes=f.getWrites();
  const dry=await runReview(f.manifest,f.host);
  assert.equal(dry.replacements.length,1);assert.equal(dry.replacements[0].bindingId,f.old.id);
  assert.deepEqual(dry.replacements[0].before,f.old);assert.equal(dry.replacements[0].after.declaration,'Project.claim0');
  assert.equal(dry.publications.length,0);assert.equal(f.getWrites(),writes);
  assert.equal(JSON.stringify([...f.files]),before,'replacement dry-run preserves the native store');
  const result=await runReview(f.manifest,f.host,{apply:true});
  const after=await f.store.readCurrent('target'),current=after.ledger.bindings.find(b=>b.id===f.old.id);
  assert.equal(current.obligationId,f.old.obligationId);assert.equal(current.status,'proposed');
  assert.equal(current.declaration,'Project.claim0');assert(current.semanticApprovalDecisionId);
  assert.equal(after.ledger.claims.length,4);assert.equal(after.ledger.claimSetReceipts[0].claimVersionIds.length,4);
  assert.equal(after.ledger.bindings.length,2);assert.equal(f.ctx.Vy(after.ledger).length,0);
  const decisions=[...f.files].filter(([p])=>p.includes('/decisions/')).map(([,v])=>JSON.parse(v));
  assert.deepEqual(decisions.find(d=>d.id==='original-proposal'),f.seed,'original proposal event remains intact');
  const updates=decisions.filter(d=>d.kind==='put-binding' && d.binding.id===f.old.id && d.id!==f.seed.id);
  assert.equal(updates.length,2,'replacement and semantic approval are separate immutable events');
  assert(updates.every(d=>d.actor==='author' && d.binding.status==='proposed' && d.binding.obligationId===f.old.obligationId));
  assert.equal(updates.filter(d=>!d.binding.semanticApprovalDecisionId).length,1);
  assert(updates.every(d=>d.provenance.includes('expectedBindingDigest') && d.provenance.includes('original unapproved')));
  assert.equal(new Set(result.publications.map(p=>p.decisionId)).size,result.publications.length);
  assert.equal(new Set(decisions.map(d=>d.baseLedgerDigest)).size,decisions.length,'fresh native head per immutable event');
  // The pre-existing ordinary approval path remains unchanged when no correction is requested.
  const ordinary=await setup(),ordinaryHead=await ordinary.store.readCurrent('target');
  const ordinaryBinding={id:'ordinary-existing',obligationId:'ob0',declaration:'Project.claim0',
    file:'Project/Model.lean',module:'Project.Model',role:'headline',status:'proposed'};
  await ordinary.store.publishDecision({id:'ordinary-seed',ledgerId:'ledger',baseLedgerDigest:ordinaryHead.head.ledgerDigest,
    actor:'planner',mode:'automatic',provenance:'fixture',kind:'put-binding',binding:ordinaryBinding});
  ordinary.manifest.baseLedgerDigest=(await ordinary.store.readCurrent('target')).head.ledgerDigest;
  const ordinaryResult=await runReview(ordinary.manifest,ordinary.host,{apply:true});
  assert.equal(ordinaryResult.replacements.length,0);assert.equal(ordinaryResult.publications.length,9);
  assert.equal((await ordinary.store.readCurrent('target')).ledger.bindings.find(b=>b.id==='ordinary-existing').declaration,'Project.claim0');
  // All replacement pins and review intent are mandatory.
  await rejectReplacement(f=>{delete f.manifest.bindings[0].replaceUnapprovedProposal;},/explicit replacement review required/);
  await rejectReplacement(f=>{f.manifest.bindings[0].replaceUnapprovedProposal.reason=' ';},/replacement reason/);
  await rejectReplacement(f=>{f.manifest.bindings[0].replaceUnapprovedProposal.expectedBindingDigest='wrong';},/record does not match its digest/);
  await rejectReplacement(f=>{f.manifest.bindings[0].replaceUnapprovedProposal.expectedBinding.declaration='invented';},/record does not match its digest/);
  await rejectReplacement(f=>{const r=f.manifest.bindings[0].replaceUnapprovedProposal;r.expectedBinding.declaration='invented';
    r.expectedBindingDigest=f.ctx.Pt('delegated-binding-proposal/1',r.expectedBinding);},/reviewed old proposal changed/);
  await rejectReplacement(f=>{f.manifest.bindings[1].replaceUnapprovedProposal=clone(f.manifest.bindings[0].replaceUnapprovedProposal);},/existing unapproved proposal/);
  await rejectReplacement(f=>{f.manifest.bindings[0].replaceUnapprovedProposal.status='verified';},/forbidden field status/);
  await rejectReplacement(f=>{
    const b=f.manifest.bindings[0];Object.assign(b,{declaration:f.old.declaration,file:f.old.file,module:f.old.module});
    f.snapshot.declarations[f.old.declaration]={...clone(f.snapshot.declarations['Project.claim0']),file:f.old.file,module:f.old.module};
  },/replacement requested without a binding change/);
  await rejectReplacement(f=>{f.manifest.bindings.push(clone(f.manifest.bindings[0]));},/duplicate binding/);
  await rejectReplacement(f=>{f.manifest.baseLedgerDigest='old';},/ledger head changed/);
  // Native-store observations in protected states must never be editable here.
  for(const change of [b=>b.status='verified',b=>b.status='stale',
    ...['semanticApprovalDecisionId','receipt','leanEvidenceSnapshotId','verifiedByDecisionId','staleReason'].map(k=>b=>b[k]=null)]) {
    await rejectReplacement(f=>{
      const read=f.store.readCurrent.bind(f.store);
      f.store.readCurrent=async id=>{const cur=clone(await read(id));change(cur.ledger.bindings.find(b=>b.id===f.old.id));return cur;};
    },/approved\/receipt-bearing\/verified\/stale/);
  }
  // A declaration already used by an untouched active proposal cannot be duplicated.
  await rejectReplacement(async f=>{
    const cur=await f.store.readCurrent('target');
    await f.store.publishDecision({id:'other-active-binding',ledgerId:'ledger',baseLedgerDigest:cur.head.ledgerDigest,
      actor:'planner',mode:'automatic',provenance:'fixture',kind:'put-binding',binding:{...f.old,id:'other-id',
        obligationId:'ob1',declaration:'Project.claim0'}});
    f.manifest.baseLedgerDigest=(await f.store.readCurrent('target')).head.ledgerDigest;
    f.manifest.bindings=f.manifest.bindings.slice(0,1);
  },/duplicate active declaration binding/);
  // A correction may free a declaration for a later obligation, but not after
  // that declaration has already been reused. Test every real publication.
  const ordered=await setupReplacement('Project.claim1');
  const publishOrdered=ordered.store.publishDecision.bind(ordered.store);
  ordered.store.publishDecision=async decision=>{
    const publication=await publishOrdered(decision);
    const live=(await ordered.store.readCurrent('target')).ledger.bindings.filter(b=>
      b.status!=='rejected' && b.status!=='superseded');
    assert.equal(new Set(live.map(b=>b.role+'\0'+b.declaration)).size,live.length,
      'every intermediate native state retains unique active declarations');
    return publication;
  };
  await runReview(ordered.manifest,ordered.host,{apply:true});
  const reversed=await setupReplacement('Project.claim1');
  reversed.manifest.bindings.reverse();
  const reversedBefore=JSON.stringify([...reversed.files]),reversedWrites=reversed.getWrites();
  await assert.rejects(()=>runReview(reversed.manifest,reversed.host,{apply:true}),
    /publication order would duplicate an active declaration binding/);
  assert.equal(reversed.getWrites(),reversedWrites,'unsafe publication order fails before all writes');
  assert.equal(JSON.stringify([...reversed.files]),reversedBefore);
  // Another writer after review is refused before replacement; no old event is removed.
  await rejectReplacement(f=>{f.host.withIdleLease=async fn=>{
    const cur=await f.store.readCurrent('target'),ev={kind:'source-reading',anchors:[]};ev.id=f.ctx.Sf(ev);
    await f.store.publishDecision({id:'interloper',ledgerId:'ledger',baseLedgerDigest:cur.head.ledgerDigest,actor:'author',mode:'automatic',
      provenance:'another writer',kind:'put-evidence',evidence:ev});
    return fn();
  };},/ledger head changed/,1);
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
async function makeApproved(make=setup) {
  const f=await make();await runReview(f.manifest,f.host,{apply:true});
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
  const replaced=await makeApproved(setupReplacement);
  const replacedVerified=await compileLoop(replaced.ctx,original)(replaced.store,'target',replaced.Fi,replaced.jn,
    {sourceFingerprint:replaced.snapshot.pins.leanSources});
  assert.equal(replaced.ctx.Vy(replacedVerified.ledger,{leanEvidence:new Map([[replaced.jn,replaced.Fi]]),requireCertifiedSurface:true}).length,0,
    'replacement proposals must still pass the unchanged real validator and full surface check');
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
module.exports={nativeHarness,compileLoop};
if(require.main===module)(async()=>{
  await testAdapter();await testReplacement();const hashes=await testValidator();
  console.log(JSON.stringify({ok:true,tests:'native replay/publication, explicit pinned unapproved-proposal replacement, dry-run, provenance-only exclusions, strict pins, authority, concurrency, and unchanged real validator verify/refresh/stale and negative-control regression',validator:hashes},null,2));
})().catch(e=>{console.error(e);process.exitCode=1;});
