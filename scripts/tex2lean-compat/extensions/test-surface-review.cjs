'use strict';
const assert=require('node:assert/strict');
const fs=require('node:fs');
assert(process.argv.length===3,'Usage: node test-surface-review.cjs /path/to/v8/out/cli.cjs');
const {nativeHarness,compileLoop}=require('./test-adapter.cjs');
const {PROVENANCE,NONMATHEMATICAL}=require('./adapter.cjs');
const {runSurfaceReview,inventoryDigest,stateDigest,preservedState,countingOwnership,COUNT,MAIN,HELPER,COUNT_OWNER}=require('./surface-review.cjs');
const {extractValidatorLoop}=require('./validator-loop.cjs');
const clone=x=>JSON.parse(JSON.stringify(x));
const mainNames=['AntichainOfGivenSize.alpha_eventual_upper','AntichainOfGivenSize.alpha_lower_density_one',MAIN,
  'AntichainOfGivenSize.alpha_maximum_order','AntichainOfGivenSize.Paper.mem_realGoodInputs_iff',
  'AntichainOfGivenSize.Paper.density_representations','AntichainOfGivenSize.Paper.maximumBelow_spec'];
const identity=name=>({declaration:name,role:'headline',file:'AntichainOfGivenSize/Model/Theorem.lean',module:'AntichainOfGivenSize.Model.Theorem'});
async function setup(counting=false) {
  const f=nativeHarness(),P=f.ctx.Pt,names=counting?[COUNT,...Array.from({length:10},(_,i)=>`AntichainOfGivenSize.Paper.exact${i}`)]:mainNames;
  const texts=names.map((_,i)=>`Exact mathematical claim ${i}.`).concat(counting?[...NONMATHEMATICAL.keys()]:[]);
  const pins={paperPacket:P('fixture','paper'),leanSources:P('fixture','sources'),configuration:P('fixture','config'),toolchain:P('fixture','toolchain')};
  const bindings=names.map((name,i)=>({id:`b${i}`,obligationId:`ob${i}`,...identity(name),status:'proposed'}));
  const old={id:'original-surface',targetVersionId:'tv',source:'sealed-blueprint',blueprintDigest:P('blueprint','old'),
    declarations:(counting?[COUNT]:[COUNT,...mainNames.slice(0,4),HELPER]).map(identity)};
  const ledger={schema:'tex2lean.paper-proof-ledger/1',ledgerId:'ledger',paper:{id:'paper'},target:{id:'target',paperId:'paper',activeVersionId:'tv'},
    activeClaimSetReceiptId:'receipt',activeSurfaceInventoryId:old.id,
    targetVersions:[{id:'tv',targetId:'target',paperPacketDigest:pins.paperPacket,status:'active'}],
    claims:texts.map((_,i)=>({id:`c${i}`,targetId:'target',activeVersionId:`v${i}`,role:'reportable'})),
    claimVersions:texts.map((text,i)=>({id:`v${i}`,claimId:`c${i}`,targetVersionId:'tv',text,status:'active'})),
    plans:texts.map((_,i)=>({claimVersionId:`v${i}`,disposition:i<names.length?'formalize':'exclude',
      ...(i<names.length?{requirements:{allOf:[{anyOf:[`ob${i}`]}]}}:{}),evidenceIds:[],reason:'earlier review'})),
    obligations:texts.map((text,i)=>({id:`ob${i}`,kind:'headline',summary:text,status:'materialized'})),
    bindings,leanRelations:[],claimSetReceipts:[{id:'receipt',targetVersionId:'tv',paperPacketDigest:pins.paperPacket,
      claimVersionIds:texts.map((_,i)=>`v${i}`)}],evidence:[],surfaceInventories:[old],appliedDecisionIds:[]};
  await f.store.publishGenesis(ledger);
  for(const b of bindings) {
    const cur=await f.store.readCurrent('target'),id='approval-'+b.id;
    await f.store.publishDecision({id,ledgerId:'ledger',baseLedgerDigest:cur.head.ledgerDigest,actor:'author',mode:'automatic',
      provenance:'fixture: earlier truthful semantic review',kind:'put-binding',binding:{...b,semanticApprovalDecisionId:id}});
  }
  const current=await f.store.readCurrent('target'),paper=texts.concat(['Separate counting theorem.','The conditional lemma is used in the unconditional conclusion.']).join('\n');
  const file={text:paper,digest:P('file',paper),kind:'paper'},q=i=>({file:'paper/main.tex',from:i+1,to:i+1,text:paper.split('\n')[i],fileDigest:file.digest});
  const allNames=[...new Set([...names,COUNT,HELPER,COUNT_OWNER,MAIN])];
  const declarations=Object.fromEntries(allNames.map((name,i)=>[name,{...identity(name),elaboratedType:`ExactType${i}`,
    semanticDefinitions:[],inCertifiedModuleClosure:true}]));
  const proofFacts={sourceFingerprint:pins.leanSources,declarations:Object.fromEntries(allNames.map(name=>[name,{
    file:identity(name).file,hasSorry:false,references:name===MAIN?[HELPER]:name===COUNT?[COUNT_OWNER]:[]}]))};
  const ownership={label:'thm:attainable-count',targetId:'counting-target',targetVersionId:'count-tv',ledgerDigest:'count-head',
    paperPacketDigest:'count-packet',capstone:COUNT,blueprint:'.blueprint/count/blueprint.json',blueprintDigest:'count-blueprint'};
  const snapshot={complete:true,diagnosticsComplete:true,pins,interfaceEvidenceSourceFingerprint:pins.leanSources,
    leanProofFactsFingerprint:pins.leanSources,buildFingerprint:pins.leanSources,
    idle:{workers:0,liveTransactions:0,otherLease:false,workflowRunning:false},files:{'paper/main.tex':file},declarations,
    targetLabel:counting?'thm:attainable-count':'thm:main',capstone:counting?COUNT:MAIN,proofFacts,
    ...counting?{}:{relatedCountingTarget:ownership}};
  const row=(name,index)=>({...identity(name),elaboratedType:declarations[name].elaboratedType,semanticDefinitions:[],sourceQuote:q(index),
    reason:'Reviewed exact statement and mathematical ownership.'});
  const manifest={schema:'tex2lean.delegated-surface-review/1',targetId:'target',targetVersionId:'tv',baseLedgerDigest:current.head.ledgerDigest,
    pins:clone(pins),review:{authority:'user-delegated-author',authorizationDigest:P('authorization','explicit task'),provenance:PROVENANCE},
    expectedInventory:clone(old),expectedInventoryDigest:inventoryDigest(f.ctx,old),expectedPreservedStateDigest:stateDigest(f.ctx,current.ledger),
    declarations:names.map(row),changes:{additions:names.filter(name=>!old.declarations.some(b=>b.declaration===name)).map(declaration=>({declaration,reason:'Exact reviewed mathematical obligation.'})),
      removals:counting?[]:[{...row(COUNT,texts.length),category:'separate-counting-target',ownership:clone(ownership)},
        {...row(HELPER,texts.length+1),category:'proved-conditional-helper'}]},reason:'Correct the target scope, preserving all claims and source proofs.'};
  let writes=0;const publish=f.store.publishDecision.bind(f.store);
  f.store.publishDecision=async d=>{writes++;return publish(d)};
  const host={native:f.ctx,store:f.store,authorizedUserRequestDigest:manifest.review.authorizationDigest,
    captureSnapshot:async()=>clone(snapshot),withIdleLease:async fn=>fn()};
  return {...f,manifest,snapshot,host,before:clone(current.ledger),getWrites:()=>writes};
}
async function reject(change,pattern,counting=false) {
  const f=await setup(counting);await change(f);const before=f.getWrites();
  await assert.rejects(()=>runSurfaceReview(f.manifest,f.host,{apply:true}),pattern);
  assert.equal(f.getWrites(),before,'failed review writes no native decisions');
}
async function verifyNative(f) {
  const {loop}=extractValidatorLoop(fs.readFileSync(process.argv[2],'utf8'));
  const current=await f.store.readCurrent('target');
  const Fi={schema:'tex2lean.lean-evidence/1',sourceFingerprint:f.snapshot.pins.leanSources,
    buildFingerprint:f.snapshot.pins.leanSources,dependencyFingerprint:f.snapshot.pins.leanSources,toolchainDigest:f.snapshot.pins.toolchain,
    relationEvidence:[],interfaceReceipts:current.ledger.bindings.map(b=>{
      const receipt={sourceSignatureDigest:'signature-'+b.id,elaboratedTypeDigest:'type-'+b.id,semanticRootPolicyId:'project-type-closure/1',
        semanticRootDigests:[],leanVersion:'synthetic-test-only',toolchainDigest:f.snapshot.pins.toolchain,optionsDigest:'test-options'};
      return {bindingId:b.id,declaration:b.declaration,receiptDigest:f.ctx.Tu(receipt),receipt};})};
  const jn=await f.store.writeLeanEvidence(Fi),result=await compileLoop(f.ctx,loop)(f.store,'target',Fi,jn,
    {sourceFingerprint:f.snapshot.pins.leanSources});
  assert.equal(f.ctx.Vy(result.ledger,{leanEvidence:new Map([[jn,Fi]]),requireCertifiedSurface:true}).length,0);
}
async function main() {
  for(const counting of [false,true]) {
    const f=await setup(counting),before=JSON.stringify([...f.files]);
    const dry=await runSurfaceReview(f.manifest,f.host);assert.equal(dry.publications.length,0);assert.equal(f.getWrites(),0);
    assert.equal(JSON.stringify([...f.files]),before);
    const result=await runSurfaceReview(f.manifest,f.host,{apply:true}),after=await f.store.readCurrent('target');
    assert.equal(result.publications.length,3);assert.deepEqual(preservedState(after.ledger),preservedState(f.before));
    assert.equal(after.ledger.surfaceInventories.length,2);assert.deepEqual(after.ledger.surfaceInventories[0],f.before.surfaceInventories[0]);
    assert.equal(after.ledger.surfaceInventories[1].source,'author-reviewed-target-scope');
    assert.equal(after.ledger.surfaceInventories[1].declarations.length,counting?11:7);
    assert.equal(after.ledger.claimSetReceipts[0].claimVersionIds.length,counting?13:7);
    assert.equal(after.ledger.bindings.filter(b=>b.status==='verified').length,0);
    assert.equal(f.ctx.Vy(after.ledger,{requireCertifiedSurface:true}).filter(e=>e.code==='surface-binding').length,counting?11:7,
      'inventory correction does not certify proposed bindings');
    assert(!after.head.certifiedSnapshotDigest);
    const events=[...f.files].filter(([p])=>p.includes('/decisions/')).map(([,v])=>JSON.parse(v)).filter(d=>d.provenance.startsWith(PROVENANCE));
    assert.deepEqual(events.map(e=>e.kind),['put-evidence','put-surface-inventory','select-surface-inventory']);
    assert(events.every(e=>e.actor==='author'));assert.equal(new Set(events.map(e=>e.baseLedgerDigest)).size,3);
    await verifyNative(f);
  }
  await reject(f=>f.manifest.declarations.pop(),/exactly all mathematical bindings/);
  await reject(f=>f.manifest.declarations=[],/exactly all mathematical bindings/);
  await reject(f=>f.manifest.declarations.push(clone(f.manifest.declarations[0])),/exactly all mathematical bindings/);
  await reject(f=>f.manifest.changes.additions.pop(),/unreviewed inventory addition/);
  await reject(f=>f.manifest.changes.removals.pop(),/unreviewed inventory removal/);
  await reject(f=>f.manifest.changes.removals[0].reason='',/scope reason/);
  await reject(f=>f.manifest.changes.removals[1].category='not-a-claim',/Expected values/);
  await reject(f=>f.snapshot.proofFacts.declarations[MAIN].references=[],/does not directly reference/);
  await reject(f=>f.snapshot.proofFacts.declarations[COUNT].references=[],/does not directly reference/);
  await reject(f=>f.snapshot.proofFacts.declarations[HELPER].hasSorry=true,/open native proof facts/);
  await reject(f=>f.snapshot.proofFacts.sourceFingerprint='old',/proof-reference evidence is stale/);
  await reject(f=>f.snapshot.relatedCountingTarget.ledgerDigest='new',/ownership changed/);
  await reject(f=>f.manifest.declarations[0].elaboratedType='True',/elaborated type changed/);
  await reject(f=>f.manifest.declarations[0].semanticDefinitions=[{}],/definition review/);
  await reject(f=>f.manifest.declarations[0].sourceQuote.text='invented',/quote is not exact/);
  await reject(f=>f.manifest.expectedInventory.declarations=[],/old record\/digest mismatch/);
  await reject(f=>f.manifest.expectedInventoryDigest='wrong',/active inventory changed/);
  await reject(f=>f.manifest.expectedPreservedStateDigest='old',/claims\/receipts\/plans\/bindings changed/);
  await reject(f=>f.manifest.baseLedgerDigest='old',/ledger head changed/);
  await reject(f=>f.manifest.review.authorizationDigest='other',/trusted authorization/);
  await reject(f=>f.snapshot.targetLabel='another-target',/unsupported paper target/);
  await reject(f=>f.snapshot.pins.toolchain='old',/toolchain changed/);
  // Independent ownership must be actual reviewed ledger coverage, not merely a
  // blueprint declaring COUNT. Historical status is reported without upgrading it.
  const owning=await setup(true),ownLedger=(await owning.store.readCurrent('target')).ledger;
  assert.equal(countingOwnership(ownLedger).binding.status,'proposed');
  for(const status of ['verified','stale']) {
    const l=clone(ownLedger);l.bindings[0].status=status;l.bindings[0].receipt={historical:true};
    assert.equal(countingOwnership(l).binding.status,status);assert.deepEqual(countingOwnership(l).binding.receipt,{historical:true});
  }
  for(const change of [l=>l.bindings=[],l=>l.bindings[0].status='rejected',l=>l.bindings[0].status='superseded',
    l=>l.plans[0].disposition='exclude',l=>l.claimSetReceipts[0].claimVersionIds.shift(),
    l=>delete l.bindings[0].semanticApprovalDecisionId]) {
    const l=clone(ownLedger);change(l);assert.throws(()=>countingOwnership(l),/counting/);
  }
  // Even self-consistent new heads cannot reclassify a mathematical obligation
  // or avoid the exact two already-reviewed metadata exclusions.
  await reject(async f=>{
    const r=await f.store.readCurrent('target');
    await f.store.publishDecision({id:'bad-math-exclusion',ledgerId:'ledger',baseLedgerDigest:r.head.ledgerDigest,
      actor:'author',mode:'automatic',provenance:'test-only invalid scope candidate',kind:'set-disposition',claimVersionId:'v0',
      plan:{claimVersionId:'v0',disposition:'exclude',evidenceIds:[],reason:'test negative control'}});
    const now=await f.store.readCurrent('target');f.manifest.baseLedgerDigest=now.head.ledgerDigest;
    f.manifest.expectedPreservedStateDigest=stateDigest(f.ctx,now.ledger);
  },/every mathematical claim must remain formalize/);
  await reject(async f=>{
    const r=await f.store.readCurrent('target');
    await f.store.publishDecision({id:'metadata-not-excluded',ledgerId:'ledger',baseLedgerDigest:r.head.ledgerDigest,
      actor:'author',mode:'automatic',provenance:'test-only incomplete metadata review',kind:'set-disposition',claimVersionId:'v11',
      plan:{claimVersionId:'v11',disposition:'formalize',requirements:{allOf:[{anyOf:['ob11']}]},evidenceIds:[],reason:'test'}});
    const now=await f.store.readCurrent('target');f.manifest.baseLedgerDigest=now.head.ledgerDigest;
    f.manifest.expectedPreservedStateDigest=stateDigest(f.ctx,now.ledger);
  },/metadata must already have its reviewed exclusion/,true);
  await reject(async f=>{
    const r=await f.store.readCurrent('target'),binding={...r.ledger.bindings[0]};delete binding.semanticApprovalDecisionId;
    await f.store.publishDecision({id:'unreviewed',ledgerId:'ledger',baseLedgerDigest:r.head.ledgerDigest,
      actor:'planner',mode:'automatic',provenance:'test-only unreviewed binding',kind:'put-binding',binding});
    const now=await f.store.readCurrent('target');f.manifest.baseLedgerDigest=now.head.ledgerDigest;
    f.manifest.expectedPreservedStateDigest=stateDigest(f.ctx,now.ledger);
  },/binding lacks native semantic approval/);
  // Native authority guard remains decisive even for a structurally valid new inventory.
  const authority=await setup(),cur=await authority.store.readCurrent('target');
  await assert.rejects(()=>authority.store.publishDecision({id:'unauthorized',ledgerId:'ledger',baseLedgerDigest:cur.head.ledgerDigest,
    actor:'planner',mode:'automatic',provenance:'not reviewed',kind:'select-surface-inventory',inventoryId:'original-surface'}),/requires a reviewed proposal/);
  // Interrupt after put: immutable evidence/new inventory remain, original active scope remains.
  const stop=await setup(),publish=stop.store.publishDecision.bind(stop.store);let n=0;
  stop.store.publishDecision=async decision=>{if(++n===3)throw Error('simulated interruption');return publish(decision)};
  await assert.rejects(()=>runSurfaceReview(stop.manifest,stop.host,{apply:true}),/simulated interruption/);
  const stopped=await stop.store.readCurrent('target');assert.equal(stopped.ledger.activeSurfaceInventoryId,'original-surface');
  assert.equal(stopped.ledger.surfaceInventories.length,2);assert.deepEqual(preservedState(stopped.ledger),preservedState(stop.before));
  for(const change of [f=>f.snapshot.proofFacts.declarations[MAIN].references=[],
    f=>f.snapshot.relatedCountingTarget.ledgerDigest='changed-counting-head']) {
    const mid=await setup(),publishMid=mid.store.publishDecision.bind(mid.store);
    mid.store.publishDecision=async d=>{const result=await publishMid(d);change(mid);return result;};
    await assert.rejects(()=>runSurfaceReview(mid.manifest,mid.host,{apply:true}),/directly reference|counting ownership changed/);
    assert.equal(mid.getWrites(),1);assert.equal((await mid.store.readCurrent('target')).ledger.activeSurfaceInventoryId,'original-surface');
  }
  // A racing writer is refused; existing history is never rolled back or forged.
  const race=await setup();race.host.withIdleLease=async fn=>{
    const r=await race.store.readCurrent('target'),e={kind:'source-reading',anchors:[]};e.id=race.ctx.Sf(e);
    await race.store.publishDecision({id:'outside',ledgerId:'ledger',baseLedgerDigest:r.head.ledgerDigest,actor:'author',mode:'automatic',
      provenance:'outside writer',kind:'put-evidence',evidence:e});return fn();};
  await assert.rejects(()=>runSurfaceReview(race.manifest,race.host,{apply:true}),/ledger head changed/);assert.equal(race.getWrites(),1);
  console.log(JSON.stringify({ok:true,tests:'native immutable inventory publication; exact 7/11 math coverage; preserved claims/receipts/status/history; fixed justified removals; compiler reference pins; dry-run; authority/head guards; interruption safety; unchanged native validator still requires verification',nativeWorkflowExecuted:false,compilerExecuted:false},null,2));
}
main().catch(e=>{console.error(e);process.exitCode=1;});
