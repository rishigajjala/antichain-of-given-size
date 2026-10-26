'use strict';
const assert=require('node:assert/strict'),fs=require('node:fs');
assert(process.argv.length===3,'Usage: node test-future-surface-review.cjs /path/to/v8/out/cli.cjs');
const {nativeHarness,compileLoop}=require('./test-adapter.cjs');
const {extractValidatorLoop}=require('./validator-loop.cjs');
const {PROVENANCE}=require('./adapter.cjs');
const {stateDigest,inventoryDigest,preservedState}=require('./surface-review.cjs');
const {SCHEMA,runFutureSurfaceReview,ownedBinding,readRelatedTargets,completeBindings}=require('./future-surface-review.cjs');
const clone=x=>JSON.parse(JSON.stringify(x));
const id=name=>({declaration:name,role:'headline',file:'Project/Model.lean',module:'Project.Model'});
const A='Project.futureOne',B='Project.futureTwo',OWN='Project.owned',MID='Project.middle',HELP='Project.helper';
async function verify(f,target,pins) {
  const {loop}=extractValidatorLoop(fs.readFileSync(process.argv[2],'utf8')),cur=await f.store.readCurrent(target);
  const evidence={schema:'tex2lean.lean-evidence/1',sourceFingerprint:pins.leanSources,buildFingerprint:pins.leanSources,
    dependencyFingerprint:pins.leanSources,toolchainDigest:pins.toolchain,relationEvidence:[],
    interfaceReceipts:cur.ledger.bindings.map(b=>{const receipt={sourceSignatureDigest:'s-'+b.id,elaboratedTypeDigest:'t-'+b.id,
      semanticRootPolicyId:'project-type-closure/1',semanticRootDigests:[],leanVersion:'synthetic-test-only',toolchainDigest:pins.toolchain,optionsDigest:'test-options'};
      return {bindingId:b.id,declaration:b.declaration,receiptDigest:f.ctx.Tu(receipt),receipt};})};
  const evidenceId=await f.store.writeLeanEvidence(evidence);
  await compileLoop(f.ctx,loop)(f.store,target,evidence,evidenceId,{sourceFingerprint:pins.leanSources});
}
async function setup() {
  const f=nativeHarness(),P=f.ctx.Pt;
  const pins={paperPacket:P('f','paper'),leanSources:P('f','sources'),configuration:P('f','config'),toolchain:P('f','toolchain')};
  async function publish(target,names,inventoryNames) {
    const bindings=names.map((name,i)=>({id:target+'b'+i,obligationId:target+'o'+i,...id(name),status:'proposed'}));
    const inventory={id:target+'inventory',targetVersionId:target+'v',source:'sealed-blueprint',declarations:inventoryNames.map(id)};
    const ledger={schema:'tex2lean.paper-proof-ledger/1',ledgerId:target+'ledger',paper:{id:'paper'},
      target:{id:target,paperId:'paper',activeVersionId:target+'v'},targetVersions:[{id:target+'v',targetId:target,paperPacketDigest:pins.paperPacket,status:'active'}],
      claims:names.map((_,i)=>({id:target+'c'+i,targetId:target,activeVersionId:target+'cv'+i,role:'reportable'})),
      claimVersions:names.map((_,i)=>({id:target+'cv'+i,claimId:target+'c'+i,targetVersionId:target+'v',text:'Exact mathematical statement '+i,status:'active'})),
      plans:names.map((_,i)=>({claimVersionId:target+'cv'+i,disposition:'formalize',requirements:{allOf:[{anyOf:[target+'o'+i]}]},evidenceIds:[]})),
      obligations:names.map((_,i)=>({id:target+'o'+i,kind:'headline',summary:'Exact claim '+i,status:'materialized'})),bindings,leanRelations:[],
      activeClaimSetReceiptId:target+'receipt',claimSetReceipts:[{id:target+'receipt',targetVersionId:target+'v',paperPacketDigest:pins.paperPacket,claimVersionIds:names.map((_,i)=>target+'cv'+i)}],
      activeSurfaceInventoryId:inventory.id,surfaceInventories:[inventory],evidence:[],appliedDecisionIds:[]};
    await f.store.publishGenesis(ledger);
    for(const b of bindings){const c=await f.store.readCurrent(target),decision=target+'approve'+b.id;
      await f.store.publishDecision({id:decision,ledgerId:ledger.ledgerId,baseLedgerDigest:c.head.ledgerDigest,actor:'author',mode:'automatic',
        provenance:'test-only earlier semantic review',kind:'put-binding',binding:{...b,semanticApprovalDecisionId:decision}});}
  }
  await publish('future',[A,B],[A,OWN,HELP]);await publish('owner',[OWN],[OWN]);await verify(f,'owner',pins);
  const current=await f.store.readCurrent('future'),related=await f.store.readCurrent('owner');
  const selector={targetId:'owner',targetVersionId:'ownerv',ledgerDigest:related.head.ledgerDigest,
    blueprint:'.blueprint/owner/blueprint.json',blueprintDigest:'owner-blueprint',activeInventoryId:'ownerinventory',bindingIds:['ownerb0']};
  const ownership={selector,targetLabel:'thm:earlier',paperPacketDigest:pins.paperPacket,capstone:OWN,
    paperSourceDigests:{'paper.tex':'paper-digest'},owned:[ownedBinding(related.ledger,'ownerb0')]};
  const inspection={relatedTargets:[clone(selector)],helperPaths:[{declaration:HELP,path:[A,MID,HELP]}]};
  const text='First exact mathematical claim.\nSecond exact mathematical claim.\nSeparate earlier theorem.\nAn internal helper used in its proof.';
  const file={text,digest:P('file',text),kind:'paper'},q=i=>({file:'paper.tex',from:i+1,to:i+1,text:text.split('\n')[i],fileDigest:file.digest});
  const declarations=Object.fromEntries([A,B,OWN,MID,HELP].map(name=>[name,{...id(name),elaboratedType:'TypeOf '+name,
    semanticDefinitions:[],inCertifiedModuleClosure:true}]));
  const proofFacts={sourceFingerprint:pins.leanSources,declarations:Object.fromEntries([A,B,OWN,MID,HELP].map(name=>[name,
    {file:'Project/Model.lean',kind:'theorem',hasSorry:false,references:name===A?[MID]:name===MID?[HELP]:[]}]))};
  const fullAxiomEvidence={declarations:Object.fromEntries([A,OWN,MID,HELP].map(name=>[name,{declaration:name,module:'Project.Model',
    method:'native Lean.collectAxioms after module build',pins:clone(pins),answered:true,sorried:false,axioms:['propext','Classical.choice','Quot.sound'],output:name+' depends only on standard axioms'}]))};
  const snapshot={complete:true,diagnosticsComplete:true,pins,interfaceEvidenceSourceFingerprint:pins.leanSources,
    leanProofFactsFingerprint:pins.leanSources,buildFingerprint:pins.leanSources,idle:{workers:0,liveTransactions:0,otherLease:false,workflowRunning:false},
    files:{'paper.tex':file},targetLabel:'thm:future',targetOrigin:'latex',targetEnvironment:'theorem',capstone:A,declarations,proofFacts,fullAxiomEvidence,
    futureInspection:inspection,relatedTargets:[ownership]};
  const row=(name,i)=>({...id(name),elaboratedType:declarations[name].elaboratedType,semanticDefinitions:[],sourceQuote:q(i),reason:'Exact reviewed paper meaning and target ownership.'});
  const old=current.ledger.surfaceInventories[0];
  const manifest={schema:SCHEMA,targetLabel:'thm:future',targetId:'future',targetVersionId:'futurev',baseLedgerDigest:current.head.ledgerDigest,pins:clone(pins),
    review:{authority:'user-delegated-author',authorizationDigest:P('auth','explicit task'),provenance:PROVENANCE},
    expectedInventory:clone(old),expectedInventoryDigest:inventoryDigest(f.ctx,old),expectedPreservedStateDigest:stateDigest(f.ctx,current.ledger),
    declarations:[row(A,0),row(B,1)],inspection:clone(inspection),relatedTargets:clone(snapshot.relatedTargets),
    owners:[{...row(OWN,2),targetId:'owner',bindingId:'ownerb0'}],axiomEvidence:clone(fullAxiomEvidence),
    changes:{additions:[{declaration:B,reason:'All exact mathematical obligations retained.'}],removals:[
      {...row(OWN,2),category:'separate-reviewed-target',ownerTargetId:'owner',ownerBindingId:'ownerb0'},
      {...row(HELP,3),category:'proved-internal-helper'}]},reason:'Scope shared-file inventory to exactly this target without changing any claim.'};
  let writes=0;const publishDecision=f.store.publishDecision.bind(f.store);f.store.publishDecision=async d=>{writes++;return publishDecision(d);};
  const host={native:f.ctx,store:f.store,authorizedUserRequestDigest:manifest.review.authorizationDigest,
    captureSnapshot:async()=>clone(snapshot),withIdleLease:async fn=>fn()};
  return {...f,pins,snapshot,manifest,host,before:clone(current.ledger),ownerBefore:clone(related.ledger),writes:()=>writes};
}
async function reject(change,re) {
  const f=await setup();await change(f);const writes=f.writes(),before=JSON.stringify([...f.files]);
  await assert.rejects(()=>runFutureSurfaceReview(f.manifest,f.host,{apply:true}),re);
  assert.equal(f.writes(),writes);assert.equal(JSON.stringify([...f.files]),before,'failed review changed native store');
}
async function main() {
  const f=await setup(),before=JSON.stringify([...f.files]);
  const dry=await runFutureSurfaceReview(f.manifest,f.host);assert.equal(dry.mode,'dry-run');assert.equal(f.writes(),0);assert.equal(JSON.stringify([...f.files]),before);
  const result=await runFutureSurfaceReview(f.manifest,f.host,{apply:true}),after=await f.store.readCurrent('future');
  assert.equal(result.publications.length,3);assert.deepEqual(preservedState(after.ledger),preservedState(f.before));
  assert.deepEqual(after.ledger.surfaceInventories[0],f.before.surfaceInventories[0]);assert.equal(after.ledger.surfaceInventories.length,2);
  assert.deepEqual((await f.store.readCurrent('owner')).ledger,f.ownerBefore,'related owner ledger was modified');
  assert.equal(after.ledger.claimSetReceipts[0].claimVersionIds.length,2);assert(after.ledger.bindings.every(b=>b.status==='proposed'));
  assert.equal(f.ctx.Vy(after.ledger,{requireCertifiedSurface:true}).filter(e=>e.code==='surface-binding').length,2);
  assert(!after.head.certifiedSnapshotDigest);await verify(f,'future',f.pins);
  assert.equal(f.ctx.Vy((await f.store.readCurrent('future')).ledger,{requireCertifiedSurface:true}).filter(e=>e.code==='surface-binding').length,0);
  for(const label of ['thm:main','thm:attainable-count'])await reject(f=>{f.manifest.targetLabel=label;f.snapshot.targetLabel=label;},/original scope rules/);
  for(const environment of ['definition','remark'])await reject(f=>f.snapshot.targetEnvironment=environment,/only numbered mathematical/);
  await reject(f=>f.snapshot.targetOrigin='lean',/frozen LaTeX/);
  await reject(f=>f.manifest.declarations.pop(),/all mathematical receipt/);
  await reject(f=>f.manifest.changes.removals.pop(),/unreviewed removal/);
  await reject(f=>f.manifest.changes.removals[1].category='nonmathematical',/unsupported removal/);
  await reject(f=>f.manifest.owners=[],/every explicitly selected owner/);
  await reject(f=>f.snapshot.relatedTargets[0].selector.ledgerDigest='changed',/ownership evidence changed/);
  await reject(f=>f.snapshot.proofFacts.declarations[MID].references=[],/compiler dependency path/);
  await reject(f=>f.snapshot.proofFacts.declarations[MID].hasSorry=true,/node missing or open/);
  await reject(f=>f.snapshot.proofFacts.declarations[A].kind='def',/compiler theorem evidence/);
  await reject(f=>f.snapshot.proofFacts.declarations[OWN].kind='def',/compiler theorem evidence/);
  await reject(f=>{delete f.snapshot.fullAxiomEvidence.declarations[HELP];delete f.manifest.axiomEvidence.declarations[HELP];},/full axiom evidence missing/);
  for(const change of [a=>a.answered=false,a=>a.sorried=true,a=>a.axioms.push('sorryAx'),a=>a.axioms.push('Project.badAxiom'),a=>a.pins.configuration='old'])
    await reject(f=>{change(f.snapshot.fullAxiomEvidence.declarations[MID]);f.manifest.axiomEvidence=clone(f.snapshot.fullAxiomEvidence);},/axiom closure|stale source/);
  await reject(f=>{f.manifest.inspection.helperPaths[0].path=[B,HELP];f.snapshot.futureInspection=clone(f.manifest.inspection);},/full axiom evidence missing|dependency path/);
  await reject(f=>f.manifest.declarations[0].elaboratedType='True',/reviewed type/);
  await reject(f=>f.manifest.declarations[0].semanticDefinitions=[{}],/definition review/);
  await reject(f=>f.manifest.declarations[0].sourceQuote.text='fiction',/quote is not exact/);
  await reject(f=>f.manifest.baseLedgerDigest='old',/target head changed/);
  await reject(f=>f.manifest.review.authorizationDigest='other',/authorization differs/);
  for(const disposition of ['exclude']) await reject(async f=>{
    const current=await f.store.readCurrent('future');
    // Native authority/store accepts the authored plan event; the optional future operation rejects its scope.
    await f.store.publishDecision({id:'invalid-plan-'+disposition,ledgerId:current.ledger.ledgerId,baseLedgerDigest:current.head.ledgerDigest,
      actor:'author',mode:'automatic',provenance:'test-only negative plan',kind:'set-disposition',claimVersionId:'futurecv0',
      plan:{claimVersionId:'futurecv0',disposition,evidenceIds:[],reason:'negative fixture'}});
    const now=await f.store.readCurrent('future');f.manifest.baseLedgerDigest=now.head.ledgerDigest;f.manifest.expectedPreservedStateDigest=stateDigest(f.ctx,now.ledger);
  },/cannot be excluded|Unsupported|unsupported|disposition/);
  for(const disposition of ['assume-instead','unsupported']) {
    const l=clone(f.before);l.plans[0].disposition=disposition;assert.throws(()=>completeBindings(l),/cannot be excluded, assumed or unsupported/);
  }
  const missing=clone(f.before);missing.claimSetReceipts[0].claimVersionIds.pop();assert.throws(()=>completeBindings(missing),/receipt must cover/);
  for(const change of [l=>l.bindings[0].status='proposed',l=>delete l.bindings[0].receipt,l=>l.activeSurfaceInventoryId='absent',
    l=>l.surfaceInventories[0].declarations=[],l=>l.claimSetReceipts[0].claimVersionIds=[],l=>l.plans[0].disposition='exclude']) {
    const l=clone(f.ownerBefore);change(l);assert.throws(()=>ownedBinding(l,'ownerb0'));
  }
  // Exercise the exact read-only owner collector: caller-selected IDs and heads,
  // full native ownership records, active inventory, current source and blueprint pins.
  const fixture=await setup(),selected=fixture.manifest.inspection.relatedTargets[0];
  const bundle={origin:'latex',files:['paper.tex'],macros:[],theoremEnvironments:['theorem'],
    target:{label:'thm:earlier',body:'Separate earlier theorem.',start:{file:'paper.tex',line:1},end:{file:'paper.tex',line:1},environment:'theorem'}};
  const packet=fixture.ctx.Pt('paper-packet/1',{origin:bundle.origin,files:bundle.files,macros:bundle.macros,
    theoremEnvironments:bundle.theoremEnvironments,target:{body:bundle.target.body,start:bundle.target.start,end:bundle.target.end,environment:bundle.target.environment}});
  const ownerCurrent=await fixture.store.readCurrent('owner');
  ownerCurrent.ledger.targetVersions[0].paperPacketDigest=packet;ownerCurrent.ledger.claimSetReceipts[0].paperPacketDigest=packet;
  const blueprint={bundle,paperProofMapping:{targetId:'owner'},filePlan:{capstone:OWN}};
  const records={'.blueprint/owner/blueprint.json':{text:JSON.stringify(blueprint),digest:selected.blueprintDigest},
    'paper.tex':{text:bundle.target.body,digest:'current-paper-digest'}};
  const collector={targetId:'future',native:fixture.ctx,store:{readCurrent:async target=>target==='owner'?clone(ownerCurrent):undefined},
    readProject:async file=>clone(records[file])};
  const collected=await readRelatedTargets(fixture.manifest.inspection,collector);
  assert.equal(collected[0].owned[0].binding.status,'verified');assert.equal(collected[0].paperSourceDigests['paper.tex'],'current-paper-digest');
  for(const [field,value] of [['ledgerDigest','wrong-head'],['targetVersionId','wrong-version'],['activeInventoryId','wrong-inventory'],['blueprintDigest','wrong-blueprint']]) {
    const request=clone(fixture.manifest.inspection);request.relatedTargets[0][field]=value;
    await assert.rejects(()=>readRelatedTargets(request,collector),/changed/);
  }
  const missingBinding=clone(fixture.manifest.inspection);missingBinding.relatedTargets[0].bindingIds=['absent'];
  await assert.rejects(()=>readRelatedTargets(missingBinding,collector),/natively verified/);
  records['paper.tex'].text='Changed source';await assert.rejects(()=>readRelatedTargets(fixture.manifest.inspection,collector),/paper target source changed/);
  const stop=await setup(),publish=stop.store.publishDecision.bind(stop.store);let n=0;
  stop.store.publishDecision=async d=>{if(++n===3)throw Error('interrupted');return publish(d);};
  await assert.rejects(()=>runFutureSurfaceReview(stop.manifest,stop.host,{apply:true}),/interrupted/);
  const stopped=await stop.store.readCurrent('future');assert.equal(stopped.ledger.activeSurfaceInventoryId,'futureinventory');
  assert.equal(stopped.ledger.surfaceInventories.length,2);assert.deepEqual(preservedState(stopped.ledger),preservedState(stop.before));
  for(const mutate of [f=>f.snapshot.relatedTargets[0].selector.ledgerDigest='drift',f=>f.snapshot.fullAxiomEvidence.declarations[HELP].answered=false]) {
    const mid=await setup(),pub=mid.store.publishDecision.bind(mid.store);mid.store.publishDecision=async d=>{const r=await pub(d);mutate(mid);return r;};
    await assert.rejects(()=>runFutureSurfaceReview(mid.manifest,mid.host,{apply:true}),/ownership evidence changed|axiom evidence changed/);
    assert.equal(mid.writes(),1);assert.equal((await mid.store.readCurrent('future')).ledger.activeSurfaceInventoryId,'futureinventory');
  }
  console.log(JSON.stringify({ok:true,tests:'actual native immutable store/replay; exact receipt coverage; all mathematical plans retained; explicit owners and full kernel axiom closure; source/head/authority guards; no status certification; native Vy still requires verification',runtimeExecuted:false,compilerExecuted:false},null,2));
}
main().catch(e=>{console.error(e);process.exitCode=1;});
