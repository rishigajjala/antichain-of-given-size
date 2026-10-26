'use strict';
// Reviewed target ownership only. Native proof receipts and certification are untouched.
const assert=require('node:assert/strict');
const {PROVENANCE,NONMATHEMATICAL,reviewChecks}=require('./adapter.cjs');
const {keys,requiredText,pinInputs,quote,activeVersion,requirements}=reviewChecks;
const clone=x=>JSON.parse(JSON.stringify(x));
const COUNT='AntichainOfGivenSize.attainable_count';
const MAIN='AntichainOfGivenSize.alpha_asymptotic_order';
const HELPER='AntichainOfGivenSize.alpha_simultaneous_density_one';
const COUNT_OWNER='AntichainOfGivenSize.Analysis.AttainableCountProof.attainableCount';
const scopeByLabel=new Map([
  ['thm:main',{math:7,metadata:0,capstone:MAIN}],
  ['thm:attainable-count',{math:11,metadata:2,capstone:COUNT}],
]);
const inventoryDigest=(native,x)=>native.Pt('delegated-surface-inventory/1',x);
// This includes every mathematical status and all original claim/receipt records.
function preservedState(ledger) {
  const {surfaceInventories,activeSurfaceInventoryId,evidence,appliedDecisionIds,...rest}=ledger;
  return rest;
}
const stateDigest=(native,ledger)=>native.Pt('delegated-surface-preserved-state/1',preservedState(ledger));
const tuple=b=>({declaration:b.declaration,role:b.role,file:b.file,module:b.module});
const sorted=xs=>[...xs].sort((a,b)=>a.declaration.localeCompare(b.declaration));
function countingOwnership(ledger) {
  const bindings=ledger.bindings.filter(b=>b.declaration===COUNT && b.role==='headline' &&
    !['rejected','superseded'].includes(b.status));
  assert.equal(bindings.length,1,'separate counting target must retain one active counting binding');
  const binding=bindings[0];
  assert(['proposed','verified','stale'].includes(binding.status) && binding.semanticApprovalDecisionId &&
    ledger.appliedDecisionIds.includes(binding.semanticApprovalDecisionId),'separate counting binding lacks semantic ownership review');
  const obligation=ledger.obligations.find(o=>o.id===binding.obligationId);
  assert.equal(obligation?.kind,'headline','separate counting obligation missing');
  const plans=ledger.plans.filter(p=>p.disposition==='formalize' &&
    p.requirements?.allOf.some(g=>g.anyOf.includes(binding.obligationId)));
  assert.equal(plans.length,1,'separate counting target must retain its formalize plan');
  const plan=plans[0],claimVersion=activeVersion(ledger,plan.claimVersionId);
  const claim=ledger.claims.find(c=>c.id===claimVersion.claimId);
  assert.equal(claim.role,'reportable','separate counting claim is not reportable');
  const claimSetReceipt=ledger.claimSetReceipts.find(r=>r.id===ledger.activeClaimSetReceiptId);
  assert(claimSetReceipt && claimSetReceipt.targetVersionId===ledger.target.activeVersionId &&
    claimSetReceipt.claimVersionIds.filter(id=>id===claimVersion.id).length===1,
    'separate counting claim is missing from the active receipt');
  const version=ledger.targetVersions.find(v=>v.id===ledger.target.activeVersionId);
  assert.equal(claimSetReceipt.paperPacketDigest,version?.paperPacketDigest,'separate counting receipt paper changed');
  // Retain the actual status/receipt, including a historically stale binding.
  // Fresh proof references elsewhere establish the current source relationship;
  // this ownership record never upgrades a historical native proof status.
  return clone({binding,obligation,plan,claim,claimVersion,claimSetReceipt});
}
function mathematicalBindings(ledger,spec) {
  const bindings=[],metadata=[];
  assert(ledger.claims.every(c=>c.role==='reportable'),'unsupported non-reportable claim scope');
  for(const claim of ledger.claims) {
    const cv=activeVersion(ledger,claim.activeVersionId),req=requirements(ledger,cv.id);
    if(NONMATHEMATICAL.has(cv.text)) {
      assert.equal(req.plan.disposition,'exclude','metadata must already have its reviewed exclusion');
      assert.equal(req.ids.length,0,'excluded metadata retains requirements');metadata.push(cv.text);continue;
    }
    assert.equal(req.plan.disposition,'formalize','every mathematical claim must remain formalize');
    assert(req.plan.requirements.allOf.length===1 && req.plan.requirements.allOf[0].anyOf.length===1,
      'this reviewed scope requires one exact obligation per mathematical claim');
    const obligation=ledger.obligations.find(o=>o.id===req.ids[0]);
    assert(obligation && obligation.kind==='headline','mathematical headline obligation missing');
    const active=ledger.bindings.filter(b=>b.obligationId===obligation.id &&
      b.status!=='rejected' && b.status!=='superseded');
    assert.equal(active.length,1,'one reviewed binding per mathematical obligation required');
    const b=active[0];
    assert(['proposed','verified'].includes(b.status) && b.semanticApprovalDecisionId &&
      ledger.appliedDecisionIds.includes(b.semanticApprovalDecisionId),'binding lacks native semantic approval');
    assert.equal(b.role,'headline');bindings.push(b);
  }
  assert.equal(bindings.length,spec.math,'wrong number of retained mathematical claims');
  assert.equal(metadata.length,spec.metadata,'wrong metadata scope');
  assert.equal(new Set(metadata).size,metadata.length,'duplicate metadata claim');
  assert.equal(new Set(bindings.map(b=>b.id)).size,bindings.length,'shared obligation binding');
  assert.equal(new Set(bindings.map(b=>b.declaration)).size,bindings.length,'duplicate mathematical declaration');
  const active=ledger.bindings.filter(b=>b.status!=='rejected' && b.status!=='superseded');
  assert.deepEqual(active.map(b=>b.id).sort(),bindings.map(b=>b.id).sort(),'active bindings outside the mathematical claim set');
  return bindings;
}
function checkedDeclaration(snapshot,row) {
  const actual=snapshot.declarations?.[row.declaration];
  assert(actual?.inCertifiedModuleClosure===true,'review declaration outside certified closure');
  assert.equal(actual.file,row.file,'review file changed');assert.equal(actual.module,row.module,'review module changed');
  assert.equal(actual.elaboratedType,row.elaboratedType,'reviewed elaborated type changed');
  assert.deepEqual(actual.semanticDefinitions,row.semanticDefinitions,'semantic definition review changed or incomplete');
  requiredText(row.reason,'declaration scope reason');
  const q=quote(snapshot,row.sourceQuote);
  assert.equal(snapshot.files[q.file].kind,'paper','declaration review requires exact paper evidence');
  return q;
}
function directReference(snapshot,from,to) {
  assert.equal(snapshot.proofFacts?.sourceFingerprint,snapshot.pins.leanSources,'proof-reference evidence is stale');
  const a=snapshot.proofFacts.declarations[from],b=snapshot.proofFacts.declarations[to];
  assert(a && b && a.hasSorry===false && b.hasSorry===false,'reviewed helper has missing or open native proof facts');
  assert(a.references.includes(to),`native proof does not directly reference ${to}`);
  return {from,to,fromFile:a.file,toFile:b.file,sourceFingerprint:snapshot.pins.leanSources};
}
function validateSurface(manifest,snapshot,current,host) {
  keys(manifest,['schema','targetId','targetVersionId','baseLedgerDigest','pins','review',
    'expectedInventory','expectedInventoryDigest','expectedPreservedStateDigest','declarations','changes','reason'],'surface manifest');
  assert.equal(manifest.schema,'tex2lean.delegated-surface-review/1');
  keys(manifest.pins,['paperPacket','leanSources','configuration','toolchain'],'pins');
  keys(manifest.review,['authority','authorizationDigest','provenance'],'review');
  assert.equal(manifest.review.authority,'user-delegated-author');assert.equal(manifest.review.provenance,PROVENANCE);
  requiredText(host.authorizedUserRequestDigest,'trusted authorization required');
  assert.equal(manifest.review.authorizationDigest,host.authorizedUserRequestDigest,'trusted authorization differs');
  pinInputs(manifest,snapshot);requiredText(manifest.reason,'scope correction reason');
  const ledger=current?.ledger;assert(ledger,'mapping target missing');
  assert.equal(ledger.target.id,manifest.targetId);assert.equal(ledger.target.activeVersionId,manifest.targetVersionId);
  assert.equal(current.head.ledgerDigest,manifest.baseLedgerDigest,'reviewed ledger head changed');
  assert.equal(ledger.targetVersions.find(v=>v.id===manifest.targetVersionId)?.paperPacketDigest,manifest.pins.paperPacket);
  const spec=scopeByLabel.get(snapshot.targetLabel);assert(spec,'unsupported paper target for scope correction');
  assert.equal(snapshot.capstone,spec.capstone,'target capstone changed');
  assert.equal(stateDigest(host.native,ledger),manifest.expectedPreservedStateDigest,'claims/receipts/plans/bindings changed');
  const old=ledger.surfaceInventories.find(x=>x.id===ledger.activeSurfaceInventoryId);assert(old,'active inventory missing');
  assert.equal(inventoryDigest(host.native,old),manifest.expectedInventoryDigest,'active inventory changed');
  assert.equal(inventoryDigest(host.native,manifest.expectedInventory),manifest.expectedInventoryDigest,'old record/digest mismatch');
  const bindings=mathematicalBindings(ledger,spec),expected=sorted(bindings.map(tuple));
  assert(Array.isArray(manifest.declarations),'complete declaration review required');
  const quotes=manifest.declarations.map(row=>{
    keys(row,['declaration','role','file','module','elaboratedType','semanticDefinitions','sourceQuote','reason'],'surface declaration');
    return checkedDeclaration(snapshot,row);
  });
  assert.deepEqual(sorted(manifest.declarations.map(tuple)),expected,'inventory must cover exactly all mathematical bindings');
  const oldMap=new Map(old.declarations.map(b=>[b.declaration,b])),newMap=new Map(expected.map(b=>[b.declaration,b]));
  assert.equal(oldMap.size,old.declarations.length,'duplicate declaration in previous inventory');
  for(const [name,row] of oldMap) if(newMap.has(name)) assert.deepEqual(tuple(row),newMap.get(name),'retained inventory identity changed');
  const added=expected.filter(b=>!oldMap.has(b.declaration)).map(b=>b.declaration).sort();
  const removed=old.declarations.filter(b=>!newMap.has(b.declaration)).map(b=>b.declaration).sort();
  keys(manifest.changes,['additions','removals'],'inventory changes');
  assert(Array.isArray(manifest.changes.additions) && Array.isArray(manifest.changes.removals),'explicit inventory changes required');
  assert.deepEqual(manifest.changes.additions.map(x=>x.declaration).sort(),added,'unreviewed inventory addition');
  for(const change of manifest.changes.additions) {keys(change,['declaration','reason'],'addition');requiredText(change.reason,'addition reason');}
  assert.deepEqual(manifest.changes.removals.map(x=>x.declaration).sort(),removed,'unreviewed inventory removal');
  assert(added.length||removed.length,'inventory review makes no change');
  const proofReferences=[];
  if(snapshot.targetLabel==='thm:main') {
    assert.deepEqual(removed,[COUNT,HELPER].sort(),'main permits only the separate target and conditional helper removals');
    for(const removal of manifest.changes.removals) {
      keys(removal,['declaration','role','file','module','elaboratedType','semanticDefinitions','sourceQuote','reason',
        'category','ownership'],'removal');
      assert.deepEqual(tuple(removal),tuple(oldMap.get(removal.declaration)),'removed declaration identity changed');
      assert(!bindings.some(b=>b.declaration===removal.declaration),'cannot remove a mathematical obligation binding');
      quotes.push(checkedDeclaration(snapshot,removal));
      if(removal.declaration===HELPER) {
        assert.equal(removal.category,'proved-conditional-helper');assert.equal(removal.ownership,undefined);
        proofReferences.push(directReference(snapshot,MAIN,HELPER));
      } else {
        assert.equal(removal.category,'separate-counting-target');
        assert(snapshot.relatedCountingTarget,'independent counting ownership evidence missing');
        assert.deepEqual(removal.ownership,snapshot.relatedCountingTarget,'counting target ownership changed');
        assert.equal(removal.ownership.label,'thm:attainable-count');assert.equal(removal.ownership.capstone,COUNT);
        assert.notEqual(removal.ownership.targetId,manifest.targetId);
        proofReferences.push(directReference(snapshot,COUNT,COUNT_OWNER));
      }
    }
  } else {
    assert.deepEqual(removed,[],'counting scope may only expand');
    assert.deepEqual(old.declarations.map(b=>b.declaration),[COUNT],'unexpected original counting surface');
    assert.equal(added.length,10,'counting scope must expand to all eleven mathematical bindings');
  }
  return {old,expected,quotes,proofReferences};
}
async function runSurfaceReview(manifest,host,{apply=false}={}) {
  assert(typeof apply==='boolean','apply must be explicit boolean');manifest=clone(manifest);
  const {native,store}=host,manifestDigest=native.Pt('delegated-surface-review-manifest/1',manifest);
  const prepare=async()=>{const snapshot=await host.captureSnapshot(),current=await store.readCurrent(manifest.targetId);
    return {snapshot,current,plan:validateSurface(manifest,snapshot,current,host)};};
  const initial=await prepare();
  const inventory={id:native.Pt('delegated-target-surface/1',{manifestDigest,targetVersionId:manifest.targetVersionId}),
    targetVersionId:manifest.targetVersionId,source:'author-reviewed-target-scope',declarations:initial.plan.expected};
  const summary={mode:apply?'apply':'dry-run',manifestDigest,previousInventory:initial.plan.old,
    inventory,changes:manifest.changes,proofReferences:initial.plan.proofReferences,
    proofCertification:'not run; native proof reconciliation and handoff are mandatory'};
  if(!apply)return {...summary,publications:[]};
  assert(typeof host.withIdleLease==='function','exclusive idle lease required');
  return host.withIdleLease(async()=>{
    const {current,plan}=await prepare();let expectedHead=current.head.ledgerDigest;const publications=[];
    const evidence={kind:'source-reading',anchors:plan.quotes.map(q=>({file:q.file,from:q.from,to:q.to,
      excerptDigest:native.Pt('paper-target-excerpt/1',q.text)}))};evidence.id=native.Sf(evidence);
    const provenance=PROVENANCE+'\n'+JSON.stringify({manifestDigest,authorizationDigest:manifest.review.authorizationDigest,
      reason:manifest.reason,expectedInventoryDigest:manifest.expectedInventoryDigest,originalInventory:plan.old,
      changes:manifest.changes,exactQuotes:plan.quotes,proofReferences:plan.proofReferences,pins:manifest.pins});
    for(const payload of [{kind:'put-evidence',evidence},{kind:'put-surface-inventory',inventory},
      {kind:'select-surface-inventory',inventoryId:inventory.id}]) {
      const snapshot=await host.captureSnapshot();pinInputs(manifest,snapshot);
      for(const q of plan.quotes)quote(snapshot,q);
      for(const ref of plan.proofReferences)directReference(snapshot,ref.from,ref.to);
      if(initial.snapshot.relatedCountingTarget)assert.deepEqual(snapshot.relatedCountingTarget,
        initial.snapshot.relatedCountingTarget,'independent counting ownership changed');
      const fresh=await store.readCurrent(manifest.targetId);
      assert.equal(fresh?.head.ledgerDigest,expectedHead,'another ledger writer changed the head');
      assert.equal(stateDigest(native,fresh.ledger),manifest.expectedPreservedStateDigest,'protected mathematical state changed');
      assert.equal(fresh.ledger.activeSurfaceInventoryId,plan.old.id,'active inventory changed before selection');
      assert.equal(inventoryDigest(native,fresh.ledger.surfaceInventories.find(x=>x.id===plan.old.id)),
        manifest.expectedInventoryDigest,'original inventory history changed');
      const decision={...payload,ledgerId:fresh.ledger.ledgerId,baseLedgerDigest:expectedHead,
        actor:'author',mode:'automatic',provenance};decision.id=native.Pt('delegated-surface-decision/1',decision);
      const publication=await store.publishDecision(decision);publications.push(publication);
      expectedHead=publication.resultingLedgerDigest;
      assert.equal((await store.readCurrent(manifest.targetId))?.head.ledgerDigest,expectedHead,'published head replaced');
    }
    const final=await store.readCurrent(manifest.targetId),snapshot=await host.captureSnapshot();pinInputs(manifest,snapshot);
    assert.equal(final.head.ledgerDigest,expectedHead);assert.equal(stateDigest(native,final.ledger),manifest.expectedPreservedStateDigest);
    assert.deepEqual(final.ledger.surfaceInventories.filter(x=>x.id!==inventory.id),current.ledger.surfaceInventories);
    return {...summary,publications,finalLedgerDigest:expectedHead};
  });
}
module.exports={runSurfaceReview,inventoryDigest,stateDigest,preservedState,countingOwnership,COUNT,MAIN,HELPER,COUNT_OWNER};
