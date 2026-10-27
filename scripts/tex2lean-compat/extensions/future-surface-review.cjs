'use strict';
// Optional, fail-closed target scoping. This never certifies proofs or edits claims.
const assert=require('node:assert/strict');
const {PROVENANCE,reviewChecks}=require('./adapter.cjs');
const {inventoryDigest,stateDigest}=require('./surface-review.cjs');
const {keys,requiredText,pinInputs,quote,activeVersion,requirements}=reviewChecks;
const SCHEMA='tex2lean.delegated-future-surface-review/1';
const clone=x=>JSON.parse(JSON.stringify(x));
const tuple=b=>({declaration:b.declaration,role:b.role,file:b.file,module:b.module});
const sorted=xs=>[...xs].sort((a,b)=>a.declaration.localeCompare(b.declaration));
const active=b=>!['rejected','superseded'].includes(b.status);
const ALLOWED_AXIOMS=Object.freeze(['propext','Classical.choice','Quot.sound']);
function futureScope(label,origin,environment) {
  requiredText(label,'explicit numbered target label required');
  assert.equal(origin,'latex','future scope requires a frozen LaTeX target');
  assert(['theorem','lemma','corollary','claim'].includes(environment),'future scope accepts only numbered mathematical statements');
  assert(!['thm:main','thm:attainable-count'].includes(label),'main/counting must use their original scope rules');
}
function checkedReceipt(ledger) {
  const version=ledger.targetVersions.find(v=>v.id===ledger.target.activeVersionId);
  const receipt=ledger.claimSetReceipts.find(r=>r.id===ledger.activeClaimSetReceiptId);
  assert(receipt && receipt.targetVersionId===version?.id && receipt.paperPacketDigest===version.paperPacketDigest,
    'active claim-set receipt is missing or stale');
  assert(ledger.claims.length>0 && ledger.claims.every(c=>c.role==='reportable'),'all future claims must be reportable mathematical claims');
  const ids=ledger.claims.map(c=>activeVersion(ledger,c.activeVersionId).id);
  assert.equal(new Set(ids).size,ids.length,'duplicate active claim version');
  assert.deepEqual([...receipt.claimVersionIds].sort(),ids.sort(),'active receipt must cover every mathematical claim exactly');
  return receipt;
}
function completeBindings(ledger) {
  checkedReceipt(ledger);
  const bindings=ledger.claims.map(c=>{
    const req=requirements(ledger,c.activeVersionId);
    assert.equal(req.plan.disposition,'formalize','future mathematical claims cannot be excluded, assumed or unsupported');
    assert(req.plan.requirements?.allOf.length===1 && req.plan.requirements.allOf[0].anyOf.length===1,
      'one exact required obligation per mathematical claim is required');
    const obligation=ledger.obligations.find(o=>o.id===req.ids[0]);
    assert.equal(obligation?.kind,'headline','native mathematical headline obligation required');
    const bs=ledger.bindings.filter(b=>b.obligationId===obligation.id && active(b));
    assert.equal(bs.length,1,'one active binding per mathematical obligation required');
    const b=bs[0];assert.equal(b.role,'headline');
    assert(['proposed','verified'].includes(b.status) && b.semanticApprovalDecisionId &&
      ledger.appliedDecisionIds.includes(b.semanticApprovalDecisionId),'native semantic approval required');return b;
  });
  assert.equal(new Set(bindings.map(b=>b.id)).size,bindings.length,'shared mathematical obligation');
  assert.equal(new Set(bindings.map(b=>b.declaration)).size,bindings.length,'duplicate mathematical declaration');
  assert.deepEqual(ledger.bindings.filter(active).map(b=>b.id).sort(),bindings.map(b=>b.id).sort(),
    'active binding outside the exact mathematical claim set');return bindings;
}
function ownedBinding(ledger,id) {
  const binding=ledger.bindings.find(b=>b.id===id);
  assert(binding && binding.role==='headline' && binding.status==='verified','related binding must already be natively verified');
  for(const key of ['semanticApprovalDecisionId','verifiedByDecisionId'])
    assert(binding[key] && ledger.appliedDecisionIds.includes(binding[key]),'related binding lacks applied native review/verification');
  assert(binding.receipt && binding.leanEvidenceSnapshotId,'related binding lacks its native proof receipt');
  const obligation=ledger.obligations.find(o=>o.id===binding.obligationId);assert.equal(obligation?.kind,'headline');
  const plans=ledger.plans.filter(p=>p.disposition==='formalize' &&
    p.requirements?.allOf.some(g=>g.anyOf.includes(binding.obligationId)));
  assert.equal(plans.length,1,'related owner must retain its formalize plan');
  const plan=plans[0],claimVersion=activeVersion(ledger,plan.claimVersionId);
  const claim=ledger.claims.find(c=>c.id===claimVersion.claimId);assert.equal(claim?.role,'reportable');
  const receipt=ledger.claimSetReceipts.find(r=>r.id===ledger.activeClaimSetReceiptId);
  const version=ledger.targetVersions.find(v=>v.id===ledger.target.activeVersionId);
  assert(receipt && receipt.targetVersionId===version?.id && receipt.paperPacketDigest===version.paperPacketDigest &&
    receipt.claimVersionIds.filter(v=>v===claimVersion.id).length===1,'related owner is absent from the active claim receipt');
  const inventory=ledger.surfaceInventories.find(i=>i.id===ledger.activeSurfaceInventoryId);
  assert(inventory && inventory.targetVersionId===version.id,'related active inventory missing or stale');
  const entries=inventory.declarations.filter(x=>x.declaration===binding.declaration && x.role===binding.role);
  assert.equal(entries.length,1,'related owner absent/duplicated in active inventory');assert.deepEqual(tuple(entries[0]),tuple(binding));
  return clone({binding,obligation,plan,claim,claimVersion,claimSetReceipt:receipt,activeInventory:inventory});
}
function validateInspection(request) {
  keys(request,['relatedTargets','helperPaths'],'future inspection');
  assert(Array.isArray(request.relatedTargets) && Array.isArray(request.helperPaths),'explicit future ownership and paths required');
  const ids=new Set();
  for(const r of request.relatedTargets) {
    keys(r,['targetId','targetVersionId','ledgerDigest','blueprint','blueprintDigest','activeInventoryId','bindingIds'],'related target selector');
    for(const key of ['targetId','targetVersionId','ledgerDigest','blueprint','blueprintDigest','activeInventoryId'])requiredText(r[key],key);
    assert(!ids.has(r.targetId),'duplicate related target');ids.add(r.targetId);
    assert(Array.isArray(r.bindingIds) && r.bindingIds.length && new Set(r.bindingIds).size===r.bindingIds.length,'explicit unique owned binding IDs required');
    r.bindingIds.forEach(id=>requiredText(id,'owned binding ID'));
  }
  const helpers=new Set();
  for(const p of request.helperPaths) {
    keys(p,['declaration','path','ownerTargetId','ownerBindingId'],'reviewed helper path');requiredText(p.declaration,'helper name');
    assert(!helpers.has(p.declaration),'duplicate helper path');helpers.add(p.declaration);
    assert(Array.isArray(p.path) && p.path.length>=2 && p.path.every(n=>typeof n==='string'&&n.length) &&
      new Set(p.path).size===p.path.length && p.path.at(-1)===p.declaration,'explicit acyclic root-to-helper compiler path required');
    assert((p.ownerTargetId===undefined)===(p.ownerBindingId===undefined),'helper owner target/binding must be supplied together');
  }
  return request;
}
async function readRelatedTargets(request,{targetId,readProject,store,native}) {
  validateInspection(request);const result=[];
  for(const selector of request.relatedTargets) {
    assert.notEqual(selector.targetId,targetId,'related ownership must be a different target');
    const record=await readProject(selector.blueprint);
    assert.equal(record.digest,selector.blueprintDigest,'related blueprint changed');
    const blueprint=JSON.parse(record.text);assert(!blueprint.inProgress,'related blueprint is not finalized');
    assert.equal(blueprint.paperProofMapping?.targetId,selector.targetId,'related blueprint target changed');
    const current=await store.readCurrent(selector.targetId);assert(current,'explicit related target missing');
    assert.equal(current.head.ledgerDigest,selector.ledgerDigest,'related target head changed');
    assert.equal(current.ledger.target.activeVersionId,selector.targetVersionId,'related target version changed');
    assert.equal(current.ledger.activeSurfaceInventoryId,selector.activeInventoryId,'related active inventory changed');
    const b=blueprint.bundle,packet=native.Pt('paper-packet/1',{origin:b.origin,files:b.files,macros:b.macros,
      theoremEnvironments:b.theoremEnvironments,target:{body:b.target.body,start:b.target.start,end:b.target.end,environment:b.target.environment}});
    const version=current.ledger.targetVersions.find(v=>v.id===selector.targetVersionId);
    assert.equal(version?.paperPacketDigest,packet,'related paper packet changed');
    const paperSources={};
    for(const file of b.files)paperSources[file]=await readProject(file);
    assert(paperSources[b.target.start.file]?.text.includes(b.target.body),'related paper target source changed');
    for(const macro of b.macros??[])assert(paperSources[macro.source?.file]?.text.includes(macro.declaration),'related paper macro changed');
    result.push({selector:clone(selector),targetLabel:b.target.label,paperPacketDigest:packet,
      paperSourceDigests:Object.fromEntries(Object.entries(paperSources).map(([file,record])=>[file,record.digest])),
      capstone:blueprint.filePlan?.capstone??blueprint.decomposition?.capstone?.name,
      owned:selector.bindingIds.map(id=>ownedBinding(current.ledger,id))});
  }
  return result;
}
function checkedDeclaration(snapshot,row,extra=[]) {
  keys(row,['declaration','role','file','module','elaboratedType','semanticDefinitions','sourceQuote','reason',...extra],'reviewed declaration');
  const actual=snapshot.declarations?.[row.declaration];assert(actual?.inCertifiedModuleClosure===true,'declaration outside inspected module closure');
  assert.equal(actual.file,row.file,'reviewed declaration file changed');assert.equal(actual.module,row.module,'reviewed module changed');
  assert.equal(actual.elaboratedType,row.elaboratedType,'reviewed type changed');assert.deepEqual(actual.semanticDefinitions,row.semanticDefinitions,'full definition review changed');
  requiredText(row.reason,'explicit semantic scope reason');const q=quote(snapshot,row.sourceQuote);
  assert.equal(snapshot.files[q.file].kind,'paper','exact paper quotation required');return q;
}
function closedAxioms(snapshot,name) {
  const evidence=snapshot.fullAxiomEvidence?.declarations?.[name];
  assert(evidence && evidence.declaration===name && evidence.method==='native Lean.collectAxioms after module build',
    'fresh native full axiom evidence missing');
  assert.deepEqual(evidence.pins,snapshot.pins,'full axiom evidence has stale source/config/toolchain pins');
  assert.equal(evidence.module,snapshot.declarations?.[name]?.module,'axiom declaration module changed');
  assert(evidence.answered===true && evidence.sorried===false && Array.isArray(evidence.axioms) &&
    evidence.axioms.every(a=>ALLOWED_AXIOMS.includes(a)),'full native axiom closure is open, unknown or nonstandard');
  requiredText(evidence.output,'raw native axiom output required');return evidence;
}
function closedTheorem(snapshot,name) {
  closedAxioms(snapshot,name);
  assert.equal(snapshot.proofFacts?.sourceFingerprint,snapshot.pins.leanSources,'compiler theorem evidence stale');
  const fact=snapshot.proofFacts.declarations[name];
  assert(fact && ['theorem','lemma'].includes(fact.kind) && fact.hasSorry===false,
    'retained/owned root and removed helper must have closed compiler theorem evidence');
}
function validate(manifest,snapshot,current,host) {
  keys(manifest,['schema','targetLabel','targetId','targetVersionId','baseLedgerDigest','pins','review','expectedInventory',
    'expectedInventoryDigest','expectedPreservedStateDigest','declarations','inspection','relatedTargets','owners','axiomEvidence','changes','reason'],'future surface manifest');
  assert.equal(manifest.schema,SCHEMA);futureScope(manifest.targetLabel,snapshot.targetOrigin,snapshot.targetEnvironment);assert.equal(snapshot.targetLabel,manifest.targetLabel);
  keys(manifest.pins,['paperPacket','leanSources','configuration','toolchain'],'pins');pinInputs(manifest,snapshot);
  keys(manifest.review,['authority','authorizationDigest','provenance'],'review');assert.equal(manifest.review.authority,'user-delegated-author');
  assert.equal(manifest.review.provenance,PROVENANCE);requiredText(host.authorizedUserRequestDigest,'trusted authority required');
  assert.equal(manifest.review.authorizationDigest,host.authorizedUserRequestDigest,'trusted authorization differs');requiredText(manifest.reason,'target scope reason');
  const ledger=current?.ledger;assert(ledger,'target missing');assert.equal(ledger.target.id,manifest.targetId);
  assert.equal(ledger.target.activeVersionId,manifest.targetVersionId);assert.equal(current.head.ledgerDigest,manifest.baseLedgerDigest,'reviewed target head changed');
  assert.equal(ledger.targetVersions.find(v=>v.id===manifest.targetVersionId)?.paperPacketDigest,manifest.pins.paperPacket);
  assert.equal(stateDigest(host.native,ledger),manifest.expectedPreservedStateDigest,'protected mathematical state changed');
  const old=ledger.surfaceInventories.find(i=>i.id===ledger.activeSurfaceInventoryId);assert(old,'active inventory absent');
  assert.equal(old.targetVersionId,manifest.targetVersionId,'active inventory target version changed');
  assert.equal(inventoryDigest(host.native,old),manifest.expectedInventoryDigest,'active inventory changed');
  assert.equal(inventoryDigest(host.native,manifest.expectedInventory),manifest.expectedInventoryDigest,'old inventory record changed');
  const bindings=completeBindings(ledger),expected=sorted(bindings.map(tuple));assert(Array.isArray(manifest.declarations));
  assert.deepEqual(sorted(manifest.declarations.map(tuple)),expected,'inventory must cover all mathematical receipt obligations exactly');
  const quotes=manifest.declarations.map(row=>checkedDeclaration(snapshot,row));
  validateInspection(manifest.inspection);assert.deepEqual(manifest.inspection,snapshot.futureInspection,'explicit ownership/path selection changed');
  assert.deepEqual(manifest.relatedTargets,snapshot.relatedTargets,'related ownership evidence changed');
  assert.deepEqual(manifest.axiomEvidence,snapshot.fullAxiomEvidence,'full axiom evidence changed');
  const owners=new Map();assert(Array.isArray(manifest.owners));
  for(const related of snapshot.relatedTargets)for(const record of related.owned) {
    const key=related.selector.targetId+'\0'+record.binding.id;assert(!owners.has(key),'duplicate owned binding');owners.set(key,record.binding);
  }
  const reviewedOwnerKeys=[];
  for(const row of manifest.owners) {
    quotes.push(checkedDeclaration(snapshot,row,['targetId','bindingId']));const key=row.targetId+'\0'+row.bindingId;
    assert.deepEqual(tuple(owners.get(key)??{}),tuple(row),'reviewed ownership identity changed');reviewedOwnerKeys.push(key);closedTheorem(snapshot,row.declaration);
  }
  assert.deepEqual(reviewedOwnerKeys.sort(),[...owners.keys()].sort(),'every explicitly selected owner needs exact semantic review');
  const oldMap=new Map(old.declarations.map(x=>[x.declaration,x])),newMap=new Map(expected.map(x=>[x.declaration,x]));
  assert.equal(oldMap.size,old.declarations.length,'duplicate old inventory declaration');
  for(const [name,row] of oldMap)if(newMap.has(name))assert.deepEqual(tuple(row),newMap.get(name),'retained declaration identity changed');
  const added=expected.filter(x=>!oldMap.has(x.declaration)).map(x=>x.declaration).sort();
  const removed=old.declarations.filter(x=>!newMap.has(x.declaration)).map(x=>x.declaration).sort();
  keys(manifest.changes,['additions','removals'],'changes');
  assert(Array.isArray(manifest.changes.additions)&&Array.isArray(manifest.changes.removals),'explicit changes required');
  assert.deepEqual(manifest.changes.additions.map(x=>x.declaration).sort(),added,'unreviewed addition');
  for(const c of manifest.changes.additions){keys(c,['declaration','reason'],'addition');requiredText(c.reason,'addition reason');}
  assert.deepEqual(manifest.changes.removals.map(x=>x.declaration).sort(),removed,'unreviewed removal');assert(added.length||removed.length,'scope review changes nothing');
  const usedPaths=new Set(),usedOwners=new Set(),proofPaths=[];
  for(const removal of manifest.changes.removals) {
    quotes.push(checkedDeclaration(snapshot,removal,['category','ownerTargetId','ownerBindingId']));
    assert.deepEqual(tuple(removal),tuple(oldMap.get(removal.declaration)),'removed declaration identity changed');
    assert(!bindings.some(b=>b.declaration===removal.declaration),'mathematical claim binding cannot be removed');
    closedTheorem(snapshot,removal.declaration);
    if(removal.category==='separate-reviewed-target') {
      const key=removal.ownerTargetId+'\0'+removal.ownerBindingId;assert.deepEqual(tuple(owners.get(key)??{}),tuple(removal),'explicit separate owner missing');usedOwners.add(key);
    } else {
      assert.equal(removal.category,'proved-internal-helper','unsupported removal category');
      assert(removal.ownerTargetId===undefined && removal.ownerBindingId===undefined,'helper ownership belongs in its reviewed path');
      const path=manifest.inspection.helperPaths.find(p=>p.declaration===removal.declaration);assert(path,'explicit compiler helper path absent');usedPaths.add(path.declaration);
      if(path.ownerTargetId===undefined)assert(newMap.has(path.path[0]),'helper root must be a retained mathematical binding');
      else {const key=path.ownerTargetId+'\0'+path.ownerBindingId;assert.equal(owners.get(key)?.declaration,path.path[0],'explicit reviewed helper owner missing');usedOwners.add(key);}
      closedTheorem(snapshot,path.path[0]);
      assert.equal(snapshot.proofFacts?.sourceFingerprint,snapshot.pins.leanSources,'compiler path evidence stale');
      path.path.forEach((name,i)=>{
        closedAxioms(snapshot,name);const fact=snapshot.proofFacts.declarations[name];assert(fact && fact.hasSorry===false,'compiler path node missing or open');
        if(i+1<path.path.length)assert(fact.references.includes(path.path[i+1]),'reviewed path is not a compiler dependency path');
      });proofPaths.push(clone(path));
    }
  }
  assert.deepEqual([...usedPaths].sort(),manifest.inspection.helperPaths.map(p=>p.declaration).sort(),'unused/unreviewed helper path');
  assert.deepEqual([...usedOwners].sort(),[...owners.keys()].sort(),'unneeded related ownership selection');
  return {old,expected,quotes,proofPaths};
}
async function runFutureSurfaceReview(manifest,host,{apply=false}={}) {
  assert(typeof apply==='boolean');manifest=clone(manifest);const {native,store}=host;
  const manifestDigest=native.Pt('delegated-future-surface-manifest/1',manifest);
  const prepare=async()=>{const snapshot=await host.captureSnapshot(),current=await store.readCurrent(manifest.targetId);
    return {snapshot,current,plan:validate(manifest,snapshot,current,host)};};
  const initial=await prepare(),inventory={id:native.Pt('delegated-future-target-surface/1',{manifestDigest,targetVersionId:manifest.targetVersionId}),
    targetVersionId:manifest.targetVersionId,source:'author-reviewed-target-scope',declarations:initial.plan.expected};
  const summary={mode:apply?'apply':'dry-run',manifestDigest,previousInventory:initial.plan.old,inventory,changes:manifest.changes,
    proofPaths:initial.plan.proofPaths,proofCertification:'not run; unchanged native proof reconciliation and handoff remain mandatory'};
  if(!apply)return {...summary,publications:[]};assert(typeof host.withIdleLease==='function','exclusive idle lease required');
  return host.withIdleLease(async()=>{
    const {current,plan}=await prepare();let head=current.head.ledgerDigest;const publications=[];
    const evidence={kind:'source-reading',anchors:plan.quotes.map(q=>({file:q.file,from:q.from,to:q.to,excerptDigest:native.Pt('paper-target-excerpt/1',q.text)}))};evidence.id=native.Sf(evidence);
    const provenance=PROVENANCE+'\n'+JSON.stringify({manifestDigest,authorizationDigest:manifest.review.authorizationDigest,
      originalInventory:plan.old,changes:manifest.changes,relatedTargets:manifest.relatedTargets,proofPaths:plan.proofPaths,
      axiomEvidence:manifest.axiomEvidence,exactQuotes:plan.quotes,pins:manifest.pins,reason:manifest.reason});
    for(const payload of [{kind:'put-evidence',evidence},{kind:'put-surface-inventory',inventory},{kind:'select-surface-inventory',inventoryId:inventory.id}]) {
      const snapshot=await host.captureSnapshot(),fresh=await store.readCurrent(manifest.targetId);
      // Revalidate every source, receipt, owner, path and full axiom record at each fresh head.
      validate({...manifest,baseLedgerDigest:head},snapshot,fresh,host);
      const decision={...payload,ledgerId:fresh.ledger.ledgerId,baseLedgerDigest:head,actor:'author',mode:'automatic',provenance};
      decision.id=native.Pt('delegated-future-surface-decision/1',decision);const publication=await store.publishDecision(decision);
      publications.push(publication);head=publication.resultingLedgerDigest;
      assert.equal((await store.readCurrent(manifest.targetId))?.head.ledgerDigest,head,'published head replaced');
    }
    const final=await store.readCurrent(manifest.targetId),snapshot=await host.captureSnapshot();pinInputs(manifest,snapshot);
    assert.equal(final.head.ledgerDigest,head);assert.equal(stateDigest(native,final.ledger),manifest.expectedPreservedStateDigest);
    assert.deepEqual(final.ledger.surfaceInventories.filter(x=>x.id!==inventory.id),current.ledger.surfaceInventories);
    assert.deepEqual(snapshot.relatedTargets,manifest.relatedTargets,'related ownership changed after selection');
    assert.deepEqual(snapshot.fullAxiomEvidence,manifest.axiomEvidence,'axiom evidence changed after selection');
    return {...summary,publications,finalLedgerDigest:head};
  });
}
module.exports={SCHEMA,ALLOWED_AXIOMS,runFutureSurfaceReview,futureScope,validateInspection,readRelatedTargets,ownedBinding,completeBindings};
