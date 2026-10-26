'use strict';
// Prototype only. No CLI bootstrap, filesystem writes, subprocesses or native-status edits.
const assert = require('node:assert/strict');
const PROVENANCE = 'Codex assistant review under user-authorized formalization; no human review asserted';
const NONMATHEMATICAL = new Map([
  ['The existing endpoint proves the exact target with a different, larger clustered record encoding; identify reuse honestly and preserve the correspondence note.', 'implementation-provenance'],
  ['This target asserts no probabilistic or computational resource result; the following uniformly sampled dyadic corollary is separate.', 'scope-metadata'],
]);
const clone = x => JSON.parse(JSON.stringify(x));
const same = (a,b) => JSON.stringify(a) === JSON.stringify(b);
function keys(x, allowed, where) {
  assert(x && typeof x === 'object' && !Array.isArray(x), where);
  for (const key of Object.keys(x)) assert(allowed.includes(key), `${where}: forbidden field ${key}`);
}
function requiredText(s, where) { assert(typeof s === 'string' && s.trim().length > 0, where); }
function idle(s) {
  assert(s.idle && s.idle.workers === 0 && s.idle.liveTransactions === 0 &&
    s.idle.otherLease === false && s.idle.workflowRunning === false,
    'project is busy or held by another operation');
}
function pinInputs(manifest, snapshot) {
  assert(snapshot.complete === true && snapshot.diagnosticsComplete === true,
    'complete source snapshot and completed Lean diagnostics required');
  assert.equal(snapshot.leanProofFactsFingerprint, manifest.pins.leanSources,
    'native proof facts do not belong to the pinned source snapshot');
  assert.equal(snapshot.buildFingerprint, manifest.pins.leanSources,
    'build evidence does not belong to the pinned source snapshot');
  idle(snapshot);
  for (const field of ['paperPacket', 'leanSources', 'configuration', 'toolchain']) {
    requiredText(manifest.pins?.[field], `missing ${field} pin`);
    assert.equal(snapshot.pins?.[field], manifest.pins[field], `${field} changed`);
  }
  assert.equal(snapshot.interfaceEvidenceSourceFingerprint, manifest.pins.leanSources,
    'elaborated interfaces do not belong to the pinned complete source snapshot');
}
function quote(snapshot, q) {
  keys(q, ['file','from','to','text','fileDigest'], 'source quote');
  requiredText(q.file, 'source quote file');
  assert(!q.file.startsWith('/') && !q.file.split('/').includes('..'), 'quote must use a project-relative file');
  const source = snapshot.files?.[q.file];
  assert(source, `source quote file absent: ${q.file}`);
  assert.equal(source.digest, q.fileDigest, 'quoted file changed');
  assert(Number.isInteger(q.from) && Number.isInteger(q.to) && q.from >= 1 && q.to >= q.from,
    'invalid quote line range');
  assert.equal(source.text.split('\n').slice(q.from-1,q.to).join('\n'), q.text,
    'source quote is not exact');
  return clone(q);
}
function activeVersion(ledger, id) {
  const version = ledger.claimVersions.find(v => v.id === id);
  assert(version && version.targetVersionId === ledger.target.activeVersionId &&
    ledger.claims.some(c => c.id === version.claimId && c.activeVersionId === id),
    'claim version is not active');
  return version;
}
function requirements(ledger,id) {
  const plans = ledger.plans.filter(p => p.claimVersionId === id);
  assert.equal(plans.length,1,'exactly one claim plan required');
  return {plan:plans[0], ids:(plans[0].requirements?.allOf ?? []).flatMap(g => g.anyOf)};
}
function validate(manifest, snapshot, current, host) {
  keys(manifest,['schema','targetId','baseLedgerDigest','pins','review','bindings','exclusions'],'manifest');
  assert.equal(manifest.schema,'tex2lean.delegated-ledger-review/1');
  keys(manifest.pins,['paperPacket','leanSources','configuration','toolchain'],'pins');
  keys(manifest.review,['authority','authorizationDigest','provenance'],'review');
  assert.equal(manifest.review.authority,'user-delegated-author');
  assert.equal(manifest.review.provenance,PROVENANCE);
  requiredText(host.authorizedUserRequestDigest,'trusted host must identify the authorizing user request');
  assert.equal(manifest.review.authorizationDigest,host.authorizedUserRequestDigest,
    'manifest does not match trusted user authorization');
  pinInputs(manifest,snapshot);
  assert(current,'mapping target absent');
  assert.equal(current.ledger.target.id,manifest.targetId);
  assert.equal(current.head.ledgerDigest,manifest.baseLedgerDigest,'reviewed ledger head changed');
  const ledger=current.ledger;
  const target=ledger.targetVersions.find(v => v.id===ledger.target.activeVersionId);
  assert.equal(target?.paperPacketDigest,manifest.pins.paperPacket,'ledger paper packet changed');
  const usedObligations=new Set(), usedClaims=new Set(), usedDeclarations=new Set();
  const bindings=(manifest.bindings ?? []).map(b => {
    keys(b,['claimVersionId','obligationId','declaration','file','module','elaboratedType',
      'semanticDefinitions','sourceQuote','reason'],'binding review');
    activeVersion(ledger,b.claimVersionId);
    const req=requirements(ledger,b.claimVersionId);
    assert.equal(req.plan.disposition,'formalize','only formalize obligations supported');
    assert(req.ids.includes(b.obligationId),'obligation is not required by this claim');
    assert(ledger.obligations.some(o=>o.id===b.obligationId && o.kind==='headline'),'headline obligation required');
    assert(!usedObligations.has(b.obligationId) && !usedDeclarations.has(b.declaration),'duplicate binding');
    usedObligations.add(b.obligationId); usedClaims.add(b.claimVersionId); usedDeclarations.add(b.declaration);
    requiredText(b.reason,'semantic equivalence review reason');
    const actual=snapshot.declarations?.[b.declaration];
    assert(actual && actual.inCertifiedModuleClosure===true,'declaration outside certified module closure');
    assert.equal(actual.file,b.file,'declaration file mismatch');
    assert.equal(actual.module,b.module,'declaration module mismatch');
    assert.equal(actual.elaboratedType,b.elaboratedType,'elaborated type changed');
    // Full sorted lists, not a selected subset of semantic dependencies.
    assert(same(actual.semanticDefinitions,b.semanticDefinitions),'definition review omits or changes semantic roots');
    const sourceQuote=quote(snapshot,b.sourceQuote);
    assert(snapshot.files[b.sourceQuote.file].kind==='paper','binding source must be the pinned paper');
    const existing=ledger.bindings.filter(x=>x.obligationId===b.obligationId && x.status!=='rejected' && x.status!=='superseded');
    assert(existing.length<=1,'ambiguous existing binding');
    if(existing.length) {
      const x=existing[0];
      assert(x.status==='proposed' && !x.semanticApprovalDecisionId,
        'already approved/verified/stale binding requires separate review');
      for(const field of ['declaration','file','module']) assert.equal(x[field],b[field],'existing binding differs');
      assert.equal(x.role,'headline');
    }
    return {...clone(b),sourceQuote,existingBindingId:existing[0]?.id};
  });
  const exclusions=(manifest.exclusions ?? []).map(e => {
    keys(e,['claimVersionId','exactClaimText','category','metadataQuote','sourceQuotes','reason'],'exclusion review');
    const cv=activeVersion(ledger,e.claimVersionId);
    assert(!usedClaims.has(cv.id),'cannot bind and exclude the same claim'); usedClaims.add(cv.id);
    assert.equal(cv.text,e.exactClaimText,'excluded claim text changed');
    assert.equal(NONMATHEMATICAL.get(cv.text),e.category,
      'only the two exact reviewed nonmathematical metadata rows may be excluded');
    assert(NONMATHEMATICAL.has(cv.text),'mathematical claims cannot be excluded');
    const req=requirements(ledger,cv.id);
    assert.equal(req.plan.disposition,'formalize','unexpected existing disposition');
    assert(!ledger.bindings.some(b=>req.ids.includes(b.obligationId) && b.status!=='rejected' && b.status!=='superseded'),
      'a bound claim cannot be excluded by this adapter');
    requiredText(e.reason,'nonmathematical classification reason');
    const metadataQuote=quote(snapshot,e.metadataQuote);
    assert(metadataQuote.text.includes(cv.text),'metadata quote must contain the complete exact ledger claim');
    assert(Array.isArray(e.sourceQuotes) && e.sourceQuotes.length>=2,'both original source contexts required');
    const sourceQuotes=e.sourceQuotes.map(q=>quote(snapshot,q));
    assert(new Set(sourceQuotes.map(q=>`${q.file}:${q.from}:${q.to}`)).size===sourceQuotes.length,
      'source contexts must be distinct');
    const kinds=sourceQuotes.map(q=>snapshot.files[q.file].kind);
    assert(e.category==='implementation-provenance' ? kinds.includes('lean') && kinds.includes('documentation') :
      kinds.filter(k=>k==='paper').length>=2,'source contexts do not support the metadata classification');
    return {...clone(e),metadataQuote,sourceQuotes};
  });
  return {bindings,exclusions};
}
async function runReview(manifest, host, {apply=false}={}) {
  assert(typeof apply==='boolean','apply must be an explicit boolean');
  manifest=clone(manifest);
  // Required native functions: Pt, Sf; store is the real wd in a future host adapter.
  const {native,store}=host;
  assert(native && typeof native.Pt==='function' && typeof native.Sf==='function');
  assert(store && typeof store.readCurrent==='function' && typeof store.publishDecision==='function');
  assert(typeof host.captureSnapshot==='function');
  const manifestDigest=native.Pt('delegated-review-manifest/1',manifest);
  async function prepare() {
    const snapshot=await host.captureSnapshot();
    const current=await store.readCurrent(manifest.targetId);
    return {snapshot,current,plan:validate(manifest,snapshot,current,host)};
  }
  const initial=await prepare();
  const summary={mode:apply?'apply':'dry-run',manifestDigest,
    bindings:initial.plan.bindings.map(b=>({obligationId:b.obligationId,declaration:b.declaration})),
    exclusions:initial.plan.exclusions.map(e=>({claimVersionId:e.claimVersionId,category:e.category})),
    proofCertification:'not run; use the native /prove command afterwards'};
  if(!apply) return {...summary,publications:[]};
  assert(typeof host.withIdleLease==='function','apply requires an exclusive idle-project lease');
  return host.withIdleLease(async()=>{
    const {plan,current}=await prepare();
    let expectedHead=current.head.ledgerDigest;
    const publications=[];
    function checkQuotes(snapshot) {
      for(const b of plan.bindings) quote(snapshot,b.sourceQuote);
      for(const e of plan.exclusions) for(const q of [e.metadataQuote,...e.sourceQuotes]) quote(snapshot,q);
    }
    async function publish(payload, detail, decorate) {
      const snapshot=await host.captureSnapshot();
      pinInputs(manifest,snapshot); checkQuotes(snapshot);
      const fresh=await store.readCurrent(manifest.targetId);
      assert.equal(fresh?.head.ledgerDigest,expectedHead,'another ledger writer changed the head');
      assert.equal(fresh.ledger.target.activeVersionId,current.ledger.target.activeVersionId,'target changed');
      const envelope={ledgerId:fresh.ledger.ledgerId,baseLedgerDigest:fresh.head.ledgerDigest,
        actor:'author',mode:'automatic',provenance:PROVENANCE+'\n'+
          JSON.stringify({manifestDigest,authorizationDigest:manifest.review.authorizationDigest,...detail})};
      // Includes the exact fresh base in the ID: no orphan decision ID is reused with different content.
      const id=native.Pt('delegated-review-decision/1',{...envelope,...payload});
      const decision={id,...envelope,...payload};
      if(decorate) decorate(decision,id);
      assert(['put-evidence','put-binding','set-disposition'].includes(decision.kind));
      if(decision.kind==='put-binding') assert.equal(decision.binding.status,'proposed');
      const publication=await store.publishDecision(decision);
      expectedHead=publication.resultingLedgerDigest;
      const after=await store.readCurrent(manifest.targetId);
      assert.equal(after?.head.ledgerDigest,expectedHead,'published head was replaced');
      publications.push(publication);
    }
    async function evidence(quotes,detail) {
      const ev={kind:'source-reading',anchors:quotes.map(q=>({file:q.file,from:q.from,to:q.to,
        excerptDigest:native.Pt('paper-target-excerpt/1',q.text)}))};
      ev.id=native.Sf(ev);
      await publish({kind:'put-evidence',evidence:ev},{...detail,exactQuotes:quotes});
      return ev.id;
    }
    for(const b of plan.bindings) {
      const review={claimVersionId:b.claimVersionId,obligationId:b.obligationId,reason:b.reason,
        elaboratedType:b.elaboratedType,semanticDefinitions:b.semanticDefinitions};
      await evidence([b.sourceQuote],review);
      const binding={id:b.existingBindingId ?? native.Pt('delegated-binding/1',{
        targetId:manifest.targetId,obligationId:b.obligationId,declaration:b.declaration,file:b.file,module:b.module}),
        obligationId:b.obligationId,declaration:b.declaration,file:b.file,module:b.module,
        role:'headline',status:'proposed'};
      if(!b.existingBindingId) await publish({kind:'put-binding',binding},review);
      await publish({kind:'put-binding',binding},review,(decision,id)=>{
        decision.binding={...binding,semanticApprovalDecisionId:id};
      });
    }
    for(const e of plan.exclusions) {
      const evidenceId=await evidence([e.metadataQuote,...e.sourceQuotes],{
        claimVersionId:e.claimVersionId,exactClaimText:e.exactClaimText,category:e.category,reason:e.reason});
      await publish({kind:'set-disposition',claimVersionId:e.claimVersionId,plan:{
        claimVersionId:e.claimVersionId,disposition:'exclude',evidenceIds:[evidenceId],reason:e.reason}},
        {claimVersionId:e.claimVersionId,category:e.category,reason:e.reason});
    }
    const finalSnapshot=await host.captureSnapshot();
    pinInputs(manifest,finalSnapshot); checkQuotes(finalSnapshot);
    return {...summary,publications,finalLedgerDigest:expectedHead};
  });
}
module.exports={runReview,PROVENANCE,NONMATHEMATICAL:new Map(NONMATHEMATICAL)};
