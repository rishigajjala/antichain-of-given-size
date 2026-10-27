'use strict';
const assert=require('node:assert/strict');
const fs=require('node:fs');
const {runReview,staleBindingDigest}=require('./adapter.cjs');
const {makeApproved,compileLoop}=require('./test-adapter.cjs');
const {extractValidatorLoop}=require('./validator-loop.cjs');
const clone=x=>JSON.parse(JSON.stringify(x));
assert(process.argv.length===3,'Usage: node test-stale-refresh.cjs /path/to/v8/out/cli.cjs');
const source=fs.readFileSync(process.argv[2],'utf8');
const {loop,digest}=extractValidatorLoop(source);
async function fixture() {
  const f=await makeApproved();
  const validator=compileLoop(f.ctx,loop);
  await validator(f.store,'target',f.Fi,f.jn,{sourceFingerprint:f.snapshot.pins.leanSources});
  const changed=clone(f.Fi);
  changed.sourceFingerprint=changed.buildFingerprint=changed.dependencyFingerprint=f.ctx.Pt('fixture','new source');
  for(const row of changed.interfaceReceipts) {
    row.receipt.semanticRootDigests=[{declaration:'Project.Model',digest:f.ctx.Pt('definition','new body')}];
    row.receiptDigest=f.ctx.Tu(row.receipt);
  }
  const changedId=await f.store.writeLeanEvidence(changed);
  const stale=await validator(f.store,'target',changed,changedId,{sourceFingerprint:changed.sourceFingerprint});
  assert(stale.ledger.bindings.every(b=>b.status==='stale'));
  const old=clone(stale.ledger.bindings);
  f.snapshot.pins.leanSources=f.snapshot.interfaceEvidenceSourceFingerprint=
    f.snapshot.leanProofFactsFingerprint=f.snapshot.buildFingerprint=changed.sourceFingerprint;
  f.manifest.pins=clone(f.snapshot.pins);
  f.manifest.baseLedgerDigest=stale.head.ledgerDigest;
  f.manifest.exclusions=[]; // Existing metadata dispositions are retained, not republished.
  for(const b of f.manifest.bindings) {
    const x=old.find(x=>x.obligationId===b.obligationId);
    b.semanticDefinitions=[{declaration:'Project.Model',elaboratedType:'Type',valueDigest:f.ctx.Pt('definition','new body')}];
    f.snapshot.declarations[b.declaration].semanticDefinitions=clone(b.semanticDefinitions);
    b.refreshStaleBinding={expectedBinding:clone(x),expectedBindingDigest:staleBindingDigest(f.ctx,x),
      reason:'Reviewed complete current definition bodies after vocabulary relocation; the exact paper claim and declaration identity remain unchanged.'};
  }
  return {...f,validator,old,changed,changedId,beforeLedger:clone(stale.ledger)};
}
async function reject(change,pattern) {
  const f=await fixture();await change(f);
  const writes=f.getWrites(),before=JSON.stringify([...f.files]);
  await assert.rejects(()=>runReview(f.manifest,f.host,{apply:true}),pattern);
  assert.equal(f.getWrites(),writes,'rejected refresh performs no publication');
  assert.equal(JSON.stringify([...f.files]),before,'rejected refresh preserves immutable store');
}
function liveUnique(ledger) {
  const live=ledger.bindings.filter(b=>!['rejected','superseded'].includes(b.status));
  assert.equal(new Set(live.map(b=>b.role+'\0'+b.declaration)).size,live.length);
  assert.equal(new Set(live.map(b=>b.obligationId)).size,live.length);
}
function retained(ledger,before) {
  for(const k of ['claims','claimVersions','plans','obligations','claimSetReceipts','activeClaimSetReceiptId',
    'surfaceInventories','activeSurfaceInventoryId','leanRelations','target','targetVersions'])
    assert.deepEqual(ledger[k],before[k],`refresh preserves ${k}`);
}
async function run() {
  const f=await fixture(),writes=f.getWrites(),before=JSON.stringify([...f.files]);
  // Establish the real native transition restriction; the adapter must not bypass it.
  assert.equal(f.ctx.oue(f.old[0],'proposed'),false);
  assert.equal(f.ctx.oue(f.old[0],'superseded'),true);
  const dry=await runReview(f.manifest,f.host);
  assert.equal(dry.staleRefreshes.length,2);assert.equal(dry.publications.length,0);
  assert(dry.staleRefreshes.every(x=>x.oldBindingId!==x.newBindingId));
  assert.equal(f.getWrites(),writes);assert.equal(JSON.stringify([...f.files]),before);
  const originalFiles=new Map(f.files),publish=f.store.publishDecision.bind(f.store);
  const events=[];
  f.store.publishDecision=async d=>{
    const p=await publish(d);events.push(clone(d));
    const current=await f.store.readCurrent('target');liveUnique(current.ledger);retained(current.ledger,f.beforeLedger);
    return p;
  };
  const applied=await runReview(f.manifest,f.host,{apply:true});
  assert.equal(applied.publications.length,8,'each refresh: evidence, supersede, new proposal, semantic approval');
  const after=await f.store.readCurrent('target');
  for(const old of f.old) {
    assert.deepEqual(after.ledger.bindings.find(b=>b.id===old.id),{...old,status:'superseded'});
    const successor=after.ledger.bindings.find(b=>b.supersedes?.includes(old.id));
    assert(successor && successor.id!==old.id && successor.status==='proposed' && successor.semanticApprovalDecisionId);
    for(const key of ['obligationId','declaration','file','module','role'])assert.equal(successor[key],old[key]);
    for(const key of ['receipt','leanEvidenceSnapshotId','verifiedByDecisionId','staleReason'])
      assert(!Object.hasOwn(successor,key),`new proposal must not inherit old ${key}`);
  }
  for(const [file,bytes] of originalFiles)
    if(file.includes('/decisions/')||file.includes('/objects/'))assert.equal(f.files.get(file),bytes,'old immutable history retained');
  assert(events.every(d=>d.actor==='author' && ['put-evidence','put-binding'].includes(d.kind)));
  assert(events.every(d=>!d.binding || ['proposed','superseded'].includes(d.binding.status)));
  assert.equal(new Set(events.map(d=>d.baseLedgerDigest)).size,events.length,'fresh head for every event');
  assert(f.ctx.Vy(after.ledger,{leanEvidence:new Map(),requireCertifiedSurface:true}).length>0,
    'review alone does not certify the target surface');
  // Only the unchanged native validator can verify fresh successor receipts.
  const fresh=clone(f.changed);
  fresh.interfaceReceipts=after.ledger.bindings.filter(b=>b.status==='proposed').map(b=>{
    const row=clone(f.changed.interfaceReceipts.find(row=>row.declaration===b.declaration));
    row.bindingId=b.id;return row;
  });
  const freshId=await f.store.writeLeanEvidence(fresh);
  const certified=await f.validator(f.store,'target',fresh,freshId,{sourceFingerprint:fresh.sourceFingerprint});
  assert(certified.ledger.bindings.filter(b=>b.status!=='superseded').every(b=>b.status==='verified'));
  assert.equal(f.ctx.Vy(certified.ledger,{leanEvidence:new Map([[freshId,fresh]]),requireCertifiedSurface:true}).length,0);
  // State, identity, complete review, and exact old-record guards all precede any publication.
  for(const status of ['proposed','verified','superseded','rejected'])
    await reject(f=>{
      const read=f.store.readCurrent.bind(f.store);
      f.store.readCurrent=async id=>{const cur=clone(await read(id));cur.ledger.bindings[0].status=status;return cur;};
    },/stale refresh requires an existing stale binding/);
  await reject(f=>{delete f.manifest.bindings[0].refreshStaleBinding;},/approved\/receipt-bearing\/verified\/stale/);
  await reject(f=>{f.manifest.bindings[0].refreshStaleBinding.reason=' ';},/stale refresh reason/);
  await reject(f=>{f.manifest.bindings[0].refreshStaleBinding.expectedBindingDigest='wrong';},/stale record does not match/);
  await reject(f=>{const r=f.manifest.bindings[0].refreshStaleBinding;r.expectedBinding.id='invented';
    r.expectedBindingDigest=staleBindingDigest(f.ctx,r.expectedBinding);},/reviewed old stale binding changed/);
  await reject(f=>{f.manifest.bindings[0].refreshStaleBinding.status='verified';},/forbidden field status/);
  await reject(f=>{f.manifest.bindings[0].status='proposed';},/forbidden field status/);
  await reject(f=>{f.manifest.bindings[0].replaceUnapprovedProposal={};},/distinct reviews/);
  for(const field of ['declaration','file','module'])await reject(f=>{
    const b=f.manifest.bindings[0],actual=clone(f.snapshot.declarations[b.declaration]);
    b[field]+='_changed';
    actual.file=b.file;actual.module=b.module;f.snapshot.declarations[b.declaration]=actual;
  },new RegExp('cannot change '+field));
  await reject(f=>{
    // A coherent alternative required obligation still cannot change the old binding's identity.
    const read=f.store.readCurrent.bind(f.store);
    f.store.readCurrent=async id=>{const c=clone(await read(id));c.ledger.bindings[0].obligationId='ob1';
      c.ledger.bindings=c.ledger.bindings.slice(0,1);return c;};
    f.manifest.bindings=[{...f.manifest.bindings[0],claimVersionId:'cv1',obligationId:'ob1'}];
  },/reviewed old stale binding changed/);
  for(const change of [b=>b.staleReason='paper-facing Lean statement changed during repair',
    b=>b.role='helper',b=>delete b.receipt,b=>delete b.semanticApprovalDecisionId,
    b=>delete b.leanEvidenceSnapshotId,b=>delete b.verifiedByDecisionId,
    b=>b.semanticApprovalDecisionId='unknown-approval',b=>b.verifiedByDecisionId='unknown-verification'])
    await reject(f=>{
      const read=f.store.readCurrent.bind(f.store);
      f.store.readCurrent=async id=>{const c=clone(await read(id));change(c.ledger.bindings[0]);return c;};
    },/known native interface-change reason|headline role|lacks/);
  await reject(f=>{f.manifest.bindings[0].semanticDefinitions=[];},/omits or changes/);
  await reject(f=>{f.manifest.bindings[0].elaboratedType='True';},/elaborated type changed/);
  await reject(f=>{f.manifest.baseLedgerDigest='old';},/head changed/);
  for(const pin of ['paperPacket','leanSources','configuration','toolchain'])
    await reject(f=>{f.manifest.pins[pin]='old';},/changed|pinned/);
  await reject(f=>{f.snapshot.complete=false;},/complete source snapshot/);
  await reject(f=>{f.snapshot.diagnosticsComplete=false;},/complete source snapshot/);
  await reject(f=>{f.manifest.bindings[0].sourceQuote.text='invented';},/quote is not exact/);
  await reject(f=>{f.manifest.review.authorizationDigest='invented';},/trusted user authorization/);
  // Every persisted prefix is safe if interrupted: never two active successors,
  // no forgotten claim/receipt/history, and no invented verified status.
  for(let stop=1;stop<8;stop++) {
    const interrupted=await fixture(),pub=interrupted.store.publishDecision.bind(interrupted.store);
    let count=0;
    interrupted.store.publishDecision=async d=>{
      const p=await pub(d);const c=await interrupted.store.readCurrent('target');
      liveUnique(c.ledger);retained(c.ledger,interrupted.beforeLedger);
      if(++count===stop)throw Error('simulated interruption');return p;
    };
    await assert.rejects(()=>runReview(interrupted.manifest,interrupted.host,{apply:true}),/simulated interruption/);
    const c=await interrupted.store.readCurrent('target');liveUnique(c.ledger);retained(c.ledger,interrupted.beforeLedger);
    assert(c.ledger.bindings.every(b=>['stale','superseded','proposed'].includes(b.status)));
  }
  // A fresh review can finish an interrupted unapproved successor through the
  // ordinary proposal path without dropping its immutable lineage metadata.
  const resume=await fixture(),resumePub=resume.store.publishDecision.bind(resume.store);let n=0;
  resume.store.publishDecision=async d=>{const p=await resumePub(d);if(++n===3)throw Error('pause after successor');return p;};
  await assert.rejects(()=>runReview(resume.manifest,resume.host,{apply:true}),/pause after successor/);
  resume.store.publishDecision=resumePub;
  const pending=await resume.store.readCurrent('target');
  const successor=pending.ledger.bindings.find(b=>b.status==='proposed');
  assert(successor && !successor.semanticApprovalDecisionId);
  resume.manifest.baseLedgerDigest=pending.head.ledgerDigest;
  resume.manifest.bindings=resume.manifest.bindings.slice(0,1);
  delete resume.manifest.bindings[0].refreshStaleBinding;
  await runReview(resume.manifest,resume.host,{apply:true});
  const resumed=(await resume.store.readCurrent('target')).ledger.bindings.find(b=>b.id===successor.id);
  assert.deepEqual(resumed.supersedes,successor.supersedes,'ordinary approval retains successor lineage');
  assert.equal(resumed.status,'proposed');assert(resumed.semanticApprovalDecisionId);
  const drift=await fixture(),pub=drift.store.publishDecision.bind(drift.store);let count=0;
  drift.store.publishDecision=async d=>{const p=await pub(d);if(++count===2)drift.snapshot.pins.leanSources='changed';return p;};
  await assert.rejects(()=>runReview(drift.manifest,drift.host,{apply:true}),/changed|pinned/);
  const driftState=await drift.store.readCurrent('target');liveUnique(driftState.ledger);
  assert.equal(driftState.ledger.bindings.find(b=>b.id===drift.old[0].id).status,'superseded');
  assert(!driftState.ledger.bindings.some(b=>b.supersedes?.includes(drift.old[0].id)),
    'source drift after superseding prevents an unreviewed successor');
  console.log(JSON.stringify({ok:true,nativeValidatorLoopSha256:digest,
    tests:'native stale→superseded plus exact reviewed successor; fresh semantic approval; no verified shortcuts; all interrupted prefixes safe; immutable history/claim coverage retained; ordinary native validator still mandatory',
    runtimeExecuted:false,compilerExecuted:false,realLedgerMutated:false},null,2));
}
run().catch(error=>{console.error(error);process.exitCode=1;});
