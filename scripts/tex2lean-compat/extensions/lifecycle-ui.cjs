'use strict';
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const digest = source => crypto.createHash('sha256').update(source).digest('hex');

// These functions are inserted into the native lexical scope. Neither writes state.
function compatRetainGraphTimestamp(previous, fresh) {
  if (!previous || !fresh || typeof previous.updatedAt !== 'string' || typeof fresh.updatedAt !== 'string') return fresh;
  // Only this top-level display timestamp may differ. Nested timestamps and all
  // proof/ledger/source fields still participate in native canonical equality.
  return Au({...previous, updatedAt: null}) === Au({...fresh, updatedAt: null}) ? previous : fresh;
}

async function compatMatchingHandoffProgress(session, root, cfg, target, evidence) {
  try {
    const state = session.getProofState(), certificate = state?.compatClaimProgressCertificate;
    if (!state?.claimProgress || !certificate || state.targetKey !== Oe(target) || certificate.targetKey !== Oe(target)) return;
    if (!evidence || evidence.complete === false || evidence.sourceFingerprint !== certificate.sourceFingerprint) return;
    const store = new wd(root, cfg.leanProjectPath);
    const current = await store.readCurrent(certificate.targetId);
    if (!current || current.head.ledgerDigest !== certificate.ledgerDigest || current.head.certifiedSnapshotDigest !== certificate.snapshotDigest) return;
    const snapshot = await store.readCertifiedSnapshot(certificate.snapshotDigest);
    const graph = await ts(root, cfg.leanProjectPath);
    if (!snapshot || !graph || graph.target.key !== Oe(target) || graph.target.paperDigest !== Yt(target)) return;
    if (snapshot.targetId !== certificate.targetId || snapshot.targetVersionId !== current.ledger.target.activeVersionId || snapshot.ledgerDigest !== current.head.ledgerDigest) return;
    if (graph.mappingDigest !== current.head.ledgerDigest || snapshot.graphDigest !== certificate.graphDigest || snapshot.graphDigest !== Pt('proof-graph/6', graph)) return;
    for (const key of ['sourceFingerprint', 'buildFingerprint', 'dependencyFingerprint']) {
      if (snapshot[key] !== graph[key] || snapshot[key] !== certificate[key] || snapshot[key] !== evidence.sourceFingerprint) return;
    }
    // The handoff readers may take minutes. Recheck the source bytes at the point
    // the report is assembled; cached UI state alone is not current evidence.
    const fresh = await na(root, cfg.leanProjectPath);
    if (fresh.complete === false || fresh.sourceFingerprint !== certificate.sourceFingerprint) return;
    const finalGraph = await ts(root, cfg.leanProjectPath);
    if (!finalGraph || Pt('proof-graph/6', finalGraph) !== certificate.graphDigest) return;
    const finalHead = (await store.readCurrent(certificate.targetId))?.head;
    if (!finalHead || finalHead.ledgerDigest !== certificate.ledgerDigest || finalHead.certifiedSnapshotDigest !== certificate.snapshotDigest) return;
    // A changed session projection is not silently substituted for the checked one.
    if (session.getProofState() !== state) return;
    return state.claimProgress;
  } catch (error) {
    W('could not attach current certified claim progress to the handoff', error);
  }
}

function patchLifecycleUi(source) {
  assert.equal(typeof source, 'string', 'CLI source text required');
  let result = source;
  const changes = [];
  function replaceUnique(before, after, purpose) {
    assert.equal(result.split(before).length - 1, 1, `lifecycle UI anchor mismatch: ${purpose}`);
    result = result.replace(before, after); changes.push(purpose);
  }
  replaceUnique('this.queued(()=>(this.choice=t,this.waitOnUser(',
    'this.queued(()=>(this.choice={...t,compatChoiceRequestSequence:this.compatChoiceRequestSequence=(this.compatChoiceRequestSequence??0)+1},this.waitOnUser(',
    'Give each native choice request a process-local sequence without changing its public ID or actions');
  replaceUnique('async answerIfAsked(n){let r=n.choice;if(!(!r||this.lastChoice===r.id)){this.lastChoice=r.id;',
    'async answerIfAsked(n){let r=n.choice,i=r?.compatChoiceRequestSequence??r?.id;if(!(!r||this.lastChoice===i)){this.lastChoice=i;',
    'Deduplicate repeated renders of the same request while allowing a later request with the same ID');
  const derive = 'reachableModules:J.scope.modules});return ve(re)},Ct=';
  replaceUnique(derive,
    'reachableModules:J.scope.modules});return ve(compatRetainGraphTimestamp(z,re))},Ct=',
    'Retain the previous graph only when the freshly derived graph differs solely in top-level updatedAt');
  replaceUnique('Ge={ledger:z.ledger,digest:z.head.ledgerDigest};let re=!1;if(T&&z.head.certifiedSnapshotDigest)',
    'Ge={ledger:z.ledger,digest:z.head.ledgerDigest};let re=!1,compatClaimSnapshot;if(T&&z.head.certifiedSnapshotDigest)',
    'Record the identity of the already validated native certificate in the ephemeral UI projection');
  const strictEnd = 'ae.dependencyFingerprint===T.dependencyFingerprint)}let de=QJ(';
  replaceUnique(strictEnd,
    'ae.dependencyFingerprint===T.dependencyFingerprint);re&&(compatClaimSnapshot={targetId:_.targetId,targetKey:T.target.key,ledgerDigest:z.head.ledgerDigest,snapshotDigest:z.head.certifiedSnapshotDigest,graphDigest:Pt("proof-graph/6",T),sourceFingerprint:T.sourceFingerprint,buildFingerprint:T.buildFingerprint,dependencyFingerprint:T.dependencyFingerprint})}let de=QJ(',
    'Preserve every existing strict certificate comparison before attaching its read-only identity');
  replaceUnique('let K={...F,claimProgress:de};e.setProofState(K)',
    'let K={...F,claimProgress:de,compatClaimProgressCertificate:compatClaimSnapshot};e.setProofState(K)',
    'Keep unvalidated working projections without any certificate identity');
  replaceUnique('p.claimProgress=e.getProofState()?.claimProgress;',
    'p.claimProgress=await compatMatchingHandoffProgress(e,n,r,s,h);',
    'Attach handoff progress only for the selected target and exact current native certificate/source/graph');
  replaceUnique('async function gd(e,t={}){',
    compatRetainGraphTimestamp.toString() + '\n' + compatMatchingHandoffProgress.toString() + '\nasync function gd(e,t={}){',
    'Install read-only UI projection helpers; standalone or mismatched progress is safely omitted');
  const unchanged = {};
  for (const [name,start,end] of [
    ['native-certification','ai=async(F,G=Q','},qe='],
    ['native-graph-construction','function zT(','function '],
    ['native-claim-progress','function mue(','var hue,'],
    ['native-ledger-validation-store','function KJ(','function XJ('],
    ['native-interface-certifier','async function o4(','function '],
    ['native-model-closure','function BD(','async function qD('],
    ['native-cost-seal','function ZA(','function XA(']
  ]) {
    const region = text => {
      const a=text.indexOf(start),b=text.indexOf(end,a+start.length);
      assert(a>=0&&b>a,`lifecycle preserved-region anchor mismatch: ${name}`);
      return text.slice(a,b);
    };
    assert.equal(region(result),region(source),`lifecycle patch changed ${name}`);
    unchanged[name]=digest(region(source));
  }
  return {source: result, changes, before: digest(source), after: digest(result),
    unchanged,nativeCertifierChanged: false, nativeValidatorChanged: false, ledgerWritesAdded: false, workflowExecuted: false};
}
module.exports = {patchLifecycleUi};
