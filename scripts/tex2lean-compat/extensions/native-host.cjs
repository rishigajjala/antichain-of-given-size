'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');
const crypto=require('node:crypto');
const {runReview,PROVENANCE,isUnapprovedProposal,proposalDigest}=require('./adapter.cjs');
const {runSurfaceReview,inventoryDigest,stateDigest,countingOwnership,COUNT,MAIN,HELPER,COUNT_OWNER}=require('./surface-review.cjs');
const {SCHEMA:FUTURE_SCHEMA,runFutureSurfaceReview,futureScope,validateInspection,readRelatedTargets}=require('./future-surface-review.cjs');
const hash=bytes=>'sha256-'+crypto.createHash('sha256').update(bytes).digest('hex');
function parseRequest(raw) {
  const q=typeof raw==='string'?JSON.parse(raw):raw;
  assert(q && typeof q==='object' && !Array.isArray(q),'JSON command request required');
  for(const k of Object.keys(q)) assert(['inspect','manifest','authority','declarations','apply','futureSurface'].includes(k),`unknown request field ${k}`);
  assert(q.apply===undefined || typeof q.apply==='boolean','apply must be a boolean');
  assert(q.inspect===undefined || typeof q.inspect==='boolean','inspect must be a boolean');
  assert(typeof q.authority==='string' && path.isAbsolute(q.authority),'separate absolute authority-record path required');
  if(q.inspect) {
    assert(q.apply!==true && q.manifest===undefined,'inspection cannot apply a manifest');
    assert(Array.isArray(q.declarations) && q.declarations.length>0,'explicit declaration names required');
    assert(q.declarations.every(x=>typeof x==='string' && x.length>0),'invalid declaration name');
  } else {
    assert(typeof q.manifest==='string' && path.isAbsolute(q.manifest),'absolute manifest path required');
    assert(q.declarations===undefined,'manifest declarations cannot be overridden');
  }
  if(q.futureSurface!==undefined) {assert(q.inspect===true,'future inspection selection is only for inspect requests');validateInspection(q.futureSurface);}
  return q;
}
function inside(root,file) {
  assert(typeof file==='string' && !path.isAbsolute(file) && !file.split(/[\\/]/).includes('..'),'project-relative path required');
  const p=path.resolve(root,file);
  assert(p.startsWith(root+path.sep),'path escapes project');return p;
}
function idleRuntime(d,ownControl) {
  assert.equal(d.go(),ownControl?1:0,'another active control/worker exists');
  assert(!d.isBatchWorking(),'a batch is active');
  assert(!d.hasLiveTransaction(),'a transaction is active');
  assert(!d.hasRecoveryInFlight(),'transaction recovery is active');
}
async function withStrictNativeLease(d,fs,fn) {
  idleRuntime(d,false);
  const ctrl=d.newControl(); // Native lr: also keeps background Pf recovery from entering.
  const file=d.leaseFile();
  const value=d.makeLease('delegated ledger review '+crypto.randomUUID());
  let acquired=false,held;
  const assertOwner=async()=>{
    const current=JSON.parse(await fs.readFile(file,'utf8'));
    assert.equal(current.schema,value.schema,'lease schema changed');
    for(const k of ['machine','pid','takenAt','what']) assert.equal(current[k],value[k],'lease ownership changed');
  };
  try {
    await d.assertNoJournalFiles();
    assert(!d.hasProcessLease(),'another command in this process holds the native lease');
    await fs.mkdir(path.dirname(file),{recursive:true});
    // Unlike SG, this never prompts, forces, seizes a stale lease, or treats malformed JSON as free.
    const handle=await fs.open(file,'wx');
    acquired=true;
    try { await handle.writeFile(JSON.stringify(value)+'\n'); } finally { await handle.close(); }
    held=d.newHeldLease(value,async text=>{await assertOwner();await fs.writeFile(file,text);},
      async()=>{await assertOwner();await fs.unlink(file);});
    // No background write promise can be left running across release. Refresh explicitly after
    // each completed native inspection; the native lease remains held while its PID is alive.
    return await fn({token:ctrl.token,assertOwner,refresh:()=>held.refresh()});
  } finally {
    try {
      if(held) await held.release();
      else if(acquired) { try {await assertOwner();await fs.unlink(file);} catch {} }
    } finally {ctrl.dispose();}
  }
}
async function executeNativeReview(raw,d,options={}) {
  const fs=options.fs ?? require('node:fs/promises');
  const q=parseRequest(raw);
  assert(typeof d.authorityRecordDigest==='string' && /^sha256-[0-9a-f]{64}$/.test(d.authorityRecordDigest),
    'the reviewed host build has no trusted authority-record pin');
  const authorityBytes=await fs.readFile(q.authority);
  assert.equal(hash(authorityBytes),d.authorityRecordDigest,'authority record differs from the separately reviewed host pin');
  const authority=JSON.parse(authorityBytes.toString('utf8'));
  assert.equal(authority.schema,'tex2lean.delegated-authority-record/1');
  assert.equal(authority.scope,'formalization-and-correspondence-review');
  assert.equal(authority.recordedBy,'Codex assistant');
  assert.equal(authority.noHumanSemanticReviewAsserted,true);
  assert(typeof authority.userRequest==='string' && authority.userRequest.trim(),'authorizing user request required');
  const root=await fs.realpath(d.rootPath());
  assert.equal(await fs.realpath(authority.projectRoot),root,'authority belongs to another project');
  assert.equal(await fs.realpath(d.projectPath()),root,'this scoped prototype requires --lean .');
  const readProject=async(file,optional=false)=>{
    const absolute=inside(root,file);
    try {
      const real=await fs.realpath(absolute);
      assert(real.startsWith(root+path.sep),'source symlink escapes project');
      const bytes=await fs.readFile(real);return {text:bytes.toString('utf8'),digest:hash(bytes)};
    } catch(e) {if(optional && e.code==='ENOENT') return {missing:true,digest:'missing'};throw e;}
  };
  const bpFile=authority.blueprint;
  const bpRecord=await readProject(bpFile);
  const blueprint=JSON.parse(bpRecord.text);
  const targetId=blueprint.paperProofMapping?.targetId;
  assert(typeof targetId==='string' && authority.targetIds?.includes(targetId),'target outside delegated scope');
  const store=d.newStore();
  const manifest=q.inspect?undefined:JSON.parse(await fs.readFile(q.manifest,'utf8'));
  if(manifest) assert.equal(manifest.targetId,targetId,'manifest target differs from the reviewed blueprint');
  const surfaceReview=manifest?.schema==='tex2lean.delegated-surface-review/1';
  const futureReview=manifest?.schema===FUTURE_SCHEMA;
  const futureInspection=q.futureSurface??(futureReview?manifest.inspection:undefined);
  if(futureInspection)validateInspection(futureInspection);
  const reviewedRows=surfaceReview||futureReview?manifest.declarations:manifest?.bindings;
  const removals=surfaceReview||futureReview?manifest.changes.removals:[];
  let names=q.inspect?q.declarations:[...reviewedRows,...removals].map(b=>b.declaration);
  assert(new Set(names).size===names.length,'duplicate declarations requested');
  const initial=await store.readCurrent(targetId);assert(initial,'native mapping target absent');
  const target=initial.ledger.targetVersions.find(v=>v.id===initial.ledger.target.activeVersionId);
  const bundle=blueprint.bundle;
  if(futureInspection)futureScope(bundle.target.label,bundle.origin,bundle.target.environment);
  const paperPacket=d.Pt('paper-packet/1',{origin:bundle.origin,files:bundle.files,macros:bundle.macros,
    theoremEnvironments:bundle.theoremEnvironments,target:{body:bundle.target.body,start:bundle.target.start,
      end:bundle.target.end,environment:bundle.target.environment}});
  assert.equal(target.paperPacketDigest,paperPacket,'sealed blueprint and native paper packet disagree');
  const capstone=blueprint.filePlan?.capstone ?? blueprint.decomposition?.capstone?.name;
  assert(typeof capstone==='string','blueprint capstone absent');
  const quoteFiles=new Set(manifest?[...reviewedRows.map(b=>b.sourceQuote.file),...removals.map(b=>b.sourceQuote.file),
    ...((surfaceReview||futureReview)?[]:manifest.exclusions.flatMap(e=>[e.metadataQuote.file,...e.sourceQuotes.map(x=>x.file)]))]:[]);
  if(futureReview)for(const owner of manifest.owners)quoteFiles.add(owner.sourceQuote.file);
  const paperFiles=new Set(bundle.files);
  for(const file of paperFiles) quoteFiles.add(file);
  quoteFiles.add(bpFile);
  // Read-only ownership evidence for the one permitted separate-target removal.
  // This never authorizes writes to, or changes the authority scope of, that target.
  let relatedBlueprint;
  if(bundle.target.label==='thm:main') {
    const output=path.posix.dirname(path.posix.dirname(bpFile)),found=[];
    for(const entry of await fs.readdir(inside(root,output),{withFileTypes:true})) {
      if(!entry.isDirectory())continue;
      const file=path.posix.join(output,entry.name,'blueprint.json'),record=await readProject(file,true);
      if(record.missing)continue;
      const candidate=JSON.parse(record.text);
      if(candidate.bundle?.target?.label==='thm:attainable-count' && !candidate.inProgress)
        found.push({file,record,blueprint:candidate});
    }
    assert.equal(found.length,1,'one finalized counting blueprint is required for ownership review');
    relatedBlueprint=found[0];quoteFiles.add(relatedBlueprint.file);
  }
  const configFiles=['formalize.json','lakefile.toml','lakefile.lean','lake-manifest.json'];
  let certified,material,firstPins,scope,fullAxiomEvidence;
  return withStrictNativeLease(d,fs,async lease=>{
    async function readInputs() {
      idleRuntime(d,true);await lease.assertOwner();await d.assertNoJournalFiles();
      const files={};
      for(const file of quoteFiles) files[file]={...await readProject(file),kind:paperFiles.has(file)?'paper':
        file.endsWith('.lean')?'lean':file.startsWith('docs/')?'documentation':'metadata'};
      assert.equal(files[bpFile].digest,bpRecord.digest,'blueprint changed');
      const targetSource=files[bundle.target.start.file];
      assert(targetSource?.text.includes(bundle.target.body),'paper target body changed');
      for(const macro of bundle.macros ?? []) {
        const source=files[macro.source?.file];
        assert(source?.text.includes(macro.declaration),'paper macro declaration changed');
      }
      const configuration={blueprint:{file:bpFile,digest:files[bpFile].digest},paperFiles:{},files:{}};
      for(const file of paperFiles) configuration.paperFiles[file]=files[file].digest;
      for(const file of configFiles) configuration.files[file]=(await readProject(file,true)).digest;
      const toolchain=await readProject('lean-toolchain');
      let relatedCountingTarget;
      if(relatedBlueprint) {
        const b=relatedBlueprint.blueprint;
        assert.equal(files[relatedBlueprint.file].digest,relatedBlueprint.record.digest,'counting blueprint changed');
        const id=b.paperProofMapping?.targetId,related=await store.readCurrent(id);
        assert(related && id!==targetId,'independent counting target missing');
        const version=related.ledger.targetVersions.find(v=>v.id===related.ledger.target.activeVersionId);
        const packet=d.Pt('paper-packet/1',{origin:b.bundle.origin,files:b.bundle.files,macros:b.bundle.macros,
          theoremEnvironments:b.bundle.theoremEnvironments,target:{body:b.bundle.target.body,start:b.bundle.target.start,
            end:b.bundle.target.end,environment:b.bundle.target.environment}});
        assert.equal(version?.paperPacketDigest,packet,'counting target paper packet changed');
        const ownCapstone=b.filePlan?.capstone??b.decomposition?.capstone?.name;
        assert.equal(ownCapstone,COUNT,'counting target capstone changed');
        relatedCountingTarget={label:'thm:attainable-count',targetId:id,targetVersionId:version.id,
          ledgerDigest:related.head.ledgerDigest,paperPacketDigest:packet,capstone:ownCapstone,
          blueprint:relatedBlueprint.file,blueprintDigest:relatedBlueprint.record.digest,
          ownership:countingOwnership(related.ledger)};
      }
      const relatedTargets=futureInspection?await readRelatedTargets(futureInspection,{targetId,readProject,store,native:d}):undefined;
      return {files,configuration:d.Pt('delegated-review-configuration/1',configuration),
        toolchain:d.Pt('lean-toolchain/1',toolchain.text),relatedCountingTarget,...futureInspection?{relatedTargets}:{}};
    }
    async function captureSnapshot() {
      const inputs=await readInputs();
      const scan=await d.scan(lease.token);
      assert(scan.complete===true && scan.sourceFingerprint,'complete current source inventory required');
      const pins={paperPacket,leanSources:scan.sourceFingerprint,configuration:inputs.configuration,toolchain:inputs.toolchain};
      if(firstPins) assert.deepEqual(pins,firstPins,'review inputs changed');
      if(!certified) {
        d.clearProjectEvidenceCaches();
        certified=await d.certify(lease.token); // Actual native cr: build + diagnostics + elaborated proof facts.
        assert.equal(certified.sourceFingerprint,pins.leanSources,'source changed during native certification');
        assert.equal(certified.leanProofFactsFingerprint,pins.leanSources,'native proof facts are incomplete');
        assert.equal(certified.leanDiagnostics?.complete,true,'Lean diagnostics are incomplete');
        scope=d.scope(certified,capstone);
        if(futureInspection) {
          names=[...new Set([...names,...futureInspection.helperPaths.flatMap(p=>p.path),
            ...inputs.relatedTargets.flatMap(r=>r.owned.map(o=>o.binding.declaration))])];
          // Explicit selected owners/path nodes may live outside the current capstone imports.
          // This extends read-only evidence inspection, never a proof receipt or target inventory.
          const scopes=[scope,...names.map(name=>d.scope(certified,name))];
          scope={...scope,files:[...new Set(scopes.flatMap(s=>s.files))],modules:[...new Set(scopes.flatMap(s=>s.modules))]};
        }
        const declarations=names.map((name,i)=>{
          const found=certified.statements.find(s=>s.name===name);assert(found,`missing declaration ${name}`);
          assert(scope.files.includes(found.file),'declaration is outside the capstone module closure');
          return {id:`inspection:${i}`,declaration:name};
        });
        material=await d.inspectInterfaces(scope.modules,declarations,certified,{token:lease.token,
          toolchainDigest:pins.toolchain,includeReviewMaterial:true});
        if(futureInspection) {
          assert.equal(typeof d.inspectFullAxioms,'function','native full axiom inspector is required');
          const axiomNames=new Set([...futureInspection.helperPaths.flatMap(p=>p.path),
            ...inputs.relatedTargets.flatMap(r=>r.owned.map(o=>o.binding.declaration)),...removals.map(r=>r.declaration)]);
          fullAxiomEvidence={declarations:{}};
          for(const name of axiomNames) {
            const statement=certified.statements.find(s=>s.name===name);
            const module=certified.modules.find(m=>m.file===statement?.file)?.module;
            assert(module,'full axiom probe module is absent');
            const result=await d.inspectFullAxioms(name,module);
            fullAxiomEvidence.declarations[name]={declaration:name,module,method:'native Lean.collectAxioms after module build',
              pins:{...pins},answered:result.answered,sorried:result.sorried,axioms:result.axioms,output:result.output};
          }
        }
        const confirmed=await d.scan(lease.token);
        assert.equal(confirmed.complete,true);assert.equal(confirmed.sourceFingerprint,pins.leanSources,
          'sources changed while elaborated review material was extracted');
        const confirmedInputs=await readInputs();
        assert.equal(confirmedInputs.configuration,pins.configuration);assert.equal(confirmedInputs.toolchain,pins.toolchain);
        firstPins=pins;await lease.refresh();
      }
      const declarations={};
      for(const row of material.reviewMaterial) {
        const module=certified.modules.find(m=>m.file===row.file)?.module;
        assert(module && scope.modules.includes(module),'review declaration has no certified module owner');
        declarations[row.declaration]={file:row.file,module,elaboratedType:row.elaboratedType,
          semanticDefinitions:row.semanticDefinitions,inCertifiedModuleClosure:true};
      }
      const proofFacts={sourceFingerprint:certified.leanProofFactsFingerprint,declarations:{}};
      for(const name of new Set(futureInspection?certified.statements.map(s=>s.name):[...names,COUNT,MAIN,HELPER,COUNT_OWNER])) {
        const row=certified.statements.find(s=>s.name===name);
        if(row && scope.files.includes(row.file))proofFacts.declarations[name]={file:row.file,kind:row.kind,
          hasSorry:row.hasSorry,references:[...(row.references??[])]};
      }
      return {complete:true,diagnosticsComplete:true,pins,interfaceEvidenceSourceFingerprint:material.sourceFingerprint,
        leanProofFactsFingerprint:certified.leanProofFactsFingerprint,buildFingerprint:material.buildFingerprint,
        idle:{workers:d.go()-1,liveTransactions:d.hasLiveTransaction()?1:0,otherLease:false,workflowRunning:d.isBatchWorking()},
        files:inputs.files,declarations,targetLabel:bundle.target.label,capstone,proofFacts,
        relatedCountingTarget:inputs.relatedCountingTarget,...futureInspection?{futureInspection,relatedTargets:inputs.relatedTargets,fullAxiomEvidence,targetOrigin:bundle.origin,targetEnvironment:bundle.target.environment}:{}};
    }
    const snapshot=await captureSnapshot();
    if(q.inspect) {
      // Complete source bodies are supplied for manual review, including structure fields/constructors
      // beyond the older native receipt's project-type closure. This does not change receipt semantics.
      const sourceBodies={};
      for(const file of scope.files) sourceBodies[file]=await readProject(file);
      const confirmed=await d.scan(lease.token);
      assert.equal(confirmed.complete,true);assert.equal(confirmed.sourceFingerprint,snapshot.pins.leanSources);
      return {schema:'tex2lean.delegated-review-evidence/1',mode:'inspect',provenance:PROVENANCE,
        authorizationDigest:d.Pt('user-authorized-formalization/1',authority.userRequest),
        targetId,ledgerDigest:initial.head.ledgerDigest,pins:snapshot.pins,
        ledger:initial.ledger,declarations:snapshot.declarations,
        targetLabel:snapshot.targetLabel,capstone,proofFacts:snapshot.proofFacts,
        relatedCountingTarget:snapshot.relatedCountingTarget,...futureInspection?{futureInspection,relatedTargets:snapshot.relatedTargets,fullAxiomEvidence,targetOrigin:snapshot.targetOrigin,targetEnvironment:snapshot.targetEnvironment}: {},
        expectedPreservedStateDigest:stateDigest(d,initial.ledger),
        activeInventory:(()=>{const inventory=initial.ledger.surfaceInventories?.find(x=>x.id===initial.ledger.activeSurfaceInventoryId);
          return inventory?{inventory,expectedInventoryDigest:inventoryDigest(d,inventory)}:undefined;})(),
        unapprovedProposals:initial.ledger.bindings.filter(isUnapprovedProposal).map(binding=>({
          binding,expectedBindingDigest:proposalDigest(d,binding)})),
        elaboratedDefinitionBodies:material.reviewMaterial,sourceBodies,paperSources:snapshot.files,
        nativeInterfaceEvidence:material,
        instruction:'Review exact paper claims, types and all relevant definition/structure bodies before writing a manifest. Inspection approves nothing.'};
    }
    const host={native:{Pt:d.Pt,Sf:d.Sf},store,
      authorizedUserRequestDigest:d.Pt('user-authorized-formalization/1',authority.userRequest),
      captureSnapshot,withIdleLease:async fn=>{idleRuntime(d,true);await lease.assertOwner();return fn();}};
    return (futureReview?runFutureSurfaceReview:surfaceReview?runSurfaceReview:runReview)(manifest,host,{apply:q.apply===true});
  });
}
module.exports={executeNativeReview,parseRequest,withStrictNativeLease,idleRuntime};
