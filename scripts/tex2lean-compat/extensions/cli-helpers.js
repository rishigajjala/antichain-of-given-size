var compatLedgerReviewActive = false;
var compatLedgerReviewAuthorityDigest = "";
function compatClearReviewCaches(project, proofFacts, diagnostics) {
  for(const key of [...proofFacts.keys()]) if(key.startsWith(project+":")) proofFacts.delete(key);
  for(const key of [...diagnostics.keys()]) if(key.startsWith(project+"\0")) diagnostics.delete(key);
}
function compatInterfaceReviewMaterial(bindings, roots, rows, statements, values) {
  return bindings.map(binding => {
    const row=rows.get(binding.declaration), statement=statements.get(binding.declaration);
    if(!row || !statement) throw new Error("missing elaborated review declaration");
    return {declaration:binding.declaration,file:statement.file,sourceHeader:statement.header,
      elaboratedType:row.type,semanticDefinitions:(roots.get(binding.id)??[]).map(name=>{
        const definition=rows.get(name),value=values.get(name);
        if(!definition || typeof value!=="string") throw new Error("missing elaborated review definition");
        return {declaration:name,elaboratedType:definition.type,elaboratedValue:value,
          valueDigest:Pt("lean-declaration-value/1",{type:definition.type,value})};
      })};
  });
}
async function compatRunLedgerReview(session, request) {
  if(compatLedgerReviewActive) throw new Error("a ledger review is already active");
  const root=Ft();
  if(!root) throw new Error("open a project before reviewing its ledger");
  const cfg=me(root),project=x(root,cfg.leanProjectPath);
  if(go()>0 || Ae.batchState==="working" || Ae.mode?.permits("no-work"))
    throw new Error("stop the current workflow before reviewing its ledger");
  compatLedgerReviewActive=true;
  try {
    const hostModule=require(require("node:path").join(__dirname,"..","ledger-review","native-host.cjs"));
    const result=await hostModule.executeNativeReview(request,{
      Pt,Sf,go,authorityRecordDigest:compatLedgerReviewAuthorityDigest,
      rootPath:()=>root.fsPath,projectPath:()=>project.fsPath,
      newStore:()=>new wd(root,cfg.leanProjectPath),
      isBatchWorking:()=>Ae.batchState==="working",
      hasLiveTransaction:()=>compatHasLiveTransaction(project.fsPath),
      hasRecoveryInFlight:()=>compatRecoveryInFlight.has(project.fsPath),
      hasProcessLease:()=>!!Iy,
      assertNoJournalFiles:async()=>{
        let entries;
        try {entries=await A.list(NW(root,cfg));}
        catch(error) {if(compatMissingFile(error))return;throw error;}
        if(entries.some(([name,kind])=>kind==="file"&&name.endsWith(".json")))
          throw new Error("transaction journals remain; settle recovery before ledger review");
      },
      newControl:()=>new lr(),
      leaseFile:()=>mG(root,cfg.outputDirectory).fsPath,
      makeLease:what=>bG({host:"cli",...Q0()},what,new Date().toISOString()),
      newHeldLease:(value,write,remove)=>new zx(mG(root,cfg.outputDirectory),value,write,remove),
      scan:token=>na(root,cfg.leanProjectPath,token),
      clearProjectEvidenceCaches:()=>compatClearReviewCaches(project.fsPath,Fl,Hc),
      certify:token=>cr(root,cfg.leanProjectPath,token),
      scope:Kh,
      inspectInterfaces:(modules,bindings,evidence,options)=>o4(project,modules,bindings,evidence,options),
    });
    const fs=require("node:fs/promises"),path=require("node:path"),os=require("node:os");
    const directory=await fs.mkdtemp(path.join(os.tmpdir(),"tex2lean-ledger-review-"));
    const artifact=path.join(directory,result.mode==="inspect"?"evidence.json":result.mode==="apply"?"publication.json":"dry-run.json");
    await fs.writeFile(artifact,JSON.stringify(result,null,2)+"\n",{flag:"wx"});
    g(`ledger review ${result.mode}: ${artifact}`);
    if(result.mode==="apply") g("Run the normal /prove target and /handoff checks after reviewing the publication record.");
    return {mode:result.mode,artifact};
  } finally {compatLedgerReviewActive=false;}
}
