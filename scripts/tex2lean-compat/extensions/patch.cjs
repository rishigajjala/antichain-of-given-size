'use strict';
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const crypto=require('node:crypto');
const digest=s=>crypto.createHash('sha256').update(s).digest('hex');
const EXPECTED='93d40c1b5465f43c456a0a46c63995a2d5f4439027fccbd57c3ecfee877af4b7';
function patch(source,{authorityDigest=""}={}) {
  assert(authorityDigest==="" || /^sha256-[0-9a-f]{64}$/.test(authorityDigest),"invalid trusted authority pin");
  assert.equal(digest(source),EXPECTED,'not the reviewed v8 bundle');
  let result=source;const changes=[];
  function replace(before,after,purpose) {
    assert.equal(result.split(before).length-1,1,`anchor mismatch: ${purpose}`);
    result=result.replace(before,after);changes.push(purpose);
  }
  replace('function T8(e){',fs.readFileSync(path.join(__dirname,'cli-helpers.js'),'utf8').replace(
    'var compatLedgerReviewAuthorityDigest = "";', 'var compatLedgerReviewAuthorityDigest = '+JSON.stringify(authorityDigest)+';')+'\nfunction T8(e){',
    'Add optional read-only material renderer and guarded handler');
  const begin=result.indexOf('async function o4('),end=result.indexOf('var r4,',begin);
  assert(begin>=0 && end>begin);
  let o4=result.slice(begin,end);
  assert.equal(o4.split('let R=[];').length-1,1);
  o4=o4.replace('let R=[];',
    'if(i.includeReviewMaterial&&y.size!==f.rows.length)throw new Error("ambiguous duplicate declaration names in review evidence");let R=[];');
  const receipt='interfaceReceipts:R,relationEvidence:[]}';
  assert.equal(o4.split(receipt).length-1,1);
  o4=o4.replace(receipt,
    'interfaceReceipts:R,relationEvidence:[],...(i.includeReviewMaterial?{reviewMaterial:compatInterfaceReviewMaterial(n,k,y,w,v)}:{})}');
  result=result.slice(0,begin)+o4+result.slice(end);
  changes.push('Expose actual elaborated review types/bodies only when explicitly requested; ordinary receipts unchanged');
  replace('remap:{command:"formalize.remapStatements",',
    '"ledger-review":{command:"formalize.reviewLedger",what:"reviewing a paper-to-Lean ledger",writes:!0,summary:"inspect or review exact ledger bindings; default dry-run",args:"<JSON request>",group:"Read the paper"},remap:{command:"formalize.remapStatements",',
    'Register optional command metadata');
  replace('{name:"remap",needs:["record","no-run"],',
    '{name:"ledger-review",args:"<JSON request>",needs:["record","lean","no-run"],built:!0,command:"formalize.reviewLedger",subcommand:"ledger-review",takesArg:!0,takesRest:!0},{name:"remap",needs:["record","no-run"],',
    'Expose slash command with idle prerequisites');
  replace('n("formalize.remapStatements",async()=>{',
    'n("formalize.reviewLedger",r=>compatRunLedgerReview(t,r)),n("formalize.remapStatements",async()=>{',
    'Wire handler after normal CLI boot');
  replace('_M=new Set([','_M=new Set(["formalize.reviewLedger",',
    'Preserve normal no-work and batch guard semantics');
  replace('Rx.set(r,async(...o)=>{if(Ef(void 0),',
    'Rx.set(r,async(...o)=>{if(compatLedgerReviewActive)throw new Error("finish the ledger review before starting another command");if(Ef(void 0),',
    'Prevent another registered command from entering during the leased review');
  replace('finally{_M.has(r)&&await Oi(t),await s?.release()}',
    'finally{_M.has(r)&&r!=="formalize.reviewLedger"&&await Oi(t),await s?.release()}',
    'Skip only ledger-review post-handler theorem-record reconciliation; retain entry guards');
  return {source:result,changes,before:digest(source),after:digest(result),authorityDigest:authorityDigest||null};
}
module.exports={patch};
if(require.main===module) {
  const [input,output,authorityDigest=""]=process.argv.slice(2);
  assert(input && output,'Usage: node patch.cjs /path/to/v8/out/cli.cjs /new/external/output');
  const destination=path.resolve(output);
  assert(destination.startsWith('/tmp/') || destination.startsWith('/private/tmp/'),'generated CLI output must remain outside the repository in /tmp');
  assert(!fs.existsSync(destination),'refusing to overwrite an existing directory');
  const built=patch(fs.readFileSync(input,'utf8'),{authorityDigest});
  fs.mkdirSync(path.join(destination,'out'),{recursive:true});
  fs.mkdirSync(path.join(destination,'ledger-review'));
  fs.writeFileSync(path.join(destination,'out/cli.cjs'),built.source);
  for(const f of ['adapter.cjs','native-host.cjs']) fs.copyFileSync(path.join(__dirname,f),path.join(destination,'ledger-review',f));
  fs.writeFileSync(path.join(destination,'manifest.json'),JSON.stringify({
    ...built,source:undefined,productionAdopted:false,workflowRun:false,validatorChanged:false,
    supportModules:Object.fromEntries(['adapter.cjs','native-host.cjs'].map(f=>[f,digest(fs.readFileSync(path.join(destination,'ledger-review',f)))])),
  },null,2)+'\n');
  console.log(JSON.stringify({output:destination,...built,source:undefined},null,2));
}
