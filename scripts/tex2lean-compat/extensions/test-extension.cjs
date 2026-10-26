'use strict';
const assert=require('node:assert/strict');
const fs=require('node:fs');
assert(process.argv.length === 3 && process.argv[2], 'Usage: node test-extension.cjs /path/to/v8/out/cli.cjs');
const {buildSource,SUPPORT_MODULES}=require('./extend.cjs');
assert.deepEqual(SUPPORT_MODULES,['adapter.cjs','surface-review.cjs','native-host.cjs']);
const source=fs.readFileSync(process.argv[2],'utf8');
const repair=buildSource(source);
assert.equal(repair.optionalLedger.enabled,false);
assert(!repair.source.includes('function compatRunLedgerReview('));
assert(repair.source.includes('let s=dte(r,a,e)'));
assert(repair.source.includes('missing tools with those literal names do not prevent source inspection.'));
assert(repair.source.includes('finally{_M.has(r)&&await Oi(t),await s?.release()}'));
const testPin='sha256-'+'7'.repeat(64); // synthetic unit-test pin, no authority record or runtime execution
const optional=buildSource(source,{ledgerAuthorityPin:testPin});
assert.equal(optional.optionalLedger.enabled,true);
assert.equal(optional.optionalLedger.authorityRecordPin,testPin);
assert(optional.source.includes('function compatRunLedgerReview('));
assert(optional.source.includes('let s=dte(r,a,e)'));
assert(optional.source.includes('r!=="formalize.reviewLedger"&&await Oi(t)'));
assert.deepEqual(optional.unchanged,repair.unchanged);
assert.throws(()=>buildSource(source,{ledgerAuthorityPin:''}),/reviewed authority pin/);
assert.throws(()=>buildSource(source+'\n'),/not the reviewed v8/);
console.log(JSON.stringify({ok:true,defaultRepairSha256:repair.outputSha256,
  optionalCompositionSha256:optional.outputSha256,ledgerDefaultEnabled:false,
  unchanged:repair.unchanged,cliExecuted:false,compilerExecuted:false},null,2));
