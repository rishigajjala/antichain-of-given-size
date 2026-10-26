#!/usr/bin/env node
'use strict';
// Reproducible extension of the reviewed v8 task-local CLI. Never edits its input.
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const crypto=require('node:crypto');
const {patch:patchLedger}=require('./patch.cjs');
const {patchInspectionPrompt}=require('./inspection-prompt.cjs');
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const EXPECTED='93d40c1b5465f43c456a0a46c63995a2d5f4439027fccbd57c3ecfee877af4b7';
function section(source,start,end) {
  const a=source.indexOf(start),b=source.indexOf(end,a+start.length);
  assert(a>=0&&b>a,start);return source.slice(a,b);
}
function buildSource(source,{ledgerAuthorityPin}={}) {
  assert.equal(sha(source),EXPECTED,'input is not the reviewed v8 task-local bundle');
  let next=source,ledger;
  if(ledgerAuthorityPin!==undefined) {
    assert(/^sha256-[0-9a-f]{64}$/.test(ledgerAuthorityPin),'explicit independently reviewed authority pin required');
    ledger=patchLedger(next,{authorityDigest:ledgerAuthorityPin});next=ledger.source;
  }
  const inspection=patchInspectionPrompt(next);next=inspection.source;
  const unchanged={};
  for(const [name,start,end] of [
    ['ModelClosure','function BD(','async function qD('],
    ['CostSeal','function ZA(','function XA('],
    ['native-ledger-replay-validation-store','function KJ(','function XJ('],
  ]) {
    const old=section(source,start,end),now=section(next,start,end);
    assert.equal(now,old,`${name} changed`);unchanged[name]=sha(old);
  }
  const marker='for(let Zt of un.ledger.bindings){let nt=nr.get(Zt.id);';
  const suffix='un=await it.readCurrent(Ge.ledger.target.id)??un}';
  const loop=s=>{const a=s.indexOf(marker),b=s.indexOf(suffix,a);assert(a>=0&&b>a);return s.slice(a,b+suffix.length);};
  assert.equal(loop(next),loop(source),'native validator loop changed');
  unchanged['native-binding-validator-loop']=sha(loop(source));
  return {source:next,inputSha256:sha(source),outputSha256:sha(next),
    bugFix:{name:'Codex read-only source-inspection capabilities',changes:inspection.changes},
    optionalLedger:ledger?{enabled:true,authorityRecordPin:ledgerAuthorityPin,changes:ledger.changes}:{enabled:false},
    unchanged,cliExecuted:false,compilerExecuted:false};
}
module.exports={buildSource};
if(require.main===module) {
  const args=process.argv.slice(2),options={};
  for(let i=0;i<args.length;i+=2) {
    assert(['--input','--output','--ledger-authority-pin','--node'].includes(args[i]),'unknown option '+args[i]);
    assert(args[i+1]!==undefined,'option value required');assert(!Object.hasOwn(options,args[i]),'duplicate option');
    options[args[i]]=args[i+1];
  }
  assert(options['--input']&&options['--output'],'--input and new --output are required');
  const out=path.resolve(options['--output']);
  assert(out.startsWith('/tmp/')||out.startsWith('/private/tmp/'),'generated CLI output must remain outside the repository in /tmp');
  assert(!fs.existsSync(out),'refusing to overwrite existing output');
  const result=buildSource(fs.readFileSync(options['--input'],'utf8'),{ledgerAuthorityPin:options['--ledger-authority-pin']});
  fs.mkdirSync(path.join(out,'out'),{recursive:true});fs.writeFileSync(path.join(out,'out/cli.cjs'),result.source);
  const supportModules={};
  if(result.optionalLedger.enabled) {
    fs.mkdirSync(path.join(out,'ledger-review'));
    for(const file of ['adapter.cjs','native-host.cjs']) {
      const bytes=fs.readFileSync(path.join(__dirname,file));fs.writeFileSync(path.join(out,'ledger-review',file),bytes);
      supportModules[file]=sha(bytes);
    }
  }
  const quote=s=>"'"+s.replaceAll("'","'\\''")+"'";
  const node=path.resolve(options['--node']??process.execPath);
  fs.writeFileSync(path.join(out,'tex2lean'),'#!/bin/sh\nexec '+quote(node)+' '+quote(path.join(out,'out/cli.cjs'))+' "$@"\n');
  fs.chmodSync(path.join(out,'tex2lean'),0o755);
  const manifest={...result,source:undefined,supportModules,node,output:out};
  fs.writeFileSync(path.join(out,'manifest.json'),JSON.stringify(manifest,null,2)+'\n');
  console.log(JSON.stringify(manifest,null,2));
}
