
'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm');
const assert=require('node:assert/strict'),crypto=require('node:crypto');
const project=process.argv[2];assert(project,'pass the source project root');
const dir=__dirname,m=JSON.parse(fs.readFileSync(path.join(dir,'manifest.json'),'utf8'));
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const ctx=vm.createContext({});
for(const name of ['In','Ffe','zhe']){const f=m.nativeFunctions[name],b=fs.readFileSync(path.join(dir,f.file));assert.equal(sha(b),f.sha256);vm.runInContext(b.toString(),ctx);}
vm.runInContext('var jhe=3;',ctx);
const sources=Object.entries(m.sources).map(([file,r])=>{const bytes=fs.readFileSync(path.join(project,file));assert.equal(sha(bytes),r.sha256);return{file,text:bytes.toString()};});
const raw=JSON.parse(JSON.stringify(ctx.Ffe({auditSurfaceSources:sources})));
const affected=raw.filter(row=>row.lines>3);
for(const row of affected){const source=sources.find(s=>s.file===row.file).text.split('\n').slice(row.line-1);const marker=source.findIndex(x=>/:= by\s*$/.test(x));assert(marker>=0);const body=[];for(const line of source.slice(marker+1)){if(/^\S/.test(line))break;if(line.trim()&&!line.trim().startsWith('--'))body.push(line.trim());}assert.equal(body.length,1);assert.match(body[0],/^exact /);row.actualProofLines=body;}
const diagnostic=JSON.parse(JSON.stringify(ctx.zhe({surfaceProofs:raw})));
assert.equal(diagnostic.ok,false);assert.equal(diagnostic.id,'surface-states');
console.log(JSON.stringify({kind:m.kind,sourceCommit:m.sourceCommit,sourceFingerprint:m.sourceFingerprint,bundleSha256:m.bundle.sha256,modelFileCount:sources.length,affectedWrapperCount:affected.length,affectedWrappers:affected,nativeDiagnostic:diagnostic,nativeWorkflowExecuted:false,compilerExecuted:false,overallNativeCheckPassClaim:false},null,2));
