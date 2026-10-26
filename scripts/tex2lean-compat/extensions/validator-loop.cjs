'use strict';
const assert=require('node:assert/strict');
const crypto=require('node:crypto');
// Inspection/test helper only: returns the complete, unchanged native for-loop.
function extractValidatorLoop(source) {
  const start=source.indexOf('for(let Zt of un.ledger.bindings){let nt=nr.get(Zt.id);');
  assert(start>=0,'expected native validator loop absent');
  // The refresh is INSIDE the loop. Including its closing brace is essential.
  const suffix='un=await it.readCurrent(Ge.ledger.target.id)??un}';
  const at=source.indexOf(suffix+'Ge=',start);
  assert(at>start,'expected native validator loop boundary absent');
  const loop=source.slice(start,at+suffix.length);
  return {loop,digest:crypto.createHash('sha256').update(loop).digest('hex')};
}
module.exports={extractValidatorLoop};
