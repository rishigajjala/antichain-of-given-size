'use strict';
const assert = require('node:assert/strict');
const crypto = require('node:crypto');
const digest = source => crypto.createHash('sha256').update(source).digest('hex');

// Source transformation only. Does not load the CLI, invoke a provider, or write files.
function patchInspectionPrompt(source) {
  assert.equal(typeof source, 'string', 'CLI source text required');
  let result = source;
  const changes = [];
  function replaceUnique(before, after, purpose) {
    assert.equal(result.split(before).length - 1, 1, `inspection prompt anchor mismatch: ${purpose}`);
    result = result.replace(before, after);
    changes.push(purpose);
  }
  replaceUnique(
    'async function ste(e,t,n,r,i,o,a){let s=dte(r,a),d=lte(n,r,i,o)',
    'async function ste(e,t,n,r,i,o,a){let s=dte(r,a,e),d=lte(n,r,i,o)',
    'Pass the actual provider kind to the existing standing-prompt generator');
  replaceUnique(
    'function dte(e,t){let n=!xT(e),r=R1(e.tools),i=r.includes("Bash"),o=',
    'function dte(e,t,providerKind){let n=!xT(e),r=R1(e.tools),i=r.includes("Bash"),o=',
    'Allow provider-specific wording without changing configured tool permissions');
  const legacy = ':o.push("","## Available tools",`You have ${r.join(", ")||"no tools"}. Bash is not available. Do not attempt shell`,"commands or Lean probes. Use Read, Glob, and Grep to inspect files, and Write or Edit only where","this task permits it.")';
  const inspectionLines = [
    '', '## Source inspection and permitted output',
    'This is an inspection task. The configured Read, Glob, and Grep labels describe',
    'capabilities, not required API names. Use the equivalent tools actually available',
    'in Codex; missing tools with those literal names do not prevent source inspection.',
    'You may use read-only file/search APIs, or exec_command, shell_command, or an',
    'equivalent shell tool for read-only local inspection with rg, cat, sed -n, head,',
    'tail, nl, ls, or pwd. Read only within this project and the explicitly listed',
    'read-only library directories. This permission does not grant general shell use.',
    '',
    'Read the actual source files required by the task, including relevant surrounding',
    'definitions and conventions. The supplied excerpt is a starting point, not a',
    'substitute for source inspection. If no available tool can access those sources,',
    'stop and report the access blocker; do not present an excerpt-only answer as verified.',
    '',
    'Do not run Lean, Lake, builds, compilation, probes, package installation, network',
    'commands, or Git commands. Do not edit Lean source, configuration, workflow/status',
    'records, libraries, or any other file. Do not use shell redirection or commands to',
    'create, modify, move, or delete files.'
  ];
  const writePermission = '(r.includes("Write")||r.includes("Edit"))?' + JSON.stringify(
    'The sole write exception is the single JSON result file at the exact path explicitly named in this task. Use an available file-writing or patch API for that file only. Write JSON, not Lean or other code; do not create any other artifact. If no exact result path is authorized, write nothing.'
  ) + ':' + JSON.stringify('This task permits no file writes or edits, including temporary output files.');
  const replacement = ':providerKind==="codex"?o.push(' +
    inspectionLines.map(s => JSON.stringify(s)).join(',') + ',' + writePermission + ')' + legacy;
  replaceUnique(legacy, replacement,
    'Replace only Codex inspection wording with capability-based read permission and exact JSON-only output limits');
  return {
    source: result,
    changes,
    before: digest(source),
    after: digest(result),
    provider: 'codex',
    configuredToolsChanged: false,
    claudePromptChanged: false,
    nativeValidatorChanged: false,
    workflowExecuted: false
  };
}
module.exports = {patchInspectionPrompt};
