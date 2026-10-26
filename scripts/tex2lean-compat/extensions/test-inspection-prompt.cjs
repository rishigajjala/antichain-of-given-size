'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
assert(process.argv.length === 3 && process.argv[2], 'Usage: node test-inspection-prompt.cjs /path/to/v8/out/cli.cjs');
const vm = require('node:vm');
const {patchInspectionPrompt} = require('./inspection-prompt.cjs');
const bundle = process.argv[2];
const source = fs.readFileSync(bundle, 'utf8');
const patched = patchInspectionPrompt(source);
function between(s, start, end) {
  const a = s.indexOf(start), b = s.indexOf(end, a + start.length);
  assert(a >= 0 && b > a, `generator extraction failed: ${start}`);
  return s.slice(a, b);
}
function context(s) {
  const ctx = vm.createContext({
    JSON,
    xT: e => e.elaborateOnly !== true,
    nk: () => [],
    ig: async () => false,
    og: async () => { throw Error('unexpected temporary prompt write'); },
    ol: () => ({}),
    $1: () => ({permissions: {}}),
    _c: '--append-system-prompt',
    ag: () => {},
    _e: condition => assert(condition),
    zc: 'Preserve all mathematical statements and definitions.',
    g: () => {},
    Ys: [], Js: [], Zs: ''
  });
  vm.runInContext(between(s, 'function R1(', 'async function ste('), ctx);
  vm.runInContext(between(s, 'async function ste(', 'function dte('), ctx);
  vm.runInContext(between(s, 'function dte(', 'function lte('), ctx);
  vm.runInContext(between(s, 'function lte(', 'function cte('), ctx);
  return ctx;
}
const task = {
  cfg: {agentSubagent: '', agentBuildCheck: false},
  tools: 'Read,Grep,Glob,Write,Edit',
  role: ['Read the paper and state its theorem exactly. Write no Lean.'],
  blueprint: {agentPlan: {definitionOfDone: []}},
  resultMode: 'file',
  projectDir: '/virtual/project',
  libraryDirs: ['/virtual/pinned-library'],
  rules: () => [
    '  - Read the actual paper and its surrounding definitions.',
    '  - Write exactly one file: `.blueprint/in-progress/restatement.agent.json`. Nothing else, anywhere.',
    '  - Do not commit; nothing here is committed.'
  ]
};
const brief = {
  title: 'Read the target', file: '.blueprint/in-progress/restatement.agent.json',
  goal: 'Read paper/main.tex and return the exact theorem contract as JSON.',
  exactStatements: [], allowedLemmas: [], strategy: [], incremental: [], buildCommand: ''
};
const plain = x => JSON.parse(JSON.stringify(x));
async function main() {
  const old = context(source), next = context(patched.source);
  const oldCodex = await old.ste('codex', '/mock/codex', brief, task);
  const newCodex = await next.ste('codex', '/mock/codex', brief, task);
  assert(oldCodex.input.includes('Bash is not available. Do not attempt shell'));
  assert(!newCodex.input.includes('Bash is not available. Do not attempt shell'));
  assert.deepEqual(plain(newCodex.args), plain(oldCodex.args), 'Codex execution permissions/arguments unchanged');
  assert(newCodex.input.includes('exec_command, shell_command'));
  assert(newCodex.input.includes('read-only local inspection with rg, cat, sed -n'));
  assert(newCodex.input.includes('Read the actual source files required by the task'));
  assert(newCodex.input.includes('stop and report the access blocker'));
  assert(newCodex.input.includes('do not present an excerpt-only answer as verified'));
  assert(newCodex.input.includes('single JSON result file at the exact path explicitly named'));
  assert(newCodex.input.includes('file-writing or patch API for that file only'));
  assert(newCodex.input.includes(task.rules()[1]), 'original exact output path rule retained');
  assert(newCodex.input.includes('Do not run Lean, Lake, builds, compilation, probes, package installation, network'));
  assert(newCodex.input.includes('commands, or Git commands. Do not edit Lean source'));
  assert(newCodex.input.includes('Do not use shell redirection or commands to'));
  assert(!newCodex.input.includes('You have full shell and editing access'));
  assert.equal(task.tools, 'Read,Grep,Glob,Write,Edit', 'configured tool list not mutated');

  const oldClaude = await old.ste('claude', '/mock/claude', brief, task);
  const newClaude = await next.ste('claude', '/mock/claude', brief, task);
  assert.deepEqual(plain(newClaude.args), plain(oldClaude.args), 'Claude prompt and CLI whitelist unchanged');
  assert.equal(newClaude.input, oldClaude.input, 'Claude task prompt unchanged');
  const ti = newClaude.args.indexOf('--tools');
  assert.equal(newClaude.args[ti + 1], task.tools);
  assert(newClaude.args[newClaude.args.indexOf('--append-system-prompt') + 1]
    .includes('Bash is not available. Do not attempt shell'));

  const readOnly = {...task, tools: 'Read,Grep,Glob'};
  const readOnlyPrompt = await next.ste('codex', '/mock/codex', brief, readOnly);
  assert(readOnlyPrompt.input.includes('This task permits no file writes or edits'));
  assert(!readOnlyPrompt.input.includes('The sole write exception'));
  assert.deepEqual(plain(next.R1(readOnly.tools)), ['Read', 'Grep', 'Glob']);

  const full = {...task, tools: 'Read,Write,Edit,Glob,Grep,Bash'};
  const fullOld = await old.ste('codex', '/mock/codex', brief, full);
  const fullNext = await next.ste('codex', '/mock/codex', brief, full);
  assert.equal(fullNext.input, fullOld.input, 'ordinary full-access proof prompt unchanged');
  assert.deepEqual(plain(fullNext.args), plain(fullOld.args));
  assert.equal(next.dte(task), old.dte(task), 'unspecified provider retains legacy restrictive wording');

  assert.throws(() => patchInspectionPrompt(patched.source), /anchor mismatch/, 'double application refused');
  assert.throws(() => patchInspectionPrompt(source.replace('function dte(e,t){', 'function dte(changed){')),
    /anchor mismatch/, 'unknown generator shape refused');
  const validatorStart = 'for(let Zt of un.ledger.bindings){let nt=nr.get(Zt.id);';
  const validatorEnd = 'un=await it.readCurrent(Ge.ledger.target.id)??un}';
  const loop = s => s.slice(s.indexOf(validatorStart), s.indexOf(validatorEnd, s.indexOf(validatorStart)) + validatorEnd.length);
  assert.equal(loop(patched.source), loop(source), 'native validator unchanged');
  assert.equal(between(patched.source, 'function KJ(', 'function XJ('),
    between(source, 'function KJ(', 'function XJ('), 'native ledger replay/store unchanged');
  console.log(JSON.stringify({ok: true, before: patched.before, after: patched.after,
    tests: ['actual dte/ste/lte generators; Codex read-only capability equivalents',
      'mandatory actual source inspection; exact JSON-only write exception',
      'no-write task remains no-write; forbidden builds/network/git/source edits',
      'Claude prompt and native tool whitelist unchanged',
      'ordinary full-access proof prompt and Codex arguments unchanged',
      'unique-anchor/double-application refusal; native validator/store unchanged'],
    cliExecuted: false, providerInvoked: false, compilerExecuted: false, repositoryChanged: false}, null, 2));
}
main().catch(error => {console.error(error); process.exitCode = 1;});
