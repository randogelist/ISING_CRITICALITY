#!/usr/bin/env python3
"""GitHub Actions only: compile/audit new modules and verify cached CI receipts."""
import atexit, datetime, argparse, hashlib, json, os, pathlib, re, shutil, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
PIN = 'db584cd6d46c92f209a44c0f1c829460d327499d'
p = argparse.ArgumentParser()
p.add_argument('--mathlib', default=os.environ.get('MATHLIB_DIR'))
p.add_argument('--lean', default=os.environ.get('LEAN', 'lean'))
p.add_argument('--fresh', action='store_true')
a = p.parse_args()
if (os.environ.get('GITHUB_ACTIONS') != 'true'
        or os.environ.get('CI') != 'true'
        or not os.environ.get('GITHUB_RUN_ID', '').isdigit()
        or not os.environ.get('GITHUB_REPOSITORY')
        or not os.environ.get('GITHUB_SHA')):
    sys.exit('LEAN_CI_ONLY: Lean compilation and audit must run in GitHub Actions. '
             'Push the source or dispatch the Verify Lean and C++ workflow.')
os.chdir(ROOT)
ci = dict(execution_environment='github_actions',
          repository=os.environ['GITHUB_REPOSITORY'],
          commit=os.environ['GITHUB_SHA'],
          run_id=os.environ['GITHUB_RUN_ID'],
          run_attempt=os.environ.get('GITHUB_RUN_ATTEMPT', '1'),
          run_url=f"https://github.com/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{os.environ['GITHUB_RUN_ID']}",
          runner_os=os.environ.get('RUNNER_OS'),
          runner_arch=os.environ.get('RUNNER_ARCH'))
(ROOT/'audit').mkdir(parents=True,exist_ok=True)
run_status = dict(status='RUNNING',started_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),**ci)
status_path = ROOT/'audit/last-run-status.json'
status_path.write_text(json.dumps(run_status,indent=2)+'\n')
def finish_status():
    if run_status['status']=='RUNNING': run_status['status']='FAILED_OR_INTERRUPTED'
    status_path.write_text(json.dumps(run_status,indent=2)+'\n')
atexit.register(finish_status)
mathlib = pathlib.Path(a.mathlib).resolve() if a.mathlib else ROOT/'.lake/packages/mathlib'
if not (mathlib/'.lake/build/lib/lean/Mathlib.olean').exists():
    sys.exit('Mathlib cache missing: the CI dependency step must run lake update and lake exe cache get.')
lean = shutil.which(a.lean) or a.lean
version = subprocess.check_output([lean,'--version'],text=True).strip()
if 'version 4.33.0,' not in version: sys.exit('Expected Lean 4.33.0; got '+version)
revision = subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()
if revision != PIN: sys.exit('Mathlib pin mismatch: '+revision)
if subprocess.run(['git','-C',str(mathlib),'diff','--quiet','HEAD','--','Mathlib','Mathlib.lean','lake-manifest.json','lean-toolchain']).returncode:
    sys.exit('Mathlib tracked source or dependency manifest changed from pinned revision')
out = ROOT/'.lake/build/lib/lean'; out.mkdir(parents=True,exist_ok=True)
paths = [out, mathlib/'.lake/build/lib/lean']
for base in [mathlib/'.lake/packages',ROOT/'.lake/packages']:
    paths += sorted(base.glob('*/.lake/build/lib/lean'))
env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,paths)))
modules = ['PCD.Q3Defs','PCD.Q3BaseBounds']+[f'PCD.Q3D{d}' for d in range(3,12)]+['PCD.Q3Aggregate','IsingCriticality.Approximants','IsingCriticality.FinitePartition','IsingCriticality.Identification','IsingCriticality','Audit']
receipt_path = ROOT/'audit/build-receipt.json'
old = json.loads(receipt_path.read_text()) if receipt_path.exists() else {}
compile_flags = ['-o']
environment = [ci['runner_os'], ci['runner_arch'], compile_flags,
               hashlib.sha256((mathlib/'lake-manifest.json').read_bytes()).hexdigest()]
rows=[]; hashes={}; compiled=0
all_log=[]
for module in modules:
    src=ROOT/(module.replace('.','/')+'.lean')
    if not src.exists(): sys.exit('Missing module '+str(src))
    text=src.read_text()
    # Text scan supplements, never substitutes for compiler and #print axioms.
    if re.search(r'\b(sorry|admit|unsafe|implemented_by|native_decide)\b|^\s*axiom\s', re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S), re.M):
        sys.exit('Proof escape scan failed: '+module)
    imports=re.findall(r'^import\s+(\S+)',text,re.M)
    for imported in imports:
        if (imported.startswith('PCD.') or imported.startswith('IsingCriticality')) and imported not in hashes:
            sys.exit('Unresolved local import '+imported+' in '+module)
    source_hash=hashlib.sha256(src.read_bytes()).hexdigest()
    identity=hashlib.sha256(json.dumps([source_hash,version,revision,environment,[(i,hashes.get(i,revision)) for i in imports]]).encode()).hexdigest()
    target=out/(module.replace('.','/')+'.olean'); target.parent.mkdir(parents=True,exist_ok=True)
    previous=next((r for r in old.get('modules',[]) if r['module']==module),{})
    cached=old.get('execution_environment')=='github_actions' and old.get('repository')==ci['repository'] and old.get('result')=='PASS' and previous.get('result')=='PASS' and not a.fresh and module!='Audit' and previous.get('identity')==identity and target.exists() and previous.get('olean_sha256')==hashlib.sha256(target.read_bytes()).hexdigest()
    if cached:
        print('REUSE='+module,flush=True)
    else:
        print('COMPILE='+module,flush=True)
        result=subprocess.run([lean,'-o',str(target),str(src.relative_to(ROOT))],env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        all_log.append(f'--- {module} ---\n'+result.stdout)
        if result.stdout: print(result.stdout,flush=True)
        if result.returncode:
            (ROOT/'audit/last-build.log').write_text('\n'.join(all_log))
            sys.exit(result.returncode)
        compiled+=1
    hashes[module]=identity
    rows.append(dict(module=module,identity=identity,source_sha256=source_hash,olean_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),result='PASS',cache_reused=cached))
log='\n'.join(all_log)
if 'sorryAx' in log or 'Lean.ofReduceBool' in log: sys.exit('Unapproved axiom in audit')
for found in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):
    if {x.strip() for x in found.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}: sys.exit('Unexpected axioms: '+found)
expected_audits=re.findall(r'^#print axioms (\S+)', (ROOT/'Audit.lean').read_text(), re.M)
for declaration in expected_audits:
    if declaration not in log: sys.exit('Missing audited declaration '+declaration)
if 'AXIOM_AUDIT_END' not in log: sys.exit('Audit did not finish')
receipt=dict(verified_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),lean=version,mathlib_revision=revision,compile_flags=compile_flags,modules=rows,new_compiled=compiled,frozen_reused=len(rows)-compiled,axioms_allowed=['propext','Classical.choice','Quot.sound'],physical_identification='CONDITIONAL_ONLY',formula_precision='q3 d3..11 nearest 1e-8',result='PASS',**ci)
receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
(ROOT/'audit/last-build.log').write_text(log)
run_status.update(status='PASS',finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat())
print('LEAN_BUILD=PASS\nAXIOM_AUDIT=PASS_STANDARD_ONLY\nPHYSICAL_IDENTIFICATION=CONDITIONAL_ONLY')
