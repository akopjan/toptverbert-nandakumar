#!/usr/bin/env python3
"""Record the genuine local sandboxed Comparator attempt; do not bypass bwrap."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json,os,subprocess,time
root=Path(__file__).resolve().parents[2]
out=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():
    paths=[]
    for p in root.rglob('*.lean'):
        rel=p.relative_to(root)
        if {'.lake','.git','verification','tests'} & set(rel.parts): continue
        paths.append(p)
    paths += [root/p for p in ('comparator.json','lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify-comparator.sh')]
    return {str(p.relative_to(root)):sha(p) for p in sorted(paths)}
started=datetime.now(timezone.utc).isoformat(); before=snapshot()
env=os.environ.copy(); env['TMPDIR']=str(out/'tmp'); (out/'tmp').mkdir(exist_ok=True)
command=['bash','scripts/verify-comparator.sh']; t=time.monotonic()
with (out/'comparator.log').open('wb') as log:
    result=subprocess.run(command,cwd=root,env=env,stdout=log,stderr=log)
after=snapshot(); content=(out/'comparator.log').read_text(errors='replace')
report={'started_utc':started,'finished_utc':datetime.now(timezone.utc).isoformat(),'command':command,'exit_code':result.returncode,'elapsed_seconds':round(time.monotonic()-t,3),'input_sha256_before':before,'input_sha256_after':after,'inputs_unchanged':before==after,'local_sandboxed_comparator_passed':result.returncode==0,'full_palomar_workflow':False,'bwrap_mount_failure_observed':'bwrap: Failed to mount tmpfs' in content,'sandbox_bypassed':False,'log_sha256':sha(out/'comparator.log')}
report['outcome']='local-sandboxed-comparator-passed' if result.returncode==0 else 'local-sandboxed-comparator-unsuccessful'
(out/'results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('outcome','exit_code','elapsed_seconds','inputs_unchanged','bwrap_mount_failure_observed')}))
raise SystemExit(result.returncode)
