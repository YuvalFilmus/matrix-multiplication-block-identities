#!/usr/bin/env python3
"""Check or initially record pretty-printed elaborated types, never proof bodies."""
from pathlib import Path
import hashlib,json,os,subprocess,tempfile,sys
root=Path(__file__).resolve().parents[1]; path=root/'review/frozen-manifest.json'
m=json.loads(path.read_text());code='module\n'
for a in m['anchors']:code+='public import '+a['path'][:-5].replace('/','.')+'\n'
code+='set_option pp.all true\n'
for a in m['anchors']:
    code+=f'#eval IO.println "ABI-BEGIN:{a["id"]}"\n#check @{a["export"]}\n#eval IO.println "ABI-END:{a["id"]}"\n'
(root/'work').mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile('w',suffix='.lean',dir=root/'work',delete=False) as f:f.write(code);probe=Path(f.name)
try:r=subprocess.run(['lake','env','lean',str(probe)],cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1'),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
finally:probe.unlink()
if r.returncode:print(r.stdout);raise SystemExit(r.returncode)
(root/'review/elaborated-abi.txt').write_text(r.stdout)
for a in m['anchors']:
    text=r.stdout.split('ABI-BEGIN:'+a['id']+'\n',1)[1].split('ABI-END:'+a['id'],1)[0]
    digest=hashlib.sha256(text.encode()).hexdigest()
    if a['abi_sha256'] is None:
        assert '--record-initial' in sys.argv,'Initial ABI recording requires explicit flag'
        a['abi_sha256']=digest
    else:assert a['abi_sha256']==digest, f'Elaborated ABI drift: {a["id"]}'
if '--record-initial' in sys.argv:path.write_text(json.dumps(m,indent=2)+'\n')
print(f'Elaborated ABI check passed: {len(m["anchors"])} exact exports.')
