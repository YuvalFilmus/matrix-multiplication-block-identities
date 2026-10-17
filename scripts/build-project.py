#!/usr/bin/env python3
"""One serialized Lake build of production modules and quarantined anchors."""
from pathlib import Path
import os,json,subprocess
root=Path(__file__).resolve().parents[1]
m=json.loads((root/'review/frozen-manifest.json').read_text())
targets=['BlockIdentities']+[a['path'][:-5].replace('/','.') for a in m['anchors']]
for a in m['anchors']:
    if a.get('provider'):
        module = a['provider']['module']
        present = (root / (module.replace('.', '/') + '.lean')).is_file()
        assert present or a['state'] == 'DRAFT_SORRY', f'Missing sealed provider: {module}'
        if present:
            targets.append(module)
# Compile ordinary helpers as well, including modules not yet used by a sealed root.
targets += sorted(str(p.relative_to(root)).removesuffix('.lean').replace('/', '.')
                  for p in (root / 'BlockIdentities').rglob('*.lean')
                  if 'Frozen' not in p.relative_to(root).parts)
targets = list(dict.fromkeys(targets))
raise SystemExit(subprocess.run(['lake','build',*targets],cwd=root,env=dict(os.environ,LEAN_NUM_THREADS='1')).returncode)
