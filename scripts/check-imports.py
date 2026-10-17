#!/usr/bin/env python3
"""Check the source import closure of the new library against spectral/final proofs."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[1]
up=root/'vendor/navot/lean'
seen=set(); pending=['BlockIdentities'] + [str(p.relative_to(root)).removesuffix('.lean').replace('/', '.')
    for p in (root/'BlockIdentities').rglob('*.lean')]
forbidden=[]
while pending:
    name=pending.pop()
    if name in seen: continue
    seen.add(name)
    path=(root if name.startswith('BlockIdentities') else up)/Path(name.replace('.','/')).with_suffix('.lean')
    if not path.exists(): continue
    if name.startswith('OAI.LinearAlgebra.MatrixMultiplication') and (
       '.Character.' in name or '.Spectrum.' in name or name.endswith('.Characters') or '.Duality.' in name
       or name.endswith('.RankBound') or name.endswith('.AllFields') or name.endswith('.Main')):
        forbidden.append(name)
    text=path.read_text()
    # Mask nested Lean block comments and line comments, preserving line starts.
    raw=path.read_text(); masked=[]; depth=0; i=0
    while i<len(raw):
        pair=raw[i:i+2]
        if pair=='/-': depth+=1; masked.extend('  '); i+=2
        elif depth and pair=='-/': depth-=1; masked.extend('  '); i+=2
        elif not depth and pair=='--':
            end=raw.find('\n',i)
            end=len(raw) if end<0 else end
            masked.extend(' '*(end-i)); i=end
        else:
            masked.append('\n' if raw[i]=='\n' else (' ' if depth else raw[i])); i+=1
    text=''.join(masked)
    for dependency in re.findall(r'^(?:public )?import\s+(\S+)',text,re.M):
        if dependency.startswith(('BlockIdentities','OAI.')): pending.append(dependency)
report='\n'.join(sorted(seen))+'\n'
(root/'review/import-closure.txt').write_text(report)
if forbidden: raise SystemExit('Prohibited imports: '+', '.join(forbidden))
print(f'Import boundary passed: {len(seen)} project/upstream modules, no final bound or character proof.')
