#!/usr/bin/env python3
"""Fail closed on frozen types, semantic bytes, draft bodies and import quarantine."""
from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parents[1]
m=json.loads((root/'review/frozen-manifest.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha((root/'review/AuthorReview.txt').read_bytes())==m['author_approval']['packet_sha256']
assert sha((root/m['source']['path']).read_bytes())==m['source']['sha256']
if 'rectangular_author_approval' in m:
    approval=m['rectangular_author_approval']
    assert sha((root/approval['packet']).read_bytes())==approval['packet_sha256']
for path,digest in m['semantic_modules'].items():
    assert sha((root/path).read_bytes())==digest, f'Semantic drift: {path}'
paths=set();exports=set();allowed={}
for a in m['anchors']:
    assert a['path'] not in paths and a['export'] not in exports
    paths.add(a['path']);exports.add(a['export'])
    text=(root/a['path']).read_text()
    prefix,rest=text.split('-- BEGIN APPROVED PROOF REGION\n')
    body,suffix=rest.split('-- END APPROVED PROOF REGION\n')
    prefix+='-- BEGIN APPROVED PROOF REGION\n';suffix='-- END APPROVED PROOF REGION\n'+suffix
    assert sha(prefix.encode())==a['prefix_sha256'],f'Prefix drift: {a["id"]}'
    assert sha(suffix.encode())==a['suffix_sha256'],f'Suffix drift: {a["id"]}'
    declaration=prefix[prefix.index('theorem '):].rsplit(':=',1)[0].strip()
    assert sha(declaration.encode())==a['declaration_sha256'], f'Declaration drift: {a["id"]}'
    assert len(re.findall(r'^theorem ',text,re.M))==1
    assert re.search(r'^theorem '+re.escape(a['export'].rsplit('.',1)[1])+r'\b',text,re.M)
    if a['state']=='DRAFT_SORRY':
        assert body==a['allowed_body']=='by sorry\n'
        allowed[a['path']]=text.index(body)+3
    else:
        assert a['state']=='SEALED' and 'sorry' not in body
        assert sha(body.encode())==a['sealed_body_sha256']
    assert a['quarantine'] == (a['state']=='DRAFT_SORRY')
quarantined = {}
for a in m['anchors']:
    if a['state']=='DRAFT_SORRY' and a.get('provider'):
        quarantined.setdefault(a['provider']['module'],set()).add(a['path'])
for path in [root/'BlockIdentities.lean',*(root/'BlockIdentities').rglob('*.lean')]:
    rel=str(path.relative_to(root));text=path.read_text()
    module=rel[:-5].replace('/','.')
    masked=re.sub(r'/\-.*?\-/|--[^\n]*','',text,flags=re.S)
    dependencies=[]
    # Lean header whitespace includes newlines. Scan complete identifier runs
    # after import, rather than just the first column or first physical line.
    for group in re.findall(r"\bimport\s+((?:[\w.']+\s*)+)",masked):
        dependencies.extend(group.split())
    for dependency in dependencies:
        if dependency in quarantined:
            assert module==dependency or rel in quarantined[dependency], f'Provider quarantine violation: {rel} -> {dependency}'
    for dependency in dependencies:
        target=dependency.replace('.', '/')+'.lean'
        if target in paths:
            assert target not in allowed, f'Draft frozen import: {rel} -> {dependency}'
        elif re.match(r'BlockIdentities\.(?:Rectangular\.)?Frozen\.',dependency):
            raise AssertionError(f'Unknown frozen import: {rel} -> {dependency}')
    # The owned sources contain no tactic strings or comments mentioning holes.
    if rel not in paths:
        assert not re.search(r'\b(?:sorry|admit|axiom)\b',masked),f'Unauthorized hole/axiom: {rel}'

        for dep in re.findall(r'^(?:public )?import (BlockIdentities\.(?:Rectangular\.)?Frozen\.\S+)',masked,re.M):
            target=dep.replace('.','/')+'.lean'
            assert target in paths and target not in allowed, f'Draft/unknown frozen import: {rel} -> {dep}'
    else:
        assert not re.search(r'\b(?:admit|axiom)\b',masked),f'Unauthorized axiom: {rel}'
        assert len(re.findall(r'\bsorry\b',masked))==(1 if rel in allowed else 0)
discovered={str(p.relative_to(root)) for p in (root/'BlockIdentities').rglob('*.lean') if 'Frozen' in p.relative_to(root).parts}
assert discovered == paths, f'Frozen ownership mismatch: {discovered ^ paths}'
print(f'Frozen guard passed: {len(paths)} exact theorem anchors; semantic bytes and quarantine intact.')
print('DRAFT_ANCHORS:',len(allowed))
print('UNREGISTERED_SORRIES: 0; DRAFT_IMPORT_VIOLATIONS: 0')
