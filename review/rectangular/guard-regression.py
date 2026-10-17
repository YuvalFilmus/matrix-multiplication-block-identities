#!/usr/bin/env python3
"""Isolated source guard regression. Never runs Lean/Lake or edits production."""
from pathlib import Path
import tempfile, shutil, subprocess, json, sys
src=Path(__file__).resolve().parents[2]
with tempfile.TemporaryDirectory(prefix='rect-guard-review-') as td:
    root=Path(td)
    shutil.copytree(src/'BlockIdentities',root/'BlockIdentities')
    shutil.copy(src/'BlockIdentities.lean',root/'BlockIdentities.lean')
    (root/'scripts').mkdir(); shutil.copy(src/'scripts/check-frozen.py',root/'scripts/check-frozen.py')
    (root/'review/rectangular').mkdir(parents=True); (root/'source').mkdir()
    for p in ['review/AuthorReview.txt','review/frozen-manifest.json','review/rectangular/AuthorReview.txt','source/manuscript.tex']:
        shutil.copy(src/p,root/p)
    manifest=json.loads((src/'review/frozen-manifest.json').read_text())
    anchor=next((a for a in manifest['anchors']
                 if a['id'].startswith('rectangular.') and a['state']=='DRAFT_SORRY'), None)
    if "--simulate-closed" in sys.argv:
        anchor=None
    if anchor is None:
        # Recreate a quarantined leaf ONLY in the isolated fixture after closure.
        anchor=next(a for a in manifest['anchors']
                    if a['id']=='rectangular.rectangular_alpha_ge_half')
        anchor.update(state='DRAFT_SORRY',quarantine=True)
        frozen=root/anchor['path']
        prefix,rest=frozen.read_text().split('-- BEGIN APPROVED PROOF REGION\n')
        _,suffix=rest.split('-- END APPROVED PROOF REGION\n')
        frozen.write_text(prefix+'-- BEGIN APPROVED PROOF REGION\nby sorry\n'+
                          '-- END APPROVED PROOF REGION\n'+suffix)
        (root/'review/frozen-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
        leaf=anchor['path'][:-5].replace('/','.')
        # No implementation theorem is checked here: this is a source guard test.
        # Remove aggregation imports of the simulated draft leaf in the fixture.
        for path in [root/'BlockIdentities.lean',*(root/'BlockIdentities').rglob('*.lean')]:
            if path!=frozen:
                path.write_text(path.read_text().replace('public import '+leaf+'\n',''))
    target=anchor['path'][:-5].replace('/','.')
    provider=anchor['provider']['module']
    cases={
        'baseline':('module\n',0),
        'leading-space':('module\n public import '+target+'\n',1),
        'second-module':('module\npublic import BlockIdentities.Tensor.Value '+target+'\n',1),
        'multiline-first':('module\npublic import\n '+target+'\n',1),
        'multiline-second':('module\npublic import BlockIdentities.Tensor.Value\n '+target+'\n',1),
        'unknown':('module\n public import BlockIdentities.Rectangular.Frozen.Unknown\n',1),
        'provider':('module\n public import\n '+provider+'\n',1),
        'comment':('module\n-- public import '+target+'\n',0),
    }
    fixture=root/'BlockIdentities/Rectangular/GuardRegression.lean'
    for label,(code,expected) in cases.items():
        fixture.write_text(code)
        proc=subprocess.run(['python3',str(root/'scripts/check-frozen.py')],capture_output=True,text=True)
        assert proc.returncode==expected,(label,proc.stdout,proc.stderr)
        print(label, 'PASS')
