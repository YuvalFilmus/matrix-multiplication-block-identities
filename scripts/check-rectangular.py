#!/usr/bin/env python3
"""Check the approved rectangular interface, draft quarantine, and proved basics.
Draft types are elaborated but never counted as proved or axiom-clean.
"""
from pathlib import Path
import hashlib,json,os,re,subprocess,tempfile
root=Path(__file__).resolve().parents[1]
subprocess.run(['python3',str(root/'scripts/check-frozen.py')],cwd=root,check=True)
m=json.loads((root/'review/frozen-manifest.json').read_text())
a=m['rectangular_author_approval']
packet=(root/a['packet']).read_text()
assert hashlib.sha256(packet.encode()).hexdigest()==a['packet_sha256']
parts=packet.split('\n'+'='*76+'\n')
defs=parts[0].split('PROPOSED FILE: BlockIdentities/Rectangular/Definitions.lean\n\n',1)[1]
assert defs==(root/'BlockIdentities/Rectangular/Definitions.lean').read_text()
code='module\npublic import BlockIdentities.Arithmetic.RectangularBasics\npublic import BlockIdentities.Arithmetic.ShapeBasics\n'
anchors={a['path']:a for a in m['anchors'] if a['id'].startswith('rectangular.')}
assert len(anchors)==18
for a in anchors.values():
    code+='public import '+a['path'][:-5].replace('/','.')+'\n'
code+='open scoped BigOperators NNReal\nnamespace BlockIdentities.Rectangular\nopen BlockIdentities.Square\nopen OAI.MatrixMultiplication.AuxiliarySeparation\n'
for part in parts[1:]:
    header,text=part.split('\n\n',1)
    path=header.split('PROPOSED FILE: ',1)[1].strip()
    approved=text[text.index('theorem '):].split(':= by\n  sorry\n',1)[0].strip()
    frozen=(root/path).read_text().split('-- BEGIN APPROVED PROOF REGION\n')[0]
    frozen=frozen[frozen.index('theorem '):].rsplit(':=',1)[0].strip()
    assert approved==frozen, f'Approved declaration drift: {path}'
    name,tail=approved.removeprefix('theorem ').split(' ',1)
    binders,result=tail.rsplit(' :\n  ',1)
    code+='\n#check fun '+binders+' => ('+result+' : Prop)\n'
    if anchors[path]['state']=='SEALED':
        code+='#print axioms '+anchors[path]['export']+'\n'
code+='end BlockIdentities.Rectangular\n'
# Definitions and actual elementary results must have no unapproved proof inputs.
for namespace,names in {
'Arithmetic':['FormalShapeAdmissibleExponent','formalShapeOmega',
 'FormalRectangularAdmissibleExponent','formalRectangularOmega','formalAlpha',
 'FormalRectangularAdmissibleExponent.admissible',
 'formalRectangularAdmissibleExponent_naive','formalRectangularAdmissibleExponent_nonempty',
 'formalRectangularAdmissibleExponent_two_le','formalRectangularAdmissibleExponent_bddBelow',
 'formalRectangularOmega_two_le','formalRectangularOmega_le_naive','formalRectangularOmega_zero',
 'formalShapeAdmissibleExponent_iff_rectangular','formalShapeOmega_one_k_one',
 'formalShapeAdmissibleExponent_naive','formalShapeAdmissibleExponent_nonempty',
 'formalShapeAdmissibleExponent_output_le','formalShapeAdmissibleExponent_bddBelow',
 'formalShapeOmega_output_le','formalShapeOmega_nonneg','formalShapeOmega_le_naive',
 'formalShapeAdmissibleExponent_formalShapeOmega','formalShapeOmega_zero_zero_zero',
 'rectangularOmega_le_formalRectangularOmega',
 'formalRectangularAdmissibleExponent_formalRectangularOmega',
 'formalRectangularAdmissibleExponent_of_omega_le','formalAlpha_nonneg','formalAlpha_le_one'],
'Rectangular':['orientedExponent','matrixWeight','logDotDimensions','orientedGains',
 'orientedValue','tensorAsymptoticRank','generalTriplingSplit'],
}.items():
    for name in names:code+='#print axioms BlockIdentities.'+namespace+'.'+name+'\n'
(root/'work').mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile('w',suffix='.lean',dir=root/'work',delete=False) as f:
    f.write(code);probe=Path(f.name)
try:
    r=subprocess.run(['lake','env','lean',str(probe)],cwd=root,
        env=dict(os.environ,LEAN_NUM_THREADS='1'),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
finally:probe.unlink()
(root/'review/rectangular/current-interface-check.txt').write_text(r.stdout)
if r.returncode:print(r.stdout);raise SystemExit(r.returncode)
assert 'sorryAx' not in r.stdout, 'Unapproved proof input in a definition or proved result'
for used in re.findall(r'depends on axioms: \[([^]]*)\]',r.stdout):
    assert set(map(str.strip,used.split(','))) <= {'propext','Classical.choice','Quot.sound',''}
print('Rectangular check passed: 18 approved types; definitions and proved rectangular/shape basics use standard axioms only.')
print('FROZEN_UNPROVED:',sum(a['state']=='DRAFT_SORRY' for a in anchors.values()))
