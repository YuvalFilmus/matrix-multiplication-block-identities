#!/usr/bin/env python3
"""Elaborate every review header as a function returning Prop, without proof holes.
This checks types and binders, not truth or fidelity to the manuscript.
"""
from pathlib import Path
import os
import re
import subprocess
import tempfile

root = Path(__file__).resolve().parents[1]
source = (root / 'review/SquareStatements.lean.txt').read_text()
start = source.index('module\n')
source = source[start:]
preamble, rest = source.split('namespace BlockIdentities.Square\n', 1)
rest = rest.rsplit('end BlockIdentities.Square', 1)[0]
parts = re.split(r'^theorem ([a-zA-Z0-9_]+)\n', rest, flags=re.M)
code = preamble.replace('module\n', 'module\npublic import BlockIdentities.Tensor.Isomorphism\npublic import BlockIdentities.Square.FieldDescent\npublic import BlockIdentities.Providers.RankAndField\npublic import BlockIdentities\npublic import BlockIdentities.Frozen.formalCorrect_implies_correct\n', 1) + '\nset_option linter.unusedVariables false\nnamespace BlockIdentities.Square\n'
names = []
for i in range(1, len(parts), 2):
    name = parts[i]
    body = re.sub(r'--[^\n]*', '', parts[i + 1]).strip()
    binders, result = body.split('\n    : ', 1)
    code += f'-- Header: {name}\n#check fun {binders}\n    => ({result.strip()} : Prop)\n\n'
    names.append(name)
code += 'end BlockIdentities.Square\n'
for module in ['BlockIdentities.Frozen.formalOmega_eq_exactRankExponent_v2', 'BlockIdentities.Frozen.formalOmega_eq_algebraicClosure_v2', 'BlockIdentities.Frozen.scalar_descent_v2', 'BlockIdentities.Frozen.tripling_middle_isomorphism_v2', 'BlockIdentities.Frozen.convolution_boundary_isomorphism_v2']:
    code = code.replace('module\n', 'module\npublic import '+module+'\n', 1)
for module in ['BlockIdentities.Frozen.convolution_neighbor_degeneration_v2', 'BlockIdentities.Frozen.convolution_tripling_degeneration_v2']:
    code = code.replace('module\n', 'module\npublic import '+module+'\n', 1)
for module in ['BlockIdentities.Frozen.asymptotic_cancellation_v2', 'BlockIdentities.Frozen.value_matrix_factor_v2', 'BlockIdentities.Frozen.general_extraction_v3', 'BlockIdentities.Frozen.identities_to_exponent_v2', 'BlockIdentities.Frozen.finite_convolution_bound_v2', 'BlockIdentities.Frozen.formalOmega_le_nine_quarters_v2', 'BlockIdentities.Frozen.formal_matrix_multiplication_cost_le_v2', 'BlockIdentities.Frozen.omega_le_nine_quarters_v2', 'BlockIdentities.Frozen.shared_leg_value_inequality_v2']:
    code = code.replace('module\n', 'module\npublic import '+module+'\n', 1)
for theorem in ['map_evalProgramIn', 'evalProgramIn_id', 'eval_polynomialOutputs',
                'formalCorrect_implies_correct']:
    code += '#print axioms BlockIdentities.Arithmetic.' + theorem + '\n'
for namespace, theorems in {
    'Arithmetic': ['naiveAlgorithm_formalCorrect', 'formalOmega_mem_Icc',
                   'formalAdmissibleExponent_formalOmega', 'omega_le_formalOmega',
                   'evalProgramIn_substitute', 'FormalCorrect.evalProgramIn',
                   'recursiveAlgorithm_formalCorrect', 'FormalCorrect.pad',
                   'formalAdmissibleExponent_of_rankAtMost', 'formalOmega_le_exactRankExponent',
                   'mixedJet_mul', 'program_mixedJet_rankAtMost',
                   'matrix_rankAtMost_of_formalCorrect', 'exactRankExponent_le_formalOmega'],
    'Providers': ['formalOmega_eq_exactRankExponent', 'formalOmega_eq_algebraicClosure'],
    'Square': ['scalar_descent_bound', 'certificate_weakDuality', 'convolution_row_certificate',
               'convolutionYield_pos', 'convolutionYield_cube_lower', 'convolutionYield_gt_half',
               'tendsto_log_square_ratio', 'le_nine_fourths_of_finite_certificate_bounds',
               'degenerates_of_restriction', 'Degenerates.cyclic',
               'middleConvolution_isomorphic', 'convolution_boundary_isomorphic',
               'formalCorrect_implies_correct', 'formalOmega_eq_exactRankExponent',
               'formalOmega_eq_algebraicClosure', 'scalar_descent',
               'tripling_middle_isomorphism', 'convolution_boundary_isomorphism',
               'convolution_neighbor_degeneration', 'convolution_tripling_degeneration',
               'asymptotic_cancellation', 'value_matrix_factor', 'general_extraction',
               'shared_leg_value_inequality', 'identities_to_exponent', 'finite_convolution_bound',
               'formalOmega_le_nine_quarters', 'formal_matrix_multiplication_cost_le',
               'omega_le_nine_quarters'],
}.items():
    for theorem in theorems:
        code += f'#print axioms BlockIdentities.{namespace}.{theorem}\n'

work = root / 'work'
work.mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile(mode='w', suffix='.lean', dir=work, delete=False) as f:
    f.write(code)
    probe = Path(f.name)
try:
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    result = subprocess.run(['lake', 'env', 'lean', str(probe)], cwd=root, env=env,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (root / 'review/statement-elaboration.txt').write_text(result.stdout)
    if 'sorryAx' in result.stdout:
        raise SystemExit('Unexpected proof hole in audited dependency closure')
    for used in re.findall(r'depends on axioms: \[([^]]*)\]', result.stdout):
        unexpected = {a.strip() for a in used.split(',')} - {'propext', 'Classical.choice', 'Quot.sound', ''}
        if unexpected:
            raise SystemExit('Unexpected axioms: ' + ', '.join(unexpected))
    print(result.stdout if result.returncode else f'Elaborated {len(names)} headers: ' + ', '.join(names))
    raise SystemExit(result.returncode)
finally:
    probe.unlink()
