#!/usr/bin/env python3
"""Check the standard-axiom closure of the new finite/value proof frontier."""
from pathlib import Path
import os, re, subprocess, tempfile
root = Path(__file__).resolve().parents[1]
modules = [
    'BlockIdentities.Tensor.RectangularFlattening',
    'BlockIdentities.Tensor.MatrixShapeNonzero',
    'BlockIdentities.Tensor.NonzeroSum',
    'BlockIdentities.Providers.GeneralExtraction',
    'BlockIdentities.Tensor.SeparatorDegeneration',
    'BlockIdentities.Tensor.ValuePowers',
    'BlockIdentities.Tensor.ValueSymmetries',
    'BlockIdentities.Tensor.ValueSupermultiplicativity',
    'BlockIdentities.Tensor.ValueCopiesLower',
    'BlockIdentities.Tensor.ValueMatrices',
    'BlockIdentities.Tensor.ValueBorderRank',
    'BlockIdentities.Tensor.ConvolutionRankBound',
    'BlockIdentities.Tensor.SharedEntropyInequality',
    'BlockIdentities.Tensor.ConvolutionSharedIdentities',
    'BlockIdentities.Tensor.ConvolutionTerminal',
    'BlockIdentities.Square.ConvolutionPotentialBound',
    'BlockIdentities.Square.ExponentCriterionNumerics',
    'BlockIdentities.Tensor.ConvolutionValueRows',
    'BlockIdentities.Square.RankPowerComparison',
]
exports = [
    'Square.matrix_rankAtMost_entry_counts',
    'Square.nonzero_matrixShape', 'Square.MatrixShape.nonzeroTensor',
    'Square.nonzero_finiteTensor_sum', 'Square.NonzeroTensor.sum',
    'Providers.general_extraction',
    'Square.extraction_finite_value_bound',
    'Square.value_power_nat', 'Square.value_symmetrize', 'Square.value_permute',
    'Square.valueAtOmega_supermultiplicative', 'Square.mul_value_le_value_copies',
    'Square.valueAtOmega_mono_of_asymptoticallyRestricts',
    'Square.cyclic_cube_supplies_two', 'Square.MatrixRate.absorb_copies',
    'Square.matrixRate_of_fixed_extraction', 'Square.MatrixRate.divide_matrix_of_lt',
    'Square.asymptoticallyRestricts_of_eventually_classes',
    'Square.Degenerates.identityMinor_card_le',
    'Square.coefficient_isRestriction_directSum', 'Square.weightPartDegeneration',
    'Square.separator_degeneration',
    'Square.SharedLegIdentity.extraction_conversion',
    'Square.SharedLegIdentity.entropy_inequality',
    'Square.valueAtOmega_square', 'Square.normalizedValueAtOmega_terminal',
    'Square.Degenerates.matrix_rpow_exactRankExponent_le',
    'Square.MatrixRate.diagonal_rpow_le',
    'Square.valueAtOmega_le_of_borderRankAtMost',
    'Square.normalizedValueAtOmega_le_of_borderRankAtMost',
    'Square.convolution_borderRankAtMost',
    'Square.sharedFirstPairIdentity', 'Square.sharedFirstThreeIdentity',
    'Square.convolutionNeighborIdentity', 'Square.convolutionTriplingIdentity',
    'Square.convolution_two_one_terminal_isomorphic',
    'Square.normalizedValue_convolution_two_one',
    'Square.exponent_le_of_certificate_values',
    'Square.convolutionPotential_diagonal_lower',
    'Square.convolutionNormalizedValue_neighbor',
    'Square.convolutionNormalizedValue_tripling',
    'Square.convolutionNormalizedValue_diagonal_upper',
    'Square.convolution_normalized_diagonal_lower',
    'Square.exponent_le_of_rank_power_bound',
]
code = 'module\n' + ''.join('public import '+m+'\n' for m in modules)
code += ''.join('#print axioms BlockIdentities.'+e+'\n' for e in exports)
(root/'work').mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=root/'work', delete=False) as f:
    f.write(code)
    probe=Path(f.name)
try:
    result=subprocess.run(['lake','env','lean',str(probe)],cwd=root,
        env=dict(os.environ,LEAN_NUM_THREADS='1'),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
finally:
    probe.unlink()
(root/'review/helper-axioms.txt').write_text(result.stdout)
if result.returncode:
    print(result.stdout)
    raise SystemExit(result.returncode)
if 'sorryAx' in result.stdout:
    raise SystemExit('Unexpected proof hole in helper closure')
for used in re.findall(r'depends on axioms: \[([^]]*)\]',result.stdout):
    bad={a.strip() for a in used.split(',')}-{'propext','Classical.choice','Quot.sound',''}
    if bad:
        raise SystemExit('Unexpected axioms: '+', '.join(sorted(bad)))
print(f'Helper axiom closure passed: {len(exports)} exports, standard axioms only.')
