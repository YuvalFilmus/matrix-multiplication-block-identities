#!/usr/bin/env python3
"""Kernel axiom audit for the explicit ordinary rectangular proof frontier."""
from pathlib import Path
import os, re, subprocess, tempfile
root = Path(__file__).resolve().parents[1]
modules = [
    'Arithmetic.RectangularRecursion', 'Arithmetic.RectangularGrowth',
    'Arithmetic.RectangularProgramRank', 'Arithmetic.ShapeMonotonicity',
    'Arithmetic.ShapeHomogeneity', 'Arithmetic.ShapeRankSeeds',
    'Arithmetic.RectangularRankProduct', 'Arithmetic.ShapeSubadditivity',
    'Arithmetic.ShapeCoordinateBound', 'Arithmetic.ShapeFieldDescent',
    'Arithmetic.ShapeRankLimits', 'Arithmetic.ShapeContinuity',
    'Arithmetic.ShapeLimitScales', 'Arithmetic.ShapeRankAsymptotics',
    'Rectangular.ConeSupport', 'Rectangular.SupportBounds',
    'Rectangular.OrientedGeometry', 'Rectangular.OrientedWeights',
    'Rectangular.OrientedGainBasics', 'Rectangular.MatrixWeightProducts',
    'Rectangular.AsymptoticRankBasics', 'Rectangular.AsymptoticRankGrowth',
    'Rectangular.MatrixSupportRank', 'Rectangular.RankBoundMatrices',
    'Rectangular.AsymptoticRankMonotonicity', 'Rectangular.RankBoundSupply',
    'Rectangular.MatrixShapeClasses', 'Rectangular.AsymptoticRankCopies',
    'Rectangular.OrientedGainOperations', 'Rectangular.OrientedGainRankBound',
    'Rectangular.AngularOffsets', 'Rectangular.ProfileSlopes',
    'Rectangular.WeightedTrigonometry', 'Rectangular.AngularOptimization',
    'Arithmetic.ShapeSymmetry',
    'Rectangular.OrientedGainRankLimit', 'Rectangular.OrientedGainProducts',
    'Rectangular.OrientedGainMatrix', 'Rectangular.OrientedValueOperations',
    'Rectangular.OrientedGainSums', 'Rectangular.OrientedValueSums',
    'Rectangular.OrientedValueCopies', 'Rectangular.OrientedValueCopiesLower',
    'Rectangular.OrientedConvolutionProfiles', 'Rectangular.OrientedProfileReplication',
    'Rectangular.OrientedSharedPermutation', 'Rectangular.OrientedSharedEntropy',
    'Rectangular.ExtractionLogLimits', 'Rectangular.ExtractionFiniteValue',
    'Rectangular.AngularParameters', 'Rectangular.ProfileIncrements',
    'Rectangular.ProfileRescaling', 'Rectangular.ProfileRescalingConcavity',
    'Rectangular.ProfileRescalingBounds', 'Rectangular.ProfileRescalingFamily',
    'Rectangular.ProfileRescalingTripling', 'Rectangular.SupportOptimization',
    'Rectangular.ProfileCompletion', 'Rectangular.ProfileRealExtension',
    'Tensor.OrientedConvolutionIdentities',
    'Tensor.ScalarRank', 'Tensor.OrientedSharedExtraction',
    'Tensor.ConvolutionReplicationBasis', 'Tensor.ConvolutionReplicationMaps',
    'Tensor.ConvolutionReplicationContraction', 'Tensor.ConvolutionReplicationInputs',
    'Tensor.ConvolutionReplicationDegeneration', 'Tensor.ConvolutionReplicationFinite',
]
# Keep the ordinary rectangular closure explicit in the generated audit output;
# include every newly integrated leaf, rather than silently missing unused APIs.
modules = sorted(set(modules) | {
    'Rectangular.' + p.stem
    for p in (root / 'BlockIdentities/Rectangular').glob('*.lean')
    if p.stem != 'Definitions'
})

exports = []
for module in modules:
    source = (root / 'BlockIdentities' / (module.replace('.', '/') + '.lean')).read_text()
    namespace = None
    names = []
    for line in source.splitlines():
        if line.startswith('namespace '):
            assert namespace is None, (module, 'nested namespace unsupported')
            namespace = line.split()[1]
        elif namespace and line == 'end ' + namespace:
            namespace = None
        else:
            match = re.match(r'^(?:@\[[^\n]*\]\s*)?(?:theorem|def) ([^\s({:]+)', line)
            if match:
                assert namespace is not None, (module, line)
                names.append(namespace + '.' + match.group(1))
    assert names, module
    exports += names
code = 'module\n' + ''.join('public import BlockIdentities.' + m + '\n' for m in modules)
code += ''.join('#print axioms ' + e + '\n' for e in exports)
(root / 'work').mkdir(exist_ok=True)
with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=root / 'work', delete=False) as f:
    f.write(code)
    probe = Path(f.name)
try:
    result = subprocess.run(['lake', 'env', 'lean', str(probe)], cwd=root,
        env=dict(os.environ, LEAN_NUM_THREADS='1'), text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
finally:
    probe.unlink()
(root / 'review/rectangular/frontier-axioms.txt').write_text(result.stdout)
if result.returncode:
    print(result.stdout)
    raise SystemExit(result.returncode)
assert 'sorryAx' not in result.stdout, 'Unexpected proof hole in frontier closure'
for used in re.findall(r'depends on axioms: \[([^]]*)\]', result.stdout):
    bad = {a.strip() for a in used.split(',')} - {'propext', 'Classical.choice', 'Quot.sound', ''}
    assert not bad, 'Unexpected axioms: ' + ', '.join(sorted(bad))
assert len(re.findall(r"'[^']+' (?:depends on axioms:|does not depend on any axioms)", result.stdout)) == len(exports)
print(f'Rectangular frontier axiom closure passed: {len(exports)} exports, standard axioms only.')
