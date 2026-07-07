import RamanujanTau.Basic
import RamanujanTau.SmallValues
import RamanujanTau.Multiplicativity
import RamanujanTau.HeckeRecurrence
import RamanujanTau.HeckeTheory
import RamanujanTau.HeckeEigenform
import RamanujanTau.HeckeOperator
import RamanujanTau.HeckeConstruction
import RamanujanTau.HeckeReps
import RamanujanTau.OctonionBridge
import RamanujanTau.E8Eisenstein
import RamanujanTau.EllipticHecke
import RamanujanTau.Deligne
import RamanujanTau.Lehmer
import RamanujanTau.EulerFactor
import RamanujanTau.HeckePowers
import RamanujanTau.Gegenbauer
import RamanujanTau.Congruences
import RamanujanTau.Congruences.Sigma
import RamanujanTau.Congruences.Mod2
import RamanujanTau.Congruences.Mod3
import RamanujanTau.Congruences.Mod5
import RamanujanTau.Congruences.Mod7
import RamanujanTau.Congruences.Mod23
import RamanujanTau.MathlibBridge
-- Bridge to Mathlib's modular discriminant: leading q-expansion coefficients (coeff 0 = 0, coeff 1 = 1)
import RamanujanTau.DiscriminantBridge
-- τ(n) ≡ σ₁₁(n) mod 691: the M₁₂ relation E₄³ = E₁₂ + (432000/691)·Δ, 691·[qⁿ]E₄³ = 65520σ₁₁ + 432000τ(n)
import RamanujanTau.Mod691
import RamanujanTau.MockTheta5
import RamanujanTau.MockTheta5Series
import RamanujanTau.MockTheta5Lemmas
import RamanujanTau.MockTheta5Defs
import RamanujanTau.MockTheta5Bailey
import RamanujanTau.MockTheta5QBinom
import RamanujanTau.MockTheta5BaileyPair
import RamanujanTau.MockTheta5BaileyLemma
import RamanujanTau.MockTheta5QChu
import RamanujanTau.MockTheta5BaileyChain
import RamanujanTau.MockTheta5BaileyQ
import RamanujanTau.MockTheta5BaileyTier3
import RamanujanTau.MockTheta5JacobiTriple
import RamanujanTau.MockTheta5JacobiBilateral
import RamanujanTau.MockTheta5JacobiFinite
import RamanujanTau.MockTheta5JacobiLimit
import RamanujanTau.MockTheta5JacobiCauchy
import RamanujanTau.MockTheta5JacobiBilateralize
import RamanujanTau.MockTheta5DurfeeRect
import RamanujanTau.MockTheta5DurfeeInf
import RamanujanTau.MockTheta5DurfeeBase
import RamanujanTau.MockTheta5DurfeeQ
import RamanujanTau.MockTheta5JacobiAssembly
import RamanujanTau.MockTheta5CauchySum
import RamanujanTau.MockTheta5ZProj
import RamanujanTau.MockTheta5ZConv
-- The bilateral Jacobi triple product (JTP L8 capstone)
import RamanujanTau.MockTheta5JacobiL8
-- A Gauss/Jacobi theta evaluation (the z=1 corollary)
import RamanujanTau.MockTheta5GaussTheta
-- The alternating Jacobi theta evaluation (the z=-1 corollary)
import RamanujanTau.MockTheta5AltTheta
-- Euler's pentagonal number theorem (statement side; proof = pending substitution build)
import RamanujanTau.MockTheta5Pentagonal
-- Parity decomposition of the theta series (combining the z=±1 evaluations)
import RamanujanTau.MockTheta5ThetaCombination
-- Euler's distinct = odd partition theorem (generating-function form)
import RamanujanTau.MockTheta5EulerDistinctOdd
-- Even/odd factorization of (q;q)_∞ and distinct=odd made manifest
import RamanujanTau.MockTheta5EvenOdd
-- Odd-index pairing (distinct odd parts × odd parts)
import RamanujanTau.MockTheta5OddPairing
-- Distinct even/odd split
import RamanujanTau.MockTheta5DistinctSplit
-- Gauss theta in classical product form (Cauchy/Euler sum=product)
import RamanujanTau.MockTheta5GaussProduct
-- Alternating theta in classical product form
import RamanujanTau.MockTheta5AltProduct
-- Partial-theta representation of the Euler product
import RamanujanTau.MockTheta5EulerPartialTheta
-- Partial-theta representation of (-q^2;q^2)_inf
import RamanujanTau.MockTheta5DistinctEvenTheta
-- The classical (product-form) Jacobi triple product
import RamanujanTau.MockTheta5ClassicalJTP
-- The Bailey-transform limit (Rogers-Ramanujan engine)
import RamanujanTau.MockTheta5BaileyTransform
import RamanujanTau.MockTheta5BaileyQTransform
import RamanujanTau.MockTheta5BaileyQPairA
import RamanujanTau.MockTheta5BaileyQPairB
import RamanujanTau.MockTheta5BaileyRR1
import RamanujanTau.MockTheta5EulerCauchy
import RamanujanTau.MockTheta5LaurentEval
-- Ramanujan's partition congruence p(5n+4) ≡ 0 (mod 5): the arithmetic heart (kernel-clean)
import RamanujanTau.PartitionCongruenceMod5
-- Jacobi's cube identity (q;q)³ = Σ(−1)ᵐ(2m+1)q^{m(m+1)/2}: statement side + rung-2 check
import RamanujanTau.MockTheta5JacobiCube
-- Triangular JTP stone 1: the bilateral theta Σ zⁿ q^{n(n−1)/2} (RHS series of the triangular JTP)
import RamanujanTau.MockTheta5TriangularTheta
-- Triangular JTP stone 2: one-sided ∏(1+z qⁱ), projected base-q Cauchy identity zProj_triProdQInf
import RamanujanTau.MockTheta5TriangularProd
-- Triangular JTP stone 2b: shifted one-sided ∏_{i≥1}(1+z qⁱ), projected Cauchy q^{C(k+1,2)}/(q;q)_k
import RamanujanTau.MockTheta5TriangularProd2
-- Triangular JTP stone 3 (part A): the (1+z) factorization triProdQInf = (1+z)·triProdQ1Inf
import RamanujanTau.MockTheta5TriangularJTP
-- Triangular JTP stone 3C stage 1: the Cauchy sum objects TZ, TZ1inv (for the z-convolution)
import RamanujanTau.MockTheta5TriangularConv
-- Triangular JTP stone 3 CAPSTONE: the bilateral triangular JTP (q;q)∞·∏(1+zqⁱ)·∏(1+z⁻¹qⁱ) = Σ zⁿq^{n(n−1)/2}
import RamanujanTau.MockTheta5TriangularBilateral
-- Jacobi cube stone 4: d/dz|_{z=−1} functional L; series side L(triTheta) = jacobiCubeSum
import RamanujanTau.MockTheta5JacobiCubeProof
-- Euler pentagonal stone 1: the shifted theta pentTheta = Σ zⁿ q^{(3n²−n)/2} (RHS of the base-q³ JTP)
import RamanujanTau.MockTheta5PentTheta
-- Euler pentagonal engine: E3 dilation (q↦q³) + base-q³ Durfee identity E3(rectInf n)=1/(q³;q³)∞
import RamanujanTau.MockTheta5PentEngine
-- Euler pentagonal: finite shifted base-q³ product ∏(1+z q^{3i+1}) = Σ q^{3C(k,2)+k}[n,k]_{q³} zᵏ
import RamanujanTau.MockTheta5PentProd
-- Euler pentagonal: z-side product ∏_{i≥0}(1+z q^{3i+1}) in z-outer ring + projected Cauchy zProj_pentProdAInf
import RamanujanTau.MockTheta5PentProdZ
-- Euler pentagonal: z⁻¹-side product ∏(1+z q^{3i+2}) + projected Cauchy zProj_pentProdBInf (e(−k) exponent)
import RamanujanTau.MockTheta5PentProdB
-- Euler pentagonal: convolution foundation — sum-form Cauchy objects PZ/PZ1inv + Durfee recognition pent_rectTerm
import RamanujanTau.MockTheta5PentConv
-- Euler pentagonal: theta-side projection zProj_pentTheta = q^{(3n²−n)/2}
import RamanujanTau.MockTheta5PentThetaProj
-- Euler pentagonal CAPSTONE-JTP: (q³;q³)∞·∏(1+zq^{3i+1})·∏(1+z⁻¹q^{3i−1}) = Σ zⁿq^{(3n²−n)/2}
import RamanujanTau.MockTheta5PentBilateral
-- Euler pentagonal: z=−1 evaluation (products→residue-class products; theta→pentSeries)
import RamanujanTau.MockTheta5PentEval
-- Euler pentagonal CAPSTONE: (q;q)∞ = Σ(−1)ⁿq^{n(3n−1)/2} (euler_pentagonal)
import RamanujanTau.MockTheta5EulerPentagonal
-- Fifth-order mock-theta relation R1: infinite statement + engine scoping
import RamanujanTau.MockTheta5R1
-- p(5n+4): char-5 Frobenius (q;q)∞⁵ ≡ (q⁵;q⁵)∞
import RamanujanTau.MockTheta5Frobenius
-- p(5n+4): (q;q)∞⁴ coefficients at exponent ≡4 (mod 5) vanish mod 5 (the arithmetic heart applied)
import RamanujanTau.MockTheta5Qfac4
-- p(5n+4) ≡ 0 (mod 5) CAPSTONE: 5 ∣ coeff(5n+4)(1/(q;q)∞)
import RamanujanTau.MockTheta5PartitionCongruence
-- p(7n+5) ≡ 0 (mod 7): arithmetic heart over ZMod 7
import RamanujanTau.PartitionCongruenceMod7
-- p(7n+5) ≡ 0 (mod 7) CAPSTONE: 7 ∣ coeff(7n+5)(1/(q;q)∞), via (q;q)⁶ = jacobiCubeSum²
import RamanujanTau.MockTheta5PartitionCongruence7
-- Partition-count bridge: coeff n (1/(q;q)∞) = #(Nat.Partition n); congruences for the honest count
import RamanujanTau.MockTheta5PartitionCount
-- Euler's pentagonal recurrence p(n) = Σ(−1)ᵐ(p(n−g₁)+p(n−g₂)) from pentSeries·partitionGF = 1
import RamanujanTau.MockTheta5PentagonalRecurrence
-- Ramanujan's theta functions φ(q)=Σq^{n²}, φ(−q), ψ(q)=(q²;q²)/(q;q²), f(−q)=(q;q)∞ (JTP specializations)
import RamanujanTau.MockTheta5RamanujanTheta
-- Gauss's series form ψ(q) = Σ_{n≥0} q^{n(n+1)/2} (z=1 triangular-JTP double cover, domain-2 cancellation)
import RamanujanTau.MockTheta5PsiSeries
-- Relations among theta functions: φ(q)·φ(−q) = φ(−q²)²
import RamanujanTau.MockTheta5ThetaIdentities
