module

public import RiemannMasullo.AppB_AnalyticNT.Sec7a
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Norm-ordered Euler products on the 1-line

Masullo, §B.7.2, pp. 648–653. The logarithmic series is grouped by prime-power
norm. The Euler products and the prime sum use a strict cutoff on prime norm.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Equation (B.7.2.2), p. 649. The function `g_n` uses the
oscillatory pole term with its constant term subtracted.
Deviation: At the removable singularity we use the limiting value `log n`
for positive `n`. -/
def heckePrimePowerTailOscillation (t₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  if s = ⟨1, t₀⟩ then (Real.log n : ℂ)
  else ((n : ℂ) ^ ((⟨1, t₀⟩ : ℂ) - s) - 1) / ((⟨1, t₀⟩ : ℂ) - s)

/-- Paper: Equations (B.7.2.2) and (B.7.2.12), pp. 649–650.
For positive `n`, the oscillatory term tends to `log n` at the pole ordinate.
Deviation: The printed proof gives the opposite sign for `g_n / log n`. -/
theorem heckePrimePowerTailOscillation_tendsto_at_pole
    (t₀ : ℝ) {n : ℕ} (hn : 0 < n) :
    Tendsto (heckePrimePowerTailOscillation t₀ n)
      (𝓝[≠] (⟨1, t₀⟩ : ℂ)) (𝓝 (Real.log n : ℂ)) := by
  set w : ℂ := ⟨1, t₀⟩
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hd := (Complex.hasStrictDerivAt_const_cpow (x := (n : ℂ)) (y := 0)
    (Or.inl hn0)).hasDerivAt
  rw [Complex.cpow_zero, one_mul] at hd
  have hs := hasDerivAt_iff_tendsto_slope.mp hd
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n), Complex.ofReal_natCast]
  rw [hlog] at hs
  have hmap : Tendsto (fun s : ℂ ↦ w - s) (𝓝[≠] w) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℂ ↦ w - s) (𝓝 w) (𝓝 (w - w)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.mpr (Ne.symm hs)
  refine (hs.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ ⟨1, t₀⟩ := hs
  simp only [Function.comp_apply, slope, sub_zero, Complex.cpow_zero, vsub_eq_sub, smul_eq_mul,
    heckePrimePowerTailOscillation, hs', ↓reduceIte]
  ring

/-- Paper: Remark B.7.2.2, p. 649. Index `k` represents the positive
exponent `k + 1`. The ideal character is zero on ramified prime powers. -/
def heckePrimePowerLogTerm (χ : U[F]) (v : V[F]) (k : ℕ) (s : ℂ) : ℂ :=
  heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) /
    ((k + 1 : ℕ) * ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ s)

/-- Paper: Equation (B.7.2.15), p. 651. The exponent-one logarithmic term is
the ordinary prime term of the Hecke Dirichlet series. -/
theorem heckePrimePowerLogTerm_zero (χ : U[F]) (v : V[F]) (s : ℂ) :
    heckePrimePowerLogTerm χ v 0 s =
      heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal / (v.asIdeal.absNorm : ℂ) ^ s := by
  simp [heckePrimePowerLogTerm]

/-- Paper: Remark B.7.2.2 and Equation (B.7.2.4), p. 649. Dividing the
norm-grouped von Mangoldt coefficient by the logarithm of the norm gives
the coefficient of the logarithmic Euler series. The norms zero and one
have coefficient zero. -/
def heckePrimePowerLogCoefficient (χ : U[F]) (n : ℕ) : ℂ :=
  heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n / (Real.log n : ℂ)

/-- Paper: Remark B.7.2.2, p. 649. The coefficient at `n` sums
`χ(𝔭^m) / m` over the positive prime powers of norm exactly `n`. -/
theorem heckePrimePowerLogCoefficient_eq_sum (χ : U[F]) (n : ℕ) :
    heckePrimePowerLogCoefficient χ n =
      ∑ᶠ a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckeIdealValue (ideleClassNormTwist χ 0) (a.val.1.asIdeal ^ (a.val.2 + 1)) /
          ((a.val.2 + 1 : ℕ) : ℂ) := by
  classical
  let P (a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}) :
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ⟨a.val.1.asIdeal ^ (a.val.2 + 1), pow_ne_zero _ a.val.1.ne_bot, by
      rw [map_pow]; exact a.property⟩
  have hP : Function.Injective P := by
    rintro ⟨⟨v, k⟩, hk⟩ ⟨⟨w, j⟩, hj⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Subtype.ext (Prod.ext rfl
      (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq)))
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset
      (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n} ⊆ {I | I.absNorm = n} from
        fun I hI ↦ hI.2)).to_subtype
  have : Finite {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := Finite.of_injective P hP
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := Fintype.ofFinite _
  have : Fintype {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := Fintype.ofFinite _
  rw [heckePrimePowerLogCoefficient, heckeLogDerivCoefficient, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.sum_div]
  symm
  refine Fintype.sum_of_injective P hP _ _ (fun I hI ↦ ?_) (fun a ↦ ?_)
  · have h : ¬ ∃ v : V[F], ∃ k : ℕ, 0 < k ∧ I.val = v.asIdeal ^ k := by
      rintro ⟨v, _ | k, hk, he⟩
      · exact hk.false
      · refine hI ⟨⟨(v, k), ?_⟩, Subtype.ext he.symm⟩
        have h2 := I.property.2
        rw [he, map_pow] at h2
        exact h2
    simp [heckeIdealVonMangoldt, idealVonMangoldt, h]
  · obtain ⟨⟨v, k⟩, hk⟩ := a
    have hN : (1 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hlog : Complex.log (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos hN).ne'
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [P, heckeIdealVonMangoldt, idealVonMangoldt_prime_pow v k.succ_pos]
    rw [← hk, Nat.cast_pow, Real.log_pow]
    push_cast
    field_simp

/-- Paper: Remark B.7.2.2, p. 649. This is the Dirichlet term for each
integer norm, with the terms below the cutoff replaced by zero. -/
def heckePrimePowerLogTailTerm (χ : U[F]) (x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if x ≤ (n : ℝ) then LSeries.term (heckePrimePowerLogCoefficient χ) s n else 0

/-- Paper: Remark B.7.2.2, p. 649. At a positive integer norm equal to the
cutoff, the tail includes the full Dirichlet term for that norm. -/
theorem heckePrimePowerLogTailTerm_at_cutoff (χ : U[F]) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    heckePrimePowerLogTailTerm χ n s n =
      heckePrimePowerLogCoefficient χ n / (n : ℂ) ^ s := by
  simp [heckePrimePowerLogTailTerm, LSeries.term_of_ne_zero hn.ne']

/-- Paper: Remark B.7.2.2, p. 649. The logarithmic tail sums the norm-grouped
terms in increasing order of integer norm, starting at the first norm at least `x`. -/
def heckePrimePowerLogTail (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  tsum (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ)

/-- Paper: Remark B.7.2.2, p. 649, and the absolute convergence on p. 653.
To the right of one the same tail is the absolute sum over prime powers
whose norms are at least the cutoff. -/
theorem heckePrimePowerLogTail_hasSum_of_one_lt_re (χ : U[F]) (x : ℝ) (s : halfPlane) :
    HasSum (fun a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)} ↦
      heckePrimePowerLogTerm χ a.val.1 a.val.2 s) (heckePrimePowerLogTail χ x s) := by
  sorry

local notation "invLog(" n ")" => ((Real.log ((n : ℕ) : ℝ) : ℂ)⁻¹)

/-- Paper: Equations (B.7.2.1) and (B.7.2.19), pp. 649 and 652. These
are the oscillatory summands weighted by the difference of reciprocal
logarithms at successive norms at or above the cutoff. -/
def heckePrimePowerTailOscillationTerm (t₀ x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if x ≤ (n : ℝ) then
    heckePrimePowerTailOscillation t₀ (n - 1) s * (invLog(n) - invLog(n - 1))
  else 0

/-- Paper: Equations (B.7.2.1) and (B.7.2.19), pp. 649 and 652. The weighted
oscillatory terms are summable on the 1-line away from the pole.
Deviation: The cutoff is greater than two so the reciprocal logarithms
in the tail have nonzero denominators. -/
theorem summable_heckePrimePowerTailOscillationTerm (t₀ x t : ℝ) (hx : 2 < x) (ht : t ≠ t₀) :
    Summable (heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩) := by
  sorry

/-- Paper: Theorem B.7.2.1(1), pp. 649–651. For a pure norm character,
the grouped logarithmic tail converges uniformly on compact sets away from
the pole. The oscillatory terms give the displayed main term and the continuous
error is bounded uniformly by `2 ε / log x`.
Deviation: The formula holds for all sufficiently large real cutoffs. Partial summation
uses only integer endpoints, including `M - 1`. The threshold exceeds two. -/
theorem heckePrimePowerLogTail_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ ∀ x ≥ x₀,
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
        (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K ∧
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        heckePrimePowerLogTail χ x ⟨1, t⟩ =
          -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) +
            error t - ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n := by
  sorry

/-- Paper: Theorem B.7.2.1(2), pp. 649–651. For a character nontrivial on
the norm-one subgroup the grouped tail converges uniformly on each compact set
on the 1-line. Its limit is continuous and uniformly smaller than `2 ε / log x`.
Deviation: The compact set of ordinates refers to `1 + iK`, as in the
equation and the convergence clause. -/
theorem heckePrimePowerLogTail_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x ≥ x₀,
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
        (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K ∧
      ContinuousOn (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) K ∧
      ∀ t ∈ K, ‖heckePrimePowerLogTail χ x ⟨1, t⟩‖ < 2 * ε / Real.log x := by
  sorry

-- TODO(paper-gap): The proof on p. 651 uses a uniform bound for the Perron error
-- on the entire 1-line. The compact-set estimates of §B.7.1 suffice here.

/-- Paper: Equation (B.7.2.15), p. 651. This finite set contains the
finite places whose prime ideals have norm strictly below `x`. -/
def heckePrimesBelow (F : Type*) [Field F] [NumberField F] (x : ℝ) : Finset (V[F]) :=
  (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 F)
    (⌈x⌉₊ - 1)).toFinset

/-- Paper: Equation (B.7.2.15), p. 651. The strict cutoff excludes primes of
norm exactly `x`, including when `x` is an integer. -/
theorem heckePrimesBelow_mem_iff (v : V[F]) (x : ℝ) :
    v ∈ heckePrimesBelow F x ↔ (v.asIdeal.absNorm : ℝ) < x := by
  have h1 : 1 < v.asIdeal.absNorm := HeightOneSpectrum.one_lt_absNorm v
  rw [heckePrimesBelow, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ← Nat.lt_ceil]
  omega

/-- Paper: Corollary B.7.2.3, p. 651. For a character nontrivial on the
norm-one subgroup, the prime sum converges locally uniformly on the 1-line. -/
theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop := by
  sorry

/-- Paper: Corollary B.7.2.3, p. 651. For a pure norm character, the
prime sum converges locally uniformly on the 1-line away from the pole. -/
theorem heckePrimeSum_tendstoLocallyUniformlyOn_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop ({t₀}ᶜ : Set ℝ) := by
  sorry

/-- Paper: Equation (B.7.2.17), p. 652. The reciprocal partial Euler product
uses the finite Euler factors with prime norm strictly below the cutoff.
Deviation: The strict cutoff extends the definition to real `x`. -/
def reciprocalHeckeEulerProductBelow (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  reciprocalPartialHeckeEulerProduct χ (heckePrimesBelow F x) s

/-- Paper: Equation (B.7.2.17), p. 652. Each prime below the strict cutoff
contributes its linear Euler polynomial, with coefficient zero at ramified primes. -/
theorem reciprocalHeckeEulerProductBelow_eq_prod (χ : U[F]) (x : ℝ) (s : ℂ) :
    reciprocalHeckeEulerProductBelow χ x s =
      ∏ v ∈ heckePrimesBelow F x,
        (1 - heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal *
          (v.asIdeal.absNorm : ℂ) ^ (-s)) := by
  classical
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have h := heckeIdealValue_prime_pow (ideleClassNormTwist χ 0) v one_pos
  rw [pow_one] at h
  rw [h, finiteHeckeEulerFactor]
  split_ifs <;> simp

/-- Paper: Equation (B.7.2.19), p. 652. This is the oscillatory part of
the logarithmic tail for a pure norm character, evaluated at ordinate `t`.
Deviation: The first term uses `t₀ - t` in its denominator, as required by
Equation (B.7.2.1). Its use is on the complement of the pole ordinate. -/
def heckeEulerProductOscillation (t₀ x t : ℝ) : ℂ :=
  -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) -
    ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n

/-- Paper: Equation (B.7.2.19), p. 652. On compact sets away from the pole,
the endpoint term minus the finite correction sums converges uniformly to `G_x`.
Deviation: The cutoff is greater than two so `log (M - 1)` is nonzero. -/
theorem heckeEulerProductOscillation_tendstoUniformlyOn (t₀ x : ℝ) (hx : 2 < x)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    TendstoUniformlyOn (fun N : ℕ ↦ fun t : ℝ ↦
      -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) -
        ∑ n ∈ Finset.range N, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n)
      (heckeEulerProductOscillation t₀ x) atTop K := by
  sorry

/-- Paper: Theorem B.7.2.4(1), Equation (B.7.2.19), p. 652. The oscillatory
part is real analytic away from the pole ordinate.
Deviation: The cutoff is greater than two so `log (M - 1)` is nonzero. -/
theorem heckeEulerProductOscillation_analyticOnNhd (t₀ x : ℝ) (hx : 2 < x) :
    AnalyticOnNhd ℝ (heckeEulerProductOscillation t₀ x) ({t₀}ᶜ : Set ℝ) := by
  sorry

/-- Paper: Equation (B.7.2.19), p. 652. The oscillatory part is uniformly
`O(1 / log x)` on any compact set of ordinates away from the pole. -/
theorem heckeEulerProductOscillation_bound (t₀ : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ t ∈ K,
      ‖heckeEulerProductOscillation t₀ x t‖ ≤ C / Real.log x := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction `H_x` is minus
the logarithmic terms whose primes lie below the cutoff but whose powers
have reached or exceeded it. Such powers have exponent at least two. -/
def heckeEulerProductLogCorrection (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  -(∑' a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
      heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s)

/-- Paper: Theorem B.7.2.4(1), p. 652. The positive majorant over prime powers
of exponent at least two is summable for an abscissa greater than one half. -/
theorem summable_heckeHigherPrimePowerWeights (F : Type*) [Field F] [NumberField F]
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun a : V[F] × ℕ ↦
      (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ σ))) := by
  have hσ0 : 0 < σ := by linarith
  have hu : Summable fun v : V[F] ↦ (v.asIdeal.absNorm : ℝ) ^ (-(2 * σ)) :=
    (summable_absNorm_rpow F (by linarith)).comp_injective
      (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hr0 : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable fun k : ℕ ↦ ((2 : ℝ) ^ (-σ)) ^ k := summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_)
    (hu.mul_of_nonneg hg (fun v ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun k ↦ pow_nonneg hr0 k))
  obtain ⟨v, k⟩ := a
  dsimp only
  have hN : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hN0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have hpow : ((v.asIdeal.absNorm ^ (k + 2) : ℕ) : ℝ) ^ σ =
      (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_natCast (_ ^ σ),
      ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  rw [hpow]
  have hA : 0 < (v.asIdeal.absNorm : ℝ) ^ (2 * σ) := Real.rpow_pos_of_pos hN0 _
  have hB : 0 < ((2 : ℝ) ^ σ) ^ k := pow_pos (Real.rpow_pos_of_pos (by norm_num) _) k
  have hle : ((2 : ℝ) ^ σ) ^ k ≤ ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_le_rpow (by norm_num) hN hσ0.le) k
  have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 2)
  calc 1 / (((k + 2 : ℕ) : ℝ) *
        ((v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k))
      ≤ 1 / ((v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ σ) ^ k) := by
        apply one_div_le_one_div_of_le (mul_pos hA hB)
        calc (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ σ) ^ k
            ≤ (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k :=
              mul_le_mul_of_nonneg_left hle hA.le
          _ ≤ _ := le_mul_of_one_le_left (by positivity) h1
    _ = (v.asIdeal.absNorm : ℝ) ^ (-(2 * σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
        rw [Real.rpow_neg hN0.le, Real.rpow_neg (by norm_num), inv_pow, one_div, mul_inv]

/-- Paper: Theorem B.7.2.4(1), p. 652. The series defining the correction
converges absolutely and uniformly on half-planes strictly to the right of one half.
Its sum is the negative of `H_x`. -/
theorem heckeEulerProductLogCorrection_hasSumUniformlyOn (χ : U[F]) (x : ℝ)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSumUniformlyOn
      (fun (a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
        x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}) s ↦
        heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s)
      (fun s ↦ -heckeEulerProductLogCorrection χ x s) {s : ℂ | σ ≤ s.re} := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction has norm at most
the tail of the positive majorant with prime-power norm at least `x`.
Deviation: The absolute majorant is evaluated at the real part of `s`. -/
theorem heckeEulerProductLogCorrection_norm_le (χ : U[F]) (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re) :
    ‖heckeEulerProductLogCorrection χ x s‖ ≤
      ∑' a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
        (1 : ℝ) / ((a.val.2 + 2 : ℕ) *
          (((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) ^ s.re)) := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction tends to zero
uniformly on the whole 1-line. -/
theorem heckeEulerProductLogCorrection_tendstoUniformly (χ : U[F]) :
    TendstoUniformly (fun x : ℝ ↦ fun t : ℝ ↦ heckeEulerProductLogCorrection χ x ⟨1, t⟩)
      (fun _ ↦ 0) atTop := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. Off the pole, multiplying the
reciprocal partial product by the continued finite L-function gives the
exponential of the oscillation, the cutoff correction and a small continuous error.
Deviation: Uses the sign-corrected oscillation from Equation (B.7.2.19).
The cutoff threshold is greater than two. Real cutoffs have the same strict
norm rule as integer cutoffs. -/
theorem reciprocalHeckeEulerProductBelow_mul_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ ∀ x ≥ x₀,
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
          Complex.exp (error t + heckeEulerProductOscillation t₀ x t +
            heckeEulerProductLogCorrection χ x ⟨1, t⟩) := by
  sorry

/-- Paper: Theorem B.7.2.4(1), Equation (B.7.2.20), p. 652. The product
with the finite L-function tends uniformly to one on compact sets away from the pole. -/
theorem reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_normTwist
    (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    TendstoUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩)
      (fun _ ↦ 1) atTop K := by
  sorry

/-- Paper: Theorem B.7.2.4(2), Equation (B.7.2.21), p. 652. For a
character nontrivial on the norm-one subgroup the product with the finite
L-function has an exponential comparison on every compact set of ordinates.
Deviation: Uses `+ H_x` from the definition of the correction, in agreement
with (B.7.2.18). Real cutoffs have the same strict norm rule as integer cutoffs. -/
theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x ≥ x₀,
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
          Complex.exp (error t + heckeEulerProductLogCorrection χ x ⟨1, t⟩) := by
  sorry

/-- Paper: Theorem B.7.2.4(2), Equation (B.7.2.22), p. 652. For a
character nontrivial on the norm-one subgroup the product with the finite
L-function tends uniformly to one on every compact set of ordinates. -/
theorem reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_of_nontrivial_on_normOne
    (χ : U[F]) (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩)
      (fun _ ↦ 1) atTop K := by
  sorry

/-- Paper: Equation (B.7.2.23), p. 653. At a regular nonzero point of the
continued L-function on or to the right of the 1-line, the norm-ordered
logarithmic tail and its correction give the reciprocal product comparison.
Deviation: Uses `+ H_x` and exponentiates to avoid selecting a logarithm branch.
The convergence of the ordered sum is explicit. -/
theorem reciprocalHeckeEulerProductBelow_mul_eq_exp_logTail (χ : U[F]) {x : ℝ} (hx : 1 < x)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : ℂ) (hs : 1 ≤ s.re) (hregular : meromorphicOrderAt L s = 0) :
    Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) ∧
      reciprocalHeckeEulerProductBelow χ x s * L s =
        Complex.exp (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
  sorry

/-- Paper: Equation (B.7.2.23), p. 653. The logarithmic tail restricted to
primes of norm at least `x`, grouped by prime-power norm, is the full
prime-power tail plus the cutoff correction.
Deviation: Adds `H_x`, which already carries the minus sign. -/
theorem heckePrimePowerLogTail_add_correction (χ : U[F]) (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re)
    (hsum : Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ)) :
    HasSum (fun n : ℕ ↦
      ∑ᶠ a : {a : V[F] × ℕ // x ≤ (a.1.asIdeal.absNorm : ℝ) ∧
        a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckePrimePowerLogTerm χ a.val.1 a.val.2 s)
      (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s)
      (SummationFilter.conditional ℕ) := by
  sorry

/-- Paper: Corollary B.7.2.5, Equation (B.7.2.24), p. 653. For a character
nontrivial on the norm-one subgroup, the prime-norm-ordered Euler product
converges locally uniformly to the continued finite L-function on the 1-line. -/
theorem heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne
    (χ : U[F]) (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦ ∏ v ∈ heckePrimesBelow F x, finiteHeckeEulerFactor χ v ⟨1, t⟩)
      (fun t : ℝ ↦ L ⟨1, t⟩) atTop := by
  sorry

/-- Paper: Corollary B.7.2.5, Equation (B.7.2.24), p. 653. For a pure
norm character, the prime-norm-ordered Euler product converges locally uniformly
to the continued finite L-function off the pole ordinate. -/
theorem heckeEulerProductBelow_tendstoLocallyUniformlyOn_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ ∏ v ∈ heckePrimesBelow F x, finiteHeckeEulerFactor χ v ⟨1, t⟩)
      (fun t : ℝ ↦ L ⟨1, t⟩) atTop ({t₀}ᶜ : Set ℝ) := by
  sorry

/-- The finite Euler factor of a norm twist of the trivial character at `s` is the
reciprocal of `1 - N(v)^(-(s + a))`. -/
private theorem reciprocalHeckeEulerProductBelow_at_pole_eq_prod_factor (χ : U[F]) (a : ℂ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) a) (v : V[F]) (s : ℂ) :
    finiteHeckeEulerFactor χ v s = (1 - (v.asIdeal.absNorm : ℂ) ^ (-(s + a)))⁻¹ := by
  classical
  have hval (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) a).restrict v u =
        (‖(u : v.adicCompletion F)‖ : ℂ) ^ a := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change 1 * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : NNReal) :
      ℝ) : ℂ) ^ a = _
    rw [one_mul, ideleClassNorm_ofAdicCompletion]
    rfl
  have hu : (ideleClassNormTwist (1 : U[F]) a).IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro x
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist (1 : U[F]) a).restrict v u = 1
    rw [hval u, show ‖(u : v.adicCompletion F)‖ = 1 from ?_, Complex.ofReal_one, Complex.one_cpow]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show u ∈ (v.adicCompletionIntegers F).units from ⟨x.val.property, x.inv.property⟩)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hnorm : ‖(u : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v _ hπ
  have hN : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  rw [finiteHeckeEulerFactor, hχ, ite_eq_left hu, hu.localValue_eq u hπ, hval, hnorm,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) a,
    ← Complex.cpow_neg, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hN, neg_add, add_comm (-a)]

/-- Paper: Remark B.7.2.6, Equation (B.7.2.25), p. 653. At the pole
ordinate the reciprocal product for a pure norm character equals the untwisted
Mertens product. -/
theorem reciprocalHeckeEulerProductBelow_at_pole_eq_prod (χ : U[F]) (t₀ x : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    reciprocalHeckeEulerProductBelow χ x ⟨1, t₀⟩ =
      ∏ v ∈ heckePrimesBelow F x, (1 - (v.asIdeal.absNorm : ℂ)⁻¹) := by
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have h1 : -((⟨1, t₀⟩ : ℂ) + -Complex.I * t₀) = -1 := by
    apply Complex.ext <;> simp
  rw [reciprocalHeckeEulerProductBelow_at_pole_eq_prod_factor χ _ hχ, inv_inv, h1, Complex.cpow_neg_one]

/-- Paper: Remark B.7.2.6, Equation (B.7.2.25), p. 653. Multiplying
the Mertens product at the pole ordinate by the logarithm of the cutoff gives
a limit of `exp (-γ)` divided by the norm-one class volume. -/
theorem reciprocalHeckeEulerProductBelow_mertens (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    Tendsto (fun x : ℝ ↦ (Real.log x : ℂ) * reciprocalHeckeEulerProductBelow χ x ⟨1, t₀⟩)
      atTop (𝓝 ((Real.exp (-Real.eulerMascheroniConstant) /
        (normOneIdeleClassTamagawaMeasure F univ).toReal : ℝ) : ℂ)) := by
  sorry

/-- Paper: Remark B.7.2.7, p. 653. For a pure norm character the reciprocal
partial products tend locally uniformly on the 1-line to the reciprocal of the
continued finite L-function. Its reciprocal takes the removable value zero at the pole.
Deviation: Local uniform convergence holds across the pole ordinate as well (R27). -/
theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformly (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩)
      (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) atTop := by
  sorry

end RiemannMasullo
