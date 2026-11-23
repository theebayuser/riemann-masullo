module

import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2a
import RiemannMasullo.ForMathlib.Analysis.Normed.Field.ProperSpace
import RiemannMasullo.AppB_AnalyticNT.Sec1
public import RiemannMasullo.AppB_AnalyticNT.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec4a
public import RiemannMasullo.Ch03_IdelicZeta.Sec3b
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.ForMathlib.Analysis.Complex.LandauLemma
import RiemannMasullo.ForMathlib.Analysis.Fourier.Log
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.WeightedIntegral
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c
public import RiemannMasullo.AppD_SchwartzBruhat.Sec2a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import all RiemannMasullo.AppB_AnalyticNT.Sec2
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.DigammaIntegral
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.Digamma
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Topology.Algebra.IsOpenUnits
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import RiemannMasullo.External.Grh.Props.HeckeContourReflection

/-!
# Explicit formulas for Hecke L-functions

Masullo, §§B.4.2–B.4.4, pp. 614–626. The Schwartz test on the positive
real line is written in its logarithmic coordinate.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "halfPlane" => (Complex.re ⁻¹' Ioi (1 : ℝ))
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)
local notation "χ₀(" χ ")" => ideleClassNormTwist χ 0
local notation "logMellin" => (fun (f : ℝ → ℂ) ↦ mellin (fun t ↦ f (Real.log t)))
local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)

section MellinExplicitFormula

-- TODO(paper-gap): The unnumbered residue identity on p. 614 reverses the
-- signs in (B.4.2.2). Poles are present only for norm characters and may be shifted.

/-- Helper for `hasSlowGrowthNearPoles_completedHeckeL_logDeriv`: a function analytic at
every point of a closed horizontal segment is differentiable on a thin open strip around it. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_tube {f : ℂ → ℂ} {a b t : ℝ}
    (h : ∀ σ ∈ Icc a b, AnalyticAt ℂ f ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    ∃ δ > (0 : ℝ), DifferentiableOn ℂ f
      (Complex.re ⁻¹' Ioo a b ∩ Complex.im ⁻¹' Ioo (t - δ) (t + δ)) := by
  let K : Set ℂ := (fun σ : ℝ ↦ (σ : ℂ) + (t : ℂ) * Complex.I) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hKt : K ⊆ {z | AnalyticAt ℂ f z} := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact h σ hσ
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open (isOpen_analyticAt ℂ f) hKt
  refine ⟨δ, hδ, fun z hz ↦ ?_⟩
  have hmem : z ∈ Metric.thickening δ K := by
    rw [Metric.mem_thickening_iff]
    refine ⟨(z.re : ℂ) + (t : ℂ) * Complex.I, ⟨z.re, Ioo_subset_Icc_self hz.1, rfl⟩, ?_⟩
    rw [Complex.dist_eq]
    have he : z - ((z.re : ℂ) + (t : ℂ) * Complex.I) = (((z.im - t : ℝ)) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    have := hz.2
    simp only [mem_preimage, mem_Ioo] at this
    constructor <;> linarith
  exact (hsub hmem : AnalyticAt ℂ f z).differentiableAt.differentiableWithinAt

/-- Helper for `hasSlowGrowthNearPoles_completedHeckeL_logDeriv`: good heights near the
integers on both tails, together with the vertical-line clause, give a witness.
The finitely many indices near zero are sent to good heights by a monotone clamp. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_assemble {f : ℂ → ℂ} {a b : ℝ}
    (hab : a < b) (hf : MeromorphicOn f (Complex.re ⁻¹' Ioo a b)) (T : ℤ → ℝ)
    (hT : Monotone T) (A β : ℝ) (hA : 0 < A) (hβ : 0 < β)
    (hgood : ∀ᶠ k : ℤ in comap abs atTop, |T k - k| ≤ 1 ∧
      ∀ σ ∈ Icc a b, AnalyticAt ℂ f ((σ : ℂ) + (T k : ℂ) * Complex.I) ∧
        ‖f ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ ≤ A * |T k| ^ β)
    (hvert : ∃ ε₁ ε₂ : ℝ, 0 < ε₁ ∧ ε₁ < ε₂ ∧ ε₂ < (b - a) / 2 ∧
      ∀ σ ∈ ({a + ε₁, b - ε₂} : Set ℝ),
        Continuous (fun y : ℝ ↦ f ((σ : ℂ) + (y : ℂ) * Complex.I)) ∧
          ∃ γ > (0 : ℝ), (fun y : ℝ ↦ f ((σ : ℂ) + (y : ℂ) * Complex.I)) =O[comap abs atTop]
            (fun y : ℝ ↦ |y| ^ γ)) :
    HasSlowGrowthNearPoles f a b := by
  obtain ⟨N₀, hN₀⟩ := (atTop_basis.comap (abs : ℤ → ℤ)).eventually_iff.mp hgood
  simp only [mem_preimage, mem_Ici, true_and] at hN₀
  set N : ℤ := max N₀ 1 with hNdef
  have hN1 : 1 ≤ N := le_max_right _ _
  have hP : ∀ k : ℤ, N ≤ |k| → _ := fun k hk ↦ hN₀ (le_trans (le_max_left _ _) hk)
  let c : ℤ → ℤ := fun k ↦ if 0 ≤ k then max k N else min k (-(N + 2))
  have hc_abs : ∀ k, N ≤ |c k| := by
    intro k
    simp only [c]
    split_ifs with h
    · rw [abs_of_nonneg (show 0 ≤ max k N by omega)]; omega
    · rw [abs_of_neg (show min k (-(N + 2)) < 0 by omega)]; omega
  have hc_ge : ∀ k, |k| ≤ |c k| := by
    intro k
    simp only [c]
    split_ifs with h
    · rw [abs_of_nonneg h, abs_of_nonneg (show 0 ≤ max k N by omega)]; omega
    · rw [abs_of_neg (show k < 0 by omega),
        abs_of_neg (show min k (-(N + 2)) < 0 by omega)]; omega
  have hc_le : ∀ k, |c k| ≤ max |k| (N + 2) := by
    intro k
    simp only [c]
    split_ifs with h
    · rw [abs_of_nonneg h, abs_of_nonneg (show 0 ≤ max k N by omega)]; omega
    · rw [abs_of_neg (show k < 0 by omega),
        abs_of_neg (show min k (-(N + 2)) < 0 by omega)]; omega
  have hc_mono : Monotone c := by
    intro i j hij
    simp only [c]
    split_ifs <;> omega
  have hc_eq : ∀ k, N + 2 ≤ |k| → c k = k := by
    intro k hk
    simp only [c]
    split_ifs with h
    · rw [abs_of_nonneg h] at hk; omega
    · rw [abs_of_neg (by omega)] at hk; omega
  set T' : ℤ → ℝ := fun k ↦ T (c k) with hT'
  have hnear : ∀ k, |T' k - c k| ≤ 1 := fun k ↦ (hP (c k) (hc_abs k)).1
  have hnear' : ∀ k, (c k : ℝ) - 1 ≤ T' k ∧ T' k ≤ c k + 1 := fun k ↦ by
    have := abs_le.mp (hnear k); constructor <;> linarith [this.1, this.2]
  have hT'mono : Monotone T' := hT.comp hc_mono
  have hpos : ∀ n : ℕ, 0 ≤ T' n := by
    intro n
    have h1 : c n = max (n : ℤ) N := by simp [c]
    have h2 : (N : ℝ) ≤ c n := by rw [h1]; exact_mod_cast le_max_right _ _
    have h3 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith [(hnear' n).1]
  have hneg : ∀ n : ℕ, 1 ≤ n → T' (-(n : ℤ)) ≤ -(N + 1) := by
    intro n hn
    have h1 : c (-(n : ℤ)) = min (-(n : ℤ)) (-(N + 2)) := by
      simp only [c]; rw [ite_eq_right_iff.mpr (by omega)]
    have h2 : (c (-(n : ℤ)) : ℝ) ≤ -(N + 2) := by
      rw [h1]; exact_mod_cast min_le_right _ _
    linarith [(hnear' (-(n : ℤ))).2]
  refine ⟨T', hab, hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hvert⟩
  · -- positive tail
    intro m n hmn
    simp only
    rw [abs_of_nonneg (hpos m), abs_of_nonneg (hpos n)]
    exact hT'mono (by exact_mod_cast hmn)
  · -- negative tail
    intro m n hmn
    simp only
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact le_rfl
      · have h0 : T' (-((0 : ℕ) : ℤ)) ≤ N + 1 := by
          have h1 : c (-((0 : ℕ) : ℤ)) = N := by simp [c]; omega
          have := (hnear' (-((0 : ℕ) : ℤ))).2
          rw [h1] at this; exact this
        have h0' : 0 ≤ T' (-((0 : ℕ) : ℤ)) := by simpa using hpos 0
        have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
        rw [abs_of_nonneg h0', abs_of_neg (show T' (-(n : ℤ)) < 0 by linarith [hneg n hn])]
        linarith [hneg n hn]
    · have hn : 1 ≤ n := le_trans hm hmn
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      rw [abs_of_neg (show T' (-(m : ℤ)) < 0 by linarith [hneg m hm]),
        abs_of_neg (show T' (-(n : ℤ)) < 0 by linarith [hneg n hn])]
      have : T' (-(n : ℤ)) ≤ T' (-(m : ℤ)) := hT'mono (by omega)
      linarith
  · -- divergence
    have hlow : ∀ k : ℤ, |(k : ℝ)| - 1 ≤ |T' k| := fun k ↦ by
      have h1 : |(k : ℝ)| ≤ |(c k : ℝ)| := by
        rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast hc_ge k
      have h3 := abs_sub_abs_le_abs_sub (c k : ℝ) (T' k)
      rw [abs_sub_comm] at h3
      linarith [hnear k]
    have h1 : Tendsto (fun k : ℤ ↦ |(k : ℝ)| - 1) (comap abs atTop) atTop := by
      have h0 := (tendsto_intCast_atTop_atTop (R := ℝ)).comp
        (Filter.tendsto_comap (f := (abs : ℤ → ℤ)) (x := atTop))
      have h2 : Tendsto (fun k : ℤ ↦ |(k : ℝ)|) (comap abs atTop) atTop :=
        h0.congr fun k ↦ by simp
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-1 : ℝ) h2
    exact tendsto_atTop_mono hlow h1
  · refine ⟨1, one_pos, Asymptotics.IsBigO.of_bound 2 ?_⟩
    filter_upwards [(atTop_basis.comap (abs : ℤ → ℤ)).eventually_iff.mpr
      ⟨N + 2, trivial, fun k hk ↦ hk⟩] with k hk
    simp only [mem_preimage, mem_Ici] at hk
    rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    have hck := hc_eq k hk
    have h := hnear k
    rw [hck] at h
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast (by omega : (1 : ℤ) ≤ |k|)
    have h3 := abs_sub_abs_le_abs_sub (T' k) (k : ℝ)
    linarith
  · refine ⟨1 / 2, 1, by norm_num, one_pos, ?_⟩
    filter_upwards [(atTop_basis.comap (abs : ℤ → ℤ)).eventually_iff.mpr
      ⟨N + 2, trivial, fun k hk ↦ hk⟩] with k hk
    simp only [mem_preimage, mem_Ici] at hk
    rw [Real.rpow_one]
    have h := hnear k
    rw [hc_eq k hk] at h
    have hk1 : (2 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast (by omega : (2 : ℤ) ≤ |k|)
    have h3 := abs_sub_abs_le_abs_sub (k : ℝ) (T' k)
    rw [abs_sub_comm] at h3
    linarith
  · intro k
    exact hasSlowGrowthNearPoles_completedHeckeL_logDeriv_tube
      (fun σ hσ ↦ ((hP (c k) (hc_abs k)).2 σ hσ).1)
  · refine ⟨β, A * ((N : ℝ) + 3) ^ β, hβ, by positivity, fun k hk σ hσ ↦ ?_⟩
    have h := ((hP (c k) (hc_abs k)).2 σ (Ioo_subset_Icc_self hσ)).2
    refine h.trans ?_
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
    have hcl : |(c k : ℝ)| ≤ max |(k : ℝ)| ((N : ℝ) + 2) := by
      rw [← Int.cast_abs, ← Int.cast_abs]; exact_mod_cast hc_le k
    have h3 := abs_sub_abs_le_abs_sub (T' k) (c k : ℝ)
    have hT1 : |T' k| ≤ ((N : ℝ) + 3) * |(k : ℝ)| := by
      have hN : (0 : ℝ) ≤ N := by exact_mod_cast (by omega : (0 : ℤ) ≤ N)
      have : max |(k : ℝ)| ((N : ℝ) + 2) ≤ ((N : ℝ) + 2) * |(k : ℝ)| := by
        apply max_le <;> nlinarith
      nlinarith [hnear k]
    rw [mul_assoc, ← Real.mul_rpow (by positivity) (abs_nonneg _)]
    gcongr

section HorizontalHeights

open Metric

/-- A unit interval contains a point separated from the imaginary parts of a finite set. -/
private theorem completedHeckeL_height_avoid (S : Finset ℂ) (k W : ℝ)
    (hW : (S.card : ℝ) ≤ W) :
    ∃ t ∈ Icc (k - 1 / 2) (k + 1 / 2), ∀ ρ ∈ S, 1 / (4 * (W + 1)) ≤ |t - ρ.im| := by
  let δ := 1 / (4 * (W + 1))
  let J (ρ : ℂ) := Ioo (ρ.im - δ) (ρ.im + δ)
  let K := Icc (k - 1 / 2) (k + 1 / 2)
  have hW₀ : 0 ≤ W := (Nat.cast_nonneg _).trans hW
  have hδ : 0 < δ := by positivity
  by_contra! h
  have hK : K ⊆ ⋃ ρ ∈ S, J ρ := by
    intro t ht
    obtain ⟨ρ, hρ, ha⟩ := h t ht
    refine mem_iUnion₂.mpr ⟨ρ, hρ, ?_⟩
    have he := abs_lt.mp ha
    change ρ.im - δ < t ∧ t < ρ.im + δ
    constructor <;> linarith
  have hvol (ρ : ℂ) : volume (J ρ) = ENNReal.ofReal (2 * δ) := by
    change volume (Ioo (ρ.im - δ) (ρ.im + δ)) = _
    rw [Real.volume_Ioo]
    congr 1
    ring
  have h₁ := (measure_mono (μ := volume) hK).trans (measure_biUnion_finset_le S J)
  have hKvol : volume K = ENNReal.ofReal 1 := by
    change volume (Icc (k - 1 / 2) (k + 1 / 2)) = _
    rw [Real.volume_Icc]
    congr 1
    ring
  rw [hKvol, Finset.sum_congr rfl (fun ρ _ ↦ hvol ρ), Finset.sum_const,
    ← ENNReal.ofReal_nsmul, nsmul_eq_mul] at h₁
  have h₂ : 1 ≤ (S.card : ℝ) * (2 * δ) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h₁
  have h₃ := h₂.trans (mul_le_mul_of_nonneg_right hW (by positivity : 0 ≤ 2 * δ))
  dsimp [δ] at h₃
  have h₄ : W * (2 * (1 / (4 * (W + 1)))) = W / (2 * (W + 1)) := by
    have hp : W + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [h₄, le_div_iff₀ (by positivity)] at h₃
  linarith

/-- At the nearby heights, polynomial control of the normalized logarithmic maximum
on discs gives a uniform bound across the closed strip. -/
private theorem completedHeckeL_height_local {f : ℂ → ℂ} (k B : ℝ)
    (hB : 1 < B)
    (hf : AnalyticOnNhd ℂ f (closedBall ⟨2, k⟩ 6)) (hc : f ⟨2, k⟩ ≠ 0)
    (hbound : ∀ u ∈ closedBall ⟨2, k⟩ 6, ‖f u / f ⟨2, k⟩‖ ≤ B) :
    ∃ t ∈ Icc (k - 1 / 2) (k + 1 / 2),
      ∀ σ ∈ Icc (-1 : ℝ) 2,
        AnalyticAt ℂ (logDeriv f) ⟨σ, t⟩ ∧
          ‖logDeriv f ⟨σ, t⟩‖ ≤
            landauConstant 4 5 (11 / 2) 6 * Real.log B +
              4 * (Real.log B / Real.log (6 / 5)) * (Real.log B / Real.log (6 / 5) + 1) := by
  classical
  let c : ℂ := ⟨2, k⟩
  have hf' : AnalyticOnNhd ℂ f (closedBall c 5) :=
    hf.mono (closedBall_subset_closedBall (by norm_num))
  let S := (finite_zeros_closedBall (by norm_num) hf' hc).toFinset
  have hS (ρ : ℂ) : ρ ∈ S ↔ ρ ∈ closedBall c 5 ∧ f ρ = 0 := by simp [S]
  have hnonzero {ρ : ℂ} (hρ : f ρ ≠ 0) : analyticOrderNatAt f ρ = 0 := by
    simp [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hρ)]
  have hpositive (ρ : ℂ) (hρ : ρ ∈ S) : 1 ≤ analyticOrderNatAt f ρ := by
    obtain ⟨hb, hz⟩ := (hS ρ).mp hρ
    have ht := hf'.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c 5).isPreconnected
      (x := c) (mem_closedBall_self (by norm_num)) hb (by
        have he : analyticOrderAt f c = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hc)
        simp [he])
    have hzero : analyticOrderAt f ρ ≠ 0 := by
      rw [ne_eq, analyticOrderAt_eq_zero]
      exact not_or_intro (not_not_intro (hf' ρ hb)) (not_not_intro hz)
    have he := ENat.natCast_toNat ht
    change ((analyticOrderNatAt f ρ : ℕ) : ℕ∞) = analyticOrderAt f ρ at he
    by_contra! hn
    have hn' : analyticOrderNatAt f ρ = 0 := by omega
    rw [hn'] at he
    exact hzero (by simpa using he.symm)
  have hsum {M : Type} [AddCommMonoid M] (φ : ℂ → M)
      (hφ : ∀ ρ, analyticOrderNatAt f ρ = 0 → φ ρ = 0) :
      ∑ᶠ ρ ∈ closedBall c 5, φ ρ = ∑ ρ ∈ S, φ ρ := by
    rw [← finsum_mem_coe_finset]
    refine finsum_mem_inter_support_eq' _ _ _ fun ρ hρ ↦ ?_
    have hn : f ρ = 0 := by
      by_contra h
      exact hρ (hφ ρ (hnonzero h))
    simp [hS, hn]
  let W := Real.log B / Real.log (6 / 5)
  have hW : (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ)) ≤ W := by
    rw [← hsum (fun ρ ↦ (analyticOrderNatAt f ρ : ℝ)) (fun _ ho ↦ by simp [ho])]
    exact landau_sum_analyticOrderNatAt_le (by norm_num) (by norm_num) hf hc hbound
  have hcard : (S.card : ℝ) ≤ W := by
    refine le_trans ?_ hW
    calc
      (S.card : ℝ) = ∑ _ρ ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun ρ hρ ↦ by exact_mod_cast hpositive ρ hρ)
  obtain ⟨t, ht, havoid⟩ := completedHeckeL_height_avoid S k W hcard
  let δ := 1 / (4 * (W + 1))
  have hW₀ : 0 ≤ W := (Nat.cast_nonneg _).trans hcard
  have hδ : 0 < δ := by positivity
  refine ⟨t, ht, fun σ hσ ↦ ?_⟩
  let z : ℂ := ⟨σ, t⟩
  have hz : z ∈ closedBall c 4 := by
    rw [mem_closedBall, Complex.dist_eq]
    have hzr : z - c = ((σ - 2 : ℝ) : ℂ) + ((t - k : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [z, c, Complex.sub_re, Complex.sub_im]
    rw [hzr]
    refine norm_add_le _ _ |>.trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonpos (sub_nonpos.mpr hσ.2)]
    have ht' : |t - k| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    linarith [hσ.1]
  have hz' : z ∈ closedBall c 5 := closedBall_subset_closedBall (by norm_num) hz
  have hsep (ρ : ℂ) (hρ : ρ ∈ S) : δ ≤ ‖z - ρ‖ :=
    (havoid ρ hρ).trans (by simpa [z] using Complex.abs_im_le_norm (z - ρ))
  have hfz : f z ≠ 0 := by
    intro he
    have h := hsep z ((hS z).mpr ⟨hz', he⟩)
    exact (not_le_of_gt hδ) (by simpa using h)
  refine ⟨(hf' z hz').deriv.div (hf' z hz') hfz, ?_⟩
  have hld := landau_norm_logDeriv_sub_le hB (by norm_num : (0 : ℝ) < 4)
    (by norm_num : (4 : ℝ) < 5) (by norm_num : (5 : ℝ) < 11 / 2)
    (by norm_num : (11 / 2 : ℝ) < 6) hf hc hbound hz hfz
  let P (ρ : ℂ) := (analyticOrderNatAt f ρ : ℂ) / (z - ρ)
  rw [show (∑ᶠ ρ ∈ closedBall c 5, ((analyticOrderNatAt f ρ : ℂ) / (z - ρ))) =
      ∑ ρ ∈ S, P ρ from hsum P (fun ρ hρ ↦ by simp [P, hρ])] at hld
  have hP : ‖∑ ρ ∈ S, P ρ‖ ≤ 4 * W * (W + 1) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ) / δ := by
        refine Finset.sum_le_sum fun ρ hρ ↦ ?_
        change ‖(analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ _
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hsep ρ hρ)
      _ = (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ)) / δ := (Finset.sum_div _ _ _).symm
      _ ≤ W / δ := div_le_div_of_nonneg_right hW hδ.le
      _ = _ := by rw [show δ = (4 * (W + 1))⁻¹ by simp [δ], div_inv_eq_mul]; ring
  have h := norm_add_le (logDeriv f z - ∑ ρ ∈ S, P ρ) (∑ ρ ∈ S, P ρ)
  rw [sub_add_cancel] at h
  exact h.trans (add_le_add hld hP)

/-- A normalized disc bound at large heights gives polynomial estimates at a
monotone sequence within half a unit of each integer. -/
private theorem completedHeckeL_heights_of_discs {f : ℂ → ℂ} (C : ℝ) (hC : 0 < C)
    (h : ∀ᶠ k : ℝ in comap abs atTop,
      AnalyticOnNhd ℂ f (closedBall ⟨2, k⟩ 6) ∧ f ⟨2, k⟩ ≠ 0 ∧
        ∀ u ∈ closedBall (⟨2, k⟩ : ℂ) 6, ‖f u / f ⟨2, k⟩‖ ≤ Real.exp (C * (1 + |k|))) :
    ∃ T : ℤ → ℝ, Monotone T ∧ ∃ A β : ℝ, 0 < A ∧ 0 < β ∧
      ∀ᶠ k : ℤ in comap abs atTop, |T k - k| ≤ 1 ∧
        ∀ σ ∈ Icc (-1 : ℝ) 2,
          AnalyticAt ℂ (logDeriv f) ((σ : ℂ) + (T k : ℂ) * Complex.I) ∧
            ‖logDeriv f ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ ≤ A * |T k| ^ β := by
  classical
  let D := landauConstant 4 5 (11 / 2) 6
  let d := Real.log (6 / 5)
  have hD : 0 < D := landauConstant_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hd : 0 < d := Real.log_pos (by norm_num)
  let Q := 3 * C / d
  have hQ : 0 < Q := by positivity
  let A := D * (3 * C) + 4 * Q * (Q + 1)
  have hA : 0 < A := by positivity
  let Good (k : ℤ) (t : ℝ) :=
    t ∈ Icc ((k : ℝ) - 1 / 2) (k + 1 / 2) ∧ ∀ σ ∈ Icc (-1 : ℝ) 2,
      AnalyticAt ℂ (logDeriv f) (⟨σ, t⟩ : ℂ) ∧ ‖logDeriv f ⟨σ, t⟩‖ ≤ A * |t| ^ 2
  have htend : Tendsto (fun k : ℤ ↦ (k : ℝ)) (comap abs atTop) (comap abs atTop) := by
    apply tendsto_comap_iff.mpr
    exact ((tendsto_intCast_atTop_atTop (R := ℝ)).comp
      (Filter.tendsto_comap (f := (abs : ℤ → ℤ)) (x := atTop))).congr fun k ↦ by
        exact Int.cast_abs
  have hGood : ∀ᶠ k : ℤ in comap abs atTop, ∃ t, Good k t := by
    filter_upwards [htend.eventually h,
      htend.eventually (tendsto_comap.eventually (eventually_ge_atTop (2 : ℝ)))] with k hk hk₂
    change 2 ≤ |(k : ℝ)| at hk₂
    let B := Real.exp (C * (1 + |(k : ℝ)|))
    have hB : 1 < B := Real.one_lt_exp_iff.mpr (by positivity)
    obtain ⟨t, ht, hlocal⟩ := completedHeckeL_height_local (k : ℝ) B hB hk.1 hk.2.1 hk.2.2
    have hnear : |t - (k : ℝ)| ≤ 1 / 2 :=
      abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hheight := (abs_sub_abs_le_abs_sub (k : ℝ) t).trans (by simpa [abs_sub_comm] using hnear)
    have ht₁ : 1 ≤ |t| := by linarith
    have hlog : Real.log B ≤ (3 * C) * |t| := by
      rw [show Real.log B = C * (1 + |(k : ℝ)|) by exact Real.log_exp _]
      exact (by nlinarith : C * (1 + |(k : ℝ)|) ≤ C * (3 * |t|)).trans_eq (by ring)
    have hdiv : Real.log B / d ≤ Q * |t| := by
      exact (div_le_div_of_nonneg_right hlog hd.le).trans_eq (by dsimp [Q]; ring)
    have hdiv₁ : Real.log B / d + 1 ≤ (Q + 1) * |t| := by nlinarith
    have hdiv₀ : 0 ≤ Real.log B / d := div_nonneg (Real.log_nonneg hB.le) hd.le
    refine ⟨t, ht, fun σ hσ ↦ ⟨(hlocal σ hσ).1, (hlocal σ hσ).2.trans ?_⟩⟩
    change D * Real.log B + 4 * (Real.log B / d) * (Real.log B / d + 1) ≤ A * |t| ^ 2
    calc
      _ ≤ D * ((3 * C) * |t|) + 4 * (Q * |t|) * ((Q + 1) * |t|) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hlog hD.le)
          (mul_le_mul (mul_le_mul_of_nonneg_left hdiv (by norm_num)) hdiv₁ (by positivity) (by positivity))
      _ ≤ _ := by
        have ht₂ := mul_le_mul_of_nonneg_left ht₁ (show 0 ≤ D * (3 * C) * |t| by positivity)
        dsimp [A]
        nlinarith
  let T (k : ℤ) := if h : ∃ t, Good k t then h.choose else (k : ℝ)
  have hNear (k : ℤ) : T k ∈ Icc ((k : ℝ) - 1 / 2) (k + 1 / 2) := by
    dsimp only [T]
    split_ifs with h
    · exact h.choose_spec.1
    · constructor <;> linarith
  have hMono : Monotone T := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hij
    · rfl
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (show i + 1 ≤ j by omega)
    linarith [(hNear i).2, (hNear j).1]
  refine ⟨T, hMono, A, 2, hA, by norm_num, ?_⟩
  filter_upwards [hGood] with k hk
  have hTk : Good k (T k) := by
    dsimp only [T]
    rw [dite_eq_left hk]
    exact hk.choose_spec
  refine ⟨abs_le.mpr ⟨by linarith [hTk.1.1], by linarith [hTk.1.2]⟩, fun σ hσ ↦ ?_⟩
  have he : (σ : ℂ) + (T k : ℂ) * Complex.I = ⟨σ, T k⟩ := by
    apply Complex.ext <;> simp
  rw [he, Real.rpow_two]
  exact hTk.2 σ hσ

/-- The two possible poles are below a fixed absolute height. -/
private theorem completedHeckeL_height_analytic (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) :
    ∀ᶠ t : ℝ in comap abs atTop, AnalyticOnNhd ℂ L (closedBall ⟨2, t⟩ 6) := by
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨p, hp, -⟩ := completedHeckeL_continuation_simplePoles χ L hL hAgree hχ
    filter_upwards [tendsto_comap.eventually (eventually_ge_atTop (|p| + 7))] with t ht
    intro u hu
    have hdist : |u.im - t| ≤ 6 := by
      have h := Complex.abs_im_le_norm (u - (⟨2, t⟩ : ℂ))
      rw [Complex.sub_im] at h
      exact h.trans (by simpa [mem_closedBall, Complex.dist_eq] using hu)
    have hdiff' := abs_sub_abs_le_abs_sub t u.im
    rw [abs_sub_comm t u.im] at hdiff'
    have ht' : |p| + 7 ≤ |t| := ht
    have hne : u.im ≠ p := by
      intro hu
      rw [hu] at hdist hdiff'
      linarith
    apply hp.2.2.2 u
    have h₁ : u ≠ Complex.I * (p : ℂ) := fun h ↦ hne (by
      simpa [Complex.mul_im] using congrArg Complex.im h)
    have h₂ : u ≠ 1 + Complex.I * (p : ℂ) := fun h ↦ hne (by
      simpa [Complex.add_im, Complex.mul_im] using congrArg Complex.im h)
    simp [h₁, h₂]
  · have h := completedHeckeL_continuation_entire χ L hL hAgree hχ
    exact Eventually.of_forall fun _ u _ ↦ h.differentiableOn.analyticOnNhd isOpen_univ u (mem_univ u)

/-- Paper: §B.4.2.1, p. 614 (citing Lang, Ch. XVII, Prop. 2.3, Cor. 2.5, Prop. 2.7).
The logarithmic derivative of the completed function is polynomially bounded on
horizontal segments of the strip at a monotone sequence of heights, one within distance
one of each large integer, and is analytic along those segments.
Deviation: The heights are the horizontal part of Definition B.3.1.1, stated on both tails
at once; the segments are closed and run from `1 - a` to `a`. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_heights (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (ha : 1 < a) (haMax : a ≤ 2) :
    ∃ T : ℤ → ℝ, Monotone T ∧ ∃ A β : ℝ, 0 < A ∧ 0 < β ∧
      ∀ᶠ k : ℤ in comap abs atTop, |T k - k| ≤ 1 ∧
        ∀ σ ∈ Icc (1 - a) a,
          AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (T k : ℂ) * Complex.I) ∧
            ‖logDeriv L ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ ≤ A * |T k| ^ β := by
  obtain ⟨C, hC, hDisc⟩ :=
    completedHeckeL_continuation_disc_bound χ L hL hAgree 2 6 (by norm_num) (by norm_num)
  obtain ⟨T, hT, A, β, hA, hβ, hGood⟩ := completedHeckeL_heights_of_discs C hC
    ((completedHeckeL_height_analytic χ L hL hAgree).and hDisc)
  refine ⟨T, hT, A, β, hA, hβ, hGood.mono fun k hk ↦ ⟨hk.1, fun σ hσ ↦ hk.2 σ ?_⟩⟩
  have hleft : 1 - a ∈ Icc (-1 : ℝ) 0 := ⟨by linarith only [haMax], sub_nonpos.mpr ha.le⟩
  exact ⟨hleft.1.trans hσ.1, hσ.2.trans haMax⟩

end HorizontalHeights

local notation "finiteSeries(" χ ")" => LSeries (χ₀(χ)).LFunction

private theorem completedHeckeL_logDeriv_abscissa (χ : U[F]) {z : ℂ} (hz : 1 < z.re) :
    LSeries.abscissaOfAbsConv (χ₀(χ)).LFunction < (z.re : EReal) := by
  obtain ⟨r, hr, hrz⟩ := exists_between hz
  exact (finiteHeckeL_seriesSummable χ ⟨(r : ℂ), by simpa using hr⟩).abscissaOfAbsConv_le.trans_lt
    (by exact_mod_cast hrz)

/-- A positive lower bound from the Euler product, uniform on a line to the right of one. -/
private theorem completedHeckeL_logDeriv_finite_lower (χ : U[F]) (σ : ℝ) (hσ : 1 < σ)
    (z : ℂ) (hz : z.re = σ) :
    Real.exp (-(∑' v : Primes(F), q(v) ^ (-σ))) ≤ ‖finiteSeries(χ) z‖ := by
  have hz' : 1 < z.re := hz ▸ hσ
  let E (v : Primes(F)) := finiteHeckeEulerFactor χ v z
  let r (v : Primes(F)) := q(v) ^ (-σ)
  have hp : HasProd E (finiteSeries(χ) z) := finiteHeckeL_hasProd χ ⟨z, hz'⟩
  have hsum : Summable r :=
    (summable_absNorm_rpow F hσ).comp_injective (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hnonneg (v : Primes(F)) : 0 ≤ r v := by positivity
  have hlocal (v : Primes(F)) : Real.exp (-r v) ≤ ‖E v‖ := by
    have hv : (1 : ℝ) < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    unfold E finiteHeckeEulerFactor
    split_ifs
    · let u := (χ₀(χ)).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-z)
      change Real.exp (-r v) ≤ ‖(1 - u)⁻¹‖
      have hu : ‖u‖ = r v := by
        dsimp only [u, r]
        rw [norm_mul, norm_ideleClassNormTwist_zero_localValue, one_mul, ← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hv), Complex.neg_re, hz]
      have hu' : ‖u‖ < 1 := by
        rw [hu]
        exact Real.rpow_lt_one_of_one_lt_of_neg hv (by linarith)
      have hne : 1 - u ≠ 0 := fun h ↦ hu'.ne (by rw [← sub_eq_zero.mp h, norm_one])
      rw [norm_inv, Real.exp_neg]
      apply (inv_le_inv₀ (Real.exp_pos _) (norm_pos_iff.mpr hne)).2
      calc
        ‖1 - u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_sub_le _ _
        _ ≤ Real.exp (r v) := by rw [norm_one, hu, add_comm]; exact Real.add_one_le_exp _
    · rw [norm_one]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnonneg v))
  apply ge_of_tendsto' hp.norm
  intro T
  rw [norm_prod]
  calc
    _ ≤ Real.exp (∑ v ∈ T, -r v) := by
      rw [Finset.sum_neg_distrib]
      exact Real.exp_le_exp.mpr (neg_le_neg (hsum.sum_le_tsum T fun v _ ↦ hnonneg v))
    _ = ∏ v ∈ T, Real.exp (-r v) := Real.exp_sum _ _
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) (fun v _ ↦ hlocal v)

private theorem completedHeckeL_logDeriv_finite_bound (χ : U[F]) (σ : ℝ) (hσ : 1 < σ) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re = σ → ‖logDeriv (finiteSeries(χ)) z‖ ≤ C := by
  let c := (χ₀(χ)).LFunction
  let a := ∑' n, ‖LSeries.term (LSeries.logMul c) (σ : ℂ) n‖
  let b := Real.exp (∑' v : Primes(F), q(v) ^ (-σ))
  have ha : 0 ≤ a := tsum_nonneg (fun _ ↦ norm_nonneg _)
  have hb : 0 < b := Real.exp_pos _
  have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
  have hsσ : Summable (fun n ↦ ‖LSeries.term (LSeries.logMul c) (σ : ℂ) n‖) :=
    (LSeriesSummable_logMul_of_lt_re (completedHeckeL_logDeriv_abscissa χ hσ')).norm
  refine ⟨a * b, mul_nonneg ha hb.le, fun z hz ↦ ?_⟩
  have hz' : 1 < z.re := hz ▸ hσ
  have hc := completedHeckeL_logDeriv_abscissa χ hz'
  have hs : Summable (fun n ↦ ‖LSeries.term (LSeries.logMul c) z n‖) :=
    (LSeriesSummable_logMul_of_lt_re hc).norm
  have hA : ‖LSeries (LSeries.logMul c) z‖ ≤ a :=
    (norm_tsum_le_tsum_norm hs).trans
      (hs.tsum_le_tsum (LSeries.norm_term_le_of_re_le_re (LSeries.logMul c) (by simpa using hz.ge)) hsσ)
  have hLower := completedHeckeL_logDeriv_finite_lower χ σ hσ z hz
  have hB : ‖(finiteSeries(χ) z)⁻¹‖ ≤ b := by
    rw [norm_inv]
    calc
      _ ≤ (Real.exp (-(∑' v : Primes(F), q(v) ^ (-σ))))⁻¹ :=
        (inv_le_inv₀ ((Real.exp_pos _).trans_le hLower) (Real.exp_pos _)).2 hLower
      _ = b := by rw [Real.exp_neg, inv_inv]
  rw [logDeriv_apply, LSeries_deriv hc, div_eq_mul_inv, norm_mul, norm_neg]
  exact mul_le_mul hA hB (norm_nonneg _) ha

/-- The logarithmic derivative of the shifted real gamma factor on its right half-plane. -/
private theorem realHeckeArchimedean_mellinLogDeriv_gamma (b s : ℂ) (h : 0 < ((s + b) / 2).re) :
    logDeriv (fun w ↦ Complex.Gammaℝ (w + b)) s =
      (Complex.digamma ((s + b) / 2) - (Real.log Real.pi : ℂ)) / 2 := by
  let z (w : ℂ) := (w + b) / 2
  let E (w : ℂ) := Complex.exp (-(Real.log Real.pi : ℂ) * z w)
  have hf : (fun w ↦ Complex.Gammaℝ (w + b)) = fun w ↦ E w * Complex.Gamma (z w) := by
    funext w
    rw [Complex.Gammaℝ_def, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
      ← Complex.ofReal_log Real.pi_pos.le]
    simp only [E, z, neg_div, neg_mul, mul_neg]
  have hz : HasDerivAt z (1 / 2) s := ((hasDerivAt_id s).add_const b).div_const 2
  have hE := (hz.const_mul (-(Real.log Real.pi : ℂ))).cexp
  have hG := (Complex.hasDerivAt_Gamma_of_re_pos h).differentiableAt
  rw [hf, logDeriv_fun_mul (f := E) (g := fun w ↦ Complex.Gamma (z w)) s
    (Complex.exp_ne_zero _) (Complex.Gamma_ne_zero_of_re_pos h) hE.differentiableAt
    (hG.comp s hz.differentiableAt), hz.logDeriv_Gamma (fun m he ↦ by
      have := congrArg Complex.re he
      simp [z] at this h
      linarith [show (0 : ℝ) ≤ m by positivity])]
  rw [logDeriv_apply, show deriv E s = E s * (-(Real.log Real.pi : ℂ) * (1 / 2)) from hE.deriv,
    mul_div_cancel_left₀ _ (show E s ≠ 0 from Complex.exp_ne_zero _)]
  dsimp [z]
  ring

/-- The Gauss kernel bound gives a digamma bound linear in the absolute height. -/
private theorem completedHeckeL_logDeriv_digamma_bound (u : ℝ) (hu : 0 < u) :
    ∃ C ≥ (0 : ℝ), ∀ v : ℝ,
      ‖Complex.digamma ((u : ℂ) + (v : ℂ) * Complex.I)‖ ≤ C * (1 + |v|) := by
  let m := min 1 u
  have hm : 0 < m := lt_min one_pos hu
  let K (x : ℝ) := (1 + x) * Real.exp (-m * x)
  have hExp := integrableOn_exp_mul_Ioi (neg_neg_of_pos hm) 0
  have hxExp : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-m * x)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) one_pos hm)
  have hK : IntegrableOn K (Ioi 0) := by
    simpa only [K, Pi.add_def, add_mul, one_mul] using hExp.add hxExp
  let A := ∫ x in Ioi (0 : ℝ), K x
  have ha : 0 ≤ A := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    exact mul_nonneg (by linarith [show 0 < x from hx]) (Real.exp_pos _).le
  let D := ‖Complex.digamma 1‖
  have hd : 0 ≤ D := norm_nonneg _
  refine ⟨(1 + |1 - u|) * A + D, by positivity, fun v ↦ ?_⟩
  let w : ℂ := (u : ℂ) + (v : ℂ) * Complex.I
  have hw : 0 < (w / (1 : ℂ)).re := by simpa [w] using hu
  have hG := (integral_gaussDigammaDifferenceKernel (d := 1) (w := w) one_pos (by simpa using hw)).2
  simp only [Complex.ofReal_one, div_one] at hG
  have hB : ‖∫ x in Ioi (0 : ℝ), gaussDigammaDifferenceKernel 1 w x‖ ≤ (|1 - u| + |v|) * A := by
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hK.const_mul _) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with x hx
    simpa only [K, m, div_one] using
      (norm_gaussDigammaDifferenceKernel_le (d := 1) (u := u) (v := v) one_pos (show 0 < x from hx))
  change ‖Complex.digamma w‖ ≤ _
  calc
    _ ≤ ‖Complex.digamma w - Complex.digamma 1‖ + D :=
      (norm_le_insert' (Complex.digamma w) (Complex.digamma 1)).trans_eq (add_comm _ _)
    _ ≤ (|1 - u| + |v|) * A + D := add_le_add (hG ▸ hB) (le_refl D)
    _ ≤ _ := by
      have h₁ := mul_nonneg (mul_nonneg (abs_nonneg (1 - u)) ha) (abs_nonneg v)
      have h₂ := mul_nonneg hd (abs_nonneg v)
      nlinarith

private theorem completedHeckeL_logDeriv_GammaR_regular (b s : ℂ) (h : 0 < (s + b).re) :
    Complex.Gammaℝ (s + b) ≠ 0 ∧ DifferentiableAt ℂ (fun z ↦ Complex.Gammaℝ (z + b)) s := by
  have hn := Complex.Gammaℝ_ne_zero_of_re_pos h
  have hD := Complex.differentiable_Gammaℝ_inv.differentiableAt (x := s + b)
  have hI : DifferentiableAt ℂ (fun z ↦ ((Complex.Gammaℝ z)⁻¹)⁻¹) (s + b) :=
    hD.inv (inv_ne_zero hn)
  exact ⟨hn, (show DifferentiableAt ℂ Complex.Gammaℝ (s + b) from
    by simpa only [inv_inv] using hI).comp s (differentiableAt_id.add_const b)⟩

private theorem completedHeckeL_logDeriv_GammaR_bound (σ : ℝ) (b : ℂ) (h : 0 < σ + b.re) :
    ∃ C ≥ (0 : ℝ), ∀ y : ℝ,
      ‖logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        C * (1 + |y|) := by
  let u := (σ + b.re) / 2
  obtain ⟨A, hA, hD⟩ := completedHeckeL_logDeriv_digamma_bound u (half_pos h)
  let C := A * (1 + |b.im|) + ‖(Real.log Real.pi : ℂ)‖
  have hC : 0 ≤ C := by positivity
  refine ⟨C, hC, fun y ↦ ?_⟩
  let s := (σ : ℂ) + (y : ℂ) * Complex.I
  have hs : (s + b) / 2 = (u : ℂ) + (((y + b.im) / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [s, u, Complex.div_ofNat_re, Complex.div_ofNat_im]
  have hpos : 0 < ((s + b) / 2).re := by
    rw [hs]
    simpa using (show 0 < u from half_pos h)
  have hv : |(y + b.im) / 2| ≤ |y| + |b.im| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_add_le y b.im, abs_nonneg (y + b.im)]
  change ‖logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) s‖ ≤ _
  rw [realHeckeArchimedean_mellinLogDeriv_gamma b s hpos, norm_div, hs, Complex.norm_ofNat]
  apply (div_le_self (norm_nonneg _) (by norm_num : (1 : ℝ) ≤ 2)).trans
  refine (norm_sub_le _ _).trans ?_
  have hD' := (hD ((y + b.im) / 2)).trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hv) hA)
  refine (add_le_add hD' (le_refl _)).trans ?_
  unfold C
  have h₁ := mul_nonneg (mul_nonneg hA (abs_nonneg b.im)) (abs_nonneg y)
  have h₂ := mul_nonneg (norm_nonneg (Real.log Real.pi : ℂ)) (abs_nonneg y)
  nlinarith
private theorem completedHeckeL_logDeriv_GammaC_split (b s : ℂ) (h : 0 < (s + b).re) :
    (Complex.Gammaℂ (s + b) / 2 ≠ 0 ∧
      DifferentiableAt ℂ (fun z ↦ Complex.Gammaℂ (z + b) / 2) s) ∧
    logDeriv (fun z ↦ Complex.Gammaℂ (z + b) / 2) s =
      logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) s +
      logDeriv (fun z ↦ Complex.Gammaℝ (z + (b + 1))) s := by
  have h₁ : 0 < (s + (b + 1)).re := by
    rw [← add_assoc, Complex.add_re, Complex.one_re]
    positivity
  have hR := completedHeckeL_logDeriv_GammaR_regular b s h
  have hR₁ := completedHeckeL_logDeriv_GammaR_regular (b + 1) s h₁
  have he : (fun z ↦ Complex.Gammaℂ (z + b) / 2) =
      fun z ↦ (Complex.Gammaℝ (z + b) * Complex.Gammaℝ (z + (b + 1))) * (2 : ℂ)⁻¹ := by
    funext z
    rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one, div_eq_mul_inv, add_assoc]
  rw [show Complex.Gammaℂ (s + b) / 2 = _ from congrFun he s, he]
  refine ⟨⟨mul_ne_zero (mul_ne_zero hR.1 hR₁.1) (inv_ne_zero two_ne_zero),
    (hR.2.mul hR₁.2).mul_const _⟩, ?_⟩
  rw [logDeriv_mul_const _ _ (inv_ne_zero two_ne_zero)]
  exact logDeriv_fun_mul _ hR.1 hR₁.1 hR.2 hR₁.2

private theorem completedHeckeL_logDeriv_gammaFactor_bound (χ : U[F]) (σ : ℝ) (hσ : 0 < σ) :
    ∃ C ≥ (0 : ℝ), ∀ y : ℝ,
      ‖logDeriv (heckeGammaFactor χ) ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C * (1 + |y|) := by
  let G (v : InfinitePlace F) (s : ℂ) : ℂ :=
    if hv : v.IsReal then
      let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
    else
      let a := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2
  let s (y : ℝ) : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
  have hh (v : InfinitePlace F) : ∃ C ≥ (0 : ℝ), ∀ y,
      G v (s y) ≠ 0 ∧ DifferentiableAt ℂ (G v) (s y) ∧
        ‖logDeriv (G v) (s y)‖ ≤ C * (1 + |y|) := by
    by_cases hv : v.IsReal
    · let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      let b := a.1 + (a.2.val : ℂ)
      have h0 : 0 ≤ b.re := by
        have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
        change a.1.re = 0 at ha
        simp only [b, Complex.add_re, Complex.natCast_re, ha, zero_add]
        positivity
      have he : G v = fun z ↦ Complex.Gammaℝ (z + b) := by
        funext z
        simp only [G, dite_eq_left hv, b, a, add_assoc]
      obtain ⟨C, hC, hG⟩ := completedHeckeL_logDeriv_GammaR_bound σ b (add_pos_of_pos_of_nonneg hσ h0)
      have hpos (y : ℝ) : 0 < (s y + b).re := by
        simpa [s] using add_pos_of_pos_of_nonneg hσ h0
      refine ⟨C, hC, fun y ↦ ?_⟩
      rw [he]
      have ht := completedHeckeL_logDeriv_GammaR_regular b (s y) (hpos y)
      exact ⟨ht.1, ht.2, hG y⟩
    · let hw := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let a := (complexHeckeCharacter_parameters χ v hw).exists.choose
      let b := a.1 + (a.2.natAbs : ℂ) / 2
      have h0 : 0 ≤ b.re := by
        have ha := (complexHeckeCharacter_parameters χ v hw).exists.choose_spec.1
        change a.1.re = 0 at ha
        simp only [b, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, ha, zero_add]
        positivity
      have he : G v = fun z ↦ Complex.Gammaℂ (z + b) / 2 := by
        funext z
        simp only [G, dite_eq_right hv, b, a, add_assoc]
      obtain ⟨C, hC, hG⟩ := completedHeckeL_logDeriv_GammaR_bound σ b (add_pos_of_pos_of_nonneg hσ h0)
      obtain ⟨D, hD, hG'⟩ := completedHeckeL_logDeriv_GammaR_bound σ (b + 1) (by
        rw [Complex.add_re, Complex.one_re]
        positivity)
      refine ⟨C + D, add_nonneg hC hD, fun y ↦ ?_⟩
      have hpos : 0 < (s y + b).re := by simpa [s] using add_pos_of_pos_of_nonneg hσ h0
      have hs := completedHeckeL_logDeriv_GammaC_split b (s y) hpos
      rw [he]
      refine ⟨hs.1.1, hs.1.2, ?_⟩
      rw [hs.2, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (hG y) (hG' y))
  choose C hC hG using hh
  refine ⟨∑ v, C v, Finset.sum_nonneg fun v _ ↦ hC v, fun y ↦ ?_⟩
  change ‖logDeriv (fun z ↦ ∏ v, G v z) (s y)‖ ≤ _
  rw [logDeriv_fun_prod (fun v _ ↦ (hG v y).1) (fun v _ ↦ (hG v y).2.1), Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ ↦ (hG v y).2.2)

/-- On the right half-plane the continuation agrees with its holomorphic product,
whose two factors are nonzero. -/
private theorem completedHeckeL_logDeriv_right_local (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) {z : ℂ} (hz : 1 < z.re) :
    AnalyticAt ℂ (logDeriv L) z ∧
      logDeriv L z = logDeriv (heckeGammaFactor χ) z + logDeriv (finiteSeries(χ)) z := by
  have hEq : L =ᶠ[𝓝 z] fun w ↦ heckeGammaFactor χ w * finiteSeries(χ) w := by
    have hopen : IsOpen halfPlane := isOpen_Ioi.preimage Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show z ∈ halfPlane from hz)] with w hw
    exact hAgree ⟨w, hw⟩
  have hG₀ := heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz)
  have hF₀ : finiteSeries(χ) z ≠ 0 :=
    norm_pos_iff.mp ((Real.exp_pos _).trans_le
      (completedHeckeL_logDeriv_finite_lower χ z.re hz z rfl))
  have hL₀ : L z ≠ 0 := hEq.eq_of_nhds ▸ mul_ne_zero hG₀ hF₀
  have hNF : MeromorphicNFAt L z := hL (mem_univ z)
  have hA := hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (le_of_eq (hNF.meromorphicOrderAt_eq_zero_iff.mpr hL₀).symm)
  have hG := differentiableAt_heckeGammaFactor_of_re_pos χ (zero_lt_one.trans hz)
  have hF := (LSeries_hasDerivAt (completedHeckeL_logDeriv_abscissa χ hz)).differentiableAt
  refine ⟨hA.deriv.div hA hL₀, ?_⟩
  exact (logDeriv_congr_nhds hEq).eq_of_nhds.trans (logDeriv_fun_mul _ hG₀ hF₀ hG hF)

/-- Paper: §B.4.2.1, p. 614 (citing Lang, Ch. XVII). On a vertical line to the right
of `Re(s) = 1` the logarithmic derivative of the completed function is continuous and
grows at most polynomially in the height.
Deviation: One of the two interior lines of Definition B.3.1.1, for `1 < σ ≤ 2`. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_right (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (σ : ℝ) (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    Continuous (fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) ∧
      ∃ γ > (0 : ℝ), (fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) =O[comap abs atTop]
        (fun y : ℝ ↦ |y| ^ γ) := by
  have hσRange : σ ∈ Ioc (1 : ℝ) 2 := ⟨hσ, hσ2⟩
  let s (y : ℝ) := (σ : ℂ) + (y : ℂ) * Complex.I
  have hs (y : ℝ) : (s y).re = σ := by simp [s]
  have hloc (y : ℝ) := completedHeckeL_logDeriv_right_local χ L hL hAgree
    (show 1 < (s y).re from (hs y).symm ▸ hσ)
  refine ⟨continuous_iff_continuousAt.mpr fun y ↦ (hloc y).1.continuousAt.comp (by fun_prop), ?_⟩
  obtain ⟨C, hC, hG⟩ := completedHeckeL_logDeriv_gammaFactor_bound χ σ (zero_lt_one.trans hσRange.1)
  obtain ⟨D, hD, hF⟩ := completedHeckeL_logDeriv_finite_bound χ σ hσ
  refine ⟨1, one_pos, Asymptotics.IsBigO.of_bound (2 * C + D) ?_⟩
  filter_upwards [(eventually_ge_atTop (1 : ℝ)).comap abs] with y hy
  change ‖logDeriv L (s y)‖ ≤ _
  rw [(hloc y).2, Real.rpow_one, Real.norm_eq_abs, abs_abs]
  refine (norm_add_le _ _).trans ((add_le_add (hG y) (hF (s y) (hs y))).trans ?_)
  nlinarith [mul_nonneg hC (sub_nonneg.mpr hy), mul_nonneg hD (sub_nonneg.mpr hy)]

/-- Paper: §B.4.2.1, p. 614 (citing Lang, Ch. XVII, and (B.4.2.3)). On a vertical line
to the left of `Re(s) = 0` the logarithmic derivative of the completed function is
continuous and grows at most polynomially in the height.
Deviation: One of the two interior lines of Definition B.3.1.1, for `-1 ≤ σ < 0`.
By the functional equation it reduces to the dual character on the line `1 - σ`. -/
private theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv_left (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (σ : ℝ) (hσ : -1 ≤ σ) (hσ0 : σ < 0) :
    Continuous (fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) ∧
      ∃ γ > (0 : ℝ), (fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) =O[comap abs atTop]
        (fun y : ℝ ↦ |y| ^ γ) := by
  obtain ⟨Ldual, hLdual, hDualAgree⟩ := completedHeckeL_exists_continuation χ⁻¹
  obtain ⟨fArch, fArchDual, c, hc, hFourier, hArch, hArchDual⟩ :=
    exists_archimedeanHeckeTest_fourier χ
  obtain ⟨f, a, b, q, ha, hb, hq, hf, hFourierIntegral⟩ :=
    exists_globalHeckeTest_fourier χ fArch fArchDual c hc hFourier
  let B (s : ℂ) := b * (q : ℂ) ^ s
  have hq₀ : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hB : Differentiable ℂ B :=
    (differentiable_id.const_cpow (Or.inl hq₀)).const_mul b
  have hB₀ (s : ℂ) : B s ≠ 0 :=
    mul_ne_zero hb (fun hz ↦ hq₀ ((Complex.cpow_eq_zero_iff _ _).mp hz).1)
  have hZ := globalIdelicZFunction_eq_mul_completedHeckeL_of_integral f χ L (fun _ ↦ a)
    hL hAgree (differentiable_const a) (fun _ ↦ ha) (fun s ↦ by
      rw [hf s, hArch s]
      rfl)
  have hZdual := globalIdelicZFunction_eq_mul_completedHeckeL_of_integral
    (adeleSchwartzFourier f) χ⁻¹ Ldual B hLdual hDualAgree hB hB₀ (fun s ↦ by
      rw [hFourierIntegral s, hArchDual s]
      rfl)
  have hFE (s : ℂ) : L s = (a⁻¹ * B (1 - s)) * Ldual (1 - s) := by
    have hEq := globalIdelicZFunction_functionalEquation f (ideleClassNormTwist χ s)
    rw [dualQuasiCharacter_ideleClassNormTwist, hZ s, hZdual (1 - s)] at hEq
    calc
      L s = a⁻¹ * (a * L s) := by rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      _ = a⁻¹ * (B (1 - s) * Ldual (1 - s)) := by rw [hEq]
      _ = (a⁻¹ * B (1 - s)) * Ldual (1 - s) := by ring
  let E (s : ℂ) : ℂ := a⁻¹ * B (1 - s)
  have hE₀ (s : ℂ) : E s ≠ 0 := mul_ne_zero (inv_ne_zero ha) (hB₀ (1 - s))
  have hEderiv (s : ℂ) : HasDerivAt E (E s * (-Complex.log (q : ℂ))) s := by
    have hsub : HasDerivAt (fun z : ℂ ↦ 1 - z) (-1) s :=
      (hasDerivAt_id s).const_sub (1 : ℂ)
    have hpow : HasDerivAt (fun z : ℂ ↦ (q : ℂ) ^ (1 - z))
        ((q : ℂ) ^ (1 - s) * Complex.log (q : ℂ) * (-1)) s :=
      HasDerivAt.const_cpow (c := (q : ℂ)) hsub (Or.inl hq₀)
    have hmul := (hpow.const_mul b).const_mul a⁻¹
    refine hmul.congr_deriv ?_
    dsimp only [E, B]
    ring
  have hlogE (s : ℂ) : logDeriv E s = -Complex.log (q : ℂ) := by
    rw [logDeriv_apply, (hEderiv s).deriv, mul_div_cancel_left₀ _ (hE₀ s)]
  have hDualAnalytic : ∀ w : ℂ, 1 < w.re → AnalyticAt ℂ Ldual w := by
    intro w hw
    by_cases hχ : (χ⁻¹).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ht, -⟩ :=
        completedHeckeL_continuation_simplePoles χ⁻¹ Ldual hLdual hDualAgree hχ
      rcases ht with ⟨-, -, -, han⟩
      refine han _ ?_
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨fun he ↦ ?_, fun he ↦ ?_⟩
      · have hre : w.re = 0 := by simp [he, Complex.mul_re]
        linarith
      · have hre : w.re = 1 := by simp [he, Complex.mul_re]
        linarith
    · exact (completedHeckeL_continuation_entire χ⁻¹ Ldual hLdual hDualAgree hχ).analyticAt w
  have hDualNeZero : ∀ w : ℂ, 1 < w.re → Ldual w ≠ 0 := by
    intro w hw
    let w' : halfPlane := ⟨w, hw⟩
    rw [show Ldual w = completedHeckeL χ⁻¹ w' from hDualAgree w', completedHeckeL]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ⁻¹ (zero_lt_one.trans hw))
      (finiteHeckeL_ne_zero_of_one_lt_re χ⁻¹ w')
  have hLogDeriv_eq : ∀ s : ℂ, s.re < 0 →
      logDeriv L s = -Complex.log (q : ℂ) - logDeriv Ldual (1 - s) := by
    intro s hs
    have h1s : 1 < (1 - s).re := by simp [Complex.sub_re]; linarith
    have han := hDualAnalytic (1 - s) h1s
    have hne := hDualNeZero (1 - s) h1s
    have hsub : HasDerivAt (fun z : ℂ ↦ 1 - z) (-1) s :=
      (hasDerivAt_id s).const_sub (1 : ℂ)
    have hcomp : HasDerivAt (fun z : ℂ ↦ Ldual (1 - z)) (deriv Ldual (1 - s) * (-1)) s :=
      han.differentiableAt.hasDerivAt.comp s hsub
    have hLfun : L = fun z : ℂ ↦ E z * Ldual (1 - z) := funext hFE
    rw [hLfun, logDeriv_fun_mul (f := E) (g := fun z : ℂ ↦ Ldual (1 - z)) s
      (hE₀ s) hne (hEderiv s).differentiableAt hcomp.differentiableAt,
      hlogE s, logDeriv_apply, logDeriv_apply, hcomp.deriv]
    ring
  have hLine_eq (y : ℝ) :
      logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I) =
        -Complex.log (q : ℂ) - logDeriv Ldual (((1 - σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) := by
    have hs : ((σ : ℂ) + (y : ℂ) * Complex.I).re < 0 := by
      simpa [Complex.add_re, Complex.mul_re] using hσ0
    rw [hLogDeriv_eq _ hs]
    congr 2
    push_cast
    ring
  obtain ⟨hContR, γ, hγ, hBigOR⟩ := hasSlowGrowthNearPoles_completedHeckeL_logDeriv_right
    χ⁻¹ Ldual hLdual hDualAgree (1 - σ) (by linarith) (by linarith)
  refine ⟨?_, γ, hγ, ?_⟩
  · simp_rw [hLine_eq]
    exact continuous_const.sub (hContR.comp continuous_neg)
  · simp_rw [hLine_eq]
    have htend : Tendsto (fun y : ℝ ↦ -y) (comap abs atTop) (comap abs atTop) :=
      Filter.tendsto_comap_iff.mpr <|
        Filter.tendsto_comap.congr fun y ↦ (abs_neg y).symm
    have h1 : (fun y : ℝ ↦ logDeriv Ldual (((1 - σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I))
        =O[comap abs atTop] (fun y : ℝ ↦ |y| ^ γ) := by
      simpa only [Function.comp_def, abs_neg] using hBigOR.comp_tendsto htend
    have hconst : (fun _ : ℝ ↦ -Complex.log (q : ℂ)) =O[comap abs atTop] (fun y : ℝ ↦ |y| ^ γ) := by
      refine Asymptotics.IsBigO.of_bound ‖Complex.log (q : ℂ)‖ ?_
      filter_upwards [(atTop_basis.comap (abs : ℝ → ℝ)).eventually_iff.mpr ⟨1, trivial, fun y hy ↦ hy⟩]
        with y hy
      simp only [mem_preimage, mem_Ici] at hy
      rw [norm_neg, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)]
      exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_rpow hy hγ.le)
    exact hconst.sub h1

/-- Paper: §B.4.2.1, p. 614. The logarithmic derivative of the completed
function has slow growth near its poles on the strip used for the residue formula.
Deviation: Uses the repaired height bounds of Definition B.3.1.1. -/
theorem hasSlowGrowthNearPoles_completedHeckeL_logDeriv (χ : U[F]) (L : ℂ → ℂ)
    (_hL : MeromorphicNFOn L univ) (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (_ha : 1 < a) (_haMax : a ≤ 2) :
    HasSlowGrowthNearPoles (logDeriv L) (1 - a) a := by
  obtain ⟨T, hT, A, β, hA, hβ, hgood⟩ :=
    hasSlowGrowthNearPoles_completedHeckeL_logDeriv_heights χ L _hL _hAgree a _ha _haMax
  refine hasSlowGrowthNearPoles_completedHeckeL_logDeriv_assemble (by linarith)
    ((_hL.meromorphicOn.logDeriv).mono_set (subset_univ _)) T hT A β hA hβ hgood
    ⟨(a - 1) / 3, (a - 1) / 2, by linarith, by linarith, by linarith, ?_⟩
  intro σ hσ
  rcases hσ with rfl | rfl
  · exact hasSlowGrowthNearPoles_completedHeckeL_logDeriv_left χ L _hL _hAgree _
      (by linarith) (by linarith)
  · exact hasSlowGrowthNearPoles_completedHeckeL_logDeriv_right χ L _hL _hAgree _
      (by linarith) (by linarith)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the continuation has order zero to the
right of `Re s = 1`: no poles there by Proposition 3.2.1.3(1)–(2), no zeros by (4). -/
private theorem hasSum_heckeAsymptoticResidue_order_right (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) (hρ : 1 < ρ.re) : meromorphicOrderAt L ρ = 0 := by
  have hnonneg : 0 ≤ meromorphicOrderAt L ρ := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
    · obtain ⟨t, ⟨-, -, -, han⟩, -⟩ :=
        completedHeckeL_continuation_simplePoles χ L hL hAgree hχ
      refine (han ρ ?_).meromorphicOrderAt_nonneg
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      · intro h
        have := congrArg Complex.re h
        simp at this
        linarith
    · exact ((completedHeckeL_continuation_entire χ L hL hAgree hχ).analyticAt
        ρ).meromorphicOrderAt_nonneg
  refine le_antisymm ?_ hnonneg
  by_contra! hpos
  exact absurd (completedHeckeL_continuation_zeros χ L hL hAgree (by linarith) hpos)
    (by linarith)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the continuation has order zero to the
left of `Re s = 0`, by the functional equation and the previous lemma for the dual. -/
private theorem hasSum_heckeAsymptoticResidue_order_left (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) (hρ : ρ.re < 0) : meromorphicOrderAt L ρ = 0 := by
  obtain ⟨Ldual, hLdual, hDualAgree⟩ := completedHeckeL_exists_continuation χ⁻¹
  obtain ⟨ε, -, -, hFE⟩ :=
    completedHeckeL_continuation_functionalEquation χ L Ldual hL hAgree hLdual hDualAgree
  have hdual : meromorphicOrderAt Ldual (1 - ρ) = 0 :=
    hasSum_heckeAsymptoticResidue_order_right χ⁻¹ Ldual hLdual hDualAgree (1 - ρ)
      (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hne : Ldual (1 - ρ) ≠ 0 :=
    (hLdual (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp hdual
  rw [hFE ρ] at hne
  exact (hL (mem_univ ρ)).meromorphicOrderAt_eq_zero_iff.mpr (right_ne_zero_of_mul hne)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the continuation is not identically zero. -/
private theorem hasSum_heckeAsymptoticResidue_order_ne_top (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) : meromorphicOrderAt L ρ ≠ ⊤ := by
  intro htop
  have h2 := hL.meromorphicOn.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ ρ) (mem_univ (2 : ℂ)) htop
  rw [hasSum_heckeAsymptoticResidue_order_right χ L hL hAgree 2 (by norm_num)] at h2
  exact WithTop.zero_ne_top h2

/-- Helper for `hasSum_heckeAsymptoticResidue`: zeros and poles lie in the closed strip
`0 ≤ Re s ≤ 1`. -/
private theorem hasSum_heckeAsymptoticResidue_re_mem (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) (hρ : meromorphicOrderAt L ρ ≠ 0) : ρ.re ∈ Icc 0 1 := by
  by_contra h
  simp only [mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · exact hρ (hasSum_heckeAsymptoticResidue_order_left χ L hL hAgree ρ h)
  · exact hρ (hasSum_heckeAsymptoticResidue_order_right χ L hL hAgree ρ h)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the logarithmic derivative has a pole
exactly at the zeros and poles of the continuation. -/
private theorem hasSum_heckeAsymptoticResidue_logDeriv_order_neg_iff (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (ρ : ℂ) : meromorphicOrderAt (logDeriv L) ρ < 0 ↔ meromorphicOrderAt L ρ ≠ 0 := by
  constructor
  · intro h h0
    exact absurd (meromorphicOrderAt_logDeriv_nonneg (hL (mem_univ ρ)).meromorphicAt h0)
      (not_le.mpr h)
  · intro h
    rw [meromorphicOrderAt_logDeriv_eq_neg_one h
      (hasSum_heckeAsymptoticResidue_order_ne_top χ L hL hAgree ρ)]
    exact WithTop.coe_lt_coe.mpr (by norm_num)

/-- Helper for `hasSum_heckeAsymptoticResidue`: poles are simple and at most two. -/
private theorem hasSum_heckeAsymptoticResidue_poles (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) :
    ∃ P : Finset ℂ, P.card ≤ 2 ∧
      ∀ ρ, meromorphicOrderAt L ρ < 0 → ρ ∈ P ∧ meromorphicOrderAt L ρ = -1 := by
  by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · obtain ⟨t, ⟨-, h0, h1, han⟩, -⟩ :=
      completedHeckeL_continuation_simplePoles χ L hL hAgree hχ
    refine ⟨{Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)}, Finset.card_le_two, fun ρ hρ ↦ ?_⟩
    by_cases hmem : ρ ∈ ({Complex.I * (t : ℂ), 1 + Complex.I * (t : ℂ)} : Set ℂ)
    · refine ⟨by simpa using hmem, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hmem
      rcases hmem with rfl | rfl
      · exact h0
      · exact h1
    · exact absurd (han ρ hmem).meromorphicOrderAt_nonneg (not_le.mpr hρ)
  · refine ⟨∅, by simp, fun ρ hρ ↦ ?_⟩
    exact absurd ((completedHeckeL_continuation_entire χ L hL hAgree hχ).analyticAt
      ρ).meromorphicOrderAt_nonneg (not_le.mpr hρ)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the absolute orders exceed the signed
orders by at most `4` on every finite set, since the poles are simple and at most two. -/
private theorem hasSum_heckeAsymptoticResidue_abs_sum_le (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (s : Finset ℂ) :
    (∑ ρ ∈ s, (|(meromorphicOrderAt L ρ).untop₀| : ℝ)) ≤
      (∑ ρ ∈ s, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) + 4 := by
  obtain ⟨P, hP, hpole⟩ := hasSum_heckeAsymptoticResidue_poles χ L hL hAgree
  have key : ∀ ρ, (|(meromorphicOrderAt L ρ).untop₀| : ℝ) ≤
      ((meromorphicOrderAt L ρ).untop₀ : ℝ) + if ρ ∈ P then 2 else 0 := by
    intro ρ
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
      (hasSum_heckeAsymptoticResidue_order_ne_top χ L hL hAgree ρ)
    by_cases hneg : meromorphicOrderAt L ρ < 0
    · obtain ⟨hmem, hord⟩ := hpole ρ hneg
      rw [hord, ite_eq_left hmem]
      norm_num
    · have h0 : 0 ≤ n := by
        rw [← hn] at hneg
        exact_mod_cast not_lt.mp hneg
      rw [← hn, WithTop.untop₀_coe]
      have : (0 : ℝ) ≤ if ρ ∈ P then 2 else 0 := by split_ifs <;> norm_num
      rw [abs_of_nonneg (by exact_mod_cast h0)]
      linarith
  calc (∑ ρ ∈ s, (|(meromorphicOrderAt L ρ).untop₀| : ℝ))
      ≤ ∑ ρ ∈ s, (((meromorphicOrderAt L ρ).untop₀ : ℝ) + if ρ ∈ P then 2 else 0) :=
        Finset.sum_le_sum fun ρ _ ↦ key ρ
    _ = (∑ ρ ∈ s, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) + ∑ ρ ∈ s ∩ P, (2 : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
    _ ≤ (∑ ρ ∈ s, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) + 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have : ((s ∩ P).card : ℝ) ≤ 2 := by
          exact_mod_cast (Finset.card_le_card Finset.inter_subset_right).trans hP
        linarith

/-- Helper for `hasSum_heckeAsymptoticResidue`: the circle residue depends only on the germ
on a punctured neighbourhood. -/
private theorem hasSum_heckeAsymptoticResidue_residue_congr {f g : ℂ → ℂ} {ρ : ℂ}
    (h : f =ᶠ[𝓝[≠] ρ] g) : complexResidue f ρ = complexResidue g ρ := by
  obtain ⟨R, hR, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h
  unfold complexResidue Filter.limUnder
  apply congrArg Filter.lim
  apply Filter.map_congr
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  congr 1
  apply circleIntegral.integral_congr hr.1.le
  intro z hz
  have hdist := Metric.mem_sphere.mp hz
  refine hEq ⟨Metric.mem_ball.mpr (hdist.trans_lt hr.2), mem_compl_singleton_iff.mpr ?_⟩
  rintro rfl
  exact hr.1.ne (by simpa using hdist)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the residue of `Φ · L'/L` at a point is the
order of `L` there times `Φ`. -/
private theorem hasSum_heckeAsymptoticResidue_residue (Φ L : ℂ → ℂ) (ρ : ℂ)
    (hΦ : AnalyticAt ℂ Φ ρ) (hL : MeromorphicAt L ρ) (hne : meromorphicOrderAt L ρ ≠ ⊤) :
    complexResidue (fun z ↦ Φ z * logDeriv L z) ρ =
      ((meromorphicOrderAt L ρ).untop₀ : ℂ) * Φ ρ := by
  obtain ⟨g, hg, hgρ, hLg⟩ := (meromorphicOrderAt_ne_top_iff hL).mp hne
  set n : ℤ := (meromorphicOrderAt L ρ).untop₀ with hn
  have hgne : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hg.continuousAt.eventually_ne hgρ
  have hlog : ∀ᶠ z in 𝓝[≠] ρ, logDeriv L z = (n : ℂ) / (z - ρ) + logDeriv g z := by
    filter_upwards [logDeriv_congr_nhdsNE hLg, hgne.filter_mono nhdsWithin_le_nhds,
      hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hgz hgan hzρ
    have hzρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    simp only [smul_eq_mul] at hz
    rw [hz]
    have hpow : logDeriv (fun w : ℂ ↦ (w - ρ) ^ n) z = (n : ℂ) / (z - ρ) := by
      have hcomp := logDeriv_comp (f := fun w : ℂ ↦ w ^ n) (g := fun w : ℂ ↦ w - ρ) (x := z)
        (differentiableAt_zpow.mpr (Or.inl hzρ')) (differentiableAt_id.sub_const ρ)
      simp only [Function.comp_def] at hcomp
      rw [hcomp, logDeriv_zpow, deriv_sub_const, deriv_id'', mul_one]
    rw [← hpow]
    exact logDeriv_fun_mul z (zpow_ne_zero n hzρ') hgz
      ((differentiableAt_id.sub_const ρ).zpow (Or.inl hzρ')) hgan.differentiableAt
  have hH : (fun z ↦ Φ z * logDeriv L z) =ᶠ[𝓝[≠] ρ]
      fun z ↦ (Φ z * ((n : ℂ) + (z - ρ) * logDeriv g z)) / (z - ρ) := by
    filter_upwards [hlog, self_mem_nhdsWithin] with z hz hzρ
    have hzρ' : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
    rw [hz]
    field_simp
  rw [hasSum_heckeAsymptoticResidue_residue_congr hH,
    complexResidue_div_sub (g := fun z ↦ Φ z * ((n : ℂ) + (z - ρ) * logDeriv g z)) ?_]
  · simp [mul_comm]
  · exact hΦ.mul (analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul
      (hg.deriv.div hg hgρ)))

/-- Helper for `hasSum_heckeAsymptoticResidue`: the rectangle identity for `Φ · L'/L` on
`[1 - a, a] × [t₁, t₂]` when `L'/L` is analytic on the two horizontal edges. -/
private theorem hasSum_heckeAsymptoticResidue_rectangle (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (ha : 1 < a) (Φ : ℂ → ℂ) (hΦ : Differentiable ℂ Φ) (t₁ t₂ : ℝ) (ht : t₁ < t₂)
    (hAn : ∀ σ ∈ Icc (1 - a) a, AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (t₁ : ℂ) * Complex.I) ∧
      AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (t₂ : ℂ) * Complex.I))
    (S : Finset ℂ) (hS : ∀ ρ, ρ ∈ S ↔ ρ.re ∈ Ioo (1 - a) a ∧ ρ.im ∈ Ioo t₁ t₂ ∧
      meromorphicOrderAt L ρ ≠ 0) :
    (∫ x in (1 - a)..a, Φ ((x : ℂ) + (t₁ : ℂ) * Complex.I) *
        logDeriv L ((x : ℂ) + (t₁ : ℂ) * Complex.I)) -
      (∫ x in (1 - a)..a, Φ ((x : ℂ) + (t₂ : ℂ) * Complex.I) *
        logDeriv L ((x : ℂ) + (t₂ : ℂ) * Complex.I)) +
      Complex.I * (∫ y in t₁..t₂, Φ ((a : ℂ) + (y : ℂ) * Complex.I) *
        logDeriv L ((a : ℂ) + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in t₁..t₂, Φ (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
        logDeriv L (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =
      twoPiI * ∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * Φ ρ := by
  have hmer : MeromorphicOn (fun z ↦ Φ z * logDeriv L z) (Icc (1 - a) a ×ℂ Icc t₁ t₂) :=
    fun z _ ↦ (hΦ.analyticAt z).meromorphicAt.mul (hL.meromorphicOn.logDeriv z (mem_univ z))
  have hne (ρ : ℂ) := hasSum_heckeAsymptoticResidue_order_ne_top χ L hL hAgree ρ
  refine (rectangleIntegral_eq_sum_complexResidue (g := fun z ↦ Φ z * logDeriv L z)
    (by linarith) ht S hmer ?_ ?_).trans ?_
  · intro ρ hρ
    obtain ⟨h1, h2, -⟩ := (hS ρ).mp hρ
    exact Complex.mem_reProdIm.mpr ⟨h1, h2⟩
  · intro ρ hρ hρS
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hρ
    have hΦρ : 0 ≤ meromorphicOrderAt Φ ρ := (hΦ.analyticAt ρ).meromorphicOrderAt_nonneg
    rw [show (fun z ↦ Φ z * logDeriv L z) = Φ * logDeriv L from rfl,
      meromorphicOrderAt_mul (hΦ.analyticAt ρ).meromorphicAt
        (hL.meromorphicOn.logDeriv ρ (mem_univ ρ))]
    refine add_nonneg hΦρ ?_
    by_cases h0 : meromorphicOrderAt L ρ = 0
    · exact meromorphicOrderAt_logDeriv_nonneg (hL (mem_univ ρ)).meromorphicAt h0
    have hre' : ρ.re ∈ Ioo (1 - a) a := by
      rcases hre.1.eq_or_lt with h | h
      · exact absurd (hasSum_heckeAsymptoticResidue_order_left χ L hL hAgree ρ
          (by rw [← h]; linarith)) h0
      rcases hre.2.eq_or_lt with h' | h'
      · exact absurd (hasSum_heckeAsymptoticResidue_order_right χ L hL hAgree ρ
          (by rw [h']; exact ha)) h0
      exact ⟨h, h'⟩
    have him' : ρ.im = t₁ ∨ ρ.im = t₂ := by
      by_contra hcon
      exact hρS ((hS ρ).mpr ⟨hre', ⟨lt_of_le_of_ne him.1 fun h ↦ hcon (Or.inl h.symm),
        lt_of_le_of_ne him.2 fun h ↦ hcon (Or.inr h)⟩, h0⟩)
    have hIcc : ρ.re ∈ Icc (1 - a) a := ⟨hre'.1.le, hre'.2.le⟩
    rcases him' with h | h
    · have := (hAn ρ.re hIcc).1.meromorphicOrderAt_nonneg
      rwa [← h, Complex.re_add_im] at this
    · have := (hAn ρ.re hIcc).2.meromorphicOrderAt_nonneg
      rwa [← h, Complex.re_add_im] at this
  · congr 1
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    exact hasSum_heckeAsymptoticResidue_residue Φ L ρ (hΦ.analyticAt ρ)
      (hL (mem_univ ρ)).meromorphicAt (hne ρ)

/-- Helper for `hasSum_heckeAsymptoticResidue`: the signed divisor sum over the open rectangle
`(1 - a, a) × (t₁, t₂)` is bounded by the boundary integrals of `L'/L` (argument principle). -/
private theorem hasSum_heckeAsymptoticResidue_count (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (ha : 1 < a) (t₁ t₂ : ℝ) (ht : t₁ < t₂) (M M' : ℝ)
    (hAn : ∀ σ ∈ Icc (1 - a) a, ∀ t ∈ ({t₁, t₂} : Set ℝ),
      AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (t : ℂ) * Complex.I) ∧
        ‖logDeriv L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M)
    (hVert : ∀ σ ∈ ({1 - a, a} : Set ℝ), ∀ y ∈ Icc t₁ t₂,
      ‖logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M')
    (S : Finset ℂ) (hS : ∀ ρ, ρ ∈ S ↔ ρ.re ∈ Ioo (1 - a) a ∧ ρ.im ∈ Ioo t₁ t₂ ∧
      meromorphicOrderAt L ρ ≠ 0) :
    (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) ≤
      (2 * (2 * a - 1) * M + 2 * (t₂ - t₁) * M') / (2 * Real.pi) := by
  have hrect := hasSum_heckeAsymptoticResidue_rectangle χ L hL hAgree a ha (fun _ ↦ 1)
    (differentiable_const 1) t₁ t₂ ht
    (fun σ hσ ↦ ⟨(hAn σ hσ t₁ (by simp)).1, (hAn σ hσ t₂ (by simp)).1⟩) S hS
  simp only [one_mul, mul_one] at hrect
  have hIcc : Set.uIoc (1 - a) a ⊆ Icc (1 - a) a := by
    rw [uIoc_of_le (by linarith)]; exact Ioc_subset_Icc_self
  have hIcc' : Set.uIoc t₁ t₂ ⊆ Icc t₁ t₂ := by
    rw [uIoc_of_le ht.le]; exact Ioc_subset_Icc_self
  have hh (t : ℝ) (htt : t ∈ ({t₁, t₂} : Set ℝ)) :
      ‖∫ x in (1 - a)..a, logDeriv L ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ M * (2 * a - 1) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ ↦ logDeriv L ((x : ℂ) + (t : ℂ) * Complex.I)) (a := 1 - a) (b := a)
      (C := M) (fun x hx ↦ (hAn x (hIcc hx) t htt).2)
    rwa [show |a - (1 - a)| = 2 * a - 1 by rw [abs_of_pos (by linarith)]; ring] at this
  have hv (σ : ℝ) (hσ : σ ∈ ({1 - a, a} : Set ℝ)) :
      ‖∫ y in t₁..t₂, logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ M' * (t₂ - t₁) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y : ℝ ↦ logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)) (a := t₁) (b := t₂)
      (C := M') (fun y hy ↦ hVert σ hσ y (hIcc' hy))
    rwa [abs_of_pos (by linarith)] at this
  have hnorm : ‖twoPiI * ∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)‖ ≤
      2 * (2 * a - 1) * M + 2 * (t₂ - t₁) * M' := by
    rw [← hrect]
    calc _ ≤ ‖∫ x in (1 - a)..a, logDeriv L ((x : ℂ) + (t₁ : ℂ) * Complex.I)‖ +
          ‖∫ x in (1 - a)..a, logDeriv L ((x : ℂ) + (t₂ : ℂ) * Complex.I)‖ +
          ‖Complex.I * ∫ y in t₁..t₂, logDeriv L ((a : ℂ) + (y : ℂ) * Complex.I)‖ +
          ‖Complex.I * ∫ y in t₁..t₂,
            logDeriv L (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ M * (2 * a - 1) + M * (2 * a - 1) + M' * (t₂ - t₁) + M' * (t₂ - t₁) := by
          gcongr
          · exact hh t₁ (by simp)
          · exact hh t₂ (by simp)
          · rw [norm_mul, Complex.norm_I, one_mul]; exact hv a (by simp)
          · rw [norm_mul, Complex.norm_I, one_mul]; exact hv (1 - a) (by simp)
      _ = _ := by ring
  have h2pi : ‖twoPiI‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    norm_num
  rw [norm_mul, h2pi] at hnorm
  have hcast : (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) ≤
      ‖∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)‖ := by
    have h1 : (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) =
        (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)).re := by
      simp [Complex.re_sum]
    rw [h1]
    exact Complex.re_le_norm _
  rw [le_div_iff₀ (by positivity)]
  calc (∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) * (2 * Real.pi)
      ≤ ‖∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)‖ * (2 * Real.pi) := by gcongr
    _ = 2 * Real.pi * ‖∑ ρ ∈ S, ((meromorphicOrderAt L ρ).untop₀ : ℂ)‖ := mul_comm _ _
    _ ≤ _ := hnorm

/-- Helper for `hasSum_heckeAsymptoticResidue`: a continuous trace with polynomial growth at
infinity is polynomially bounded everywhere. -/
private theorem hasSum_heckeAsymptoticResidue_trace_bound (g : ℝ → ℂ) (hcont : Continuous g)
    (γ : ℝ) (hγ : 0 < γ) (hO : g =O[comap abs atTop] fun y : ℝ ↦ |y| ^ γ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ y : ℝ, ‖g y‖ ≤ D * (1 + |y|) ^ γ := by
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp hO
  rw [Filter.eventually_comap] at hc
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.mp hc
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -y₀) (b := y₀)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M₀ 0 + max c 0, by positivity, fun y ↦ ?_⟩
  have h1 : (1 : ℝ) ≤ (1 + |y|) ^ γ := Real.one_le_rpow (by linarith [abs_nonneg y]) hγ.le
  have h2 : |y| ^ γ ≤ (1 + |y|) ^ γ := Real.rpow_le_rpow (abs_nonneg y) (by linarith) hγ.le
  by_cases hy : y₀ ≤ |y|
  · have := hy₀ |y| hy y rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) γ)] at this
    calc ‖g y‖ ≤ c * |y| ^ γ := this
      _ ≤ max c 0 * (1 + |y|) ^ γ :=
          mul_le_mul (le_max_left _ _) h2 (by positivity) (le_max_right _ _)
      _ ≤ (max M₀ 0 + max c 0) * (1 + |y|) ^ γ := by
          gcongr; linarith [le_max_right M₀ 0]
  · have hmem : y ∈ Icc (-y₀) y₀ := abs_le.mp (not_le.mp hy).le
    calc ‖g y‖ ≤ M₀ := hM₀ y hmem
      _ ≤ max M₀ 0 * (1 + |y|) ^ γ :=
          (le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _) h1)
      _ ≤ (max M₀ 0 + max c 0) * (1 + |y|) ^ γ := by
          gcongr; linarith [le_max_right c 0]

/-- Helper for `hasSum_heckeAsymptoticResidue`: a polynomial bound on the absolute orders in
height windows and rapid decay of the test give absolute summability of the divisor sum. -/
private theorem hasSum_heckeAsymptoticResidue_summable_of_count (n : ℂ → ℤ) (Φ : ℂ → ℂ)
    (B C c : ℝ) (hc : 1 ≤ c) (m N : ℕ) (hN : m + 2 ≤ N)
    (hΦ : ∀ ρ, n ρ ≠ 0 → ‖Φ ρ‖ ≤ C / (1 + |ρ.im|) ^ N)
    (hcount : ∀ k : ℕ, ∀ s : Finset ℂ, (∀ ρ ∈ s, n ρ ≠ 0 ∧ |ρ.im| ≤ k) →
      (∑ ρ ∈ s, (|n ρ| : ℝ)) ≤ B * ((k : ℝ) + c) ^ m) :
    Summable (fun ρ : ℂ ↦ (n ρ : ℂ) * Φ ρ) := by
  have hB : 0 ≤ B := by
    have := hcount 0 ∅ (by simp)
    simp only [Finset.sum_empty, Nat.cast_zero, zero_add] at this
    exact (mul_nonneg_iff_of_pos_right (pow_pos (by linarith) m)).mp this
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hΦ' : ∀ ρ, n ρ ≠ 0 → ‖Φ ρ‖ ≤ C' / (1 + |ρ.im|) ^ N := fun ρ h ↦
    (hΦ ρ h).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsum2 : Summable (fun j : ℕ ↦ 1 / ((j : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  set K : ℝ := B * (C' * 2 ^ N * c ^ m) with hK
  have hK0 : 0 ≤ K := by positivity
  rw [← summable_norm_iff]
  refine summable_of_sum_le (fun ρ ↦ norm_nonneg _)
    (c := K * ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2) fun s ↦ ?_
  set s' := s.filter (fun ρ ↦ n ρ ≠ 0) with hs'
  have hss' : ∑ ρ ∈ s, ‖(n ρ : ℂ) * Φ ρ‖ = ∑ ρ ∈ s', ‖(n ρ : ℂ) * Φ ρ‖ := by
    rw [hs', Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ _ ↦ ?_
    split_ifs with h
    · rfl
    · simp [not_not.mp h]
  rw [hss']
  set κ : ℂ → ℕ := fun ρ ↦ ⌈|ρ.im|⌉₊ with hκ
  rw [← Finset.sum_fiberwise_of_maps_to (t := s'.image κ) (g := κ)
    (fun ρ hρ ↦ Finset.mem_image_of_mem κ hρ)]
  have hfiber : ∀ j ∈ s'.image κ, (∑ ρ ∈ s' with κ ρ = j, ‖(n ρ : ℂ) * Φ ρ‖) ≤
      K * (1 / ((j : ℝ) + 1) ^ 2) := by
    intro j _
    have hmem : ∀ ρ ∈ s'.filter (fun ρ ↦ κ ρ = j), n ρ ≠ 0 ∧ |ρ.im| ≤ j := by
      intro ρ hρ
      obtain ⟨hρs, hρj⟩ := Finset.mem_filter.mp hρ
      refine ⟨(Finset.mem_filter.mp hρs).2, ?_⟩
      rw [← hρj]
      exact Nat.le_ceil _
    have hΦj : ∀ ρ ∈ s'.filter (fun ρ ↦ κ ρ = j), ‖Φ ρ‖ ≤ C' * 2 ^ N / ((j : ℝ) + 1) ^ N := by
      intro ρ hρ
      obtain ⟨hn, -⟩ := hmem ρ hρ
      have hj : (j : ℝ) < |ρ.im| + 1 := by
        rw [← (Finset.mem_filter.mp hρ).2]
        exact Nat.ceil_lt_add_one (abs_nonneg _)
      have hle : (j : ℝ) + 1 ≤ 2 * (1 + |ρ.im|) := by linarith [abs_nonneg ρ.im]
      calc ‖Φ ρ‖ ≤ C' / (1 + |ρ.im|) ^ N := hΦ' ρ hn
        _ = C' * 2 ^ N / (2 * (1 + |ρ.im|)) ^ N := by
          rw [mul_pow]
          field_simp
        _ ≤ C' * 2 ^ N / ((j : ℝ) + 1) ^ N := by gcongr
    calc (∑ ρ ∈ s' with κ ρ = j, ‖(n ρ : ℂ) * Φ ρ‖)
        ≤ ∑ ρ ∈ s' with κ ρ = j, (|n ρ| : ℝ) * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N) := by
          refine Finset.sum_le_sum fun ρ hρ ↦ ?_
          rw [norm_mul, Complex.norm_intCast]
          exact mul_le_mul_of_nonneg_left (hΦj ρ hρ) (abs_nonneg _)
      _ = (∑ ρ ∈ s' with κ ρ = j, (|n ρ| : ℝ)) * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N) := by
          rw [Finset.sum_mul]
      _ ≤ (B * ((j : ℝ) + c) ^ m) * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N) := by
          gcongr
          exact hcount j _ hmem
      _ ≤ K * (1 / ((j : ℝ) + 1) ^ 2) := by
          have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [j.cast_nonneg (α := ℝ)]
          have h1 : ((j : ℝ) + c) ^ m ≤ c ^ m * ((j : ℝ) + 1) ^ m := by
            rw [← mul_pow]
            exact pow_le_pow_left₀ (by positivity) (by nlinarith [j.cast_nonneg (α := ℝ)]) m
          have h2 : ((j : ℝ) + 1) ^ m * ((j : ℝ) + 1) ^ 2 ≤ ((j : ℝ) + 1) ^ N := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hj1 hN
          have hpos : 0 < ((j : ℝ) + 1) ^ N := by positivity
          have hpos2 : 0 < ((j : ℝ) + 1) ^ 2 := by positivity
          have h3 : ((j : ℝ) + 1) ^ m / ((j : ℝ) + 1) ^ N ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
            rw [div_le_div_iff₀ hpos hpos2, one_mul]
            exact h2
          calc B * ((j : ℝ) + c) ^ m * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N)
              ≤ B * (c ^ m * ((j : ℝ) + 1) ^ m) * (C' * 2 ^ N / ((j : ℝ) + 1) ^ N) := by
                gcongr
            _ = K * (((j : ℝ) + 1) ^ m / ((j : ℝ) + 1) ^ N) := by rw [hK]; ring
            _ ≤ K * (1 / ((j : ℝ) + 1) ^ 2) := by gcongr
  calc (∑ j ∈ s'.image κ, ∑ ρ ∈ s' with κ ρ = j, ‖(n ρ : ℂ) * Φ ρ‖)
      ≤ ∑ j ∈ s'.image κ, K * (1 / ((j : ℝ) + 1) ^ 2) := Finset.sum_le_sum hfiber
    _ = K * ∑ j ∈ s'.image κ, 1 / ((j : ℝ) + 1) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ K * ∑' j : ℕ, 1 / ((j : ℝ) + 1) ^ 2 := by
        gcongr
        exact hsum2.sum_le_tsum _ (fun j _ ↦ by positivity)

/-- Paper: Equation (B.4.2.2), p. 614. The right vertical integral minus the
left vertical integral is the signed divisor sum of Mellin values.
Deviation: The meromorphic order includes the actual poles and zero multiplicities.
The unordered sum strengthens the rectangular limit and uses zero counting for fixed χ. -/
theorem hasSum_heckeAsymptoticResidue (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (a : ℝ) (_ha : 1 < a) (_haMax : a ≤ 2) :
    let H := fun s ↦ logMellin f s * logDeriv L s
    Complex.VerticalIntegrable H a ∧ Complex.VerticalIntegrable H (1 - a) ∧
      HasSum (fun ρ : ℂ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin f ρ)
        ((verticalLineIntegral H a - verticalLineIntegral H (1 - a)) / twoPiI) := by
  intro H
  have hΦd : Differentiable ℂ (logMellin f) := differentiable_mellin_of_exponentialDecay f _hf
  obtain ⟨hcontR, γR, hγR, hOR⟩ := hasSlowGrowthNearPoles_completedHeckeL_logDeriv_right χ L _hL _hAgree a _ha _haMax
  obtain ⟨hcontL, γL, hγL, hOL⟩ := hasSlowGrowthNearPoles_completedHeckeL_logDeriv_left χ L _hL _hAgree (1 - a) (by linarith) (by linarith)
  have hΦstrip : UniformlySchwartzOnStrip (logMellin f) (1 - a - 1) (a + 1) :=
    uniformlySchwartzOnStrip_mellin_of_exponentialDecay f _hf _ _ (by linarith)
  have hintR : Complex.VerticalIntegrable H a :=
    verticalIntegrable_mul_of_polynomialGrowth hΦstrip ⟨by linarith, by linarith⟩ hcontR
      ⟨γR, hγR, hOR⟩
  have hintL : Complex.VerticalIntegrable H (1 - a) :=
    verticalIntegrable_mul_of_polynomialGrowth hΦstrip ⟨by linarith, by linarith⟩ hcontL
      ⟨γL, hγL, hOL⟩
  refine ⟨hintR, hintL, ?_⟩
  -- Orders and the divisor.
  have hne : ∀ ρ, meromorphicOrderAt L ρ ≠ ⊤ :=
    hasSum_heckeAsymptoticResidue_order_ne_top χ L _hL _hAgree
  have hre : ∀ ρ, meromorphicOrderAt L ρ ≠ 0 → ρ.re ∈ Icc 0 1 :=
    hasSum_heckeAsymptoticResidue_re_mem χ L _hL _hAgree
  have hdiv : ∀ ρ, (MeromorphicOn.divisor L univ ρ : ℂ) =
      ((meromorphicOrderAt L ρ).untop₀ : ℂ) := fun ρ ↦ by
    rw [MeromorphicOn.divisor_apply _hL.meromorphicOn (mem_univ ρ)]
  simp_rw [hdiv]
  -- The selected heights.
  obtain ⟨T, hTmono, A, β, hA, hβ, hgood⟩ := hasSlowGrowthNearPoles_completedHeckeL_logDeriv_heights χ L _hL _hAgree a _ha _haMax
  rw [Filter.eventually_comap] at hgood
  obtain ⟨b₀, hb₀⟩ := Filter.eventually_atTop.mp hgood
  obtain ⟨k₁, hk₁b, hk₁2⟩ : ∃ k₁ : ℕ, b₀ ≤ (k₁ : ℤ) ∧ 2 ≤ k₁ :=
    ⟨max b₀.toNat 2, (Int.self_le_toNat b₀).trans (by exact_mod_cast le_max_left _ _),
      le_max_right _ _⟩
  have hgood' : ∀ j : ℤ, (k₁ : ℤ) ≤ |j| → |T j - j| ≤ 1 ∧ ∀ σ ∈ Icc (1 - a) a,
      AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (T j : ℂ) * Complex.I) ∧
        ‖logDeriv L ((σ : ℂ) + (T j : ℂ) * Complex.I)‖ ≤ A * |T j| ^ β :=
    fun j hj ↦ hb₀ |j| (hk₁b.trans hj) j rfl
  set up : ℕ → ℝ := fun k ↦ T ((k + k₁ : ℕ) : ℤ) with hup
  set lo : ℕ → ℝ := fun k ↦ T (-((k + k₁ : ℕ) : ℤ)) with hlo
  have hupG (k : ℕ) := hgood' ((k + k₁ : ℕ) : ℤ)
    (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast Nat.le_add_left k₁ k)
  have hloG (k : ℕ) := hgood' (-((k + k₁ : ℕ) : ℤ))
    (by rw [abs_neg, abs_of_nonneg (by positivity)]; exact_mod_cast Nat.le_add_left k₁ k)
  have hupB (k : ℕ) : (k : ℝ) + k₁ - 1 ≤ up k ∧ up k ≤ (k : ℝ) + k₁ + 1 := by
    have := abs_le.mp (hupG k).1
    rw [Int.cast_natCast, Nat.cast_add (R := ℝ)] at this
    show (k : ℝ) + k₁ - 1 ≤ T ((k + k₁ : ℕ) : ℤ) ∧ T ((k + k₁ : ℕ) : ℤ) ≤ (k : ℝ) + k₁ + 1
    constructor <;> linarith [this.1, this.2]
  have hloB (k : ℕ) : -((k : ℝ) + k₁) - 1 ≤ lo k ∧ lo k ≤ -((k : ℝ) + k₁) + 1 := by
    have := abs_le.mp (hloG k).1
    rw [Int.cast_neg, Int.cast_natCast, Nat.cast_add (R := ℝ)] at this
    show -((k : ℝ) + k₁) - 1 ≤ T (-((k + k₁ : ℕ) : ℤ)) ∧
      T (-((k + k₁ : ℕ) : ℤ)) ≤ -((k : ℝ) + k₁) + 1
    constructor <;> linarith [this.1, this.2]
  have hk₁R : (2 : ℝ) ≤ k₁ := by exact_mod_cast hk₁2
  have hupPos (k : ℕ) : 1 ≤ up k := by linarith [(hupB k).1, k.cast_nonneg (α := ℝ)]
  have hloNeg (k : ℕ) : lo k ≤ -1 := by linarith [(hloB k).2, k.cast_nonneg (α := ℝ)]
  have hlt (k : ℕ) : lo k < up k := by linarith [hupPos k, hloNeg k]
  have hupMono : Monotone up := fun i j hij ↦
    hTmono (by exact_mod_cast Nat.add_le_add_right hij k₁)
  have hloAnti : Antitone lo := fun i j hij ↦
    hTmono (by rw [neg_le_neg_iff]; exact_mod_cast Nat.add_le_add_right hij k₁)
  have hupTop : Tendsto up atTop atTop := by
    refine tendsto_atTop_mono (fun k ↦ (hupB k).1) ?_
    refine (tendsto_atTop_add_const_right atTop ((k₁ : ℝ) - 1)
      (tendsto_natCast_atTop_atTop (R := ℝ))).congr fun k ↦ ?_
    ring
  have hloBot : Tendsto lo atTop atBot := by
    refine tendsto_atBot_mono (fun k ↦ (hloB k).2) ?_
    refine (tendsto_atBot_add_const_right atTop (1 - (k₁ : ℝ))
      (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ)))).congr fun k ↦ ?_
    simp only [Function.comp_apply]
    ring
  -- The finite sets of zeros and poles in the rectangles.
  have hmerStrip : MeromorphicOn (logDeriv L) (Complex.re ⁻¹' Ioo (1 - a - 1) (a + 1)) :=
    (_hL.meromorphicOn.logDeriv).mono_set (subset_univ _)
  let Z : ℕ → Finset ℂ := fun k ↦ (finite_rectanglePoles (f := logDeriv L) (σ₁ := 1 - a)
    (σ₂ := a) (t₁ := lo k) (t₂ := up k) hmerStrip (by linarith) (by linarith)).toFinset
  have hZ : ∀ k ρ, ρ ∈ Z k ↔ ρ.re ∈ Ioo (1 - a) a ∧ ρ.im ∈ Ioo (lo k) (up k) ∧
      meromorphicOrderAt L ρ ≠ 0 := by
    intro k ρ
    simp only [Z, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact and_congr_right fun _ ↦ and_congr_right fun _ ↦
      hasSum_heckeAsymptoticResidue_logDeriv_order_neg_iff χ L _hL _hAgree ρ
  have hZmono : Monotone Z := by
    intro i j hij ρ hρ
    obtain ⟨h1, h2, h3⟩ := (hZ i ρ).mp hρ
    exact (hZ j ρ).mpr ⟨h1, ⟨(hloAnti hij).trans_lt h2.1, h2.2.trans_le (hupMono hij)⟩, h3⟩
  -- Polynomial bounds on the edges of the rectangles.
  have hAbs (k : ℕ) (j : ℤ) (hj : j = ((k + k₁ : ℕ) : ℤ) ∨ j = -((k + k₁ : ℕ) : ℤ)) :
      |T j| ≤ (k : ℝ) + k₁ + 1 := by
    rcases hj with rfl | rfl
    · rw [abs_of_pos (by linarith [hupPos k])]
      exact (hupB k).2
    · rw [abs_of_neg (by linarith [hloNeg k])]
      linarith [(hloB k).1]
  have hEdge (k : ℕ) : ∀ σ ∈ Icc (1 - a) a, ∀ t ∈ ({lo k, up k} : Set ℝ),
      AnalyticAt ℂ (logDeriv L) ((σ : ℂ) + (t : ℂ) * Complex.I) ∧
        ‖logDeriv L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * ((k : ℝ) + k₁ + 1) ^ β := by
    intro σ hσ t ht
    simp only [mem_insert_iff, mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · refine ⟨((hloG k).2 σ hσ).1, ((hloG k).2 σ hσ).2.trans ?_⟩
      gcongr
      exact hAbs k _ (Or.inr rfl)
    · refine ⟨((hupG k).2 σ hσ).1, ((hupG k).2 σ hσ).2.trans ?_⟩
      gcongr
      exact hAbs k _ (Or.inl rfl)
  obtain ⟨DR, hDR, hDRb⟩ := hasSum_heckeAsymptoticResidue_trace_bound _ hcontR γR hγR hOR
  obtain ⟨DL, hDL, hDLb⟩ := hasSum_heckeAsymptoticResidue_trace_bound _ hcontL γL hγL hOL
  set D := max DR DL with hD
  set γ := max γR γL with hγ
  have hγ0 : 0 < γ := lt_max_of_lt_left hγR
  have hVert : ∀ σ ∈ ({1 - a, a} : Set ℝ), ∀ y : ℝ,
      ‖logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ D * (1 + |y|) ^ γ := by
    intro σ hσ y
    have h1 : (1 : ℝ) ≤ 1 + |y| := by linarith [abs_nonneg y]
    simp only [mem_insert_iff, mem_singleton_iff] at hσ
    rcases hσ with rfl | rfl
    · exact (hDLb y).trans (mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le h1 (le_max_right _ _)) (by positivity)
        (le_max_of_le_left hDR))
    · exact (hDRb y).trans (mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)) (by positivity)
        (le_max_of_le_left hDR))
  -- The counting bound.
  set m₁ : ℕ := ⌈β⌉₊ with hm₁
  set m₂ : ℕ := ⌈γ⌉₊ with hm₂
  set m : ℕ := max m₁ (m₂ + 1) with hm
  set B₀ : ℝ := (6 * A + 4 * D) / (2 * Real.pi) with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hcountZ (k : ℕ) : (∑ ρ ∈ Z k, ((meromorphicOrderAt L ρ).untop₀ : ℝ)) ≤
      B₀ * ((k : ℝ) + k₁ + 2) ^ m := by
    set K : ℝ := (k : ℝ) + k₁ + 2 with hK
    have hK1 : (1 : ℝ) ≤ K := by linarith [k.cast_nonneg (α := ℝ)]
    have hVertK : ∀ σ ∈ ({1 - a, a} : Set ℝ), ∀ y ∈ Icc (lo k) (up k),
        ‖logDeriv L ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ D * K ^ γ := by
      intro σ hσ y hy
      refine (hVert σ hσ y).trans ?_
      gcongr
      rw [hK]
      have : |y| ≤ (k : ℝ) + k₁ + 1 := abs_le.mpr ⟨by linarith [(hloB k).1, hy.1],
        by linarith [(hupB k).2, hy.2]⟩
      linarith
    have hcount := hasSum_heckeAsymptoticResidue_count χ L _hL _hAgree a _ha (lo k) (up k)
      (hlt k) _ _ (hEdge k) hVertK (Z k) (hZ k)
    refine hcount.trans ?_
    rw [hB₀, div_mul_eq_mul_div]
    gcongr
    have hβm : ((k : ℝ) + k₁ + 1) ^ β ≤ K ^ m := by
      calc ((k : ℝ) + k₁ + 1) ^ β ≤ K ^ β :=
            Real.rpow_le_rpow (by positivity) (by rw [hK]; linarith) hβ.le
        _ ≤ K ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1
            ((Nat.le_ceil β).trans (by exact_mod_cast le_max_left m₁ (m₂ + 1)))
        _ = K ^ m := Real.rpow_natCast _ _
    have hγm : (up k - lo k) * K ^ γ ≤ 2 * K ^ m := by
      have h1 : up k - lo k ≤ 2 * K := by rw [hK]; linarith [(hupB k).2, (hloB k).1]
      have h2 : K * K ^ γ ≤ K ^ m := by
        calc K * K ^ γ = K ^ ((1 : ℝ) + γ) := by
              rw [Real.rpow_add (by linarith), Real.rpow_one]
          _ ≤ K ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hK1 (by
              have : γ ≤ m₂ := Nat.le_ceil γ
              have : ((m₂ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast le_max_right m₁ (m₂ + 1)
              push_cast at this
              linarith)
          _ = K ^ m := Real.rpow_natCast _ _
      calc (up k - lo k) * K ^ γ ≤ 2 * K * K ^ γ := by gcongr
        _ = 2 * (K * K ^ γ) := by ring
        _ ≤ 2 * K ^ m := by gcongr
    have ha3 : 2 * a - 1 ≤ 3 := by linarith
    have hKm : 0 ≤ K ^ m := by positivity
    have hAK : 0 ≤ A * K ^ m := by positivity
    have hD0 : 0 ≤ D := le_max_of_le_left hDR
    have h1 : 2 * (2 * a - 1) * (A * ((k : ℝ) + k₁ + 1) ^ β) ≤ 2 * 3 * (A * K ^ m) :=
      mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hβm hA.le) (by positivity)
        (by norm_num)
    have h2 : 2 * (up k - lo k) * (D * K ^ γ) ≤ 2 * (D * (2 * K ^ m)) := by
      calc 2 * (up k - lo k) * (D * K ^ γ) = 2 * D * ((up k - lo k) * K ^ γ) := by ring
        _ ≤ 2 * D * (2 * K ^ m) := mul_le_mul_of_nonneg_left hγm (by positivity)
        _ = 2 * (D * (2 * K ^ m)) := by ring
    calc 2 * (2 * a - 1) * (A * ((k : ℝ) + k₁ + 1) ^ β) + 2 * (up k - lo k) * (D * K ^ γ)
        ≤ 2 * 3 * (A * K ^ m) + 2 * (D * (2 * K ^ m)) := add_le_add h1 h2
      _ = (6 * A + 4 * D) * K ^ m := by ring
  -- Rapid decay of the Mellin transform on the closed strip.
  set N : ℕ := m + 2 with hN
  obtain ⟨C₁, hC₁, hbound⟩ := mellin_heightBound_of_exponentialDecay f _hf 0 1 zero_lt_one N
    (by omega)
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.reProdIm isCompact_Icc : IsCompact
    (Icc (0 : ℝ) 1 ×ℂ Icc (-1 : ℝ) 1)).exists_bound_of_continuousOn hΦd.continuous.continuousOn
  have hdecay : ∀ ρ, (meromorphicOrderAt L ρ).untop₀ ≠ 0 →
      ‖logMellin f ρ‖ ≤ 2 ^ N * max C₁ M₀ / (1 + |ρ.im|) ^ N := by
    intro ρ hρ
    have hρ' : meromorphicOrderAt L ρ ≠ 0 := by
      intro h; apply hρ; rw [h]; rfl
    have hreρ := hre ρ hρ'
    have hρeq : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := (Complex.re_add_im ρ).symm
    have hpos : 0 < (1 + |ρ.im|) ^ N := by positivity
    by_cases him : 1 ≤ |ρ.im|
    · have hy : ρ.im ≠ 0 := by
        intro h; rw [h, abs_zero] at him; linarith
      have h1 := hbound ρ.re hreρ ρ.im hy
      simp only [Complex.re_add_im] at h1
      refine h1.trans ?_
      rw [div_le_div_iff₀ (by positivity) hpos]
      have h2 : (1 + |ρ.im|) ^ N ≤ (2 * |ρ.im|) ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith) N
      calc C₁ * (1 + |ρ.im|) ^ N ≤ C₁ * (2 * |ρ.im|) ^ N := by gcongr
        _ = 2 ^ N * C₁ * |ρ.im| ^ N := by rw [mul_pow]; ring
        _ ≤ 2 ^ N * max C₁ M₀ * |ρ.im| ^ N := by gcongr; exact le_max_left _ _
    · have hmem : ρ ∈ Icc (0 : ℝ) 1 ×ℂ Icc (-1 : ℝ) 1 :=
        Complex.mem_reProdIm.mpr ⟨hreρ, abs_le.mp (not_le.mp him).le⟩
      have h1 := hM₀ ρ hmem
      refine h1.trans ?_
      rw [le_div_iff₀ hpos]
      have h2 : (1 + |ρ.im|) ^ N ≤ 2 ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith [not_le.mp him]) N
      have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans h1
      calc M₀ * (1 + |ρ.im|) ^ N ≤ M₀ * 2 ^ N := by gcongr
        _ ≤ 2 ^ N * max C₁ M₀ := by rw [mul_comm]; gcongr; exact le_max_right _ _
  -- Summability.
  have hsum : Summable (fun ρ : ℂ ↦ ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ) := by
    refine hasSum_heckeAsymptoticResidue_summable_of_count
      (fun ρ ↦ (meromorphicOrderAt L ρ).untop₀) (logMellin f) (B₀ + 4) (2 ^ N * max C₁ M₀)
      ((k₁ : ℝ) + 4) (by linarith) m N le_rfl hdecay ?_
    intro k s hs
    have hsub : s ⊆ Z (k + 2) := by
      intro ρ hρ
      obtain ⟨h0, him⟩ := hs ρ hρ
      have h0' : meromorphicOrderAt L ρ ≠ 0 := by
        intro h; apply h0; rw [h]; rfl
      have hreρ := hre ρ h0'
      refine (hZ (k + 2) ρ).mpr ⟨⟨by linarith [hreρ.1], by linarith [hreρ.2]⟩, ⟨?_, ?_⟩, h0'⟩
      · have := (hloB (k + 2)).2
        push_cast at this
        linarith [abs_le.mp him]
      · have := (hupB (k + 2)).1
        push_cast at this
        linarith [abs_le.mp him]
    calc (∑ ρ ∈ s, (|(meromorphicOrderAt L ρ).untop₀| : ℝ))
        ≤ ∑ ρ ∈ Z (k + 2), (|(meromorphicOrderAt L ρ).untop₀| : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ abs_nonneg _
      _ ≤ (∑ ρ ∈ Z (k + 2), ((meromorphicOrderAt L ρ).untop₀ : ℝ)) + 4 :=
          hasSum_heckeAsymptoticResidue_abs_sum_le χ L _hL _hAgree _
      _ ≤ B₀ * (((k + 2 : ℕ) : ℝ) + k₁ + 2) ^ m + 4 := by gcongr; exact hcountZ (k + 2)
      _ ≤ (B₀ + 4) * ((k : ℝ) + ((k₁ : ℝ) + 4)) ^ m := by
          have h1 : (1 : ℝ) ≤ ((k : ℝ) + ((k₁ : ℝ) + 4)) ^ m :=
            one_le_pow₀ (by linarith [k.cast_nonneg (α := ℝ)])
          have h2 : (((k + 2 : ℕ) : ℝ) + k₁ + 2) = (k : ℝ) + ((k₁ : ℝ) + 4) := by push_cast; ring
          rw [h2]
          nlinarith
  -- The rectangle identity for the Mellin test.
  have hrectΦ (k : ℕ) : ∑ ρ ∈ Z k, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ =
      ((∫ x in (1 - a)..a, H ((x : ℂ) + (lo k : ℂ) * Complex.I)) -
        (∫ x in (1 - a)..a, H ((x : ℂ) + (up k : ℂ) * Complex.I)) +
        Complex.I * (∫ y in lo k..up k, H ((a : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y in lo k..up k, H (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I))) /
          twoPiI := by
    have htwoPiI : twoPiI ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    rw [eq_div_iff htwoPiI, mul_comm]
    exact (hasSum_heckeAsymptoticResidue_rectangle χ L _hL _hAgree a _ha (logMellin f) hΦd
      (lo k) (up k) (hlt k) (fun σ hσ ↦ ⟨(hEdge k σ hσ (lo k) (by simp)).1,
        (hEdge k σ hσ (up k) (by simp)).1⟩) (Z k) (hZ k)).symm
  -- The horizontal edges vanish in the limit.
  set N₂ : ℕ := m₁ + 1 with hN₂
  obtain ⟨C₂, hC₂, hbound₂⟩ := mellin_heightBound_of_exponentialDecay f _hf (1 - a) a
    (by linarith) N₂ (by omega)
  have hhoriz (t : ℝ) (ht1 : 1 ≤ |t|)
      (hAnt : ∀ σ ∈ Icc (1 - a) a,
        ‖logDeriv L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A * |t| ^ β) :
      ‖∫ x in (1 - a)..a, H ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (2 * a - 1) * (C₂ * A) / |t| := by
    have ht0 : t ≠ 0 := by
      intro h; rw [h, abs_zero] at ht1; linarith
    have hIcc : Set.uIoc (1 - a) a ⊆ Icc (1 - a) a := by
      rw [uIoc_of_le (by linarith)]; exact Ioc_subset_Icc_self
    have hpt : ∀ x ∈ Set.uIoc (1 - a) a,
        ‖H ((x : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C₂ * A / |t| := by
      intro x hx
      have hx' := hIcc hx
      have h1 := hbound₂ x hx' t ht0
      simp only at h1
      have h2 := hAnt x hx'
      have hβ' : |t| ^ β ≤ |t| ^ m₁ := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le ht1 (Nat.le_ceil β)
      have habs : 0 < |t| := by linarith
      calc ‖H ((x : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖logMellin f ((x : ℂ) + (t : ℂ) * Complex.I)‖ *
              ‖logDeriv L ((x : ℂ) + (t : ℂ) * Complex.I)‖ := norm_mul _ _
        _ ≤ (C₂ / |t| ^ N₂) * (A * |t| ^ m₁) :=
            mul_le_mul h1 (h2.trans (mul_le_mul_of_nonneg_left hβ' hA.le)) (norm_nonneg _)
              (by positivity)
        _ = C₂ * A / |t| := by
            rw [hN₂, pow_succ]
            field_simp
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 1 - a) (b := a) hpt
    refine this.trans (le_of_eq ?_)
    rw [abs_of_pos (by linarith : (0 : ℝ) < a - (1 - a))]
    ring
  have hH0 : ∀ s : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 1 ≤ |s k|) →
      (∀ k : ℕ, ∀ σ ∈ Icc (1 - a) a,
        ‖logDeriv L ((σ : ℂ) + (s k : ℂ) * Complex.I)‖ ≤ A * |s k| ^ β) →
      Tendsto (fun k : ℕ ↦ ∫ x in (1 - a)..a, H ((x : ℂ) + (s k : ℂ) * Complex.I)) atTop
        (𝓝 0) := by
    intro s hs hAn
    refine squeeze_zero_norm (a := fun k : ℕ ↦ (2 * a - 1) * (C₂ * A) / ((k : ℝ) + 1))
      (fun k : ℕ ↦ (hhoriz (s k) (by linarith [hs k, k.cast_nonneg (α := ℝ)]) (hAn k)).trans ?_)
      ?_
    · exact div_le_div_of_nonneg_left (mul_nonneg (by linarith) (by positivity)) (by positivity)
        (hs k)
    · have := (tendsto_const_div_atTop_nhds_zero_nat ((2 * a - 1) * (C₂ * A))).comp
        (tendsto_add_atTop_nat 1)
      refine this.congr fun k ↦ ?_
      simp [Function.comp]
  have hlo' := hH0 lo (fun k : ℕ ↦ by
      rw [abs_of_neg (by linarith [hloNeg k])]; linarith [(hloB k).2])
    (fun k σ hσ ↦ ((hloG k).2 σ hσ).2)
  have hup' := hH0 up (fun k : ℕ ↦ by
      rw [abs_of_pos (by linarith [hupPos k])]; linarith [(hupB k).1])
    (fun k σ hσ ↦ ((hupG k).2 σ hσ).2)
  -- The vertical edges converge to the line integrals.
  have hVa : Tendsto (fun k ↦ Complex.I * ∫ y in lo k..up k, H ((a : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (verticalLineIntegral H a)) :=
    (intervalIntegral_tendsto_integral hintR hloBot hupTop).const_mul Complex.I
  have hVb : Tendsto (fun k ↦ Complex.I *
      ∫ y in lo k..up k, H (((1 - a : ℝ) : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (verticalLineIntegral H (1 - a))) :=
    (intervalIntegral_tendsto_integral hintL hloBot hupTop).const_mul Complex.I
  have hlim : Tendsto (fun k ↦ ∑ ρ ∈ Z k, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ)
      atTop (𝓝 ((verticalLineIntegral H a - verticalLineIntegral H (1 - a)) / twoPiI)) := by
    have := (((hlo'.sub hup').add hVa).sub hVb).div_const twoPiI
    simp only [sub_self, zero_add] at this
    exact this.congr fun k ↦ (hrectΦ k).symm
  -- Conclusion: the partial sums over the rectangles exhaust the support.
  set Sset : Set ℂ := {ρ | meromorphicOrderAt L ρ ≠ 0} with hSset
  have hsupp : support (fun ρ : ℂ ↦ ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ) ⊆
      Sset := by
    intro ρ hρ h0
    apply hρ
    show ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ = 0
    simp [h0]
  have hsub := (hasSum_subtype_iff_of_support_subset hsupp).mpr hsum.hasSum
  let W : ℕ → Finset Sset := fun k ↦ (Z k).subtype (· ∈ Sset)
  have hWmono : Monotone W := fun i j hij ↦ Finset.subtype_mono (hZmono hij)
  have hWex : ∀ x : Sset, ∃ k, x ∈ W k := by
    intro x
    have hx : meromorphicOrderAt L x.val ≠ 0 := x.property
    refine ⟨⌈|x.val.im|⌉₊ + 2, ?_⟩
    rw [Finset.mem_subtype]
    have hreρ := hre x.val hx
    refine (hZ _ _).mpr ⟨⟨by linarith [hreρ.1], by linarith [hreρ.2]⟩, ⟨?_, ?_⟩, hx⟩
    · have := (hloB (⌈|x.val.im|⌉₊ + 2)).2
      push_cast at this
      linarith [Nat.le_ceil |x.val.im|, neg_abs_le x.val.im]
    · have := (hupB (⌈|x.val.im|⌉₊ + 2)).1
      push_cast at this
      linarith [Nat.le_ceil |x.val.im|, le_abs_self x.val.im]
  have hWtop : Tendsto W atTop atTop := tendsto_atTop_finset_of_monotone hWmono hWex
  have hpartial : Tendsto
      (fun k ↦ ∑ ρ ∈ Z k, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ) atTop
      (𝓝 (∑' ρ, ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ)) := by
    refine (Filter.Tendsto.comp hsub hWtop).congr fun k ↦ ?_
    simp only [W, Function.comp_apply]
    exact Finset.sum_subtype_of_mem
      (fun ρ ↦ ((meromorphicOrderAt L ρ).untop₀ : ℂ) * logMellin f ρ)
      fun ρ hρ ↦ ((hZ k ρ).mp hρ).2.2
  have heq := tendsto_nhds_unique hpartial hlim
  rw [← heq]
  exact hsum.hasSum

-- TODO(paper-gap): (B.4.2.3) misses the chain-rule sign. The page specifies
-- Aχ, but the identification ε'/ε = log Aχ needs the conductor calculation.
-- The normalized integral of Φ in (B.4.2.4) gives the test value at one.

local notation "conductorExponents(" χ ", " v ")" =>
  ({n : ℕ | ∀ u : (HeightOneSpectrum.adicCompletion F v)ˣ, ‖u.val‖ = 1 →
    ‖u.val - 1‖ ≤ q(v) ^ (-(n : ℤ)) →
      χ (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) = 1} : Set ℕ)

/-- Paper: Equation (B.4.2.3), p. 614. Each finite local character has
a least conductor exponent, and only finitely many exponents are nonzero.
Deviation: The exponent is given by the local unit filtration of §3.3.1. -/
theorem exists_heckeConductorExponents (χ : U[F]) :
    ∃ n : Primes(F) → ℕ, (Function.support n).Finite ∧
      ∀ v, IsLeast (conductorExponents(χ, v)) (n v) := by
  classical
  have hlocal (v : Primes(F)) : (conductorExponents(χ, v)).Nonempty := by
    let η : (v.adicCompletion F)ˣ →ₜ* Circle := χ.comp
      ⟨IdeleClassGroup.ofAdicCompletion (𝓞 F) F v, continuous_ideleClass_ofAdicCompletion F v⟩
    have harc : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
      simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
    have hpre : η ⁻¹' Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : (v.adicCompletion F)ˣ) :=
      η.continuous.continuousAt.preimage_mem_nhds (by
        change Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (η 1)
        rwa [map_one])
    rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap] at hpre
    obtain ⟨W, hW, hsub⟩ := mem_comap.mp hpre
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hW
    have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (inv_lt_one_of_one_lt₀ hq)
    refine ⟨n, fun u hu hclose ↦ ?_⟩
    -- Every power stays close to one, so its character lies in the same half circle.
    change η u = 1
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro k _
    rw [← map_pow]
    apply hsub
    apply hball
    change dist (u.val ^ k) 1 < r
    rw [dist_eq_norm]
    apply (local_unit_pow_bound u.val hu.le k).trans_lt
    exact hclose.trans_lt (by simpa only [zpow_neg, zpow_natCast, inv_pow] using hn)
  let c := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
  have hcover : c ∈ ⋃ T : Finset (Primes(F)), (unramifiedOutside F T : Set _) := by
    rw [iUnion_unramifiedOutside]
    exact mem_univ _
  obtain ⟨T, hT⟩ := mem_iUnion.mp hcover
  refine ⟨fun v ↦ sInf (conductorExponents(χ, v)), T.finite_toSet.subset ?_,
    fun v ↦ ⟨Nat.sInf_mem (hlocal v), fun _ hn ↦ Nat.sInf_le hn⟩⟩
  intro v hv
  by_contra hvT
  have hzero : 0 ∈ conductorExponents(χ, v) := by
    intro u hu _
    have hunit : u ∈ (v.adicCompletionIntegers F).units :=
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
        (Valued.toNormedField.norm_eq_one_iff.mp hu)
    let u' := (v.adicCompletionIntegers F).toSubmonoid.unitsEquivUnitsType ⟨u, hunit⟩
    have h := (mem_unramifiedOutside_iff F T c).mp hT v hvT u'
    exact Subtype.ext h
  exact hv (Nat.eq_zero_of_le_zero (Nat.sInf_le hzero))

/-- Paper: Equation (B.4.2.3), p. 614. The logarithm of the
discriminant–conductor product adds the finite conductor exponents weighted by log prime norm.
Deviation: The conductor exponent is given by the local unit filtration of §3.3.1. -/
def heckeLogDiscriminantConductor (χ : U[F]) : ℝ :=
  Real.log (Int.natAbs (NumberField.discr F)) +
    ∑ᶠ v : Primes(F), Real.log q(v) * (sInf (conductorExponents(χ, v)) : ℕ)

/-- Paper: Equation (B.4.2.3), p. 614. The trivial character has only the
discriminant contribution. -/
theorem heckeLogDiscriminantConductor_one :
    heckeLogDiscriminantConductor (1 : U[F]) =
      Real.log (Int.natAbs (NumberField.discr F)) := by
  simp [heckeLogDiscriminantConductor]

/-- Paper: Equation (B.4.2.3), p. 614, with Proposition 3.2.1.3(3), p. 123. The epsilon
factor of the functional equation of the completed continuations is a nonzero constant times
the exponential of the discriminant–conductor logarithm centred at `1/2`:
`Λ(1 - s, χ⁻¹) = C · exp(log A_χ · (s - 1/2)) · Λ(s, χ)` for every `s`.
Deviation: `completedHeckeL_continuation_functionalEquation` only gives an unspecified entire
nowhere-vanishing factor; this identifies its exponent. The global test of
`exists_globalHeckeTest_fourier` has Fourier-side scale `q = ∏ᵥ N(𝔭ᵥ)^(dᵥ + nᵥ)` over the
finitely many places where the different exponent `dᵥ` or the conductor exponent `nᵥ` is
nonzero: at an unramified place the Fourier transform of the integer indicator is the
indicator of the inverse different, and at a ramified place the Fourier transform of the
unit test is supported on the shell of norm `N(𝔭ᵥ)^(dᵥ + nᵥ)`. The norm of the different is
`|disc F|` (`NumberField.absNorm_differentIdeal`), so `log q = heckeLogDiscriminantConductor χ`,
and `a / (b q^(1-s)) = (a / (b √q)) · exp(log q · (s - 1/2))`. -/
theorem completedHeckeL_functionalEquation_conductorScale (χ : U[F]) (L Ldual : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualAgree : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ, Ldual (1 - s) =
      C * Complex.exp ((heckeLogDiscriminantConductor χ : ℂ) * (s - 1 / 2)) * L s := by
  sorry

/-- Paper: Equation (B.4.2.3), p. 614. The reflected logarithmic derivative
and the discriminant–conductor term give the logarithmic derivative of the continuation.
Deviation: Both terms acquire the minus signs dictated by the functional equation
in Proposition 3.2.1.3(3). The order hypothesis excludes zeros and poles. -/
theorem completedHeckeL_logDeriv_reflection (χ : U[F]) (L Ldual : ℂ → ℂ)
    (_hL : MeromorphicNFOn L univ) (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (_hLdual : MeromorphicNFOn Ldual univ)
    (_hDualAgree : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s)
    (s : ℂ) (_hs : meromorphicOrderAt L s = 0) :
    logDeriv L s = -logDeriv Ldual (1 - s) - (heckeLogDiscriminantConductor χ : ℂ) := by
  obtain ⟨C, hC, hFE⟩ := completedHeckeL_functionalEquation_conductorScale χ L Ldual _hL
    _hAgree _hLdual _hDualAgree
  have hNF : MeromorphicNFAt L s := _hL (mem_univ s)
  have hLs : L s ≠ 0 := hNF.meromorphicOrderAt_eq_zero_iff.mp _hs
  have hLan : AnalyticAt ℂ L s := hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp _hs.ge
  have hG : AnalyticAt ℂ (fun z ↦ Ldual (1 - z)) s := by
    rw [show (fun z ↦ Ldual (1 - z)) = fun z ↦
        C * Complex.exp ((heckeLogDiscriminantConductor χ : ℂ) * (z - 1 / 2)) * L z from
      funext hFE]
    exact (analyticAt_const.mul
      ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).cexp')).mul hLan
  have hGdual : AnalyticAt ℂ Ldual (1 - s) := by
    have hG' : AnalyticAt ℂ (fun z ↦ Ldual (1 - z)) (1 - (1 - s)) := by
      rwa [sub_sub_cancel]
    have hcomp := hG'.comp
      (analyticAt_const.sub analyticAt_id : AnalyticAt ℂ (fun w : ℂ ↦ 1 - w) (1 - s))
    refine hcomp.congr (Eventually.of_forall fun w ↦ ?_)
    simp [Function.comp]
  exact External.Grh.completed_logDeriv_reflection hC hLan.differentiableAt
    hGdual.differentiableAt hLs (Eventually.of_forall hFE)

-- TODO(paper-gap): In (B.4.2.15) a compactly supported logarithmic profile
-- with f(0) = 1 leaves Nᵥ/x at infinity. The gamma arguments also omit
-- the sign parity or angular weight. With the printed negative αᵥ on p. 616,
-- the constant in (B.4.2.12) should be +αᵥ. The digamma integral below includes
-- the parity or angular weight and the gamma prefactor.

/-- Paper: Proposition B.4.2.1, p. 616. The combined digamma integrand uses
the gamma arguments of the two local characters and the positive and negative
samples of the logarithmic test.
Deviation: The subtraction uses Euler's convergent digamma kernel. -/
def heckeArchimedeanDigammaKernel (k : ℝ) (zPlus zMinus : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (k : ℂ) * (2 * (Real.exp (-t) : ℂ) * f 0 / (t : ℂ) -
    (f (k * t) * Complex.exp (-zPlus * (t : ℂ)) +
      f (-(k * t)) * Complex.exp (-zMinus * (t : ℂ))) / (1 - (Real.exp (-t) : ℂ)))

section GaussDigamma

open Real

/-- The factor `1 / t - 1 / (1 - e^{-t})` lies in `[-1, 0]` for positive `t`. -/
private lemma digamma_remainder_bounds {t : ℝ} (ht : 0 < t) :
    -1 ≤ 1 / t - 1 / (1 - exp (-t)) ∧ 1 / t - 1 / (1 - exp (-t)) ≤ 0 := by
  have hq : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - exp (-t) := by linarith
  have h1 : 1 - exp (-t) ≤ t := by linarith [add_one_le_exp (-t)]
  have h2 : t * exp (-t) ≤ 1 - exp (-t) := by
    have h := add_one_le_exp t
    have he : exp t * exp (-t) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos (-t)]
  constructor
  · rw [div_sub_div _ _ ht.ne' hd.ne', le_div_iff₀ (mul_pos ht hd)]
    nlinarith
  · rw [sub_nonpos]
    exact one_div_le_one_div_of_le hd h1

/-- The real Gauss kernel `e^{-t}/t - e^{-t}/(1 - e^{-t})` of `ψ(1)`. -/
private noncomputable def gaussDigammaKernel (t : ℝ) : ℝ :=
  exp (-t) / t - exp (-t) / (1 - exp (-t))

private lemma exp_neg_natCast_mul (m : ℕ) (t : ℝ) : exp (-((m : ℝ) * t)) = exp (-t) ^ m := by
  rw [← exp_nat_mul]
  ring_nf

/-- Splitting off the first `n` terms of the geometric series. -/
private lemma gaussDigammaKernel_eq (n : ℕ) {t : ℝ} (ht : 0 < t) :
    gaussDigammaKernel t =
      t⁻¹ * (exp (-(1 * t)) - exp (-(((n + 1 : ℕ) : ℝ) * t))) -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) +
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t))) := by
  have hq : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hd : 1 - exp (-t) ≠ 0 := by linarith
  simp only [exp_neg_natCast_mul, one_mul, gaussDigammaKernel]
  set q := exp (-t)
  have hgeom : (∑ i ∈ Finset.range n, q ^ (i + 1)) * (1 - q) = q - q ^ (n + 1) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  have hsum : ∑ i ∈ Finset.range n, q ^ (i + 1) = (q - q ^ (n + 1)) / (1 - q) := by
    rw [← hgeom, mul_div_cancel_right₀ _ hd]
  rw [hsum]
  field_simp
  ring

private lemma integrableOn_exp_neg_natCast_mul (m : ℕ) (hm : 0 < m) :
    IntegrableOn (fun t : ℝ ↦ exp (-((m : ℝ) * t))) (Ioi 0) := by
  simpa [neg_mul] using integrableOn_exp_mul_Ioi (a := -(m : ℝ)) (by simp [hm]) 0

private lemma integral_exp_neg_natCast_mul (m : ℕ) (hm : 0 < m) :
    ∫ t in Ioi (0 : ℝ), exp (-((m : ℝ) * t)) = 1 / m := by
  have := integral_exp_mul_Ioi (a := -(m : ℝ)) (by simp [hm]) 0
  simp only [neg_mul, mul_zero, exp_zero] at this
  rw [this]
  field_simp

private lemma integrableOn_gaussDigammaKernel : IntegrableOn gaussDigammaKernel (Ioi 0) := by
  refine Integrable.mono' (integrableOn_exp_neg_Ioi 0) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have hd : 1 - exp (-t) ≠ 0 := by
      have : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
      linarith
    have ht' : t ≠ 0 := ht.ne'
    unfold gaussDigammaKernel
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_)
    have ht : (0 : ℝ) < t := ht
    obtain ⟨h1, h2⟩ := digamma_remainder_bounds ht
    have : gaussDigammaKernel t = exp (-t) * (1 / t - 1 / (1 - exp (-t))) := by
      unfold gaussDigammaKernel; ring
    rw [this, norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
    have : |1 / t - 1 / (1 - exp (-t))| ≤ 1 := abs_le.mpr ⟨h1, by linarith⟩
    nlinarith [exp_pos (-t)]

private lemma integral_gaussDigammaKernel :
    ∫ t in Ioi (0 : ℝ), gaussDigammaKernel t = -eulerMascheroniConstant := by
  set I := ∫ t in Ioi (0 : ℝ), gaussDigammaKernel t
  -- The remainder after `n` geometric terms.
  let R : ℕ → ℝ := fun n ↦
    ∫ t in Ioi (0 : ℝ), exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))
  have hRint : ∀ n : ℕ, IntegrableOn
      (fun t ↦ exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) (Ioi 0) := by
    intro n
    refine Integrable.mono' (integrableOn_exp_neg_natCast_mul (n + 1) n.succ_pos) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht : (0 : ℝ) < t := ht
      have hd : 1 - exp (-t) ≠ 0 := by
        have : exp (-t) < 1 := exp_lt_one_iff.mpr (by linarith)
        linarith
      have ht' : t ≠ 0 := ht.ne'
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := assumption)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_)
      obtain ⟨h1, h2⟩ := digamma_remainder_bounds (show (0 : ℝ) < t from ht)
      rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
      have : |1 / t - 1 / (1 - exp (-t))| ≤ 1 := abs_le.mpr ⟨h1, by linarith⟩
      nlinarith [exp_pos (-(((n + 1 : ℕ) : ℝ) * t))]
  have hRle : ∀ n : ℕ, ‖R n‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    calc ‖R n‖ ≤ ∫ t in Ioi (0 : ℝ), exp (-(((n + 1 : ℕ) : ℝ) * t)) := by
          refine norm_integral_le_of_norm_le (integrableOn_exp_neg_natCast_mul (n + 1) n.succ_pos)
            ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht ↦ ?_))
          obtain ⟨h1, h2⟩ := digamma_remainder_bounds (show (0 : ℝ) < t from ht)
          rw [norm_mul, Real.norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs]
          have : |1 / t - 1 / (1 - exp (-t))| ≤ 1 := abs_le.mpr ⟨h1, by linarith⟩
          nlinarith [exp_pos (-(((n + 1 : ℕ) : ℝ) * t))]
      _ = 1 / ((n : ℝ) + 1) := by
          rw [integral_exp_neg_natCast_mul (n + 1) n.succ_pos]; push_cast; rfl
  -- The finite expansion of the integral.
  have hexp : ∀ n : ℕ, I = -(harmonic n - log ((n : ℝ) + 1)) + R n := by
    intro n
    have hsumint : ∀ i ∈ Finset.range n,
        IntegrableOn (fun t : ℝ ↦ exp (-(((i + 1 : ℕ) : ℝ) * t))) (Ioi 0) :=
      fun i _ ↦ integrableOn_exp_neg_natCast_mul (i + 1) i.succ_pos
    have hsumint' : IntegrableOn
        (fun t : ℝ ↦ ∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) (Ioi 0) :=
      integrable_finsetSum _ hsumint
    let Fr : ℝ → ℝ := fun t ↦ t⁻¹ * (exp (-(1 * t)) - exp (-(((n + 1 : ℕ) : ℝ) * t)))
    have hFr : EqOn Fr (fun t ↦ gaussDigammaKernel t +
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) -
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) (Ioi 0) := by
      intro t ht
      simp only [Fr, gaussDigammaKernel_eq n (show (0 : ℝ) < t from ht)]
      ring
    have hFrint : IntegrableOn Fr (Ioi 0) :=
      ((integrableOn_gaussDigammaKernel.add hsumint').sub (hRint n)).congr_fun hFr.symm
        measurableSet_Ioi
    have hFrval : ∫ t in Ioi (0 : ℝ), Fr t = log ((n : ℝ) + 1) := by
      have hc : Continuous fun x : ℝ ↦ exp (-x) := by fun_prop
      have hL : Tendsto (fun x : ℝ ↦ exp (-x)) (𝓝[>] 0) (𝓝 1) := by
        have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      have := Frullani.integral_Ioi_eq (f := fun x : ℝ ↦ exp (-x)) (a := 1)
        (b := ((n + 1 : ℕ) : ℝ)) (hc.continuousOn.locallyIntegrableOn measurableSet_Ioi)
        one_pos (by positivity) hL tendsto_exp_neg_atTop_nhds_zero hFrint
      simpa [Fr] using this
    have hsumval : ∫ t in Ioi (0 : ℝ), ∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t)) =
        harmonic n := by
      rw [integral_finsetSum _ hsumint, harmonic, Rat.cast_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [integral_exp_neg_natCast_mul (i + 1) i.succ_pos]
      push_cast
      ring
    have hI : I = ∫ t in Ioi (0 : ℝ), (Fr t -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) +
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ gaussDigammaKernel_eq n ht
    have e1 : ∫ t in Ioi (0 : ℝ), (Fr t -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))) +
        exp (-(((n + 1 : ℕ) : ℝ) * t)) * (1 / t - 1 / (1 - exp (-t)))) =
        (∫ t in Ioi (0 : ℝ), (Fr t -
          (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t))))) + R n :=
      integral_add (hFrint.sub hsumint') (hRint n)
    have e2 : ∫ t in Ioi (0 : ℝ), (Fr t -
        (∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t)))) =
        (∫ t in Ioi (0 : ℝ), Fr t) -
          ∫ t in Ioi (0 : ℝ), ∑ i ∈ Finset.range n, exp (-(((i + 1 : ℕ) : ℝ) * t)) :=
      integral_sub hFrint hsumint'
    rw [hI, e1, e2, hFrval, hsumval]
    ring
  -- Let `n → ∞`.
  have hR0 : Tendsto R atTop (𝓝 0) :=
    squeeze_zero_norm hRle tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ ↦ -(harmonic n - log ((n : ℝ) + 1)) + R n) atTop
      (𝓝 (-eulerMascheroniConstant + 0)) :=
    tendsto_harmonic_sub_log_add_one.neg.add hR0
  rw [add_zero] at hlim
  refine tendsto_nhds_unique ?_ hlim
  simp_rw [← hexp]
  exact tendsto_const_nhds

end GaussDigamma

/-- Paper: Proposition B.4.2.1, p. 616. At unit scale and unit gamma
arguments the integrable kernel for the constant test gives twice the digamma value at one.
Deviation: This is a sanity check for the corrected kernel. -/
theorem heckeArchimedeanDigammaKernel_one :
    let K := heckeArchimedeanDigammaKernel 1 1 1 (fun _ ↦ 1)
    IntegrableOn K (Ioi 0) ∧
      (∫ t in Ioi (0 : ℝ), K t) = -2 * (Real.eulerMascheroniConstant : ℂ) := by
  intro K
  have hK : K = fun t ↦ ((2 * gaussDigammaKernel t : ℝ) : ℂ) := by
    funext t
    simp only [K, heckeArchimedeanDigammaKernel, gaussDigammaKernel]
    push_cast
    simp only [neg_mul, one_mul]
    ring
  rw [hK]
  simp only []
  refine ⟨(integrableOn_gaussDigammaKernel.const_mul 2).ofReal, ?_⟩
  rw [integral_complex_ofReal, integral_const_mul, integral_gaussDigammaKernel]
  push_cast
  ring

local notation "circleToComplex" =>
  (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)

local notation "localChart(" w ", " χ ")" =>
  quasiCharacterNormTwist
    ((Units.map nnNormHom.toMonoidHom) ^ (InfinitePlace.mult w) :
      (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) (continuous_infiniteLocalModule w) (ContinuousMonoidHom.comp circleToComplex χ)

/-- A real norm twist adds its coordinate to the radial exponent and preserves parity. -/
private theorem realHeckeArchimedean_mellinLogDeriv_twist (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (z : ℂ) (k : Fin 2)
    (hχ : ∀ x : ℝˣ,
      (χ (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) : ℂ) =
        (‖(x : ℝ)‖ : ℂ) ^ z * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ k.val) :
    infiniteLocalEulerFactor w ∘ localChart(w, χ) = fun s ↦ Complex.Gammaℝ (s + (z + k.val)) := by
  funext s
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
  have h := (realLocalEulerParameters w hw (localChart(w, χ) s)).unique
    (realLocalEulerParameters w hw _).exists.choose_spec (y₂ := (s + z, k)) (by
      intro x
      have hn : ‖e (x : ℝ)‖ = ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero e) (x : ℝ)
      change (χ (Units.map e.toMonoidHom x) : ℂ) * ((‖e (x : ℝ)‖ ^ w.mult : ℝ) : ℂ) ^ s = _
      rw [hχ, hn, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))]
      simp only [InfinitePlace.mult, hw, ite_true, pow_one]
      ac_rfl)
  simp only [Function.comp_apply, infiniteLocalEulerFactor, hw, ↓reduceDIte, h, add_assoc]

/-- Unitarity forces the exponent to be imaginary. Inverting the character negates that
exponent and leaves its sign character fixed. -/
private theorem realHeckeArchimedean_mellinLogDeriv_parameters (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) :
    let p := (realLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose
    p.1.re = 0 ∧
      (infiniteLocalEulerFactor w ∘ localChart(w, χ) = fun s ↦ Complex.Gammaℝ (s + (p.1 + p.2.val))) ∧
      (infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹) = fun s ↦ Complex.Gammaℝ (s + (-p.1 + p.2.val))) := by
  intro p
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
  have hp := (realLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose_spec
  change ∀ x : ℝˣ, (χ (Units.map e.toMonoidHom x) : ℂ) =
    (‖(x : ℝ)‖ : ℂ) ^ p.1 * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ p.2.val at hp
  refine ⟨?_, realHeckeArchimedean_mellinLogDeriv_twist w hw χ _ _ hp,
    realHeckeArchimedean_mellinLogDeriv_twist w hw χ⁻¹ _ _ ?_⟩
  · have h := congrArg norm (hp (Units.mk0 (2 : ℝ) (by norm_num)))
    have hpow : ‖((2 : ℝ) : ℂ) ^ p.1‖ = 1 := by simpa using h.symm
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at hpow
    exact (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num)).mp
      (hpow.trans (Real.rpow_zero _).symm)
  · intro x
    change ((χ (Units.map e.toMonoidHom x) : ℂ))⁻¹ = _
    rw [hp, mul_inv, Complex.cpow_neg]
    split_ifs <;> simp [← inv_pow]

/-- The Gauss difference times a Schwartz trace is absolutely integrable in both variables.
Its bound uses the first absolute moment of the trace. -/
private theorem realHeckeArchimedean_mellinLogDeriv_domination (W : 𝓢(ℝ, ℂ))
    (a : ℝ) (b : ℂ) (hab : 0 < a + b.re) :
    Integrable (fun p : ℝ × ℝ ↦ W p.1 * gaussDigammaDifferenceKernel 1
      (((a : ℂ) + (p.1 : ℂ) * Complex.I + b) / 2) p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  let u := (a + b.re) / 2
  let m := min 1 u
  let C := |1 - u| + |b.im|
  have hm : 0 < m := lt_min one_pos (half_pos hab)
  have hExp := integrableOn_exp_mul_Ioi (neg_neg_of_pos hm) 0
  have hxExp : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-m * x)) (Ioi 0) := by
    simpa using (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) one_pos hm)
  have hEnv : IntegrableOn (fun x : ℝ ↦ (1 + x) * Real.exp (-m * x)) (Ioi 0) := by
    simpa only [Pi.add_def, add_mul, one_mul] using hExp.add hxExp
  have hMoment : Integrable (fun y : ℝ ↦ (C + |y|) * ‖W y‖) := by
    simpa only [Pi.add_def, add_mul, Real.norm_eq_abs, pow_one] using
      (W.integrable.norm.const_mul C).add (W.integrable_pow_mul volume 1)
  refine (hMoment.mul_prod hEnv).mono'
    (Measurable.aestronglyMeasurable (by unfold gaussDigammaDifferenceKernel; fun_prop)) ?_
  have hx : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume.restrict (Ioi 0))), p.2 ∈ Ioi 0 :=
    (Measure.ae_prod_mem_iff_ae_ae_mem (measurable_snd measurableSet_Ioi)).mpr
      (Eventually.of_forall fun _ : ℝ ↦ ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi)
  filter_upwards [hx] with ⟨y, x⟩ hx
  have hxpos : 0 < x := hx
  have he : ((a : ℂ) + (y : ℂ) * Complex.I + b) / 2 =
      (u : ℂ) + ((y + b.im) / 2 : ℝ) * Complex.I := by
    apply Complex.ext <;> simp [u, add_div, Complex.div_ofNat_re, Complex.div_ofNat_im]
  have hIm : |(y + b.im) / 2| ≤ |y| + |b.im| := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_add_le y b.im, abs_nonneg (y + b.im)]
  rw [norm_mul, he]
  have h := norm_gaussDigammaDifferenceKernel_le (d := 1) (u := u) (v := (y + b.im) / 2)
    one_pos hxpos
  simp only [div_one] at h
  change _ ≤ ((C + |y|) * ‖W y‖) * ((1 + x) * Real.exp (-m * x))
  rw [mul_assoc, mul_left_comm (C + |y|)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  dsimp [C]
  linarith

/-- A Mellin trace of an exponentially decaying test is Schwartz. Mellin inversion
evaluates its exponentially twisted integral at every log coordinate. -/
private theorem realHeckeArchimedean_mellinLogDeriv_trace (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)
    (a : ℝ) :
    let s := fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * Complex.I
    ∃ W : 𝓢(ℝ, ℂ), (∀ y, W y = logMellin f (s y)) ∧ ∀ x : ℝ,
      (∫ y : ℝ, W y * Complex.exp (-s y * (x : ℂ))) / (2 * (Real.pi : ℂ)) = f x := by
  intro s
  obtain ⟨W, hW⟩ := exists_schwartz_verticalTrace_mellin_of_weighted_schwartz f (a - 1) (a + 1)
    (by linarith) (fun c _ ↦ exponentialDecay_weighted_schwartz f hf c) a ⟨by linarith, by linarith⟩
  refine ⟨W, congrFun hW, fun x ↦ ?_⟩
  have hi : Complex.VerticalIntegrable (logMellin f) a :=
    W.integrable.congr (Eventually.of_forall (congrFun hW))
  have hx := Real.exp_pos x
  have he := mellinInv_mellin_eq a (fun t ↦ f (Real.log t)) hx
    (mellinConvergent_of_exponentialDecay f hf a) hi
    (f.continuous.continuousAt.comp (Real.continuousAt_log hx.ne'))
  rw [Real.log_exp] at he
  rw [← he, mellinInv, Complex.real_smul]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [div_eq_inv_mul, one_div]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le, Real.log_exp, smul_eq_mul, mul_comm (x : ℂ)]
  rw [mul_comm, congrFun hW y]

/-- Reversing the ordinate in Mellin inversion gives the reflected trace.
The sample at log coordinate `x` acquires the factor `exp (-x)`. -/
private theorem realHeckeArchimedean_mellinLogDeriv_reflect (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)
    (a : ℝ) :
    let s := fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * Complex.I
    ∃ W : 𝓢(ℝ, ℂ), (∀ y, W y = logMellin f (1 - s y)) ∧ ∀ x : ℝ,
      (∫ y : ℝ, W y * Complex.exp (-s y * (x : ℂ))) / (2 * (Real.pi : ℂ)) =
        Complex.exp (-(x : ℂ)) * f (-x) := by
  intro s
  obtain ⟨T, hT, hinv⟩ := realHeckeArchimedean_mellinLogDeriv_trace f hf (1 - a)
  obtain ⟨R, hR, _⟩ := exists_schwartzLogReflection
  refine ⟨R T, fun y ↦ ?_, fun x ↦ ?_⟩
  · rw [hR, hT]
    congr 1
    dsimp [s]
    push_cast
    ring
  · rw [← hinv (-x), ← mul_div_assoc, ← integral_const_mul]
    congr 1
    rw [← integral_neg_eq_self (fun y : ℝ ↦ R T y * Complex.exp (-s y * (x : ℂ)))]
    apply integral_congr_ae
    filter_upwards with y
    rw [hR, neg_neg, mul_left_comm, ← Complex.exp_add]
    congr 2
    dsimp [s]
    push_cast
    ring

local notation "gaussSample(" b ", " g ", " t ")" =>
  (((g) 0 * (Real.exp (-(t)) : ℂ) - (g) ((t) / 2) * Complex.exp (-(b) * ((t) : ℂ) / 2)) /
    (1 - (Real.exp (-(t)) : ℂ)))

/-- Evaluate one shifted real gamma factor against a Schwartz trace. The Gauss
difference stays together under Fubini, including at the singular endpoint. -/
private theorem realHeckeArchimedean_mellinLogDeriv_leg (W : 𝓢(ℝ, ℂ)) (g : ℝ → ℂ)
    (a : ℝ) (b : ℂ) (hab : 0 < a + b.re)
    (hinv : ∀ x : ℝ, (∫ y : ℝ, W y * Complex.exp
      (-((a : ℂ) + (y : ℂ) * Complex.I) * (x : ℂ))) / (2 * (Real.pi : ℂ)) = g x) :
    let s := fun y : ℝ ↦ (a : ℂ) + (y : ℂ) * Complex.I
    let L := fun y ↦ W y * logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) (s y)
    Integrable L ∧ IntegrableOn (fun t ↦ gaussSample(b, g, t)) (Ioi 0) ∧
      (∫ y, L y) / (2 * (Real.pi : ℂ)) =
        ((∫ t in Ioi (0 : ℝ), gaussSample(b, g, t)) -
          ((Real.eulerMascheroniConstant : ℂ) + (Real.log Real.pi : ℂ)) * g 0) / 2 := by
  intro s L
  let c : ℂ := 2 * Real.pi
  let A : ℂ := Real.eulerMascheroniConstant + (Real.log Real.pi : ℂ)
  let D (y t : ℝ) := gaussDigammaDifferenceKernel 1 ((s y + b) / 2) t
  have hW : Integrable (W : ℝ → ℂ) := W.integrable
  have hJ : Integrable (fun p : ℝ × ℝ ↦ W p.1 * D p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) :=
    realHeckeArchimedean_mellinLogDeriv_domination W a b hab
  have h0 : (∫ y, W y) / c = g 0 := by simpa [c] using hinv 0
  have hslice (t : ℝ) : (∫ y, W y * D y t) / c = gaussSample(b, g, t) := by
    let E : ℂ := Real.exp (-t)
    let B := Complex.exp (-b * (t : ℂ) / 2)
    let P (y : ℝ) := Complex.exp (-s y * ((t / 2 : ℝ) : ℂ))
    have hP : Integrable (fun y ↦ W y * P y) := by
      refine (hW.norm.mul_const (Real.exp (-a * (t / 2)))).mono'
        (Continuous.aestronglyMeasurable (by dsimp [P, s]; fun_prop)) ?_
      filter_upwards with y
      simp [P, s, Complex.norm_exp, Complex.mul_re]
    have hsample : (∫ y, W y * P y) / c = g (t / 2) := hinv _
    have hpoint (y : ℝ) : W y * D y t = (W y * E - (W y * P y) * B) / (1 - E) := by
      have hsplit : Complex.exp (-((s y + b) / 2) * (t : ℂ)) = P y * B := by
        change _ = Complex.exp _ * Complex.exp _
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp only [D, gaussDigammaDifferenceKernel, Complex.ofReal_one, neg_one_mul, hsplit, E,
        Complex.ofReal_exp, Complex.ofReal_neg]
      ring
    simp_rw [hpoint]
    rw [integral_div, integral_sub (hW.mul_const E) (hP.mul_const B), integral_mul_const,
      integral_mul_const]
    change ((_ - _) / (1 - E)) / c = (g 0 * E - g (t / 2) * B) / (1 - E)
    rw [← h0, ← hsample]
    ring
  have hsampleInt : IntegrableOn (fun t ↦ gaussSample(b, g, t)) (Ioi 0) :=
    (hJ.integral_prod_right.div_const c).congr (Eventually.of_forall hslice)
  have hL (y : ℝ) : L y = ((∫ t in Ioi (0 : ℝ), W y * D y t) - W y * A) / 2 := by
    have hz : 0 < ((s y + b) / 2).re := by simpa [s, Complex.div_ofNat_re] using half_pos hab
    have hψ := (integral_gaussDigammaDifferenceKernel (d := 1) (w := (s y + b) / 2)
      one_pos (by simpa using hz)).2
    simp only [Complex.ofReal_one, div_one, Complex.digamma_one] at hψ
    dsimp only [L]
    rw [realHeckeArchimedean_mellinLogDeriv_gamma b (s y) hz, integral_const_mul]
    change _ = (W y * (∫ t in Ioi (0 : ℝ), gaussDigammaDifferenceKernel 1 ((s y + b) / 2) t) - _) / 2
    rw [hψ]
    dsimp [A]
    ring
  have hline := hJ.integral_prod_left
  refine ⟨(hline.sub (hW.mul_const A)).div_const 2 |>.congr (Eventually.of_forall fun y ↦ (hL y).symm),
    hsampleInt, ?_⟩
  change (∫ y, L y) / c = ((∫ t in Ioi (0 : ℝ), gaussSample(b, g, t)) - A * g 0) / 2
  simp_rw [hL]
  rw [integral_div, integral_sub hline (hW.mul_const A), integral_mul_const, integral_integral_swap hJ]
  have hsampleTotal : (∫ t in Ioi (0 : ℝ), ∫ y, W y * D y t) / c =
      ∫ t in Ioi (0 : ℝ), gaussSample(b, g, t) := by
    rw [← integral_div]
    exact integral_congr_ae (Eventually.of_forall hslice)
  rw [← hsampleTotal, ← h0]
  ring

/-- Paper: Proposition B.4.2.1, p. 616. The two real local contour terms equal
the integral of the digamma kernel and the real gamma prefactor contribution.
Deviation: The integral converges at both endpoints and includes sign parity. -/
theorem realHeckeArchimedean_mellinLogDeriv (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (a : ℝ) (_ha : 1 < a) :
    let p := (realLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose
    let K := heckeArchimedeanDigammaKernel (1 / 2)
      ((p.1 + p.2.val) / 2) ((1 - p.1 + p.2.val) / 2) f
    let H := fun s ↦ logMellin f s * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ)) s +
      logMellin f (1 - s) * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹)) s
    Complex.VerticalIntegrable H a ∧ IntegrableOn K (Ioi 0) ∧
      verticalLineIntegral H a / twoPiI =
        (∫ t in Ioi (0 : ℝ), K t) - (Real.log Real.pi : ℂ) * f 0 := by
  intro p K H
  let b : ℂ := p.1 + p.2.val
  let b' : ℂ := -p.1 + p.2.val
  let g (x : ℝ) := Complex.exp (-(x : ℂ)) * f (-x)
  have hg0 : g 0 = f 0 := by simp [g]
  obtain ⟨hre, hχ, hχinv⟩ := realHeckeArchimedean_mellinLogDeriv_parameters w hw χ
  change p.1.re = 0 at hre
  have hb : 0 < a + b.re := by simp [b, hre]; positivity
  have hb' : 0 < a + b'.re := by simp [b', hre]; positivity
  obtain ⟨W, hW, hWinv⟩ := realHeckeArchimedean_mellinLogDeriv_trace f _hf a
  obtain ⟨V, hV, hVinv⟩ := realHeckeArchimedean_mellinLogDeriv_reflect f _hf a
  obtain ⟨hD, hKD, hDval⟩ := realHeckeArchimedean_mellinLogDeriv_leg W f a b hb hWinv
  obtain ⟨hR, hKR, hRval⟩ := realHeckeArchimedean_mellinLogDeriv_leg V g a b' hb' hVinv
  let s (y : ℝ) := (a : ℂ) + (y : ℂ) * Complex.I
  have hline (y : ℝ) : H (s y) =
      W y * logDeriv (fun z ↦ Complex.Gammaℝ (z + b)) (s y) +
        V y * logDeriv (fun z ↦ Complex.Gammaℝ (z + b')) (s y) := by
    rw [hW, hV]
    simp only [H, hχ, hχinv, b, b', p, s]
  have hK (t : ℝ) : K t = (gaussDigammaKernel t : ℂ) * f 0 +
      (gaussSample(b, f, t) + gaussSample(b', g, t)) / 2 := by
    have hsample : g (t / 2) * Complex.exp (-b' * (t : ℂ) / 2) =
        f (-(t / 2)) * Complex.exp (-((1 - p.1 + p.2.val) / 2) * (t : ℂ)) := by
      dsimp only [g]
      rw [mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
      congr 2
      dsimp [b']
      push_cast
      ring
    simp only [K, heckeArchimedeanDigammaKernel, gaussDigammaKernel, hg0, hsample, b,
      one_div_mul_eq_div]
    push_cast
    ring_nf
  have hbase : IntegrableOn (fun t ↦ (gaussDigammaKernel t : ℂ) * f 0) (Ioi 0) :=
    integrableOn_gaussDigammaKernel.ofReal.mul_const _
  have hsum : IntegrableOn (fun t ↦ gaussSample(b, f, t) + gaussSample(b', g, t)) (Ioi 0) :=
    hKD.add hKR
  have hvi : Complex.VerticalIntegrable H a :=
    (hD.add hR).congr (Eventually.of_forall fun y ↦ (hline y).symm)
  refine ⟨hvi, (hbase.add (hsum.div_const 2)).congr
    (Eventually.of_forall fun t ↦ (hK t).symm), ?_⟩
  change (Complex.I * ∫ y, H (s y)) / twoPiI = _
  rw [mul_comm (2 * (Real.pi : ℂ)) Complex.I, mul_div_mul_left _ _ Complex.I_ne_zero]
  simp_rw [hline, hK]
  rw [integral_add hD hR, add_div, hDval, hRval,
    integral_add hbase (hsum.div_const 2), integral_div, integral_add hKD hKR,
    integral_mul_const, integral_complex_ofReal, integral_gaussDigammaKernel, hg0]
  push_cast
  ring

/-- Mellin inversion on the line of abscissa `a`, together with its first absolute moment. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_trace
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a : ℝ) :
    let s := fun y : ℝ ↦ (a : ℂ) + y * Complex.I
    let W := fun y ↦ logMellin f (s y)
    Continuous W ∧ Integrable (fun y ↦ ‖W y‖ * (1 + |y|)) ∧
      ∀ x : ℝ, (∫ y, W y * Complex.exp (-s y * x)) / (2 * (Real.pi : ℂ)) = f x := by
  intro s W
  obtain ⟨g, hg⟩ := exists_schwartz_verticalTrace_mellin_of_weighted_schwartz f
    (a - 1) (a + 1) (by linarith) (fun σ _ ↦ exponentialDecay_weighted_schwartz f hf σ)
    a ⟨by linarith, by linarith⟩
  change (g : ℝ → ℂ) = W at hg
  refine ⟨hg ▸ g.continuous, ?_, fun x ↦ ?_⟩
  · rw [← hg]
    apply (g.integrable.norm.add (g.integrable_pow_mul volume 1)).congr
    filter_upwards with y
    simp [Real.norm_eq_abs, add_mul, mul_comm]
  · have hgInt : Complex.VerticalIntegrable (logMellin f) a := by
      change Integrable W volume
      rw [← hg]
      exact g.integrable
    have hi := mellinInv_mellin_eq a (fun t : ℝ ↦ f (Real.log t)) (Real.exp_pos x)
      (mellinConvergent_of_exponentialDecay f hf a) hgInt
      (f.continuous.continuousAt.comp (Real.continuousAt_log (Real.exp_pos x).ne'))
    have hpow (y : ℝ) : ((Real.exp x : ℝ) : ℂ) ^ (-s y) = Complex.exp (-s y * x) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
        ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]
    simp only [mellinInv, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Real.log_exp, smul_eq_mul] at hi
    change 1 / (2 * (Real.pi : ℂ)) * (∫ y, ((Real.exp x : ℝ) : ℂ) ^ (-s y) * W y) = f x at hi
    simpa only [hpow, mul_comm (Complex.exp _) _, div_eq_inv_mul, one_mul, mul_one] using hi

open Complex in
/-- The logarithmic derivative of the translated complex gamma factor, including its prefactor. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_gamma
    (β s : ℂ) (hs : 0 < (s + β).re) :
    logDeriv (fun z ↦ Gammaℂ (z + β) / 2) s =
      -((Real.log (2 * Real.pi) : ℂ) + Real.eulerMascheroniConstant) +
        ∫ x in Ioi (0 : ℝ), gaussDigammaDifference 1 (s + β) x := by
  let B : ℂ := (2 * Real.pi : ℝ)
  have hB : B ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hlog : log B = (Real.log (2 * Real.pi) : ℂ) :=
    (ofReal_log (by positivity : 0 ≤ 2 * Real.pi)).symm
  have heq : (fun z ↦ Gammaℂ (z + β) / 2) =
      (fun z ↦ B ^ (-(z + β)) * Gamma (z + β)) := by
    funext z
    simp only [Gammaℂ_def, B, ofReal_mul, ofReal_ofNat]
    ring
  have harg := (hasDerivAt_id' s).add_const β
  have hP := harg.neg.const_cpow (Or.inl hB)
  change HasDerivAt (fun z : ℂ ↦ B ^ (-(z + β))) (B ^ (-(s + β)) * log B * -1) s at hP
  have hP0 : B ^ (-(s + β)) ≠ 0 := by simp [cpow_eq_zero_iff, hB]
  have hreg (n : ℕ) : s + β ≠ -(n : ℂ) := by
    intro he
    simp [he] at hs
    exact (Nat.cast_nonneg n).not_gt hs
  have hG := (hasDerivAt_Gamma_of_re_pos hs).differentiableAt
  rw [heq, logDeriv_fun_mul (f := fun z ↦ B ^ (-(z + β))) (g := fun z ↦ Gamma (z + β))
    s hP0 (Gamma_ne_zero_of_re_pos hs) hP.differentiableAt (hG.comp s harg.differentiableAt),
    harg.logDeriv_Gamma hreg, one_mul, logDeriv_apply, hP.deriv]
  have hv := (integral_gaussDigammaDifference (w := s + β) (d := 1) one_pos (by simpa using hs)).2
  simp only [ofReal_one, div_one, digamma_one] at hv
  rw [hv, hlog]
  field_simp
  ring

open Complex in
/-- Evaluate one gamma contour using an ordinate weight whose inverse transform is `g`.
The joint first-moment bound permits Fubini before the two singular terms are separated. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_leg
    (a : ℝ) (ha : 0 < a) (β : ℂ) (hβ : 0 ≤ β.re) (W g : ℝ → ℂ)
    (hW : Continuous W) (hM : Integrable (fun y ↦ ‖W y‖ * (1 + |y|)))
    (hinv : ∀ x : ℝ, (∫ y : ℝ, W y * exp (-((a : ℂ) + y * I) * x)) /
      (2 * (Real.pi : ℂ)) = g x) :
    let s := fun y : ℝ ↦ (a : ℂ) + y * I
    let L := fun y ↦ W y * logDeriv (fun z ↦ Gammaℂ (z + β) / 2) (s y)
    let K := fun x : ℝ ↦ (g 0 * exp (-(x : ℂ)) - exp (-β * x) * g x) / (1 - exp (-(x : ℂ)))
    Integrable L ∧ IntegrableOn K (Ioi 0) ∧
      (∫ y, L y) / (2 * (Real.pi : ℂ)) =
        -((Real.log (2 * Real.pi) : ℂ) + Real.eulerMascheroniConstant) * g 0 + ∫ x in Ioi 0, K x := by
  intro s L K
  let c := 2 * (Real.pi : ℂ)
  let A := -((Real.log (2 * Real.pi) : ℂ) + Real.eulerMascheroniConstant)
  let H := fun y x ↦ gaussDigammaDifference 1 (s y + β) x
  have hJ : Integrable (fun p : ℝ × ℝ ↦ W p.1 * H p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    simpa only [H, s, Complex.re_add_im] using
      integrable_mul_gaussDigammaDifference (τ := β.im) ha one_pos hβ hW.measurable hM
  have hWi : Integrable W := hM.mono' hW.aestronglyMeasurable (Eventually.of_forall fun y ↦
    le_mul_of_one_le_right (norm_nonneg _) (by linarith [abs_nonneg y]))
  have hzero : (∫ y, W y) / c = g 0 := by simpa [c] using hinv 0
  have hslice (x : ℝ) : (∫ y, W y * H y x) / c = K x := by
    have hExp (y : ℝ) : exp (-(s y + β) * x) = exp (-β * x) * exp (-s y * x) := by
      rw [← Complex.exp_add]; congr 1; ring
    have hXi : Integrable (fun y ↦ W y * exp (-s y * x)) := by
      refine (hWi.norm.mul_const (Real.exp (-a * x))).mono'
        ((hW.mul (by dsimp [s]; fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun y ↦ ?_)
      simp [Complex.norm_exp, s, mul_re]
    have hpoint (y : ℝ) : W y * H y x = (W y * exp (-(x : ℂ)) -
        exp (-β * x) * (W y * exp (-s y * x))) / (1 - exp (-(x : ℂ))) := by
      simp only [H, gaussDigammaDifference, ofReal_one, neg_one_mul, hExp, div_eq_mul_inv]
      ring
    simp_rw [hpoint]
    rw [integral_div, integral_sub (hWi.mul_const _) (hXi.const_mul _), integral_mul_const,
      integral_const_mul]
    change _ = ((g 0) * _ - _ * g x) / _
    rw [← hzero, ← hinv x]
    dsimp only [c, s]
    ring
  have hK := (hJ.integral_prod_right.div_const c).congr (Eventually.of_forall hslice)
  have hline (y : ℝ) : L y = W y * A + ∫ x in Ioi (0 : ℝ), W y * H y x := by
    have hs : 0 < (s y + β).re := by simpa [s, mul_re] using add_pos_of_pos_of_nonneg ha hβ
    simp only [L, complexHeckeArchimedean_mellinLogDeriv_gamma β (s y) hs, mul_add,
      integral_const_mul, H, A]
  refine ⟨?_, hK, ?_⟩
  · simp_rw [show L = _ from funext hline]
    exact (hWi.mul_const A).add hJ.integral_prod_left
  · simp_rw [hline]
    rw [integral_add (hWi.mul_const A) hJ.integral_prod_left, integral_mul_const, add_div,
      mul_div_right_comm, hzero, mul_comm (g 0), integral_integral_swap hJ, ← integral_div]
    change _ + (∫ x in Ioi (0 : ℝ), (∫ y, W y * H y x) / c) = _
    simp_rw [hslice, A]

/-- A norm twist shifts the radial exponent and preserves the angular weight. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_factor
    (w : InfinitePlace F) (hw : w.IsComplex) (χ : PontryaginDual w.Completionˣ)
    (z : ℂ) (r : ℤ) (h : ∀ x : ℂˣ, (χ (Units.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom x) : ℂ) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ z * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ r) :
    infiniteLocalEulerFactor w ∘ localChart(w, χ) =
      fun s ↦ Complex.Gammaℂ (s + (z + (r.natAbs : ℂ) / 2)) / 2 := by
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
  have hn (x : ℂ) : ‖e x‖ = ‖x‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero
      (map_zero e) x
  have hnreal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
  funext s
  let hpar := complexLocalEulerParameters w hw (localChart(w, χ) s)
  have hp : hpar.exists.choose = (s + z, r) := by
    apply hpar.unique hpar.exists.choose_spec
    intro x
    change (χ (Units.map e.toMonoidHom x) : ℂ) * ((‖e (x : ℂ)‖ ^ w.mult : ℝ) : ℂ) ^ s = _
    have hx : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero))
    rw [h x, hn, InfinitePlace.mult, ite_eq_right hnreal, Complex.cpow_add _ _ hx]
    ac_rfl
  simp only [Function.comp_apply, infiniteLocalEulerFactor, hnreal, ↓reduceDIte, hp, ← add_assoc]

/-- Inverting the reflected Mellin weight adds the factor `exp (-x)` to the negative sample. -/
private theorem complexHeckeArchimedean_mellinLogDeriv_reflect
    (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a : ℝ) :
    let s := fun y : ℝ ↦ (a : ℂ) + y * Complex.I
    let W := fun y ↦ logMellin f (1 - s y)
    Continuous W ∧ Integrable (fun y ↦ ‖W y‖ * (1 + |y|)) ∧
      ∀ x : ℝ, (∫ y, W y * Complex.exp (-s y * x)) / (2 * (Real.pi : ℂ)) =
        Complex.exp (-(x : ℂ)) * f (-x) := by
  intro s W
  let u := fun y : ℝ ↦ ((1 - a : ℝ) : ℂ) + y * Complex.I
  have hneg (y : ℝ) : 1 - s y = u (-y) := by dsimp [s, u]; push_cast; ring
  obtain ⟨hc, hm, hi⟩ := complexHeckeArchimedean_mellinLogDeriv_trace f hf (1 - a)
  change Continuous (fun y ↦ logMellin f (u y)) at hc
  have heq : W = fun y ↦ logMellin f (u (-y)) := funext fun y ↦ congrArg (logMellin f) (hneg y)
  rw [heq]
  refine ⟨hc.comp continuous_neg, ?_, fun x ↦ ?_⟩
  · simpa only [abs_neg] using hm.comp_neg
  · have hphase (y : ℝ) : Complex.exp (-s y * x) =
        Complex.exp (-(x : ℂ)) * Complex.exp (-u (-y) * ((-x : ℝ) : ℂ)) := by
      rw [← Complex.exp_add, ← hneg]
      congr 1
      push_cast
      ring
    simp_rw [hphase, ← mul_left_comm (Complex.exp _) (logMellin f _)]
    rw [integral_const_mul, mul_div_assoc, ← hi (-x)]
    rw [integral_neg_eq_self (fun y : ℝ ↦ logMellin f (u y) *
      Complex.exp (-u y * ((-x : ℝ) : ℂ)))]

/-- Paper: Proposition B.4.2.1, p. 616. The two complex local contour terms
equal the digamma integral and the complex gamma prefactor contribution.
Deviation: The integral converges at both endpoints and includes absolute angular weight. -/
theorem complexHeckeArchimedean_mellinLogDeriv (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (a : ℝ) (_ha : 1 < a) :
    let p := (complexLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose
    let K := heckeArchimedeanDigammaKernel 1
      (p.1 + (p.2.natAbs : ℂ) / 2) (1 - p.1 + (p.2.natAbs : ℂ) / 2) f
    let H := fun s ↦ logMellin f s * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ)) s +
      logMellin f (1 - s) * logDeriv (infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹)) s
    Complex.VerticalIntegrable H a ∧ IntegrableOn K (Ioi 0) ∧
      verticalLineIntegral H a / twoPiI =
        (∫ t in Ioi (0 : ℝ), K t) - 2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by
  intro p K H
  let e := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
  let i : ℂˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
  let c := ContinuousMonoidHom.comp circleToComplex χ
  have hp := (complexLocalEulerParameters w hw c).exists.choose_spec
  have hpRe : p.1.re = 0 := by
    obtain ⟨q, ⟨hRe, hq⟩, _⟩ := existsUnique_complexUnits_character_parameters (c.comp i)
      (fun x ↦ Circle.norm_coe (χ (i x)))
    have h : p = q := (complexLocalEulerParameters w hw c).unique hp hq
    simpa only [h] using hRe
  let b := (p.2.natAbs : ℂ) / 2
  let β := p.1 + b
  let β' := -p.1 + b
  have hb : 0 ≤ b.re := by
    simp [b, Complex.div_ofNat_re]
    positivity
  have hβ : 0 ≤ β.re := by simpa [β, hpRe] using hb
  have hβ' : 0 ≤ β'.re := by simpa [β', hpRe] using hb
  have hD := complexHeckeArchimedean_mellinLogDeriv_factor w hw χ p.1 p.2 hp
  have hR : infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹) =
      fun s ↦ Complex.Gammaℂ (s + β') / 2 := by
    have hinv (x : ℂˣ) : ((χ⁻¹) (i x) : ℂ) =
        ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (-p.1) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (-p.2) := by
      change ((χ (i x) : ℂ)⁻¹) = _
      change ∀ x : ℂˣ, (χ (i x) : ℂ) = _ at hp
      rw [hp x, mul_inv, Complex.cpow_neg, zpow_neg]
    have hinvFactor := complexHeckeArchimedean_mellinLogDeriv_factor w hw χ⁻¹ (-p.1) (-p.2) hinv
    rw [Int.natAbs_neg] at hinvFactor
    exact hinvFactor
  let s := fun y : ℝ ↦ (a : ℂ) + y * Complex.I
  let directWeight := fun y ↦ logMellin f (s y)
  let reflectedWeight := fun y ↦ logMellin f (1 - s y)
  let reflectedTest := fun x : ℝ ↦ Complex.exp (-(x : ℂ)) * f (-x)
  let directLine := fun y ↦ directWeight y * logDeriv (fun z ↦ Complex.Gammaℂ (z + β) / 2) (s y)
  let reflectedLine := fun y ↦ reflectedWeight y * logDeriv (fun z ↦ Complex.Gammaℂ (z + β') / 2) (s y)
  let decay := fun x : ℝ ↦ Complex.exp (-(x : ℂ))
  let directKernel := fun x : ℝ ↦ (f 0 * decay x - Complex.exp (-β * x) * f x) / (1 - decay x)
  let reflectedKernel := fun x : ℝ ↦
    (reflectedTest 0 * decay x - Complex.exp (-β' * x) * reflectedTest x) / (1 - decay x)
  obtain ⟨hc, hm, hi⟩ := complexHeckeArchimedean_mellinLogDeriv_trace f _hf a
  obtain ⟨hc', hm', hi'⟩ := complexHeckeArchimedean_mellinLogDeriv_reflect f _hf a
  obtain ⟨hDirectLine, hDirectKernel, directEval⟩ :=
    complexHeckeArchimedean_mellinLogDeriv_leg a (by linarith) β hβ directWeight f hc hm hi
  obtain ⟨hReflectedLine, hReflectedKernel, reflectedEval⟩ :=
    complexHeckeArchimedean_mellinLogDeriv_leg a (by linarith) β' hβ' reflectedWeight reflectedTest hc' hm' hi'
  change Integrable directLine at hDirectLine
  change Integrable reflectedLine at hReflectedLine
  change IntegrableOn directKernel (Ioi 0) at hDirectKernel
  change IntegrableOn reflectedKernel (Ioi 0) at hReflectedKernel
  change (∫ y, directLine y) / _ = _ * f 0 + ∫ x in Ioi 0, directKernel x at directEval
  change (∫ y, reflectedLine y) / _ = _ * reflectedTest 0 + ∫ x in Ioi 0, reflectedKernel x at reflectedEval
  have line_eq (y : ℝ) : H (s y) = directLine y + reflectedLine y := by simp only [H, hD, hR]; rfl
  have hzero : reflectedTest 0 = f 0 := by simp [reflectedTest]
  -- The reference value of the subtracted Gauss integral is ψ(1) = -γ.
  let gaussTerm := fun x : ℝ ↦ (2 * f 0) * (gaussDigammaKernel x : ℂ)
  have kernel_eq (x : ℝ) : K x = gaussTerm x + (directKernel x + reflectedKernel x) := by
    have hphase : Complex.exp (-β' * (x : ℂ)) * Complex.exp (-(x : ℂ)) =
        Complex.exp (-(1 - p.1 + b) * (x : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; dsimp [β']; ring
    simp only [K, heckeArchimedeanDigammaKernel, Complex.ofReal_one, one_mul, gaussTerm,
      directKernel, reflectedKernel, hzero, reflectedTest, ← mul_assoc (Complex.exp (-β' * (x : ℂ))), hphase, gaussDigammaKernel, decay]
    push_cast
    simp only [β, b]
    ring
  have hGaussInt : IntegrableOn gaussTerm (Ioi 0) := integrableOn_gaussDigammaKernel.ofReal.const_mul _
  have hGauss : (∫ x in Ioi (0 : ℝ), gaussTerm x) =
      (2 * f 0) * (-(Real.eulerMascheroniConstant : ℂ)) := by
    simp [gaussTerm, integral_const_mul, integral_complex_ofReal, integral_gaussDigammaKernel]
  have hH : Complex.VerticalIntegrable H a := by
    change Integrable (fun y ↦ H (s y))
    simp_rw [line_eq]
    exact hDirectLine.add hReflectedLine
  refine ⟨hH, ?_, ?_⟩
  · rw [show K = _ from funext kernel_eq]
    exact hGaussInt.add (hDirectKernel.add hReflectedKernel)
  · change (Complex.I * ∫ y, H (s y)) / twoPiI = _
    simp_rw [line_eq, kernel_eq]
    rw [integral_add hDirectLine hReflectedLine,
      integral_add (f := gaussTerm) (g := fun x ↦ directKernel x + reflectedKernel x)
        hGaussInt (hDirectKernel.add hReflectedKernel),
      integral_add hDirectKernel hReflectedKernel, hGauss]
    have hnorm (v : ℂ) : (Complex.I * v) / twoPiI = v / (2 * (Real.pi : ℂ)) := by
      rw [mul_comm Complex.I, mul_div_mul_right _ _ Complex.I_ne_zero]
    rw [hnorm, add_div, directEval, reflectedEval, hzero]
    ring

-- TODO(paper-gap): (B.4.2.10) needs dt/(2π). With upward ds/(2πi),
-- (B.4.2.11) gives +log(q) χ̄(π)^m q^(-m) φ(q^(-m)).
-- Theorem B.4.2.2 also subtracts two pole terms for every χ and uses the
-- divergent archimedean integral from (B.4.2.15).

local notation "primeTerm(" χ ", " f ")" =>
  (fun j : Primes(F) × ℕ ↦
    if χ₀(χ).IsUnramifiedAt j.1 then
      let x := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
      (Real.log q(j.1) * Real.exp (-x / 2) : ℝ) *
        ((χ₀(χ).localValue j.1) ^ (j.2 + 1) * f x +
          (χ₀(χ⁻¹).localValue j.1) ^ (j.2 + 1) * f (-x))
    else (0 : ℂ))

/-- Paper: Theorem B.4.2.2, p. 616. The centered prime-power contributions
are absolutely summable over the finite places and positive exponents.
Deviation: Ramified Euler factors contribute zero. -/
theorem summable_heckeExplicitPrimeTerms (χ : U[F]) (f : 𝓢(ℝ, ℂ))
    (_hf : ExponentialDecay f) :
    Summable (fun j ↦ ‖primeTerm(χ, f) j‖) := by
  obtain ⟨g, hg⟩ := exponentialDecay_weighted_schwartz f _hf 3
  obtain ⟨h, hh⟩ := exponentialDecay_weighted_schwartz f _hf (-3)
  let C := SchwartzMap.seminorm ℂ 0 0 g + SchwartzMap.seminorm ℂ 0 0 h
  have hdecay (x : ℝ) : ‖f x‖ + ‖f (-x)‖ ≤ C * Real.exp (-(3 * x)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), add_mul]
    have hg' := g.norm_le_seminorm ℂ x
    have hh' := h.norm_le_seminorm ℂ (-x)
    rw [hg, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hg'
    simp only [hh, neg_mul_neg, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)] at hh'
    simpa only [mul_comm] using add_le_add hg' hh'
  -- Index the majorant by the corresponding prime-power ideals.
  let I (j : Primes(F) × ℕ) := j.1.asIdeal ^ (j.2 + 1)
  have hI : Injective I := by
    rintro ⟨v, n⟩ ⟨w, k⟩ he
    change v.asIdeal ^ (n + 1) = w.asIdeal ^ (k + 1) at he
    have hd : v.asIdeal ∣ w.asIdeal := v.prime.dvd_of_dvd_pow
      (he ▸ dvd_pow_self _ (Nat.succ_ne_zero n))
    have hvw : v = w := HeightOneSpectrum.ext
      (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hd)).symm
    subst w
    have hN := congrArg (Ideal.absNorm : Ideal (𝓞 F) → ℕ) he
    simp only [map_pow] at hN
    have hn := Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm v) hN
    exact Prod.ext rfl (Nat.succ.inj hn)
  have hsum := (summable_absNorm_rpow F (r := 2) (by norm_num)).comp_injective hI
  refine (hsum.mul_left C).of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
  rintro ⟨v, k⟩
  have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hlog := (Real.log_pos hq).le
  let x := ((k + 1 : ℕ) : ℝ) * Real.log q(v)
  have hx : Real.log q(v) ≤ x := by
    dsimp [x]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hlog]
  have hfactor : Real.log q(v) * Real.exp (-x / 2) ≤ Real.exp x :=
    (mul_le_of_le_one_right hlog (Real.exp_le_one_iff.mpr (by linarith))).trans
      (hx.trans (by linarith [Real.add_one_le_exp x]))
  change ‖(if _ then _ else (0 : ℂ))‖ ≤ C * ((I (v, k)).absNorm : ℝ) ^ (-(2 : ℝ))
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg hlog (Real.exp_nonneg _))]
    calc
      _ ≤ (Real.log q(v) * Real.exp (-x / 2)) * (‖f x‖ + ‖f (-x)‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hlog (Real.exp_nonneg _))
        simpa only [norm_mul, norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, one_mul]
          using norm_add_le ((χ₀(χ).localValue v) ^ (k + 1) * f x)
            ((χ₀(χ⁻¹).localValue v) ^ (k + 1) * f (-x))
      _ ≤ Real.exp x * (C * Real.exp (-(3 * x))) :=
        mul_le_mul hfactor (hdecay x) (by positivity) (Real.exp_nonneg _)
      _ = C * Real.exp (x + -(3 * x)) := by rw [Real.exp_add]; ring
      _ = _ := by
        change _ = C * (((v.asIdeal ^ (k + 1)).absNorm : ℕ) : ℝ) ^ (-(2 : ℝ))
        rw [map_pow, Nat.cast_pow, Real.rpow_def_of_pos (pow_pos (zero_lt_one.trans hq) _),
          Real.log_pow]
        dsimp [x]
        ring_nf
  · rw [norm_zero]
    exact mul_nonneg (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- Helper for `hasSum_heckeExplicitFormula`: the centred profile `x ↦ exp(-x/2) f x` of an
exponentially decaying Schwartz function is again an exponentially decaying Schwartz function. -/
private theorem hasSum_heckeExplicitFormula_centeredProfile (f : 𝓢(ℝ, ℂ))
    (hf : ExponentialDecay f) :
    ∃ g : 𝓢(ℝ, ℂ), ExponentialDecay g ∧ ∀ x : ℝ, g x = (Real.exp (-x / 2) : ℂ) * f x := by
  obtain ⟨R, hR, -⟩ := exists_schwartzLogReflection
  have hRf : ForwardSemiExponentialDecay (R f) :=
    (backwardSemiExponentialDecay_iff_forward_reflected (R f) f
      (fun x ↦ by rw [hR, neg_neg])).mp hf.2
  have hweight : ∀ c : ℝ, ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = (Real.exp (c * x) : ℂ) * f x := by
    intro c
    by_cases hc : 0 ≤ c
    · exact (forwardSemiExponentialDecay_iff_weighted_schwartz f).mp hf.1 c hc
    · obtain ⟨g, hg⟩ := (forwardSemiExponentialDecay_iff_weighted_schwartz (R f)).mp hRf (-c)
        (by linarith)
      exact ⟨R g, fun x ↦ by simp only [hR, hg, neg_neg, neg_mul_neg]⟩
  obtain ⟨g, hg⟩ := hweight (-1 / 2)
  refine ⟨g, ⟨?_, ?_⟩, fun x ↦ by rw [hg, show (-1 / 2 : ℝ) * x = -x / 2 by ring]⟩
  · refine (forwardSemiExponentialDecay_iff_weighted_schwartz g).mpr fun A hA ↦ ?_
    obtain ⟨h, hh⟩ := hweight (A - 1 / 2)
    refine ⟨h, fun x ↦ ?_⟩
    rw [hh, hg]
    beta_reduce
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring
  · refine (backwardSemiExponentialDecay_iff_forward_reflected (R g) g
      (fun x ↦ by rw [hR, neg_neg])).mpr ?_
    refine (forwardSemiExponentialDecay_iff_weighted_schwartz (R g)).mpr fun A hA ↦ ?_
    obtain ⟨h, hh⟩ := (forwardSemiExponentialDecay_iff_weighted_schwartz (R f)).mp hRf (A + 1 / 2)
      (by linarith)
    refine ⟨h, fun x ↦ ?_⟩
    rw [hh, hR f x, hR g x, hg (-x)]
    beta_reduce
    rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3
    ring

/-- Tilting the logarithmic test by the half weight shifts the Mellin argument. -/
private theorem heckeExplicitFormula_centeredLine_mellin
    (f g : 𝓢(ℝ, ℂ)) (hgf : ∀ x : ℝ, g x = (Real.exp (-x / 2) : ℂ) * f x)
    (s : ℂ) : logMellin g s = logMellin f (s - 1 / 2) := by
  have h : logMellin g s =
      mellin (fun t : ℝ ↦ (t : ℂ) ^ (-(1 / 2 : ℂ)) • f (Real.log t)) s := by
    show ∫ t in Ioi (0 : ℝ), _ = ∫ t in Ioi (0 : ℝ), _
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht' : (0 : ℝ) < t := ht
    simp only [hgf, smul_eq_mul]
    congr 2
    rw [show -Real.log t / 2 = Real.log t * (-(1 / 2 : ℝ)) by ring, ← Real.rpow_def_of_pos ht',
      Complex.ofReal_cpow ht'.le]
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [h, mellin_cpow_smul, sub_eq_add_neg]

/-- A Schwartz Mellin trace remains integrable when multiplied by a continuous
function with at most linear growth. -/
private theorem heckeExplicitFormula_centeredLine_integrable
    (T : 𝓢(ℝ, ℂ)) (G : ℝ → ℂ) (hG : Continuous G) (C : ℝ)
    (hC : ∀ y, ‖G y‖ ≤ C * (1 + |y|)) :
    Integrable (fun y ↦ T y * G y) := by
  have hMoment : Integrable (fun y ↦ (1 + |y|) * ‖T y‖) := by
    simpa only [Pi.add_def, add_mul, one_mul, Real.norm_eq_abs, pow_one] using
      T.integrable.norm.add (T.integrable_pow_mul volume 1)
  refine (hMoment.const_mul C).mono' (T.continuous.mul hG).aestronglyMeasurable ?_
  filter_upwards with y
  rw [norm_mul]
  calc
    _ ≤ ‖T y‖ * (C * (1 + |y|)) := mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    _ = _ := by ring

/-- On the right of one the completed logarithmic derivative splits into its
finite and gamma terms, each integrable against a Schwartz Mellin trace. -/
private theorem heckeExplicitFormula_centeredLine_decompose
    (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) (a : ℝ) (ha : 1 < a)
    (W : ℂ → ℂ) (T : 𝓢(ℝ, ℂ)) (hT : ∀ y : ℝ, T y = W ((a : ℂ) + y * Complex.I)) :
    Complex.VerticalIntegrable (fun s ↦ W s * logDeriv L s) a ∧
      verticalLineIntegral (fun s ↦ W s * logDeriv L s) a =
        verticalLineIntegral (fun s ↦ W s * logDeriv (heckeGammaFactor χ) s) a +
        verticalLineIntegral (fun s ↦ W s * logDeriv (finiteSeries(χ)) s) a := by
  let s (y : ℝ) : ℂ := (a : ℂ) + y * Complex.I
  have hs (y : ℝ) : (s y).re = a := by simp [s]
  have hs' (y : ℝ) : 1 < (s y).re := hs y ▸ ha
  have hsplit (y : ℝ) := completedHeckeL_logDeriv_right_local χ L hL hAgree (hs' y)
  have hc : Continuous s := by dsimp [s]; fun_prop
  have hcL : Continuous (fun y ↦ logDeriv L (s y)) :=
    continuous_iff_continuousAt.mpr fun y ↦ (hsplit y).1.continuousAt.comp hc.continuousAt
  have hcF : Continuous (fun y ↦ logDeriv (finiteSeries(χ)) (s y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hA := LSeries_analyticOnNhd _ (s y) (completedHeckeL_logDeriv_abscissa χ (hs' y))
    have hne : finiteSeries(χ) (s y) ≠ 0 := norm_pos_iff.mp
      ((Real.exp_pos _).trans_le (completedHeckeL_logDeriv_finite_lower χ a ha (s y) (hs y)))
    exact (hA.deriv.div hA hne).continuousAt.comp hc.continuousAt
  have hcG : Continuous (fun y ↦ logDeriv (heckeGammaFactor χ) (s y)) := by
    have he : (fun y ↦ logDeriv (heckeGammaFactor χ) (s y)) =
        fun y ↦ logDeriv L (s y) - logDeriv (finiteSeries(χ)) (s y) :=
      funext fun y ↦ by rw [(hsplit y).2, add_sub_cancel_right]
    rw [he]
    exact hcL.sub hcF
  obtain ⟨C, -, hC⟩ := completedHeckeL_logDeriv_gammaFactor_bound χ a (zero_lt_one.trans ha)
  obtain ⟨D, hD, hD'⟩ := completedHeckeL_logDeriv_finite_bound χ a ha
  have hiG := (heckeExplicitFormula_centeredLine_integrable T _ hcG C hC).congr
    (Eventually.of_forall fun y ↦ congrArg (fun z ↦ z * logDeriv (heckeGammaFactor χ) (s y)) (hT y))
  have hiF := (heckeExplicitFormula_centeredLine_integrable T _ hcF D (fun y ↦
    (hD' _ (hs y)).trans (le_mul_of_one_le_right hD (le_add_of_nonneg_right (abs_nonneg y))))).congr
      (Eventually.of_forall fun y ↦ congrArg (fun z ↦ z * logDeriv (finiteSeries(χ)) (s y)) (hT y))
  have he (y : ℝ) : W (s y) * logDeriv L (s y) =
      W (s y) * logDeriv (heckeGammaFactor χ) (s y) +
        W (s y) * logDeriv (finiteSeries(χ)) (s y) := by
    rw [(hsplit y).2, mul_add]
  refine ⟨(hiG.add hiF).congr (Eventually.of_forall fun y ↦ (he y).symm), ?_⟩
  change Complex.I * (∫ y, W (s y) * logDeriv L (s y)) =
    Complex.I * (∫ y, W (s y) * logDeriv (heckeGammaFactor χ) (s y)) +
      Complex.I * (∫ y, W (s y) * logDeriv (finiteSeries(χ)) (s y))
  simp_rw [he]
  rw [integral_add hiG hiF, mul_add]

/-- Paper: Equation (B.4.2.7), p. 615.
The finite logarithmic derivative is the negative prime-power series. On a fixed
vertical line to the right of one, the moduli are bounded by the summable series
obtained by taking the trivial local character at every place. -/
private theorem heckeExplicitFormula_centeredLine_eulerSeries
    (χ : U[F]) (a : ℝ) (ha : 1 < a) :
    let x := fun j : Primes(F) × ℕ ↦ ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
    let c := fun j : Primes(F) × ℕ ↦ if χ₀(χ).IsUnramifiedAt j.1 then
      -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) else 0
    Summable (fun j ↦ Real.log q(j.1) * Real.exp (-a * x j)) ∧
      ∀ z : ℂ, z.re = a →
        HasSum (fun j ↦ c j * Complex.exp (-z * (x j : ℂ))) (logDeriv (finiteSeries(χ)) z) := by
  intro x c
  obtain ⟨r, hr, hra⟩ := exists_between ha
  let ε := a - r
  have hε : 0 < ε := sub_pos.mpr hra
  let J (j : Primes(F) × ℕ) := j.1.asIdeal ^ (j.2 + 1)
  have hJ : Injective J := by
    rintro ⟨v, n⟩ ⟨w, m⟩ h
    change v.asIdeal ^ (n + 1) = w.asIdeal ^ (m + 1) at h
    have hdvd : v.asIdeal ∣ w.asIdeal := v.prime.dvd_of_dvd_pow
      ((dvd_pow_self _ (Nat.succ_ne_zero n)).trans h.dvd)
    have hw : v = w := HeightOneSpectrum.ext
      (w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hdvd)).symm
    subst w
    exact Prod.ext rfl (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot h))
  have hq (v : Primes(F)) : 1 < q(v) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq₀ (v : Primes(F)) : 0 < q(v) := zero_lt_one.trans (hq v)
  let d (j : Primes(F) × ℕ) := Real.log q(j.1) * Real.exp (-a * x j)
  have hd (j : Primes(F) × ℕ) : 0 ≤ d j :=
    mul_nonneg (Real.log_nonneg (hq j.1).le) (Real.exp_nonneg _)
  have hdSum : Summable d := by
    refine (((summable_absNorm_rpow F hr).comp_injective hJ).div_const ε).of_nonneg_of_le hd ?_
    intro j
    let u : ℝ := (J j).absNorm
    have hu : u = q(j.1) ^ (j.2 + 1) := by simp [u, J, map_pow]
    have hu₀ : 0 < u := hu ▸ pow_pos (hq₀ j.1) _
    have hlog : Real.log u = x j := by rw [hu, Real.log_pow]
    have hlogq : Real.log q(j.1) ≤ Real.log u := by
      rw [hlog]
      apply le_mul_of_one_le_left (Real.log_nonneg (hq j.1).le)
      exact_mod_cast (Nat.succ_pos j.2)
    change d j ≤ u ^ (-r) / ε
    calc
      _ ≤ Real.log u * u ^ (-a) := by
        have hEq : Real.exp (-a * x j) = u ^ (-a) := by
          rw [Real.rpow_def_of_pos hu₀, hlog, mul_comm]
        dsimp only [d]
        rw [hEq]
        exact mul_le_mul_of_nonneg_right hlogq (Real.rpow_nonneg hu₀.le _)
      _ ≤ (u ^ ε / ε) * u ^ (-a) :=
        mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hu₀.le hε) (Real.rpow_nonneg hu₀.le _)
      _ = _ := by
        rw [div_mul_eq_mul_div, ← Real.rpow_add hu₀, show ε + -a = -r by dsimp [ε]; ring]
  refine ⟨hdSum, fun z hz ↦ ?_⟩
  let b (v : Primes(F)) : ℂ := if χ₀(χ).IsUnramifiedAt v then (χ₀(χ)).localValue v else 0
  let U (v : Primes(F)) (w : ℂ) := b v * ((q(v) : ℝ) : ℂ) ^ (-w)
  have hb (v : Primes(F)) : ‖b v‖ ≤ 1 := by
    by_cases h : χ₀(χ).IsUnramifiedAt v <;> simp [b, h, norm_ideleClassNormTwist_zero_localValue]
  have hfactor (v : Primes(F)) :
      finiteHeckeEulerFactor χ v = fun w ↦ (1 - U v w)⁻¹ := by
    funext w
    by_cases h : χ₀(χ).IsUnramifiedAt v <;> simp [finiteHeckeEulerFactor, h, U, b]
  have hloc (v : Primes(F)) {w : ℂ} (hw : 1 < w.re) :
      DifferentiableAt ℂ (finiteHeckeEulerFactor χ v) w ∧ finiteHeckeEulerFactor χ v w ≠ 0 ∧
      logDeriv (finiteHeckeEulerFactor χ v) w = -((Real.log q(v) : ℝ) : ℂ) * U v w * (1 - U v w)⁻¹ ∧
      ‖U v w‖ < 1 := by
    have h₀ : ((q(v) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hq₀ v).ne'
    have hU : ‖U v w‖ < 1 := by
      unfold U
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hq₀ v), Complex.neg_re]
      exact (mul_le_of_le_one_left (Real.rpow_nonneg (hq₀ v).le _) (hb v)).trans_lt
        (Real.rpow_lt_one_of_one_lt_of_neg (hq v) (by linarith))
    have hne : 1 - U v w ≠ 0 := fun h ↦ hU.ne (by rw [← sub_eq_zero.mp h, norm_one])
    have dU := ((hasDerivAt_id w).neg.const_cpow (Or.inl h₀)).const_mul (b v)
    change HasDerivAt (U v)
      (b v * (((q(v) : ℝ) : ℂ) ^ (-w) * Complex.log (q(v) : ℂ) * (-1))) w at dU
    have df := (dU.const_sub 1).inv hne
    change HasDerivAt (fun w ↦ (1 - U v w)⁻¹) _ w at df
    rw [hfactor]
    refine ⟨df.differentiableAt, inv_ne_zero hne, ?_, hU⟩
    rw [logDeriv_apply, df.deriv, ← Complex.ofReal_log (hq₀ v).le]
    change _ / (1 - U v w)⁻¹ = _
    field_simp [hne]
    dsimp [U]
    ring
  have hPow (v : Primes(F)) (n : ℕ) :
      Complex.exp (-z * (x (v, n) : ℂ)) = (((q(v) : ℝ) : ℂ) ^ (-z)) ^ (n + 1) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hq₀ v).ne'),
      ← Complex.exp_nat_mul, ← Complex.ofReal_log (hq₀ v).le]
    congr 1
    dsimp [x]
    push_cast
    ring
  have hlocal (v : Primes(F)) :
      HasSum (fun n : ℕ ↦ c (v, n) * Complex.exp (-z * (x (v, n) : ℂ)))
        (logDeriv (finiteHeckeEulerFactor χ v) z) := by
    obtain ⟨-, -, hL, hU⟩ := hloc v (hz ▸ ha)
    rw [hL]
    apply ((hasSum_geometric_of_norm_lt_one hU).mul_left (-((Real.log q(v) : ℝ) : ℂ) * U v z)).congr_fun
    intro n
    rw [hPow, mul_assoc, ← pow_succ']
    simp only [U, mul_pow]
    dsimp only [c, b]
    split_ifs <;> simp [pow_succ] <;> ring
  obtain ⟨t, ht, htz⟩ := exists_between (show 1 < z.re from hz ▸ ha)
  let O := Complex.re ⁻¹' Ioi t
  have hO : IsOpen O := isOpen_Ioi.preimage Complex.continuous_re
  have hconv := (finiteHeckeEulerProduct_tendstoUniformlyOn_halfPlane χ ht).mono
    (show O ⊆ {w : ℂ | t ≤ w.re} from fun w (hw : t < w.re) ↦ hw.le)
  have hn : finiteSeries(χ) z ≠ 0 :=
    finiteHeckeL_ne_zero_of_one_lt_re χ ⟨z, show 1 < z.re from hz ▸ ha⟩
  have hplaces : HasSum (fun v ↦ logDeriv (finiteHeckeEulerFactor χ v) z) (logDeriv (finiteSeries(χ)) z) := by
    apply (Complex.logDeriv_tendsto hO (show z ∈ O from htz) hconv.tendstoLocallyUniformlyOn
      (.of_forall fun S ↦ DifferentiableOn.fun_finsetProd fun v _ w hw ↦
        (hloc v (ht.trans hw)).1.differentiableWithinAt) hn).congr
    intro S
    exact logDeriv_fun_prod (fun v _ ↦ (hloc v (hz ▸ ha)).2.1) (fun v _ ↦ (hloc v (hz ▸ ha)).1)
  have hsum : Summable (fun j ↦ c j * Complex.exp (-z * (x j : ℂ))) := by
    apply hdSum.of_norm_bounded
    intro j
    have hre : (-z * (x j : ℂ)).re = -a * x j := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.neg_re, hz]
    dsimp only [c, d]
    split_ifs
    · simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg (hq j.1).le),
        norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, mul_one, Complex.norm_exp, hre, le_refl]
    · simpa only [zero_mul, norm_zero] using hd j
  rw [← (hsum.hasSum.prod_fiberwise hlocal).unique hplaces]
  exact hsum.hasSum

/-- Mellin inversion integrates the Euler series term by term against a Schwartz
trace, with its samples supplied by the direct or reflected inversion formula. -/
private theorem heckeExplicitFormula_centeredLine_finiteLeg
    (χ : U[F]) (a : ℝ) (ha : 1 < a) (W : 𝓢(ℝ, ℂ)) (A : ℂ → ℂ) (P : ℝ → ℂ)
    (hW : ∀ y : ℝ, W y = A ((a : ℂ) + y * Complex.I))
    (hInv : ∀ x : ℝ, (∫ y : ℝ, W y * Complex.exp (-((a : ℂ) + y * Complex.I) * x)) /
      (2 * (Real.pi : ℂ)) = P x) :
    HasSum (fun j : Primes(F) × ℕ ↦ if χ₀(χ).IsUnramifiedAt j.1 then
      -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) *
        P (((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)) else 0)
      (verticalLineIntegral (fun s ↦ A s * logDeriv (finiteSeries(χ)) s) a / twoPiI) := by
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  have hspan : Surjective (fun S : Finset (𝓞 F) ↦ Ideal.span (S : Set (𝓞 F))) :=
    fun I ↦ IsNoetherian.noetherian I
  let : Countable (Ideal (𝓞 F)) := hspan.countable
  let : Countable (Primes(F)) :=
    (show Injective (HeightOneSpectrum.asIdeal (R := 𝓞 F)) from fun _ _ h ↦
      HeightOneSpectrum.ext h).countable
  let s (y : ℝ) : ℂ := (a : ℂ) + y * Complex.I
  let x (j : Primes(F) × ℕ) := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
  let c (j : Primes(F) × ℕ) : ℂ := if χ₀(χ).IsUnramifiedAt j.1 then
    -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) else 0
  let d (j : Primes(F) × ℕ) : ℝ := Real.log q(j.1) * Real.exp (-a * x j)
  let K (j : Primes(F) × ℕ) (y : ℝ) := W y * (c j * Complex.exp (-s y * (x j : ℂ)))
  obtain ⟨hs, hSeries⟩ := heckeExplicitFormula_centeredLine_eulerSeries χ a ha
  change Summable d at hs
  have hRe (y : ℝ) : (s y).re = a := by simp [s]
  have hlog (v : Primes(F)) : 0 ≤ Real.log q(v) := Real.log_nonneg
    (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le)
  have hbound (j : Primes(F) × ℕ) (y : ℝ) : ‖K j y‖ ≤ ‖W y‖ * d j := by
    change ‖W y * (c j * Complex.exp (-s y * (x j : ℂ)))‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    have hreal : (-s y * (x j : ℂ)).re = -a * x j := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.neg_re, hRe]
    dsimp only [c, d]
    split_ifs
    · simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (hlog _),
        norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow, mul_one, Complex.norm_exp, hreal,
        le_refl]
    · rw [zero_mul, norm_zero]
      exact mul_nonneg (hlog _) (Real.exp_nonneg _)
  have hInt : HasSum (fun j ↦ ∫ y, K j y) (∫ y, W y * logDeriv (finiteSeries(χ)) (s y)) := by
    apply hasSum_integral_of_dominated_convergence (fun j y ↦ ‖W y‖ * d j)
    · intro j
      apply Continuous.aestronglyMeasurable
      unfold K s
      fun_prop
    · exact fun j ↦ Eventually.of_forall (hbound j)
    · exact Eventually.of_forall fun y ↦ hs.mul_left ‖W y‖
    · simp_rw [tsum_mul_left]
      exact W.integrable.norm.mul_const _
    · exact Eventually.of_forall fun y ↦ (hSeries (s y) (hRe y)).mul_left (W y)
  have hEval (j : Primes(F) × ℕ) :
      (∫ y, K j y) / (2 * (Real.pi : ℂ)) = c j * P (x j) := by
    have he (y : ℝ) : K j y = c j * (W y * Complex.exp (-s y * (x j : ℂ))) := by
      exact mul_left_comm _ _ _
    simp_rw [he]
    rw [integral_const_mul, mul_div_assoc, hInv]
  have h := hInt.div_const (2 * (Real.pi : ℂ))
  simp_rw [hEval, hW] at h
  have hTerm (j : Primes(F) × ℕ) : c j * P (x j) = if χ₀(χ).IsUnramifiedAt j.1 then
      -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) * P (x j) else 0 := by
    by_cases h : χ₀(χ).IsUnramifiedAt j.1 <;> simp [c, h]
  simp_rw [hTerm] at h
  change HasSum _ ((Complex.I * (∫ y, A (s y) * logDeriv (finiteSeries(χ)) (s y))) / twoPiI)
  rw [mul_comm Complex.I, mul_div_mul_right _ _ Complex.I_ne_zero]
  exact h

/-- Paper: Theorem B.4.2.2, p. 616, and (B.4.2.5)–(B.4.2.11), p. 615.
The two finite logarithmic derivatives on the right-hand line give the sum
over unramified prime powers. Both Mellin inversions have weight `q^(-m/2)`. -/
private theorem heckeExplicitFormula_centeredLine_finite
    (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a : ℝ) (ha : 1 < a) :
    (verticalLineIntegral (fun s ↦ logMellin f (s - 1 / 2) * logDeriv (finiteSeries(χ)) s) a +
      verticalLineIntegral (fun s ↦ logMellin f (1 / 2 - s) * logDeriv (finiteSeries(χ⁻¹)) s) a) /
        twoPiI = -(∑' j, primeTerm(χ, f) j) := by
  obtain ⟨g, hg, hgf⟩ := hasSum_heckeExplicitFormula_centeredProfile f hf
  obtain ⟨W, hW, hInvW⟩ := realHeckeArchimedean_mellinLogDeriv_trace g hg a
  obtain ⟨V, hV, hInvV⟩ := realHeckeArchimedean_mellinLogDeriv_reflect g hg a
  have hshift := heckeExplicitFormula_centeredLine_mellin f g hgf
  have hshift' (z : ℂ) : logMellin g (1 - z) = logMellin f (1 / 2 - z) := by
    rw [hshift, show 1 - z - 1 / 2 = 1 / 2 - z by ring]
  have hD := heckeExplicitFormula_centeredLine_finiteLeg χ a ha W
    (fun s ↦ logMellin f (s - 1 / 2)) g (fun y ↦ (hW y).trans (hshift _)) hInvW
  have hR := heckeExplicitFormula_centeredLine_finiteLeg χ⁻¹ a ha V
    (fun s ↦ logMellin f (1 / 2 - s)) (fun x ↦ Complex.exp (-(x : ℂ)) * g (-x))
    (fun y ↦ (hV y).trans (hshift' _)) hInvV
  have hreflect (x : ℝ) : Complex.exp (-(x : ℂ)) * g (-x) = (Real.exp (-x / 2) : ℂ) * f (-x) := by
    rw [hgf, ← mul_assoc, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hterm (j : Primes(F) × ℕ) :
      let x := ((j.2 + 1 : ℕ) : ℝ) * Real.log q(j.1)
      ((if χ₀(χ).IsUnramifiedAt j.1 then
        -(Real.log q(j.1) : ℂ) * (χ₀(χ).localValue j.1) ^ (j.2 + 1) * g x else 0) +
        (if χ₀(χ⁻¹).IsUnramifiedAt j.1 then
          -(Real.log q(j.1) : ℂ) * (χ₀(χ⁻¹).localValue j.1) ^ (j.2 + 1) *
            (Complex.exp (-(x : ℂ)) * g (-x)) else 0)) = -primeTerm(χ, f) j := by
    intro x
    rw [show (χ₀(χ⁻¹)).IsUnramifiedAt j.1 ↔ (χ₀(χ)).IsUnramifiedAt j.1 from
      inverse_unramified j.1 χ]
    change _ = -(ite _ _ (0 : ℂ))
    split_ifs
    · rw [hreflect, hgf]
      simp only [Complex.ofReal_mul]
      ring
    · simp
  have h := (hD.add hR).congr_fun fun j ↦ (hterm j).symm
  rw [add_div, ← h.tsum_eq, tsum_neg]

/-- The same half weight shifts the gamma-kernel arguments in opposite directions. -/
private theorem heckeExplicitFormula_centeredLine_kernel
    (f g : 𝓢(ℝ, ℂ)) (hgf : ∀ x : ℝ, g x = (Real.exp (-x / 2) : ℂ) * f x)
    (k : ℝ) (z₁ z₂ : ℂ) (t : ℝ) :
    heckeArchimedeanDigammaKernel k z₁ z₂ g t =
      heckeArchimedeanDigammaKernel k (z₁ + (k : ℂ) / 2) (z₂ - (k : ℂ) / 2) f t := by
  have h₁ : g (k * t) * Complex.exp (-z₁ * (t : ℂ)) =
      f (k * t) * Complex.exp (-(z₁ + (k : ℂ) / 2) * t) := by
    rw [hgf, Complex.ofReal_exp, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h₂ : g (-(k * t)) * Complex.exp (-z₂ * (t : ℂ)) =
      f (-(k * t)) * Complex.exp (-(z₂ - (k : ℂ) / 2) * t) := by
    rw [hgf, Complex.ofReal_exp, mul_comm (Complex.exp _), mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have h₀ : g 0 = f 0 := by simp [hgf]
  simp only [heckeArchimedeanDigammaKernel, h₁, h₂, h₀]

/-- Paper: Proposition B.4.2.1 and Theorem B.4.2.2, p. 616.
The gamma factors give the sum of the real and complex local digamma terms.
Use the exponentially tilted test so that the two Mellin transforms are centred. -/
private theorem heckeExplicitFormula_centeredLine_gamma
    (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f) (a : ℝ) (ha : 1 < a) :
    (verticalLineIntegral (fun s ↦ logMellin f (s - 1 / 2) * logDeriv (heckeGammaFactor χ) s) a +
      verticalLineIntegral (fun s ↦ logMellin f (1 / 2 - s) * logDeriv (heckeGammaFactor χ⁻¹) s) a) /
        twoPiI =
        ∑ w : InfinitePlace F, if hw : w.IsReal then
          let p := (realHeckeCharacter_parameters χ w hw).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
            ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
              (Real.log Real.pi : ℂ) * f 0
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
            (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
            (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
              2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by
  obtain ⟨g, hg, hgf⟩ := hasSum_heckeExplicitFormula_centeredProfile f hf
  let G (ψ : U[F]) (w : InfinitePlace F) (s : ℂ) : ℂ :=
    if hw : w.IsReal then
      let p := (realHeckeCharacter_parameters ψ w hw).exists.choose
      Complex.Gammaℝ (s + p.1 + p.2.val)
    else
      let p := (complexHeckeCharacter_parameters ψ w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
      Complex.Gammaℂ (s + p.1 + (p.2.natAbs : ℂ) / 2) / 2
  let ρ (ψ : U[F]) (w : InfinitePlace F) : PontryaginDual w.Completionˣ :=
    ψ.comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩
  have hρ (ψ : U[F]) (w : InfinitePlace F) (u : w.Completionˣ) :
      (ρ ψ w u : ℂ) = infinitePlaceRestriction F w (χ₀(ψ)) u := by
    change (ψ _ : ℂ) = (ψ _ : ℂ) * _ ^ (0 : ℂ)
    rw [Complex.cpow_zero, mul_one]
  have hρinv (w : InfinitePlace F) : ρ χ⁻¹ w = (ρ χ w)⁻¹ := by
    ext1 u
    rfl
  have hReal (ψ : U[F]) (w : InfinitePlace F) (hw : w.IsReal) :
      (realLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex (ρ ψ w))).exists.choose =
        (realHeckeCharacter_parameters ψ w hw).exists.choose := by
    apply (realLocalEulerParameters w hw _).unique (realLocalEulerParameters w hw _).exists.choose_spec
    intro x
    change (ρ ψ w _ : ℂ) = _
    rw [hρ]
    exact (realHeckeCharacter_parameters ψ w hw).exists.choose_spec.2 x
  have hComplex (ψ : U[F]) (w : InfinitePlace F) (hw : w.IsComplex) :
      (complexLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex (ρ ψ w))).exists.choose =
        (complexHeckeCharacter_parameters ψ w hw).exists.choose := by
    apply (complexLocalEulerParameters w hw _).unique (complexLocalEulerParameters w hw _).exists.choose_spec
    intro x
    change (ρ ψ w _ : ℂ) = _
    rw [hρ]
    exact (complexHeckeCharacter_parameters ψ w hw).exists.choose_spec.2 x
  have hG (ψ : U[F]) (w : InfinitePlace F) :
      G ψ w = infiniteLocalEulerFactor w ∘ localChart(w, ρ ψ w) := by
    by_cases hw : w.IsReal
    · have h := (realHeckeArchimedean_mellinLogDeriv_parameters w hw (ρ ψ w)).2.1
      rw [hReal] at h
      simpa only [G, dite_eq_left hw, add_assoc] using h.symm
    · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hp := (complexLocalEulerParameters w hc
        (ContinuousMonoidHom.comp circleToComplex (ρ ψ w))).exists.choose_spec
      rw [hComplex] at hp
      have h := complexHeckeArchimedean_mellinLogDeriv_factor w hc (ρ ψ w) _ _ hp
      simpa only [G, dite_eq_right hw, hc, add_assoc] using h.symm
  let H (w : InfinitePlace F) (s : ℂ) :=
    logMellin g s * logDeriv (G χ w) s + logMellin g (1 - s) * logDeriv (G χ⁻¹ w) s
  have hg₀ : g 0 = f 0 := by simp [hgf]
  have hlocal (w : InfinitePlace F) : Complex.VerticalIntegrable (H w) a ∧
      verticalLineIntegral (H w) a / twoPiI =
        if hw : w.IsReal then
          let p := (realHeckeCharacter_parameters χ w hw).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
            ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
              (Real.log Real.pi : ℂ) * f 0
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
            (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
            (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
              2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by
    by_cases hw : w.IsReal
    · obtain ⟨hi, -, hv⟩ := realHeckeArchimedean_mellinLogDeriv w hw (ρ χ w) g hg a ha
      rw [hReal] at hv
      simp only [H, hG, hρinv, dite_eq_left hw]
      refine ⟨hi, hv.trans ?_⟩
      rw [hg₀]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [heckeExplicitFormula_centeredLine_kernel f g hgf]
      congr 2 <;> push_cast <;> ring
    · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      obtain ⟨hi, -, hv⟩ := complexHeckeArchimedean_mellinLogDeriv w hc (ρ χ w) g hg a ha
      rw [hComplex] at hv
      simp only [H, hG, hρinv, dite_eq_right hw]
      refine ⟨hi, hv.trans ?_⟩
      rw [hg₀]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      rw [heckeExplicitFormula_centeredLine_kernel f g hgf]
      congr 1 <;> push_cast <;> ring
  let s (y : ℝ) : ℂ := (a : ℂ) + y * Complex.I
  have hregular (ψ : U[F]) (w : InfinitePlace F) (y : ℝ) :
      G ψ w (s y) ≠ 0 ∧ DifferentiableAt ℂ (G ψ w) (s y) := by
    by_cases hw : w.IsReal
    · let p := (realHeckeCharacter_parameters ψ w hw).exists.choose
      let b := p.1 + (p.2.val : ℂ)
      have hp : p.1.re = 0 := (realHeckeCharacter_parameters ψ w hw).exists.choose_spec.1
      have hb : 0 < (s y + b).re := by
        simp only [s, b, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
          neg_zero, add_zero, hp, Complex.natCast_re, zero_add]
        positivity
      simpa only [G, dite_eq_left hw, b, p, add_assoc] using
        completedHeckeL_logDeriv_GammaR_regular b (s y) hb
    · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let p := (complexHeckeCharacter_parameters ψ w hc).exists.choose
      let b := p.1 + (p.2.natAbs : ℂ) / 2
      have hp : p.1.re = 0 := (complexHeckeCharacter_parameters ψ w hc).exists.choose_spec.1
      have hb : 0 < (s y + b).re := by
        simp only [s, b, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
          neg_zero, add_zero, hp, Complex.div_ofNat_re, Complex.natCast_re, zero_add]
        positivity
      simpa only [G, dite_eq_right hw, hc, b, p, add_assoc] using
        (completedHeckeL_logDeriv_GammaC_split b (s y) hb).1
  have hprod (ψ : U[F]) (y : ℝ) :
      logDeriv (heckeGammaFactor ψ) (s y) = ∑ w, logDeriv (G ψ w) (s y) := by
    change logDeriv (fun z ↦ ∏ w, G ψ w z) (s y) = _
    exact logDeriv_fun_prod (fun w _ ↦ (hregular ψ w y).1) (fun w _ ↦ (hregular ψ w y).2)
  have hsum (y : ℝ) : (∑ w, H w (s y)) =
      logMellin g (s y) * logDeriv (heckeGammaFactor χ) (s y) +
        logMellin g (1 - s y) * logDeriv (heckeGammaFactor χ⁻¹) (s y) := by
    simp only [H, hprod, Finset.mul_sum, Finset.sum_add_distrib]
  have hi (ψ : U[F]) (W : 𝓢(ℝ, ℂ)) (A : ℂ → ℂ)
      (hW : ∀ y, W y = A (s y)) :
      Integrable (fun y ↦ A (s y) * logDeriv (heckeGammaFactor ψ) (s y)) := by
    have hcont : Continuous (fun y ↦ logDeriv (heckeGammaFactor ψ) (s y)) := by
      apply continuous_iff_continuousAt.mpr
      intro y
      have hs : 0 < (s y).re := by simpa [s] using zero_lt_one.trans ha
      have hA : AnalyticAt ℂ (heckeGammaFactor ψ) (s y) :=
        DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
          (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos ψ hz).differentiableWithinAt)
          ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
      exact (hA.deriv.div hA (heckeGammaFactor_ne_zero_of_re_pos ψ hs)).continuousAt.comp
        (by dsimp [s]; fun_prop)
    obtain ⟨C, -, hC⟩ := completedHeckeL_logDeriv_gammaFactor_bound ψ a (zero_lt_one.trans ha)
    exact (heckeExplicitFormula_centeredLine_integrable W _ hcont C hC).congr
      (Eventually.of_forall fun y ↦ congrArg (fun z ↦ z * logDeriv (heckeGammaFactor ψ) (s y)) (hW y))
  obtain ⟨W, hW, -⟩ := realHeckeArchimedean_mellinLogDeriv_trace g hg a
  obtain ⟨V, hV, -⟩ := realHeckeArchimedean_mellinLogDeriv_reflect g hg a
  have hSumInt :
      (∫ y : ℝ, ∑ w, H w (s y)) = ∑ w, ∫ y : ℝ, H w (s y) :=
    integral_finsetSum _ fun w _ ↦ (hlocal w).1
  have hshift := heckeExplicitFormula_centeredLine_mellin f g hgf
  have hshift' (z : ℂ) : logMellin g (1 - z) = logMellin f (1 / 2 - z) := by
    rw [hshift, show 1 - z - 1 / 2 = 1 / 2 - z by ring]
  simp_rw [← hshift, ← hshift']
  change (Complex.I * (∫ y, logMellin g (s y) * logDeriv (heckeGammaFactor χ) (s y)) +
    Complex.I * (∫ y, logMellin g (1 - s y) * logDeriv (heckeGammaFactor χ⁻¹) (s y))) / twoPiI = _
  rw [← mul_add, ← integral_add (hi χ W (logMellin g) hW)
    (hi χ⁻¹ V (fun z ↦ logMellin g (1 - z)) hV)]
  simp_rw [← hsum]
  rw [hSumInt, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun w _ ↦ (hlocal w).2

/-- Paper: Theorem B.4.2.2, p. 616, with (B.4.2.5)–(B.4.2.11) and Proposition B.4.2.1,
pp. 615–616. On a line `Re s = a` with `1 < a ≤ 2`, the centred Mellin transform `Φ(s - 1/2)`
paired with `L'/L`, plus the reflected centred transform `Φ(1/2 - s)` paired with the dual
`L'/L`, divided by `2πi`, equals minus the prime-power series plus the archimedean digamma
terms; the reflected product is integrable on the line.
Deviation: The finite part is the Euler product expansion (B.4.2.5)–(B.4.2.7) integrated
termwise by Mellin inversion, with the normalizations of F36 (both samples carry the centred
weight `q^(-m/2) log q`). The archimedean part is `realHeckeArchimedean_mellinLogDeriv` and
`complexHeckeArchimedean_mellinLogDeriv` applied to the centred profile `x ↦ exp(-x/2) f x`,
whose twist moves into the digamma kernel parameters, with `realHeckeCharacter_parameters`
and `complexHeckeCharacter_parameters` identified with the local Euler parameters of the
restriction of `χ` to the place. -/
theorem heckeExplicitFormula_centeredLine (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)
    (L Ldual : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualAgree : ∀ s : halfPlane, Ldual s = completedHeckeL χ⁻¹ s)
    (a : ℝ) (ha : 1 < a) (haMax : a ≤ 2) :
    Complex.VerticalIntegrable (fun s ↦ logMellin f (1 / 2 - s) * logDeriv Ldual s) a ∧
      (verticalLineIntegral (fun s ↦ logMellin f (s - 1 / 2) * logDeriv L s) a +
        verticalLineIntegral (fun s ↦ logMellin f (1 / 2 - s) * logDeriv Ldual s) a) / twoPiI =
      -(∑' j, primeTerm(χ, f) j) +
        ∑ w : InfinitePlace F, if hw : w.IsReal then
          let p := (realHeckeCharacter_parameters χ w hw).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
            ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
              (Real.log Real.pi : ℂ) * f 0
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
            (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
            (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
              2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by
  obtain ⟨g, hg, hgf⟩ := hasSum_heckeExplicitFormula_centeredProfile f hf
  have hshift := heckeExplicitFormula_centeredLine_mellin f g hgf
  obtain ⟨W, hW, -⟩ := realHeckeArchimedean_mellinLogDeriv_trace g hg a
  obtain ⟨V, hV, -⟩ := realHeckeArchimedean_mellinLogDeriv_reflect g hg a
  have hW' (y : ℝ) : W y = logMellin f (((a : ℂ) + y * Complex.I) - 1 / 2) :=
    (hW y).trans (hshift _)
  have hV' (y : ℝ) : V y = logMellin f (1 / 2 - ((a : ℂ) + y * Complex.I)) := by
    rw [hV y, hshift]
    congr 1
    ring
  obtain ⟨-, hd⟩ := heckeExplicitFormula_centeredLine_decompose χ L hL hAgree a ha
    (fun s ↦ logMellin f (s - 1 / 2)) W hW'
  obtain ⟨hi, hr⟩ := heckeExplicitFormula_centeredLine_decompose χ⁻¹ Ldual hLdual hDualAgree
    a ha (fun s ↦ logMellin f (1 / 2 - s)) V hV'
  refine ⟨hi, ?_⟩
  rw [hd, hr, add_add_add_comm, add_div, heckeExplicitFormula_centeredLine_gamma χ f hf a ha,
    heckeExplicitFormula_centeredLine_finite χ f hf a ha, add_comm]

/-- Paper: Theorem B.4.2.2, p. 616. The centered divisor sum equals the
discriminant–conductor term, minus the prime-power series, plus the gamma terms.
Deviation: Signed meromorphic orders count zeros and the actual poles of the
norm twist. The archimedean terms use the convergent digamma kernel with the
local sign parity or angular weight from §3.2. -/
theorem hasSum_heckeExplicitFormula (χ : U[F]) (f : 𝓢(ℝ, ℂ)) (_hf : ExponentialDecay f)
    (L : ℂ → ℂ) (_hL : MeromorphicNFOn L univ)
    (_hAgree : ∀ s : halfPlane, L s = completedHeckeL χ s) :
    HasSum (fun ρ : ℂ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin f (ρ - 1 / 2))
      ((heckeLogDiscriminantConductor χ : ℂ) * f 0 - (∑' j, primeTerm(χ, f) j) +
        ∑ w : InfinitePlace F, if hw : w.IsReal then
          let p := (realHeckeCharacter_parameters χ w hw).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel (1 / 2)
            ((1 / 2 + p.1 + p.2.val) / 2) ((1 / 2 - p.1 + p.2.val) / 2) f t) -
              (Real.log Real.pi : ℂ) * f 0
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1
            (1 / 2 + p.1 + (p.2.natAbs : ℂ) / 2)
            (1 / 2 - p.1 + (p.2.natAbs : ℂ) / 2) f t) -
              2 * (Real.log (2 * Real.pi) : ℂ) * f 0) := by
  obtain ⟨g, hg, hgf⟩ := hasSum_heckeExplicitFormula_centeredProfile f _hf
  -- The Mellin transform of the centred profile is the shifted Mellin transform.
  have hshift (s : ℂ) : logMellin g s = logMellin f (s - 1 / 2) := by
    have h1 : logMellin g s =
        mellin (fun t : ℝ ↦ (t : ℂ) ^ (-(1 / 2 : ℂ)) • f (Real.log t)) s := by
      show ∫ t in Ioi (0 : ℝ), _ = ∫ t in Ioi (0 : ℝ), _
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
      have ht' : (0 : ℝ) < t := ht
      simp only [hgf, smul_eq_mul]
      congr 2
      rw [show -Real.log t / 2 = Real.log t * (-(1 / 2 : ℝ)) by ring, ← Real.rpow_def_of_pos ht',
        Complex.ofReal_cpow ht'.le]
      simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    rw [h1, mellin_cpow_smul, sub_eq_add_neg]
  have hfun : (fun s ↦ logMellin g s * logDeriv L s) =
      fun s ↦ logMellin f (s - 1 / 2) * logDeriv L s := funext fun s ↦ by rw [hshift]
  obtain ⟨Ldual, hLdual, hDualAgree⟩ := completedHeckeL_exists_continuation χ⁻¹
  obtain ⟨-, -, hsum⟩ :=
    hasSum_heckeAsymptoticResidue χ g hg L _hL _hAgree (3 / 2) (by norm_num) (by norm_num)
  obtain ⟨hintDual, hline⟩ := heckeExplicitFormula_centeredLine χ f _hf L Ldual _hL _hAgree hLdual
    hDualAgree (3 / 2) (by norm_num) (by norm_num)
  set κ : ℂ := (heckeLogDiscriminantConductor χ : ℂ) with hκ
  have hΦgInt : Complex.VerticalIntegrable (logMellin g) (1 - 3 / 2) :=
    (uniformlySchwartzOnStrip_mellin_of_exponentialDecay g hg (-2) 2 (by norm_num)).verticalIntegrable
      _ ⟨by norm_num, by norm_num⟩
  -- On the left line the reflection formula turns the integrand around.
  have hleft (y : ℝ) :
      logMellin g (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) *
          logDeriv L (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        -(logMellin f (1 / 2 - (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) *
          logDeriv Ldual (((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I)) -
          κ * logMellin g (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) := by
    set s : ℂ := ((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I with hs
    set s' : ℂ := ((3 / 2 : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I with hs'
    have hsre : s.re < 0 := by
      simp [hs]
      norm_num
    have hord := hasSum_heckeAsymptoticResidue_order_left χ L _hL _hAgree s hsre
    have hrefl := completedHeckeL_logDeriv_reflection χ L Ldual _hL _hAgree hLdual hDualAgree s hord
    have h1s : 1 - s = s' := by
      simp only [hs, hs']
      push_cast
      ring
    have h1s' : 1 / 2 - s' = s - 1 / 2 := by
      rw [← h1s]
      ring
    rw [hrefl, h1s, h1s', ← hshift]
    ring
  have hVleft : verticalLineIntegral (fun s ↦ logMellin g s * logDeriv L s) (1 - 3 / 2) =
      -(verticalLineIntegral (fun s ↦ logMellin f (1 / 2 - s) * logDeriv Ldual s) (3 / 2)) -
        κ * verticalLineIntegral (logMellin g) (1 - 3 / 2) := by
    have hintDual' : Integrable (fun y : ℝ ↦
        logMellin f (1 / 2 - (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
          logDeriv Ldual (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) := hintDual
    have hF := hintDual'.comp_neg
    have hΦ : Integrable (fun y : ℝ ↦ logMellin g (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) :=
      hΦgInt
    show Complex.I * (∫ y : ℝ, _) = -(Complex.I * (∫ y : ℝ, _)) - κ * (Complex.I * (∫ y : ℝ, _))
    beta_reduce
    rw [integral_congr_ae (Eventually.of_forall hleft),
      integral_sub (f := fun y : ℝ ↦ -((fun y : ℝ ↦
        logMellin f (1 / 2 - (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
          logDeriv Ldual (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) (-y)))
        (g := fun y : ℝ ↦ κ * logMellin g (((1 - 3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I))
        hF.neg (hΦ.const_mul κ),
      integral_neg, integral_const_mul, integral_neg_eq_self (fun y : ℝ ↦
        logMellin f (1 / 2 - (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)) *
          logDeriv Ldual (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I))]
    ring
  have hκterm : verticalLineIntegral (logMellin g) (1 - 3 / 2) / twoPiI = f 0 := by
    rw [verticalLineIntegral_div_eq_mellinInv_one _ _ hΦgInt,
      mellinInv_mellin_eq (1 - 3 / 2 : ℝ) (fun t : ℝ ↦ g (Real.log t)) one_pos
        (mellinConvergent_of_exponentialDecay g hg _) hΦgInt
        (g.continuous.continuousAt.comp (Real.continuousAt_log one_ne_zero))]
    simp [hgf]
  rw [show (fun ρ : ℂ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin f (ρ - 1 / 2)) =
      fun ρ ↦ (MeromorphicOn.divisor L univ ρ : ℂ) * logMellin g ρ from
    funext fun ρ ↦ by rw [hshift]]
  convert hsum using 1
  rw [hVleft, hfun]
  linear_combination -hline - κ * hκterm

end MellinExplicitFormula

local notation "𝒮ₐ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "𝒟(" G ")" => BruhatCompactSupport G
local notation "addTest(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "O(" v ")" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "μ𝔭(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "ν𝔭(" v ")" => finiteLocalAdditiveTamagawaMeasure F v
local notation "ν∞(" w ")" => infiniteLocalAdditiveTamagawaMeasure F w
local notation "ψ𝔭(" v ")" => finiteLocalStandardCharacter F v
local notation "ψ∞(" w ")" => (fun x ↦ adeleStandardCharacter F
  (@Pi.single _ _ _ (Classical.decEq _) w x, 0))
local notation "V𝔭(" v ")" => ((μ𝔭(v) (O(v)).units).toReal)
local notation "finiteWeilScale(" v ")" => ((Real.log q(v) / V𝔭(v) : ℝ) : ℂ)

-- Use the local-field topology and Borel measures of Appendix A.
local instance instFiniteCompletionUnitsLocallyCompactSec4b (v : Primes(F)) :
    LocallyCompactSpace (v.adicCompletion F)ˣ :=
  letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  inferInstance

local instance instFiniteCompletionMeasurableSec4b (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance instFiniteCompletionUnitsMeasurableSec4b (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _
local instance instInfiniteCompletionMeasurableSec4b (w : InfinitePlace F) :
    MeasurableSpace w.Completion := borel _
local instance instIdeleClassT2Sec4b : T2Space C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactSec4b : LocallyCompactSpace C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instIdeleClassMeasurableSec4b : MeasurableSpace C[F] := borel _
local instance instNormOneIdeleClassMeasurableSec4b :
    MeasurableSpace (MonoidHom.ker (ideleClassNorm F)) := borel _

local notation "J𝔭(" v ")" =>
  (fun y : HeightOneSpectrum.adicCompletion F v ↦ (Real.log ‖y‖ / Real.log q(v) : ℝ))
local notation "J∞(" w ")" =>
  (fun y : InfinitePlace.Completion w ↦ Real.log (‖y‖ ^ InfinitePlace.mult w))
local notation "logFourierIntegrand(" ν ", " ψ ", " J ", " f ")" =>
  (fun y ↦ ((J y : ℝ) : ℂ) * tamagawaFourier ν ψ f y)

section LocalScaling

open scoped Pointwise

local instance instFiniteCompletionLocallyCompactSec4bScaling (v : Primes(F)) :
    LocallyCompactSpace (v.adicCompletion F) :=
  letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  inferInstance

/-- The Haar character of multiplication by a unit on a finite completion is the norm.
The multiplicative measure is invariant and has density the inverse norm, which compares
the additive masses of the unit sphere and of its dilate. -/
private theorem finiteLocalAdditive_distribHaarChar (v : Primes(F))
    (w : (v.adicCompletion F)ˣ) :
    distribHaarChar (v.adicCompletion F) w = ‖w.val‖₊ := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  let ν : Measure K := ν𝔭(v)
  let : ν.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : ν.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  have he := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let C : ENNReal := (v.asIdeal.absNorm : ENNReal) / ((v.asIdeal.absNorm : ENNReal) - 1)
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hC0 : C ≠ 0 := ENNReal.div_ne_zero.mpr ⟨(zero_lt_one.trans hq).ne',
    ENNReal.sub_ne_top (ENNReal.natCast_ne_top _)⟩
  have hCtop : C ≠ ⊤ := ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (tsub_pos_of_lt hq).ne'
  -- Away from zero the multiplicative mass is `C` times the inverse-norm integral.
  have hmass (A : Set K) (hA : MeasurableSet A) (h0 : (0 : K) ∉ A) :
      μ𝔭(v) (Units.val ⁻¹' A) = C * ∫⁻ x in A, (↑‖x‖₊ : ENNReal)⁻¹ ∂ν := by
    have hsub : A ⊆ range (Units.val : Kˣ → K) := fun x hx ↦
      ⟨Units.mk0 x (fun h ↦ h0 (h ▸ hx)), rfl⟩
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, smul_apply, smul_eq_mul,
      he.comap_apply, image_preimage_eq_of_subset hsub, withDensity_apply _ hA]
  let S : Set K := Metric.sphere 0 1
  have hSo : IsOpen S := IsUltrametricDist.isOpen_sphere (0 : K) one_ne_zero
  have hS0 : (0 : K) ∉ S := by simp [S]
  have hSν0 : ν S ≠ 0 := (hSo.measure_pos ν ⟨1, by simp [S]⟩).ne'
  have hSνtop : ν S ≠ ⊤ := (isCompact_sphere (0 : K) 1).measure_lt_top.ne
  have hwS : w • S = Metric.sphere 0 ‖w.val‖ := by
    ext x
    rw [mem_smul_set_iff_inv_smul_mem, Units.smul_def, mem_sphere_zero_iff_norm,
      mem_sphere_zero_iff_norm, smul_eq_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
      inv_mul_eq_one₀ (norm_ne_zero_iff.mpr w.ne_zero), eq_comm]
  have hwSm : MeasurableSet (w • S) := hSo.measurableSet.const_smul w
  have hw0 : (0 : K) ∉ w • S := by
    rw [hwS, mem_sphere_zero_iff_norm, norm_zero]
    exact (norm_pos_iff.mpr w.ne_zero).ne
  have hwn : (↑‖w.val‖₊ : ENNReal) ≠ 0 := by simp [w.ne_zero]
  apply distribHaarChar_eq_of_measure_smul_eq_mul hSν0 hSνtop
  have hinv : μ𝔭(v) (Units.val ⁻¹' (w • S)) = μ𝔭(v) (Units.val ⁻¹' S) := by
    have hpre : Units.val ⁻¹' (w • S) = (fun u ↦ w⁻¹ * u) ⁻¹' (Units.val ⁻¹' S) := by
      ext u
      simp only [mem_preimage, Units.val_mul, Units.smul_def]
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ w.ne_zero, smul_eq_mul, Units.val_inv_eq_inv_val]
    rw [hpre, measure_preimage_mul]
  rw [hmass _ hwSm hw0, hmass _ hSo.measurableSet hS0,
    setLIntegral_congr_fun hwSm (g := fun _ ↦ (↑‖w.val‖₊ : ENNReal)⁻¹) (fun x hx ↦ by
      rw [hwS, mem_sphere_zero_iff_norm] at hx
      simp only [show ‖x‖₊ = ‖w.val‖₊ from NNReal.eq hx]),
    setLIntegral_congr_fun hSo.measurableSet (g := fun _ ↦ (1 : ENNReal)) (fun x hx ↦ by
      rw [mem_sphere_zero_iff_norm] at hx
      simp [show ‖x‖₊ = 1 from NNReal.eq hx]),
    setLIntegral_const, setLIntegral_const, one_mul] at hinv
  have h := (ENNReal.mul_right_inj hC0 hCtop).mp hinv
  calc ν (w • S) = ↑‖w.val‖₊ * ((↑‖w.val‖₊ : ENNReal)⁻¹ * ν (w • S)) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hwn ENNReal.coe_ne_top, one_mul]
    _ = _ := by rw [h]

/-- Multiplication by a unit pushes additive Tamagawa measure forward to its multiple by
the inverse norm. -/
private theorem finiteLocalAdditive_map_mul (v : Primes(F)) (u : (v.adicCompletion F)ˣ) :
    (ν𝔭(v)).map (u.val * ·) = ENNReal.ofReal ‖u.val‖⁻¹ • ν𝔭(v) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let ν : Measure K := ν𝔭(v)
  let : ν.IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : ν.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  ext s hs
  rw [Measure.map_apply (measurable_const_mul _) hs, smul_apply, smul_eq_mul]
  have hpre : (u.val * ·) ⁻¹' s = u⁻¹ • s := by
    ext x
    rw [mem_preimage, Set.mem_inv_smul_set_iff]
    rfl
  rw [hpre, ← distribHaarChar_mul, finiteLocalAdditive_distribHaarChar, Units.val_inv_eq_inv_val,
    nnNorm_inv, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, coe_nnNorm]

/-- Integrals against additive Tamagawa measure change by the inverse norm under dilation. -/
private theorem finiteLocalAdditive_integral_comp_mul (v : Primes(F))
    (u : (v.adicCompletion F)ˣ) (h : v.adicCompletion F → ℂ) :
    (∫ y, h (u.val * y) ∂ν𝔭(v)) = (‖u.val‖⁻¹ : ℝ) • ∫ z, h z ∂ν𝔭(v) := by
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let e := (Homeomorph.mulLeft₀ u.val u.ne_zero).toMeasurableEquiv
  calc (∫ y, h (u.val * y) ∂ν𝔭(v)) = ∫ y, h (e y) ∂ν𝔭(v) := rfl
    _ = ∫ z, h z ∂((ν𝔭(v)).map e) := (integral_map_equiv e h).symm
    _ = _ := by
      rw [show ⇑e = (u.val * · : _ → _) from rfl, finiteLocalAdditive_map_mul,
        integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (norm_nonneg _))]

/-- Integrability against additive Tamagawa measure is invariant under dilation. -/
private theorem finiteLocalAdditive_integrable_comp_mul (v : Primes(F))
    (u : (v.adicCompletion F)ˣ) {h : v.adicCompletion F → ℂ} (hh : Integrable h ν𝔭(v)) :
    Integrable (fun y ↦ h (u.val * y)) ν𝔭(v) := by
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let e := (Homeomorph.mulLeft₀ u.val u.ne_zero).toMeasurableEquiv
  have h' : Integrable h ((ν𝔭(v)).map e) := by
    rw [show ⇑e = (u.val * · : _ → _) from rfl, finiteLocalAdditive_map_mul]
    exact hh.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_equiv e h).mp h'

/-- Fourier inversion at zero: the Fourier transform of an additive test is integrable,
with integral the value of the test at zero. -/
private theorem finiteLocal_integral_tamagawaFourier (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) :
    Integrable (tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f)) ν𝔭(v) ∧
      (∫ y, tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) = addTest(f) 0 := by
  let K := v.adicCompletion F
  let G := Multiplicative K
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨e, he, hP⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  let μ : Measure G := ν𝔭(v)
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  have hinv := schwartzBruhat_inverse_integral μ _ hP f 1
  have hF (y : K) : lcaFourier μ f (e (Multiplicative.ofAdd y)) =
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y :=
    (tamagawaFourier_eq_lcaFourier _ _ _ y _ fun x ↦ (he y x).trans
      (congrArg _ (mul_comm y x))).symm
  let E := e.toHomeomorph.toMeasurableEquiv
  obtain ⟨hI, hval⟩ := hinv
  simp only [map_one, Circle.coe_one, mul_one] at hI hval
  change Integrable _ (Measure.map E μ) at hI
  change _ = ∫ χ, _ ∂(Measure.map E μ) at hval
  rw [integral_map_equiv] at hval
  have hI' := (integrable_map_equiv E _).mp hI
  refine ⟨hI'.congr (ae_of_all _ fun y ↦ hF y.toAdd), ?_⟩
  refine (integral_congr_ae (ae_of_all _ fun y ↦ (hF y).symm)).trans (hval.symm.trans ?_)
  rfl


/-- The normalized logarithm transforms additively under dilation, away from zero. -/
private theorem finiteLog_mul (v : Primes(F)) (a : (v.adicCompletion F)ˣ)
    {y : v.adicCompletion F} (hy : y ≠ 0) :
    (((J𝔭(v) (a.val * y)) : ℝ) : ℂ) =
      ((J𝔭(v) y : ℝ) : ℂ) + ((Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) := by
  simp only [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr a.ne_zero) (norm_ne_zero_iff.mpr hy),
    add_div]
  push_cast
  ring

/-- Dilating the argument of the Fourier transform against the normalized logarithm
shifts the pairing by the logarithm of the dilation times the value at zero. -/
private theorem finiteLogFourier_comp_mul (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F))
    (a : (v.adicCompletion F)ˣ)
    (hint : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v)) :
    Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)) ν𝔭(v) ∧
    (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) ∂ν𝔭(v)) =
      (‖a.val‖⁻¹ : ℝ) • ((∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
        tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) -
        ((Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * addTest(f) 0) := by
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  obtain ⟨hFI, hF0⟩ := finiteLocal_integral_tamagawaFourier v f
  let L : ℂ := ((Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ)
  let φ := tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f)
  let h : v.adicCompletion F → ℂ := fun z ↦ (((J𝔭(v) z : ℝ) : ℂ) - L) * φ z
  have hh : Integrable h ν𝔭(v) := by
    refine (hint.sub (hFI.const_mul L)).congr (ae_of_all _ fun z ↦ ?_)
    simp only [Pi.sub_apply, h, sub_mul]
    rfl
  have hae : (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) * φ (a.val * y)) =ᵐ[ν𝔭(v)]
      fun y ↦ h (a.val * y) := by
    have h0 : ∀ᵐ y ∂ν𝔭(v), y ≠ 0 := by
      have : (𝓝[≠] (0 : v.adicCompletion F)).NeBot := by
        let := Valued.toNontriviallyNormedField (v.adicCompletion F) _
        exact NormedField.nhdsNE_neBot 0
      rw [ae_iff]
      simp
    filter_upwards [h0] with y hy0
    simp only [h, finiteLog_mul v a hy0, L, add_sub_cancel_right]
  refine ⟨(finiteLocalAdditive_integrable_comp_mul v a hh).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, finiteLocalAdditive_integral_comp_mul v a h]
  congr 1
  simp only [h, sub_mul]
  rw [integral_sub hint (hFI.const_mul L), integral_const_mul]
  change _ - L * ∫ y, φ y ∂ν𝔭(v) = _
  rw [hF0]

/-- Multiplicative integrability on the units is additive integrability against the
inverse norm. -/
private theorem finiteLocal_units_integrable_iff (v : Primes(F)) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : v.adicCompletion F → E) :
    Integrable (fun u : (v.adicCompletion F)ˣ ↦ g u.val) μ𝔭(v) ↔
      Integrable (fun y ↦ ‖y‖⁻¹ • g y) ν𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let c : ENNReal := (↑v.asIdeal.absNorm / (↑v.asIdeal.absNorm - 1) : ENNReal)
  let d : K → ENNReal := fun x ↦ (↑‖x‖₊ : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hdlt : ∀ᵐ y ∂(ν𝔭(v).restrict (range (Units.val : Kˣ → K))), d y < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])
  have hdy (y : K) : (d y).toReal = ‖y‖⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm]
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hc0 : c ≠ 0 :=
    (ENNReal.div_pos (zero_lt_one.trans hq).ne' (ENNReal.sub_ne_top (ENNReal.natCast_ne_top _))).ne'
  have hct : c ≠ ⊤ :=
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (tsub_pos_of_lt hq).ne').ne
  have hsupp : support (fun y ↦ ‖y‖⁻¹ • g y) ⊆ range (Units.val : Kˣ → K) := by
    intro y hy
    have : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y this, rfl⟩
  rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity]
  rw [integrable_smul_measure hc0 hct, show (fun u : Kˣ ↦ g u.val) = g ∘ Units.val from rfl,
    ← hval.integrable_map_iff (g := g), hval.map_comap,
    restrict_withDensity hval.measurableSet_range,
    integrable_withDensity_iff_integrable_smul' hd hdlt,
    ← integrableOn_iff_integrable_of_support_subset hsupp]
  simp_rw [hdy]
  rfl

/-- The Fourier transform of an additive test is again an additive test. -/
private theorem finiteLocal_exists_fourier_test (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F)) :
    ∃ g : 𝒮ₐ(v.adicCompletion F), ∀ y,
      addTest(g) y = tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y := by
  let K := v.adicCompletion F
  let G := Multiplicative K
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  obtain ⟨e, he, -⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  let μ : Measure G := ν𝔭(v)
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  obtain ⟨T, hT⟩ := schwartzBruhat_fourier_equiv μ
  obtain ⟨P, hP⟩ := exists_schwartzBruhat_comp_equivCLM e
  refine ⟨P (T f), fun y ↦ ?_⟩
  calc P (T f) (Multiplicative.ofAdd y) = T f (e (Multiplicative.ofAdd y)) := hP _ _
    _ = lcaFourier μ f (e (Multiplicative.ofAdd y)) := (hT f).2 _
    _ = _ := (tamagawaFourier_eq_lcaFourier _ _ _ y _ fun x ↦ (he y x).trans
      (congrArg _ (mul_comm y x))).symm

/-- The logarithm of the norm is dominated by the sum of two square-root weights. -/
private theorem abs_log_le_two_mul_rpow {t : ℝ} (ht : 0 < t) :
    |Real.log t| ≤ 2 * (t⁻¹ * t ^ (1 / 2 : ℝ) + t⁻¹ * t ^ (3 / 2 : ℝ)) := by
  have e1 : t⁻¹ * t ^ (1 / 2 : ℝ) = t⁻¹ ^ (1 / 2 : ℝ) := by
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg_one, ← Real.rpow_add ht, ← Real.rpow_neg ht.le]
    norm_num
  have e2 : t⁻¹ * t ^ (3 / 2 : ℝ) = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    norm_num
  rw [e1, e2]
  have h1 := Real.log_le_rpow_div ht.le (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 := Real.log_le_rpow_div (inv_pos.mpr ht).le (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [Real.log_inv] at h2
  have p1 : 0 ≤ t ^ (1 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  have p2 : 0 ≤ t⁻¹ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (inv_pos.mpr ht).le _
  rw [abs_le]
  constructor <;> linarith

/-- The normalized logarithm is integrable against every additive test. -/
private theorem finiteLog_integrable_mul_test (v : Primes(F)) (g : 𝒮ₐ(v.adicCompletion F)) :
    Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) * addTest(g) y) ν𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : ProperSpace K := properSpace_adicCompletion v
  let h : K → ℂ := addTest(g)
  have hh : Continuous h := (schwartzBruhat_continuous g).comp continuous_ofAdd
  have hw (s : ℝ) (hs : 0 < s) :
      Integrable (fun y : K ↦ ‖y‖⁻¹ • (‖h y‖ * ‖y‖ ^ s)) ν𝔭(v) := by
    refine (finiteLocal_units_integrable_iff v (fun y : K ↦ ‖h y‖ * ‖y‖ ^ s)).mp ?_
    have hz := finiteLocalIdelicZetaIntegral_integrable v g 1 (s := (s : ℂ)) (by simpa using hs)
    refine hz.norm.congr (ae_of_all _ fun u ↦ ?_)
    change ‖h u.val * _‖ = ‖h u.val‖ * ‖u.val‖ ^ s
    rw [norm_mul]
    congr 1
    change ‖((1 : PontryaginDual Kˣ) u : ℂ) *
      ((((Units.map (nnNormHom : K →*₀ ℝ≥0).toMonoidHom u : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (s : ℂ)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _)),
      Complex.ofReal_re]
    rfl
  have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hlq : 0 < Real.log q(v) := Real.log_pos hq
  refine (((hw _ (by norm_num : (0 : ℝ) < 1 / 2)).add
    (hw _ (by norm_num : (0 : ℝ) < 3 / 2))).const_mul (2 / Real.log q(v))).mono' ?_
    (ae_of_all _ fun y ↦ ?_)
  · exact (Measurable.aestronglyMeasurable (by fun_prop)).mul hh.aestronglyMeasurable
  · simp only [Pi.add_apply, smul_eq_mul]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hlq]
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have ht : 0 < ‖y‖ := norm_pos_iff.mpr hy
    have hl := abs_log_le_two_mul_rpow ht
    calc |Real.log ‖y‖| / Real.log q(v) * ‖h y‖
        ≤ 2 * (‖y‖⁻¹ * ‖y‖ ^ (1 / 2 : ℝ) + ‖y‖⁻¹ * ‖y‖ ^ (3 / 2 : ℝ)) / Real.log q(v) * ‖h y‖ := by
          gcongr
      _ = _ := by ring

end LocalScaling

section LocalFourier

/-- Paper: Proposition B.4.3.1(1), p. 617. Dilation of the additive test
changes the Fourier transform of the normalized logarithm by a multiple of evaluation at zero. -/
theorem finiteLogFourier_dilate (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F))
    (a : (v.adicCompletion F)ˣ) :
    let K : (v.adicCompletion F → ℂ) → v.adicCompletion F → ℂ :=
      fun g ↦ logFourierIntegrand(ν𝔭(v), ψ𝔭(v), J𝔭(v), g)
    Integrable (K (addTest(f) ∘ (fun x ↦ a.inv * x))) ν𝔭(v) ∧
      Integrable (K addTest(f)) ν𝔭(v) ∧
      (∫ y, K (addTest(f) ∘ (fun x ↦ a.inv * x)) y ∂ν𝔭(v)) =
        (∫ y, K addTest(f) y ∂ν𝔭(v)) -
          (Real.log ‖a.val‖ / Real.log q(v) : ℝ) * addTest(f) 0 := by
  intro K
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let φ := tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f)
  obtain ⟨g, hg⟩ := finiteLocal_exists_fourier_test v f
  have hint : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) * φ y) ν𝔭(v) :=
    (finiteLog_integrable_mul_test v g).congr (ae_of_all _ fun y ↦ by
      simp only [hg]; rfl)
  obtain ⟨hI, hEq⟩ := finiteLogFourier_comp_mul v f a hint
  -- Fourier transform of the dilated test.
  have hFT (y : v.adicCompletion F) :
      tamagawaFourier ν𝔭(v) ψ𝔭(v) (addTest(f) ∘ (fun x ↦ a.inv * x)) y =
        ((‖a.val‖ : ℝ) : ℂ) * φ (a.val * y) := by
    have h := finiteLocalAdditive_integral_comp_mul v a⁻¹
      (fun z ↦ addTest(f) z * star (ψ𝔭(v) (z * (a.val * y)) : ℂ))
    rw [Units.val_inv_eq_inv_val, norm_inv, inv_inv, Complex.real_smul] at h
    unfold tamagawaFourier
    refine Eq.trans ?_ h
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    have hx : (a.val)⁻¹ * x * (a.val * y) = x * y := by
      rw [mul_mul_mul_comm, inv_mul_cancel₀ a.ne_zero, one_mul]
    have ha : a.inv = (a.val)⁻¹ := Units.val_inv_eq_inv_val a
    simp only [Function.comp_apply]
    rw [hx, ha]
  have hK (y : v.adicCompletion F) : K (addTest(f) ∘ (fun x ↦ a.inv * x)) y =
      ((‖a.val‖ : ℝ) : ℂ) * (((J𝔭(v) y : ℝ) : ℂ) * φ (a.val * y)) := by
    change ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v)
      (addTest(f) ∘ (fun x ↦ a.inv * x)) y = _
    rw [hFT]
    ring
  have hne : ((‖a.val‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_pos_iff.mpr a.ne_zero).ne'
  refine ⟨(hI.const_mul _).congr (ae_of_all _ fun y ↦ (hK y).symm), hint, ?_⟩
  rw [integral_congr_ae (ae_of_all _ hK), integral_const_mul, hEq, Complex.real_smul,
    ← mul_assoc, Complex.ofReal_inv, mul_inv_cancel₀ hne, one_mul]

/-- The norm on a finite completion is discrete: a norm in `(q⁻¹, 1]` equals `1`. -/
private theorem finiteLogFourier_eq_neg_haar_norm_eq_one (v : Primes(F))
    (x : v.adicCompletion F) (h1 : ‖x‖ ≤ 1) (h2 : q(v)⁻¹ < ‖x‖) : ‖x‖ = 1 := by
  have hx0 : Valued.v x ≠ 0 := by
    intro h
    have : x = 0 := (map_eq_zero _).mp h
    subst this
    simp at h2
    exact absurd h2 (not_lt.mpr (by positivity))
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hn : ‖x‖ = q(v) ^ WithZero.log (Valued.v x) := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hx0]
    simp
  rw [hn] at h1 h2 ⊢
  rw [← zpow_neg_one] at h2
  have a := (zpow_lt_zpow_iff_right₀ hq).mp h2
  have b := (zpow_le_zpow_iff_right₀ hq).mp (h1.trans_eq (zpow_zero _).symm)
  rw [show WithZero.log (Valued.v x) = 0 by omega, zpow_zero]

/-- Additive tests are locally constant with compact support. -/
private theorem finiteLogFourier_eq_neg_haar_testFacts (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) :
    IsLocallyConstant addTest(f) ∧ HasCompactSupport addTest(f) :=
  (mem_finitePlaceSchwartz_iff F v _).mp ⟨f, fun _ ↦ rfl⟩

/-- A continuous compactly supported function is bounded and supported in a ball. -/
private theorem finiteLogFourier_eq_neg_haar_bound (v : Primes(F))
    (φ : v.adicCompletion F → ℂ) (hc : Continuous φ) (hs : HasCompactSupport φ) :
    ∃ C R : ℝ, 0 < R ∧ (∀ z, ‖φ z‖ ≤ C) ∧ ∀ z, φ z ≠ 0 → ‖z‖ ≤ R := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hs.isCompact.isBounded
  refine ⟨C, max R 1, lt_max_of_lt_right one_pos, hC, fun z hz ↦ ?_⟩
  have := hR (subset_tsupport φ hz)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact this.trans (le_max_left _ _)

/-- A locally constant function vanishing at zero vanishes on a ball around zero. -/
private theorem finiteLogFourier_eq_neg_haar_vanish (v : Primes(F))
    (h : v.adicCompletion F → ℂ) (hl : IsLocallyConstant h) (h0 : h 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ x, h x ≠ 0 → r ≤ ‖x‖ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hl.isOpen_fiber 0) 0 h0
  refine ⟨r, hr, fun x hx ↦ not_lt.mp fun hlt ↦ hx ?_⟩
  exact hball (by rwa [Metric.mem_ball, dist_zero_right])

/-- The indicator of a compact clopen set is an additive test. -/
private theorem finiteLogFourier_eq_neg_haar_clopenTest (v : Primes(F))
    (s : Set (v.adicCompletion F)) (hs : IsClopen s) (hc : IsCompact s) :
    ∃ g : 𝒮ₐ(v.adicCompletion F), ∀ y,
      g (Multiplicative.ofAdd y) = s.indicator (fun _ ↦ (1 : ℂ)) y := by
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v (s.indicator (fun _ ↦ (1 : ℂ)))).mpr
    ⟨by
        have h : IsLocallyConstant (LocallyConstant.charFn ℂ hs : _ → ℂ) :=
          (LocallyConstant.charFn ℂ hs).isLocallyConstant
        rw [LocallyConstant.coe_charFn] at h
        exact h,
      HasCompactSupport.intro hc fun y hy ↦ indicator_of_notMem hy _⟩
  exact ⟨g, hg⟩

/-- The absolute value of the logarithm of the norm is integrable on every closed ball
about zero of a finite completion, for additive Tamagawa measure. -/
theorem finiteLog_abs_integrableOn_closedBall (v : Primes(F)) (R : ℝ) :
    IntegrableOn (fun b : v.adicCompletion F ↦ |Real.log ‖b‖|) {b | ‖b‖ ≤ R} ν𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : ProperSpace K := properSpace_adicCompletion v
  let r : ℝ := max R 1
  have hr : (0 : ℝ) < r := lt_max_of_lt_right one_pos
  let B : Set K := Metric.closedBall 0 r
  obtain ⟨g, hg⟩ := finiteLogFourier_eq_neg_haar_clopenTest v B
    (IsUltrametricDist.isClopen_closedBall 0 hr.ne') (isCompact_closedBall 0 r)
  have hint := finiteLog_integrable_mul_test v g
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hlq : 0 < Real.log q(v) := Real.log_pos hq
  have hsub : {b : K | ‖b‖ ≤ R} ⊆ B := fun b (hb : ‖b‖ ≤ R) ↦ by
    simp only [B, Metric.mem_closedBall, dist_zero_right]; exact le_max_of_le_left hb
  refine IntegrableOn.mono_set ?_ hsub
  rw [← integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
  refine (hint.norm.const_mul (Real.log q(v))).congr (ae_of_all _ fun y ↦ ?_)
  simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hlq]
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy, indicator_of_mem hy, norm_one, mul_one, mul_div_cancel₀ _ hlq.ne']
  · rw [indicator_of_notMem hy, indicator_of_notMem hy, norm_zero, mul_zero, mul_zero]

/-- The local standard character is continuous. -/
private theorem finiteLogFourier_eq_neg_haar_charContinuous (v : Primes(F)) :
    Continuous (finiteLocalStandardCharacter F v) := by
  have hψ0 := finiteLocalStandardCharacter_exists_continuousMonoidHom F v
  exact (hψ0.choose.continuous.comp continuous_ofAdd).congr hψ0.choose_spec.1

/-- The Fourier integrand of a continuous compactly supported function is integrable. -/
private theorem finiteLogFourier_eq_neg_haar_fourierIntegrable (v : Primes(F))
    (h : v.adicCompletion F → ℂ) (hc : Continuous h) (hs : HasCompactSupport h)
    (y : v.adicCompletion F) :
    Integrable (fun x ↦ h x * star (ψ𝔭(v) (x * y) : ℂ)) ν𝔭(v) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hψ := finiteLogFourier_eq_neg_haar_charContinuous v
  have hχ : Continuous fun x : v.adicCompletion F ↦ star (ψ𝔭(v) (x * y) : ℂ) :=
    continuous_star.comp (continuous_subtype_val.comp (hψ.comp (continuous_id.mul continuous_const)))
  exact (hc.mul hχ).integrable_of_hasCompactSupport hs.mul_right

/-- The logarithmic Fourier pairing of the indicator of the unit sphere is `-1`. -/
private theorem finiteLogFourier_eq_neg_haar_sphereTest (v : Primes(F)) :
    ∃ g : 𝒮ₐ(v.adicCompletion F),
      (∀ y, addTest(g) y =
        (Metric.sphere (0 : v.adicCompletion F) 1).indicator (fun _ ↦ (1 : ℂ)) y) ∧
      Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
        tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) y) ν𝔭(v) ∧
      (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) y ∂ν𝔭(v)) = -1 := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  obtain ⟨g, hg⟩ := finiteLogFourier_eq_neg_haar_clopenTest v (Metric.sphere (0 : K) 1)
    (IsUltrametricDist.isClopen_sphere 0 one_ne_zero) (isCompact_sphere 0 1)
  obtain ⟨g₁, hg₁⟩ := finiteLogFourier_eq_neg_haar_clopenTest v (Metric.closedBall (0 : K) 1)
    (IsUltrametricDist.isClopen_closedBall 0 one_ne_zero) (isCompact_closedBall 0 1)
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 π.val hπ.ne_zero
  have hp : ‖p.val‖ = q(v)⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  obtain ⟨hI1, hI2, hEq⟩ := finiteLogFourier_dilate v g₁ p
  have hpinv : p.inv = (p.val)⁻¹ := Units.val_inv_eq_inv_val p
  have hpt (x : K) : addTest(g) x =
      addTest(g₁) x - (addTest(g₁) ∘ (fun x ↦ p.inv * x)) x := by
    simp only [Function.comp_apply, hg, hg₁, Set.indicator, Metric.mem_sphere,
      Metric.mem_closedBall, dist_zero_right, hpinv, norm_mul, norm_inv, hp, inv_inv]
    by_cases h1 : ‖x‖ ≤ 1
    · by_cases h2 : ‖x‖ ≤ q(v)⁻¹
      · have hne : ‖x‖ ≠ 1 := fun h ↦ by
          rw [h] at h2
          exact absurd h2 (not_le.mpr (inv_lt_one_of_one_lt₀ hq))
        have : q(v) * ‖x‖ ≤ 1 := by
          calc q(v) * ‖x‖ ≤ q(v) * q(v)⁻¹ := by gcongr
            _ = 1 := mul_inv_cancel₀ (by positivity)
        simp [hne, h1, this]
      · have he := finiteLogFourier_eq_neg_haar_norm_eq_one v x h1 (not_le.mp h2)
        simp [he, not_le.mpr (HeightOneSpectrum.one_lt_absNorm v)]
    · have hne : ‖x‖ ≠ 1 := fun h ↦ h1 h.le
      have : ¬ q(v) * ‖x‖ ≤ 1 := fun h ↦ h1 (by nlinarith [norm_nonneg x])
      simp [hne, h1, this]
  obtain ⟨hl₁, hc₁⟩ := finiteLogFourier_eq_neg_haar_testFacts v g₁
  have hc₁' : HasCompactSupport (addTest(g₁) ∘ (fun x ↦ p.inv * x)) := by
    rw [hpinv]
    exact hc₁.comp_isClosedEmbedding
      (Homeomorph.mulLeft₀ (p.val)⁻¹ (inv_ne_zero p.ne_zero)).isClosedEmbedding
  have hFT (y : K) : tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) y =
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g₁) y -
        tamagawaFourier ν𝔭(v) ψ𝔭(v) (addTest(g₁) ∘ (fun x ↦ p.inv * x)) y := by
    unfold tamagawaFourier
    rw [← integral_sub
      (finiteLogFourier_eq_neg_haar_fourierIntegrable v _ hl₁.continuous hc₁ y)
      (finiteLogFourier_eq_neg_haar_fourierIntegrable v _
        (hl₁.continuous.comp (by fun_prop : Continuous fun x : K ↦ p.inv * x)) hc₁' y)]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    dsimp only
    rw [← sub_mul, ← hpt x]
  refine ⟨g, hg, ?_, ?_⟩
  · refine (hI2.sub hI1).congr (ae_of_all _ fun y ↦ ?_)
    simp only [Pi.sub_apply]
    rw [hFT y, mul_sub]
  · have hJ : ((Real.log ‖p.val‖ / Real.log q(v) : ℝ) : ℂ) = -1 := by
      rw [hp, Real.log_inv, neg_div, div_self (Real.log_pos hq).ne']
      push_cast; ring
    have h0 : addTest(g₁) 0 = 1 := (hg₁ 0).trans (by simp)
    calc (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) y ∂ν𝔭(v))
        = (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g₁) y ∂ν𝔭(v)) -
          ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v)
            (addTest(g₁) ∘ (fun x ↦ p.inv * x)) y ∂ν𝔭(v) := by
          rw [← integral_sub hI2 hI1]
          refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
          dsimp only
          rw [hFT y, mul_sub]
      _ = -1 := by
          rw [hEq, hJ, h0]
          ring

/-- Pairing the normalized logarithm with a dilate of the Fourier transform of the unit
sphere indicator gives minus the inverse norm of the dilation. -/
private theorem finiteLogFourier_eq_neg_haar_kernel (v : Primes(F))
    (x : v.adicCompletion F) (hx : x ≠ 0) :
    (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v)
      ((Metric.sphere (0 : v.adicCompletion F) 1).indicator (fun _ ↦ (1 : ℂ))) (x * y) ∂ν𝔭(v)) =
      -((‖x‖⁻¹ : ℝ) : ℂ) := by
  obtain ⟨g, hg, hint, hL⟩ := finiteLogFourier_eq_neg_haar_sphereTest v
  have he : addTest(g) = (Metric.sphere (0 : v.adicCompletion F) 1).indicator
      (fun _ ↦ (1 : ℂ)) := funext hg
  have h0 : addTest(g) 0 = 0 := (hg 0).trans (by simp)
  have h := (finiteLogFourier_comp_mul v g (Units.mk0 x hx) hint).2
  rw [hL, h0, mul_zero, sub_zero, he, Units.val_mk0] at h
  rw [h, Complex.real_smul]
  ring

/-- Fubini for a product of integrable functions times a bounded continuous kernel. -/
private theorem finiteLogFourier_eq_neg_haar_swap (v : Primes(F))
    (A B : v.adicCompletion F → ℂ) (k : v.adicCompletion F → v.adicCompletion F → ℂ)
    (hA : Integrable A ν𝔭(v)) (hB : Integrable B ν𝔭(v)) (hk : Continuous (Function.uncurry k))
    (C : ℝ) (hC : ∀ a b, ‖k a b‖ ≤ C) :
    (∫ a, ∫ b, A a * B b * k a b ∂ν𝔭(v) ∂ν𝔭(v)) =
      ∫ b, ∫ a, A a * B b * k a b ∂ν𝔭(v) ∂ν𝔭(v) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  apply integral_integral_swap
  exact (hA.mul_prod hB).mul_bdd hk.aestronglyMeasurable (ae_of_all _ fun p ↦ hC p.1 p.2)

/-- Fubini for the normalized logarithm against a dilated bounded kernel, when the
dilations stay away from zero and the kernel has bounded support. -/
private theorem finiteLogFourier_eq_neg_haar_swapLog (v : Primes(F))
    (A Φ : v.adicCompletion F → ℂ) (hA : Integrable A ν𝔭(v)) (r : ℝ) (hr : 0 < r)
    (hAr : ∀ a, A a ≠ 0 → r ≤ ‖a‖) (hΦ : Continuous Φ) (C R : ℝ) (hR : 0 < R)
    (hC : ∀ z, ‖Φ z‖ ≤ C) (hΦR : ∀ z, Φ z ≠ 0 → ‖z‖ ≤ R) :
    (∫ a, A a * ∫ b, ((J𝔭(v) b : ℝ) : ℂ) * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v)) =
      ∫ b, ((J𝔭(v) b : ℝ) : ℂ) * ∫ a, A a * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  obtain ⟨gB, hgB⟩ := finiteLogFourier_eq_neg_haar_clopenTest v (Metric.closedBall (0 : K) (R / r))
    (IsUltrametricDist.isClopen_closedBall 0 (div_pos hR hr).ne') (isCompact_closedBall 0 _)
  let B : K → ℂ := fun b ↦ ((J𝔭(v) b : ℝ) : ℂ) *
    (Metric.closedBall (0 : K) (R / r)).indicator (fun _ ↦ (1 : ℂ)) b
  have hB : Integrable B ν𝔭(v) :=
    (finiteLog_integrable_mul_test v gB).congr (ae_of_all _ fun b ↦ by
      dsimp only [B]
      rw [← hgB b])
  have hpt (a b : K) : A a * (((J𝔭(v) b : ℝ) : ℂ) * Φ (a * b)) = A a * B b * Φ (a * b) := by
    by_cases ha : A a = 0
    · simp [ha]
    by_cases hb : Φ (a * b) = 0
    · simp [hb]
    have h1 := hAr a ha
    have h2 := hΦR _ hb
    rw [norm_mul] at h2
    have hb' : b ∈ Metric.closedBall (0 : K) (R / r) := by
      rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hr]
      nlinarith [norm_nonneg b]
    simp only [B, Set.indicator_of_mem hb', mul_one]
    ring
  have hsw := finiteLogFourier_eq_neg_haar_swap v A B (fun a b ↦ Φ (a * b)) hA hB
    (hΦ.comp (continuous_fst.mul continuous_snd)) C (fun a b ↦ hC _)
  calc (∫ a, A a * ∫ b, ((J𝔭(v) b : ℝ) : ℂ) * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v))
      = ∫ a, ∫ b, A a * B b * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v) := by
        refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
        dsimp only
        rw [← integral_const_mul]
        exact integral_congr_ae (ae_of_all _ fun b ↦ hpt a b)
    _ = ∫ b, ∫ a, A a * B b * Φ (a * b) ∂ν𝔭(v) ∂ν𝔭(v) := hsw
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun b ↦ ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun a ↦ ?_)
        exact (hpt a b).symm.trans (by ring)

/-- Averaging the dilates of a Fourier transform against a test is the Fourier transform of
the test paired with the function. -/
private theorem finiteLogFourier_eq_neg_haar_average (v : Primes(F))
    (s h : v.adicCompletion F → ℂ) (hs : Continuous s) (hs' : HasCompactSupport s)
    (hh : Continuous h) (hh' : HasCompactSupport h) (y : v.adicCompletion F) :
    (∫ u, s u * tamagawaFourier ν𝔭(v) ψ𝔭(v) h (u * y) ∂ν𝔭(v)) =
      ∫ x, h x * tamagawaFourier ν𝔭(v) ψ𝔭(v) s (x * y) ∂ν𝔭(v) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hψ := finiteLogFourier_eq_neg_haar_charContinuous v
  let k : v.adicCompletion F → v.adicCompletion F → ℂ :=
    fun u x ↦ star (ψ𝔭(v) (x * (u * y)) : ℂ)
  have hk : Continuous (Function.uncurry k) :=
    continuous_star.comp (continuous_subtype_val.comp (hψ.comp
      (continuous_snd.mul (continuous_fst.mul continuous_const))))
  have hsw := finiteLogFourier_eq_neg_haar_swap v s h k
    (hs.integrable_of_hasCompactSupport hs') (hh.integrable_of_hasCompactSupport hh') hk 1
    (fun a b ↦ by simp [k])
  unfold tamagawaFourier
  calc (∫ u, s u * ∫ x, h x * star (ψ𝔭(v) (x * (u * y)) : ℂ) ∂ν𝔭(v) ∂ν𝔭(v))
      = ∫ u, ∫ x, s u * h x * k u x ∂ν𝔭(v) ∂ν𝔭(v) := by
        refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        dsimp only [k]
        ring
    _ = ∫ x, ∫ u, s u * h x * k u x ∂ν𝔭(v) ∂ν𝔭(v) := hsw
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        dsimp only
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
        dsimp only [k]
        rw [show u * (x * y) = x * (u * y) by ring]
        ring

/-- Integrals against multiplicative Tamagawa measure are additive integrals against the
inverse norm, up to the constant `q / (q - 1)`. -/
private theorem finiteLogFourier_eq_neg_haar_unitsIntegral (v : Primes(F))
    (g : v.adicCompletion F → ℂ) :
    (∫ u : (v.adicCompletion F)ˣ, g u.val ∂μ𝔭(v)) =
      ((v.asIdeal.absNorm : ENNReal) / ((v.asIdeal.absNorm : ENNReal) - 1)).toReal •
        ∫ y, ‖y‖⁻¹ • g y ∂ν𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let d : K → ENNReal := fun x ↦ (↑‖x‖₊ : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hdlt : ∀ᵐ y ∂(ν𝔭(v).restrict (range (Units.val : Kˣ → K))), d y < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])
  have hdy (y : K) : (d y).toReal = ‖y‖⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm]
  rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, integral_smul_measure]
  congr 1
  rw [← hval.integral_map g, hval.map_comap, restrict_withDensity hval.measurableSet_range,
    integral_withDensity_eq_integral_toReal_smul hd hdlt]
  simp_rw [hdy]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_
  have : y = 0 := by
    by_contra h
    exact hy ⟨Units.mk0 y h, rfl⟩
  simp [this]

/-- Averaging over the unit sphere: the mass of the sphere times the logarithmic Fourier
pairing of a test vanishing at zero is minus its integral against the inverse norm. -/
private theorem finiteLogFourier_eq_neg_haar_identity (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) (hf : addTest(f) 0 = 0)
    (hint : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v)) :
    ((ν𝔭(v)).real (Metric.sphere (0 : v.adicCompletion F) 1) : ℂ) *
        (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) =
      -∫ x, ((‖x‖⁻¹ : ℝ) : ℂ) * addTest(f) x ∂ν𝔭(v) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let S := Metric.sphere (0 : K) 1
  let s1 : K → ℂ := S.indicator (fun _ ↦ (1 : ℂ))
  have hSc : IsClopen S := IsUltrametricDist.isClopen_sphere 0 one_ne_zero
  obtain ⟨g₀, hg₀⟩ := finiteLogFourier_eq_neg_haar_clopenTest v S hSc (isCompact_sphere 0 1)
  have hs1 : addTest(g₀) = s1 := funext hg₀
  obtain ⟨hl₀, hc₀⟩ := finiteLogFourier_eq_neg_haar_testFacts v g₀
  rw [hs1] at hl₀ hc₀
  obtain ⟨G, hG⟩ := finiteLocal_exists_fourier_test v g₀
  have hG' : addTest(G) = tamagawaFourier ν𝔭(v) ψ𝔭(v) s1 := by
    rw [← hs1]
    exact funext hG
  obtain ⟨lG, cG⟩ := finiteLogFourier_eq_neg_haar_testFacts v G
  rw [hG'] at lG cG
  obtain ⟨CG, RG, hRG, hCG, hGR⟩ := finiteLogFourier_eq_neg_haar_bound v _ lG.continuous cG
  obtain ⟨g, hg⟩ := finiteLocal_exists_fourier_test v f
  have hφ : addTest(g) = tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) := funext hg
  obtain ⟨lφ, cφ⟩ := finiteLogFourier_eq_neg_haar_testFacts v g
  rw [hφ] at lφ cφ
  obtain ⟨Cφ, Rφ, hRφ, hCφ, hφR⟩ := finiteLogFourier_eq_neg_haar_bound v _ lφ.continuous cφ
  obtain ⟨hfl, hfc⟩ := finiteLogFourier_eq_neg_haar_testFacts v f
  obtain ⟨r, hr, hvan⟩ := finiteLogFourier_eq_neg_haar_vanish v _ hfl hf
  have hs1i : Integrable s1 ν𝔭(v) := hl₀.continuous.integrable_of_hasCompactSupport hc₀
  have hfi : Integrable addTest(f) ν𝔭(v) := hfl.continuous.integrable_of_hasCompactSupport hfc
  -- Every unit dilate has the same pairing.
  have ha (u : K) : s1 u * (∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (u * y) ∂ν𝔭(v)) =
      s1 u * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v) := by
    by_cases hu : u ∈ S
    · have hn : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
      have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
      have h := (finiteLogFourier_comp_mul v f (Units.mk0 u hu0) hint).2
      rw [hf, mul_zero, sub_zero, Units.val_mk0, hn, inv_one, one_smul] at h
      rw [h]
    · simp [s1, hu]
  -- Unit dilates of the test against the sphere indicator.
  have hb := finiteLogFourier_eq_neg_haar_swapLog v s1
    (tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f)) hs1i 1 one_pos
    (fun u hu ↦ by
      have : u ∈ S := by
        by_contra h
        exact hu (by simp [s1, h])
      rw [mem_sphere_zero_iff_norm.mp this]) lφ.continuous Cφ Rφ hRφ hCφ hφR
  have hd := finiteLogFourier_eq_neg_haar_swapLog v addTest(f)
    (tamagawaFourier ν𝔭(v) ψ𝔭(v) s1) hfi r hr hvan lG.continuous CG RG hRG hCG hGR
  have he (x : K) : addTest(f) x * (∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) s1 (x * y) ∂ν𝔭(v)) = -(((‖x‖⁻¹ : ℝ) : ℂ) * addTest(f) x) := by
    by_cases hx : x = 0
    · rw [hx, hf]
      ring
    · rw [finiteLogFourier_eq_neg_haar_kernel v x hx]
      ring
  calc ((ν𝔭(v)).real S : ℂ) *
        (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v))
      = ∫ u, s1 u * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v) ∂ν𝔭(v) := by
        rw [integral_mul_const, integral_indicator_const _ hSc.isOpen.measurableSet,
          Complex.real_smul, mul_one]
    _ = ∫ u, s1 u * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (u * y) ∂ν𝔭(v) ∂ν𝔭(v) :=
        integral_congr_ae (ae_of_all _ fun u ↦ (ha u).symm)
    _ = ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * ∫ u, s1 u *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (u * y) ∂ν𝔭(v) ∂ν𝔭(v) := hb
    _ = ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * ∫ x, addTest(f) x *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) s1 (x * y) ∂ν𝔭(v) ∂ν𝔭(v) := by
        refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
        dsimp only
        rw [finiteLogFourier_eq_neg_haar_average v s1 addTest(f) hl₀.continuous hc₀
          hfl.continuous hfc y]
    _ = ∫ x, addTest(f) x * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) *
          tamagawaFourier ν𝔭(v) ψ𝔭(v) s1 (x * y) ∂ν𝔭(v) ∂ν𝔭(v) := hd.symm
    _ = _ := by
        rw [integral_congr_ae (ae_of_all _ he), integral_neg]

/-- Paper: Proposition B.4.3.1(2), p. 617. On additive tests vanishing at
zero, the Fourier transform is minus multiplicative Haar measure divided by
the mass of the integer units. -/
theorem finiteLogFourier_eq_neg_haar (v : Primes(F)) (f : 𝒮ₐ(v.adicCompletion F))
    (_hf : addTest(f) 0 = 0) :
    let K : v.adicCompletion F → ℂ := logFourierIntegrand(ν𝔭(v), ψ𝔭(v), J𝔭(v), addTest(f))
    Integrable K ν𝔭(v) ∧ Integrable (fun u : (v.adicCompletion F)ˣ ↦ addTest(f) u.val) μ𝔭(v) ∧
      (∫ y, K y ∂ν𝔭(v)) =
        -(∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v)) / (V𝔭(v) : ℂ) := by
  intro K'
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  obtain ⟨g, hg⟩ := finiteLocal_exists_fourier_test v f
  have hint : Integrable K' ν𝔭(v) :=
    (finiteLog_integrable_mul_test v g).congr (ae_of_all _ fun y ↦ by
      simp only [hg]; rfl)
  obtain ⟨hfl, hfc⟩ := finiteLogFourier_eq_neg_haar_testFacts v f
  obtain ⟨r, hr, hvan⟩ := finiteLogFourier_eq_neg_haar_vanish v _ hfl _hf
  have hfi : Integrable addTest(f) ν𝔭(v) := hfl.continuous.integrable_of_hasCompactSupport hfc
  have hInv : Integrable (fun y ↦ ‖y‖⁻¹ • addTest(f) y) ν𝔭(v) := by
    refine (hfi.norm.const_mul r⁻¹).mono'
      ((by fun_prop : Measurable fun y : v.adicCompletion F ↦ ‖y‖⁻¹).aestronglyMeasurable.smul
        hfi.aestronglyMeasurable) (ae_of_all _ fun y ↦ ?_)
    rw [norm_smul, norm_inv, norm_norm]
    by_cases hy : addTest(f) y = 0
    · rw [hy, norm_zero, mul_zero]; positivity
    · exact mul_le_mul_of_nonneg_right (inv_anti₀ hr (hvan y hy)) (norm_nonneg _)
  have hunits := (finiteLocal_units_integrable_iff v _).mpr hInv
  refine ⟨hint, hunits, ?_⟩
  have hId := finiteLogFourier_eq_neg_haar_identity v f _hf hint
  let S := Metric.sphere (0 : v.adicCompletion F) 1
  let s1 : v.adicCompletion F → ℂ := S.indicator (fun _ ↦ (1 : ℂ))
  let c := ((v.asIdeal.absNorm : ENNReal) / ((v.asIdeal.absNorm : ENNReal) - 1)).toReal
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hc : 0 < c := ENNReal.toReal_pos (ENNReal.div_pos (zero_lt_one.trans hq).ne'
    (ENNReal.sub_ne_top (ENNReal.natCast_ne_top _))).ne'
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (tsub_pos_of_lt hq).ne').ne
  have hSo : IsOpen S := IsUltrametricDist.isOpen_sphere (0 : v.adicCompletion F) one_ne_zero
  have hνS : 0 < (ν𝔭(v)).real S := ENNReal.toReal_pos
    (hSo.measure_pos _ ⟨1, by simp [S]⟩).ne' (isCompact_sphere _ _).measure_lt_top.ne
  have hpre : ((O(v)).units : Set (v.adicCompletion F)ˣ) = Units.val ⁻¹' S := by
    ext u
    simp only [SetLike.mem_coe, mem_preimage, S, mem_sphere_zero_iff_norm]
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      Valued.toNormedField.norm_eq_one_iff]
  have hV : V𝔭(v) = c * (ν𝔭(v)).real S := by
    have h1 := finiteLogFourier_eq_neg_haar_unitsIntegral v s1
    have h2 : (fun u : (v.adicCompletion F)ˣ ↦ s1 u.val) =
        (Units.val ⁻¹' S).indicator (fun _ ↦ (1 : ℂ)) := by
      funext u
      simp only [s1, Set.indicator, mem_preimage]
    have h3 : (fun y ↦ ‖y‖⁻¹ • s1 y) = s1 := by
      funext y
      by_cases hy : y ∈ S
      · simp [s1, hy, mem_sphere_zero_iff_norm.mp hy]
      · simp [s1, hy]
    rw [h2, integral_indicator_const _ (hSo.preimage Units.continuous_val).measurableSet, h3,
      integral_indicator_const _ hSo.measurableSet, ← hpre] at h1
    have := congrArg Complex.re h1
    simpa [Measure.real, c, ENNReal.toReal_div] using this
  have hU := finiteLogFourier_eq_neg_haar_unitsIntegral v addTest(f)
  have hsm : (fun y ↦ ‖y‖⁻¹ • addTest(f) y) =
      fun y ↦ ((‖y‖⁻¹ : ℝ) : ℂ) * addTest(f) y := funext fun y ↦ Complex.real_smul
  rw [hU, hV, hsm, Complex.real_smul]
  have hνS' : (((ν𝔭(v)).real S : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hνS.ne'
  have hc' : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  change (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) = _
  rw [eq_div_iff (by push_cast; exact mul_ne_zero hc' hνS'), neg_mul_eq_mul_neg, ← hId]
  push_cast
  ring

-- TODO(paper-gap): Jᵥ is unbounded near zero and is not an additive
-- Schwartz–Bruhat test. The normalization at one is on its punctured-field representative.

/-- Every additive test of a finite completion is the Fourier transform of an additive test. -/
private theorem finiteLogFourier_unique_surjective (v : Primes(F))
    (g : 𝒮ₐ(v.adicCompletion F)) :
    ∃ f : 𝒮ₐ(v.adicCompletion F), ∀ y,
      tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ f (Multiplicative.ofAdd x)) y =
        g (Multiplicative.ofAdd y) := by
  let K := v.adicCompletion F
  let G := Multiplicative K
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  obtain ⟨e, he, -⟩ := finiteLocalAdditiveTamagawaMeasure_selfDual F v
  let μ : Measure G := ν𝔭(v)
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  let : μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := hHaar.toIsFiniteMeasureOnCompacts
      toIsOpenPosMeasure := hHaar.toIsOpenPosMeasure
      map_mul_left_eq_self := fun x ↦ hHaar.map_add_left_eq_self x.toAdd }
  let : μ.Regular := finiteLocalAdditiveTamagawaMeasure_regular F v
  obtain ⟨T, hT⟩ := schwartzBruhat_fourier_equiv μ
  obtain ⟨P, hP⟩ := exists_schwartzBruhat_comp_equivCLM e.symm
  have key (h : SchwartzBruhat G) (y : K) :
      tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ h (Multiplicative.ofAdd x)) y =
        T h (e (Multiplicative.ofAdd y)) := by
    have h1 : tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ h (Multiplicative.ofAdd x)) y =
        lcaFourier μ (fun x : G ↦ h (Multiplicative.ofAdd x.toAdd)) (e (Multiplicative.ofAdd y)) :=
      tamagawaFourier_eq_lcaFourier _ _ _ y _ fun x ↦ (he y x).trans
        (congrArg _ (mul_comm y x))
    exact h1.trans ((hT h).2 _).symm
  refine ⟨T.symm (P g), fun y ↦ ?_⟩
  rw [key, T.apply_symm_apply, hP, e.symm_apply_apply]

/-- The indicator of a closed ball of positive radius in a finite completion is an additive
test. -/
private theorem finiteLogFourier_unique_ballTest (v : Primes(F)) (x : v.adicCompletion F)
    {r : ℝ} (hr : 0 < r) :
    ∃ g : 𝒮ₐ(v.adicCompletion F), ∀ y,
      g (Multiplicative.ofAdd y) = (Metric.closedBall x r).indicator (fun _ ↦ (1 : ℂ)) y := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  have hU : IsClopen (Metric.closedBall x r) := IsUltrametricDist.isClopen_closedBall x hr.ne'
  obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v
    ((Metric.closedBall x r).indicator (fun _ ↦ (1 : ℂ)))).mpr
    ⟨by
        have h : IsLocallyConstant (LocallyConstant.charFn ℂ hU : _ → ℂ) :=
          (LocallyConstant.charFn ℂ hU).isLocallyConstant
        rw [LocallyConstant.coe_charFn] at h
        exact h,
      HasCompactSupport.intro (isCompact_closedBall x r) fun y hy ↦ indicator_of_notMem hy _⟩
  exact ⟨g, hg⟩

/-- Paper: Proposition B.4.3.1, p. 618. The restriction away from zero of the
Fourier transform determines the normalized logarithm among continuous representatives off zero.
Deviation: The representative acts by integration on Fourier-transformed tests. -/
theorem finiteLogFourier_unique (v : Primes(F)) (J : v.adicCompletion F → ℂ)
    (_hcont : ContinuousOn J ({0}ᶜ)) (_hOne : J 1 = 0)
    (_hInt : ∀ f : 𝒮ₐ(v.adicCompletion F),
      Integrable (fun y ↦ J y * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v))
    (_hAway : ∀ f : 𝒮ₐ(v.adicCompletion F), addTest(f) 0 = 0 →
      (∫ y, J y * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y ∂ν𝔭(v)) =
        -(∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v)) / (V𝔭(v) : ℂ)) :
    ∀ x ≠ 0, J x = (J𝔭(v) x : ℝ) := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  -- The difference with the normalized logarithm.
  let L : v.adicCompletion F → ℂ := fun y ↦ ((J𝔭(v) y : ℝ) : ℂ)
  -- Integrability of `J` and of `L` against every test.
  have hJint (g : 𝒮ₐ(v.adicCompletion F)) :
      Integrable (fun y ↦ J y * g (Multiplicative.ofAdd y)) ν𝔭(v) := by
    obtain ⟨f, hf⟩ := finiteLogFourier_unique_surjective v g
    have h := _hInt f
    simp only [hf] at h
    exact h
  have hLint (g : 𝒮ₐ(v.adicCompletion F)) :
      Integrable (fun y ↦ L y * g (Multiplicative.ofAdd y)) ν𝔭(v) :=
    finiteLog_integrable_mul_test v g
  -- `J` and `L` agree on tests of integral zero.
  have hzero (g : 𝒮ₐ(v.adicCompletion F))
      (hg : ∫ y, g (Multiplicative.ofAdd y) ∂ν𝔭(v) = 0) :
      ∫ y, J y * g (Multiplicative.ofAdd y) ∂ν𝔭(v) =
        ∫ y, L y * g (Multiplicative.ofAdd y) ∂ν𝔭(v) := by
    obtain ⟨f, hf⟩ := finiteLogFourier_unique_surjective v g
    have hf0 : f (Multiplicative.ofAdd 0) = 0 := by
      have h := (finiteLocal_integral_tamagawaFourier v f).2
      simp only [hf] at h
      exact h.symm.trans hg
    have h1 := _hAway f hf0
    have h2 := (finiteLogFourier_eq_neg_haar v f hf0).2.2
    simp only [hf] at h1 h2
    exact h1.trans h2.symm
  -- Integrals against ball indicators are integrals over the balls.
  have hon (g : 𝒮ₐ(v.adicCompletion F)) (s : Set (v.adicCompletion F)) (hs : MeasurableSet s)
      (hg : ∀ y, g (Multiplicative.ofAdd y) = s.indicator (fun _ ↦ (1 : ℂ)) y)
      (Φ : v.adicCompletion F → ℂ) (hΦ : Integrable (fun y ↦ Φ y * g (Multiplicative.ofAdd y)) ν𝔭(v)) :
      IntegrableOn Φ s ν𝔭(v) ∧
        ∫ y, Φ y * g (Multiplicative.ofAdd y) ∂ν𝔭(v) = ∫ y in s, Φ y ∂ν𝔭(v) := by
    have e : (fun y ↦ Φ y * g (Multiplicative.ofAdd y)) = s.indicator Φ := funext fun y ↦ by
      rw [hg y]
      simp only [indicator_apply]
      split_ifs <;> simp
    rw [e] at hΦ ⊢
    exact ⟨(integrable_indicator_iff hs).mp hΦ, integral_indicator hs⟩
  let D : v.adicCompletion F → ℂ := fun y ↦ J y - L y
  have hball (x : v.adicCompletion F) {r : ℝ} (hr : 0 < r) :
      IntegrableOn D (Metric.closedBall x r) ν𝔭(v) ∧
        IntegrableOn D (Metric.closedBall 1 r) ν𝔭(v) ∧
        ∫ y in Metric.closedBall x r, D y ∂ν𝔭(v) =
          ∫ y in Metric.closedBall 1 r, D y ∂ν𝔭(v) := by
    have hm := (Metric.isClosed_closedBall (x := x) (ε := r)).measurableSet
    have hm1 := (Metric.isClosed_closedBall (x := (1 : v.adicCompletion F)) (ε := r)).measurableSet
    obtain ⟨gx, hgx⟩ := finiteLogFourier_unique_ballTest v x hr
    obtain ⟨g1, hg1⟩ := finiteLogFourier_unique_ballTest v 1 hr
    obtain ⟨hJx, eJx⟩ := hon gx _ hm hgx J (hJint gx)
    obtain ⟨hJ1, eJ1⟩ := hon g1 _ hm1 hg1 J (hJint g1)
    obtain ⟨hLx, eLx⟩ := hon gx _ hm hgx L (hLint gx)
    obtain ⟨hL1, eL1⟩ := hon g1 _ hm1 hg1 L (hLint g1)
    have hsub (y : v.adicCompletion F) : (gx - g1) (Multiplicative.ofAdd y) =
        gx (Multiplicative.ofAdd y) - g1 (Multiplicative.ofAdd y) := rfl
    have hfin (z : v.adicCompletion F) : ν𝔭(v) (Metric.closedBall z r) ≠ ⊤ :=
      (isCompact_closedBall z r).measure_lt_top.ne
    have hconst (g : 𝒮ₐ(v.adicCompletion F)) (z : v.adicCompletion F)
        (hg : ∀ y, g (Multiplicative.ofAdd y) =
          (Metric.closedBall z r).indicator (fun _ ↦ (1 : ℂ)) y) :
        Integrable (fun y ↦ g (Multiplicative.ofAdd y)) ν𝔭(v) ∧
          ∫ y, g (Multiplicative.ofAdd y) ∂ν𝔭(v) = ((ν𝔭(v)).real (Metric.closedBall z r) : ℂ) := by
      have hm' := (Metric.isClosed_closedBall (x := z) (ε := r)).measurableSet
      rw [funext hg]
      refine ⟨(integrable_indicator_iff hm').mpr (integrableOn_const (hfin z)), ?_⟩
      rw [integral_indicator hm', setIntegral_const, Complex.real_smul, mul_one]
    obtain ⟨igx, Igx⟩ := hconst gx x hgx
    obtain ⟨ig1, Ig1⟩ := hconst g1 1 hg1
    have hmeas : (ν𝔭(v)).real (Metric.closedBall x r) =
        (ν𝔭(v)).real (Metric.closedBall 1 r) := by
      rw [Measure.addHaar_real_closedBall_center,
        Measure.addHaar_real_closedBall_center (ν𝔭(v)) (1 : v.adicCompletion F)]
    have h0 : ∫ y, (gx - g1) (Multiplicative.ofAdd y) ∂ν𝔭(v) = 0 := by
      simp only [hsub]
      rw [integral_sub igx ig1, Igx, Ig1, hmeas, sub_self]
    have hz := hzero (gx - g1) h0
    simp only [hsub, mul_sub] at hz
    rw [integral_sub (hJint gx) (hJint g1), integral_sub (hLint gx) (hLint g1),
      eJx, eJ1, eLx, eL1] at hz
    refine ⟨hJx.sub hLx, hJ1.sub hL1, ?_⟩
    rw [integral_sub hJx hLx, integral_sub hJ1 hL1]
    linear_combination hz
  -- `D` is continuous away from zero and vanishes at one.
  have hDcont : ContinuousOn D ({0}ᶜ) := by
    refine _hcont.sub (Complex.continuous_ofReal.comp_continuousOn ?_)
    refine ContinuousOn.div_const ?_ _
    exact Real.continuousOn_log.comp continuous_norm.continuousOn fun y hy ↦ by
      simpa using hy
  have hD1 : D 1 = 0 := by simp [D, L, _hOne]
  intro x hx
  suffices hDx : D x = 0 by
    have := sub_eq_zero.mp hDx
    exact this
  rw [← hD1]
  refine eq_of_forall_dist_le fun ε hε ↦ ?_
  have hcx : ContinuousAt D x := hDcont.continuousAt (isOpen_compl_singleton.mem_nhds hx)
  have hc1 : ContinuousAt D 1 :=
    hDcont.continuousAt (isOpen_compl_singleton.mem_nhds one_ne_zero)
  obtain ⟨rx, hrx, hx'⟩ := Metric.continuousAt_iff.mp hcx (ε / 2) (half_pos hε)
  obtain ⟨r1, hr1, h1'⟩ := Metric.continuousAt_iff.mp hc1 (ε / 2) (half_pos hε)
  have hr : 0 < min rx r1 / 2 := half_pos (lt_min hrx hr1)
  have hrx' : min rx r1 / 2 < rx :=
    (half_lt_self (lt_min hrx hr1)).trans_le (min_le_left _ _)
  have hr1' : min rx r1 / 2 < r1 :=
    (half_lt_self (lt_min hrx hr1)).trans_le (min_le_right _ _)
  obtain ⟨hIx, hI1, hEq⟩ := hball x hr
  have hfin (z : v.adicCompletion F) : ν𝔭(v) (Metric.closedBall z (min rx r1 / 2)) < ⊤ :=
    (isCompact_closedBall z _).measure_lt_top
  have hpos : 0 < (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) :=
    ENNReal.toReal_pos ((Metric.isOpen_ball.measure_pos _ ⟨x, Metric.mem_ball_self hr⟩).trans_le
      (measure_mono Metric.ball_subset_closedBall)).ne' (hfin x).ne
  have hmeas : (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) =
      (ν𝔭(v)).real (Metric.closedBall 1 (min rx r1 / 2)) := by
    rw [Measure.addHaar_real_closedBall_center,
      Measure.addHaar_real_closedBall_center (ν𝔭(v)) (1 : v.adicCompletion F)]
  have bound (z : v.adicCompletion F) (hI : IntegrableOn D (Metric.closedBall z (min rx r1 / 2)) ν𝔭(v))
      (hz : ∀ y, dist y z < min rx r1 / 2 + (min rx r1 / 2) → dist (D y) (D z) < ε / 2) :
      ‖(∫ y in Metric.closedBall z (min rx r1 / 2), D y ∂ν𝔭(v)) -
          (ν𝔭(v)).real (Metric.closedBall z (min rx r1 / 2)) • D z‖ ≤
        ε / 2 * (ν𝔭(v)).real (Metric.closedBall z (min rx r1 / 2)) := by
    rw [← setIntegral_const, ← integral_sub hI (integrableOn_const (hfin z).ne)]
    refine norm_setIntegral_le_of_norm_le_const (hfin z) fun y hy ↦ ?_
    rw [← dist_eq_norm]
    exact (hz y ((Metric.mem_closedBall.mp hy).trans_lt (by linarith))).le
  have bx := bound x hIx fun y hy ↦ hx' (hy.trans_le (by linarith [min_le_left rx r1]))
  have b1 := bound 1 hI1 fun y hy ↦ h1' (hy.trans_le (by linarith [min_le_right rx r1]))
  rw [hEq] at bx
  rw [← hmeas] at b1
  have hdist : (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) * dist (D x) (D 1) ≤
      (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) * ε := by
    rw [dist_eq_norm, ← Real.norm_of_nonneg hpos.le, ← norm_smul, smul_sub]
    calc _ = ‖((∫ y in Metric.closedBall 1 (min rx r1 / 2), D y ∂ν𝔭(v)) -
            (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) • D 1) -
          ((∫ y in Metric.closedBall 1 (min rx r1 / 2), D y ∂ν𝔭(v)) -
            (ν𝔭(v)).real (Metric.closedBall x (min rx r1 / 2)) • D x)‖ := by
          congr 1; abel
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add b1 bx)
      _ = _ := by rw [Real.norm_of_nonneg hpos.le]; ring
  exact le_of_mul_le_mul_left hdist hpos

-- TODO(paper-gap): (B.4.3.13)–(B.4.3.14) multiply the Fourier distributions by
-- the local norm-one volumes 2 and 2π. Dilation gives the wrong delta term
-- with those factors (already visible on the real self-dual Gaussian).

local notation "eulerLogConstant" => (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant)

/-- Express an additive Schwartz–Bruhat test in the real coordinate of the completion. -/
private theorem realLogFourier_finitePart_realTest (w : InfinitePlace F) (hw : w.IsReal)
    (f : 𝒮ₐ(w.Completion)) :
    ∃ u : 𝓢(ℝ, ℂ), ∀ x : w.Completion,
      addTest(f) x = u (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
  let c : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
    { toMulEquiv := e.toAddEquiv.toMultiplicative
      continuous_toFun := j.continuous
      continuous_invFun := j.symm.continuous }
  obtain ⟨E, hE⟩ := schwartzBruhat_realCoordinate_equiv c
  obtain ⟨u, rfl⟩ := E.surjective f
  exact ⟨u, fun x ↦ hE u (Multiplicative.ofAdd x)⟩

/-- Paper: Proposition B.4.3.2(1), p. 619. The real Fourier pairing equals
minus half the finite part and minus the logarithmic constant times evaluation at zero.
Deviation: Divides the printed distribution by two. -/
theorem realLogFourier_finitePart (w : InfinitePlace F) (_hw : w.IsReal)
    (f : 𝒮ₐ(w.Completion)) :
    let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
    Integrable K ν∞(w) ∧
      (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ addTest(f) x / ((‖x‖ : ℝ) : ℂ))
        {x : w.Completion | ε ≤ ‖x‖} ν∞(w)) ∧
      Tendsto (fun ε : ℝ ↦ (∫ x in {x : w.Completion | ε ≤ ‖x‖},
        addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w)) + 2 * addTest(f) 0 * (Real.log ε : ℂ))
        (𝓝[>] 0) (𝓝 (-2 * ((∫ y, K y ∂ν∞(w)) + (eulerLogConstant : ℂ) * addTest(f) 0))) := by
  intro K
  let : BorelSpace w.Completion := ⟨rfl⟩
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal _hw
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal _hw
  let m := j.symm.toHomeomorph.toMeasurableEquiv
  have hμ : ν∞(w) = (volume : Measure ℝ).map m := dite_eq_left _hw
  have hem (t : ℝ) : e (m t) = t := e.apply_symm_apply t
  have hnorm (t : ℝ) : ‖m t‖ = |t| := by
    change ‖j.symm t‖ = ‖t‖
    rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
      show j.symm 0 = 0 from map_zero e.symm]
  obtain ⟨u, hf⟩ := realLogFourier_finitePart_realTest w _hw f
  change ∀ x, addTest(f) x = u (e x) at hf
  have hK (t : ℝ) : K (m t) = (Real.log |t| : ℂ) * FourierTransform.fourier (u : ℝ → ℂ) t := by
    change (Real.log (‖m t‖ ^ w.mult) : ℂ) * tamagawaFourier ν∞(w) ψ∞(w) addTest(f) (m t) = _
    rw [_hw.mult_eq_one, pow_one, hnorm, funext hf, realModelFourier w _hw, hem]
  obtain ⟨hlog, hcut, hlim⟩ := real_log_fourier_cutoff u
  -- Transport the cutoff sets along the isometry, then double the real-line limit.
  simp only [hμ, integrable_map_equiv, integrableOn_map_equiv, setIntegral_map_equiv,
    integral_map_equiv, Function.comp_def, preimage_ofPred_eq, hK, hnorm, hf, hem, map_zero]
  refine ⟨hlog, hcut, ?_⟩
  have scale (x y z : ℂ) : 2 * (1 / 2 * x + y * z) = x + 2 * z * y := by ring
  have scale_limit (x y : ℂ) : 2 * (-x - y) = -2 * (x + y) := by ring
  simpa only [scale, scale_limit, Complex.ofReal_add] using hlim.const_mul (2 : ℂ)

open Real in
open scoped FourierTransform in
/-- Mean-value bound for the difference of two decaying exponentials. -/
private theorem complexLogFourier_finitePart_exp_sub_bound {α β y : ℝ} (hα : 0 < α) (hβ : 0 < β) (hy : 0 ≤ y) :
    |exp (-α * y) - exp (-β * y)| ≤ |β - α| * y * exp (-(min α β) * y) := by
  wlog h : α ≤ β generalizing α β
  · have := this hβ hα (le_of_not_ge h)
    rwa [abs_sub_comm α β, min_comm, abs_sub_comm (exp (-β * y))] at this
  rw [min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
  have h1 : exp (-β * y) ≤ exp (-α * y) := exp_le_exp.mpr (by nlinarith)
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  -- exp(-αy) - exp(-βy) = exp(-αy) (1 - exp(-(β-α)y)) ≤ exp(-αy) (β-α) y
  have h2 : 1 - exp (-((β - α) * y)) ≤ (β - α) * y := by
    have := add_one_le_exp (-((β - α) * y)); linarith
  have h3 : exp (-β * y) = exp (-α * y) * exp (-((β - α) * y)) := by
    rw [← exp_add]; ring_nf
  rw [h3]
  have := exp_pos (-α * y)
  nlinarith

open Real in
open scoped FourierTransform in
/-- Frullani's integral for two decaying exponentials. -/
private theorem complexLogFourier_finitePart_frullani_exp {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IntegrableOn (fun y ↦ y⁻¹ * (exp (-α * y) - exp (-β * y))) (Ioi 0) ∧
      ∫ y in Ioi 0, y⁻¹ * (exp (-α * y) - exp (-β * y)) = log (β / α) := by
  have hint : IntegrableOn (fun y ↦ y⁻¹ * (exp (-α * y) - exp (-β * y))) (Ioi 0) := by
    have hm : 0 < min α β := lt_min hα hβ
    have hdom : IntegrableOn (fun y ↦ |β - α| * exp (-(min α β) * y)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hm).const_mul _
    refine hdom.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y (hy : 0 < y)
    rw [norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy]
    have := complexLogFourier_finitePart_exp_sub_bound hα hβ hy.le
    rw [inv_mul_le_iff₀ hy]
    nlinarith [this]
  refine ⟨hint, ?_⟩
  have h := Frullani.integral_Ioi_eq (f := fun x : ℝ ↦ exp (-x)) (L := 1) (R := 0)
    ((by fun_prop : Continuous fun x : ℝ ↦ exp (-x)).locallyIntegrable.locallyIntegrableOn _) hα hβ
    (by simpa using ((by fun_prop : Continuous fun x : ℝ ↦ exp (-x)).tendsto 0).mono_left nhdsWithin_le_nhds)
    (by simpa using tendsto_exp_neg_atTop_nhds_zero)
    (by simpa [smul_eq_mul, neg_mul] using hint)
  simpa [smul_eq_mul, neg_mul] using h

open Real in
open scoped FourierTransform in
/-- The Frullani integrand for exponentials has constant sign. -/
private theorem complexLogFourier_finitePart_frullani_abs {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ y in Ioi 0, |y⁻¹ * (exp (-α * y) - exp (-β * y))| = |log (β / α)| := by
  obtain ⟨hi, hv⟩ := complexLogFourier_finitePart_frullani_exp hα hβ
  rcases le_total α β with h | h
  · have hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ y⁻¹ * (exp (-α * y) - exp (-β * y)) := by
      intro y (hy : 0 < y)
      exact mul_nonneg (inv_nonneg.mpr hy.le)
        (sub_nonneg.mpr (exp_le_exp.mpr (by nlinarith)))
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy ↦ abs_of_nonneg (hnn y hy)), hv,
      abs_of_nonneg (log_nonneg ((one_le_div hα).mpr h))]
  · have hnp : ∀ y ∈ Ioi (0 : ℝ), y⁻¹ * (exp (-α * y) - exp (-β * y)) ≤ 0 := by
      intro y (hy : 0 < y)
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hy.le)
        (sub_nonpos.mpr (exp_le_exp.mpr (by nlinarith)))
    rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy ↦ abs_of_nonpos (hnp y hy)),
      integral_neg, hv, abs_of_nonpos (log_nonpos (div_nonneg hβ.le hα.le) ((div_le_one hα).mpr h))]

open Real in
open scoped FourierTransform in
/-- The substitution `x ↦ x⁻¹` preserves the measure `dx / x` on the positive reals. -/
private theorem complexLogFourier_finitePart_inv_sub (g : ℝ → ℝ) :
    (IntegrableOn (fun x ↦ x⁻¹ * g x⁻¹) (Ioi 0) ↔ IntegrableOn (fun x ↦ x⁻¹ * g x) (Ioi 0)) ∧
      ∫ x in Ioi 0, x⁻¹ * g x⁻¹ = ∫ x in Ioi 0, x⁻¹ * g x := by
  have hp : (-1 : ℝ) ≠ 0 := by norm_num
  have hc : EqOn (fun x : ℝ ↦ (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • ((x ^ (-1 : ℝ))⁻¹ * g (x ^ (-1 : ℝ))))
      (fun x ↦ x⁻¹ * g x⁻¹) (Ioi 0) := by
    intro x (hx : 0 < x)
    simp only [rpow_neg_one, inv_inv, smul_eq_mul, abs_neg, abs_one, one_mul]
    rw [show (-1 : ℝ) - 1 = -2 by norm_num, rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      rpow_natCast]
    field_simp
  constructor
  · rw [← integrableOn_Ioi_comp_rpow_iff (fun y ↦ y⁻¹ * g y) hp,
      integrableOn_congr_fun hc measurableSet_Ioi]
  · rw [← integral_comp_rpow_Ioi (fun y ↦ y⁻¹ * g y) hp, setIntegral_congr_fun measurableSet_Ioi hc]

open Real in
open scoped FourierTransform in
/-- The substitution `x ↦ x⁻¹` for complex-valued integrands against `dx / x`. -/
private theorem complexLogFourier_finitePart_inv_subC (g : ℝ → ℂ) :
    ∫ x in Ioi 0, ((x⁻¹ : ℝ) : ℂ) * g x⁻¹ = ∫ x in Ioi 0, ((x⁻¹ : ℝ) : ℂ) * g x := by
  have hp : (-1 : ℝ) ≠ 0 := by norm_num
  have hc : EqOn (fun x : ℝ ↦ (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
      ((((x ^ (-1 : ℝ))⁻¹ : ℝ) : ℂ) * g (x ^ (-1 : ℝ))))
      (fun x ↦ ((x⁻¹ : ℝ) : ℂ) * g x⁻¹) (Ioi 0) := by
    intro x (hx : 0 < x)
    simp only [rpow_neg_one, inv_inv, abs_neg, abs_one, one_mul, Complex.real_smul]
    rw [show (-1 : ℝ) - 1 = -2 by norm_num, rpow_neg hx.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      rpow_natCast]
    have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast
    field_simp
  rw [← integral_comp_rpow_Ioi (fun y ↦ ((y⁻¹ : ℝ) : ℂ) * g y) hp,
    setIntegral_congr_fun measurableSet_Ioi hc]

open Real in
open scoped FourierTransform in
/-- The logarithm is integrable against `e^{-t}` on the positive reals. -/
private theorem complexLogFourier_finitePart_log_exp_integrable :
    IntegrableOn (fun t ↦ log t * exp (-t)) (Ioi 0) := by
  have h1 := GammaIntegral_convergent (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 := GammaIntegral_convergent (show (0 : ℝ) < 3 / 2 by norm_num)
  refine ((h1.add h2).const_mul 2).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (exp_pos _).le]
  have e1 : t ^ ((1 / 2 : ℝ) - 1) = t⁻¹ ^ (1 / 2 : ℝ) := by
    rw [inv_rpow ht.le, ← rpow_neg ht.le]; norm_num
  have e2 : t ^ ((3 / 2 : ℝ) - 1) = t ^ (1 / 2 : ℝ) := by norm_num
  show |log t| * exp (-t) ≤ 2 * (exp (-t) * t ^ ((1 / 2 : ℝ) - 1) + exp (-t) * t ^ ((3 / 2 : ℝ) - 1))
  rw [e1, e2]
  have h1 := log_le_rpow_div ht.le (show (0 : ℝ) < 1 / 2 by norm_num)
  have h2 := log_le_rpow_div (inv_pos.mpr ht).le (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [log_inv] at h2
  have p1 : 0 ≤ t ^ (1 / 2 : ℝ) := rpow_nonneg ht.le _
  have p2 : 0 ≤ t⁻¹ ^ (1 / 2 : ℝ) := rpow_nonneg (inv_pos.mpr ht).le _
  have hl : |log t| ≤ 2 * (t⁻¹ ^ (1 / 2 : ℝ) + t ^ (1 / 2 : ℝ)) := by
    rw [abs_le]; constructor <;> linarith
  have := exp_pos (-t)
  calc |log t| * exp (-t) ≤ 2 * (t⁻¹ ^ (1 / 2 : ℝ) + t ^ (1 / 2 : ℝ)) * exp (-t) := by gcongr
    _ = _ := by ring

open Real in
open scoped FourierTransform in
/-- Bounds for `e^{-t} - 1/(1+t)` on the positive reals. -/
private theorem complexLogFourier_finitePart_psi_bound {t : ℝ} (ht : 0 < t) :
    |exp (-t) - (1 + t)⁻¹| ≤ min t t⁻¹ ∧ t⁻¹ * |exp (-t) - (1 + t)⁻¹| ≤ 2 * ((1 + t) ^ 2)⁻¹ := by
  have h1 : exp (-t) ≤ (1 + t)⁻¹ := by
    rw [exp_neg]; exact inv_anti₀ (by linarith) (by linarith [add_one_le_exp t])
  have h2 : 1 - t ≤ exp (-t) := by linarith [add_one_le_exp (-t)]
  have hpos := exp_pos (-t)
  rw [abs_of_nonpos (by linarith), neg_sub]
  -- |ψ| = (1+t)⁻¹ - e^{-t} ≤ (1+t)⁻¹ - (1 - t) = t²/(1+t), and ≤ (1+t)⁻¹
  have hA : (1 + t)⁻¹ - exp (-t) ≤ t ^ 2 * (1 + t)⁻¹ := by
    have : (1 + t)⁻¹ - (1 - t) = t ^ 2 * (1 + t)⁻¹ := by field_simp; ring
    linarith
  have hB : (1 + t)⁻¹ - exp (-t) ≤ (1 + t)⁻¹ := by linarith
  have hti : 0 < t⁻¹ := inv_pos.mpr ht
  constructor
  · refine le_min ?_ ?_
    · refine hA.trans ?_
      rw [← div_eq_mul_inv, div_le_iff₀ (by linarith)]; nlinarith
    · refine hB.trans ?_
      exact inv_anti₀ ht (by linarith)
  · rcases le_total t 1 with h | h
    · calc t⁻¹ * ((1 + t)⁻¹ - exp (-t)) ≤ t⁻¹ * (t ^ 2 * (1 + t)⁻¹) := by gcongr
        _ = t * (1 + t)⁻¹ := by field_simp
        _ ≤ 2 * ((1 + t) ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by linarith) (by positivity)]
          nlinarith
    · calc t⁻¹ * ((1 + t)⁻¹ - exp (-t)) ≤ t⁻¹ * (1 + t)⁻¹ := by gcongr
        _ ≤ 2 * ((1 + t) ^ 2)⁻¹ := by
          rw [← mul_inv, inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith

open Real in
open scoped FourierTransform in
/-- `(e^{-t} - 1/(1+t)) / t` is integrable on the positive reals. -/
private theorem complexLogFourier_finitePart_psi_integrable :
    IntegrableOn (fun t ↦ t⁻¹ * (exp (-t) - (1 + t)⁻¹)) (Ioi 0) := by
  have hd : IntegrableOn (fun t : ℝ ↦ 2 * ((1 + t) ^ 2)⁻¹) (Ioi 0) := by
    have h := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2)
      (by simp)).integrableOn (s := Ioi 0)
    refine IntegrableOn.congr_fun (h.const_mul 2) (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi
    simp only [Real.norm_eq_abs, abs_of_pos ht]
    rw [rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
  refine hd.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ht]
  exact (complexLogFourier_finitePart_psi_bound ht).2

open Real in
open scoped FourierTransform in
/-- The symmetric splitting of `e^{-1/s} - 1 + e^{-s}`. -/
private theorem complexLogFourier_finitePart_phi_split {s : ℝ} (hs : 0 < s) :
    exp (-s⁻¹) - 1 + exp (-s) = (exp (-s) - (1 + s)⁻¹) + (exp (-s⁻¹) - (1 + s⁻¹)⁻¹) := by
  have : (1 + s)⁻¹ + (1 + s⁻¹)⁻¹ = 1 := by field_simp; ring
  linarith

open Real in
open scoped FourierTransform in
/-- `|e^{-1/s} - 1 + e^{-s}| ≤ 2 min(s, 1/s)` on the positive reals. -/
private theorem complexLogFourier_finitePart_phi_bound {s : ℝ} (hs : 0 < s) : |exp (-s⁻¹) - 1 + exp (-s)| ≤ 2 * min s s⁻¹ := by
  rw [complexLogFourier_finitePart_phi_split hs]
  have h1 := (complexLogFourier_finitePart_psi_bound hs).1
  have h2 := (complexLogFourier_finitePart_psi_bound (inv_pos.mpr hs)).1
  rw [inv_inv, min_comm] at h2
  linarith [abs_add_le (exp (-s) - (1 + s)⁻¹) (exp (-s⁻¹) - (1 + s⁻¹)⁻¹)]

open Real in
open scoped FourierTransform in
/-- `∫₀^∞ (e^{-1/s} - 1 + e^{-s}) ds / s = -2γ`, by integration by parts against the logarithm. -/
private theorem complexLogFourier_finitePart_k0 : IntegrableOn (fun s ↦ s⁻¹ * (exp (-s⁻¹) - 1 + exp (-s))) (Ioi 0) ∧
    ∫ s in Ioi 0, s⁻¹ * (exp (-s⁻¹) - 1 + exp (-s)) = -2 * eulerMascheroniConstant := by
  let ψ : ℝ → ℝ := fun t ↦ exp (-t) - (1 + t)⁻¹
  have hint : IntegrableOn (fun s ↦ s⁻¹ * (exp (-s⁻¹) - 1 + exp (-s))) (Ioi 0) := by
    have h2 : IntegrableOn (fun s ↦ s⁻¹ * ψ s⁻¹) (Ioi 0) := (complexLogFourier_finitePart_inv_sub ψ).1.mpr complexLogFourier_finitePart_psi_integrable
    refine (complexLogFourier_finitePart_psi_integrable.add h2).congr_fun (fun s (hs : 0 < s) ↦ ?_) measurableSet_Ioi
    simp only [ψ, Pi.add_apply]
    rw [complexLogFourier_finitePart_phi_split hs, mul_add]
  refine ⟨hint, ?_⟩
  -- integration by parts against the logarithm
  let g : ℝ → ℝ := fun t ↦ -(t * log t * exp (-t))
  have hg1 : EqOn (fun x : ℝ ↦ x⁻¹ * g x⁻¹) (fun x ↦ log x * ((x ^ 2)⁻¹ * exp (-x⁻¹))) (Ioi 0) := by
    intro x (hx : 0 < x)
    simp only [g, log_inv]
    field_simp
  have hg2 : EqOn (fun x : ℝ ↦ x⁻¹ * g x) (fun x ↦ -(log x * exp (-x))) (Ioi 0) := by
    intro x (hx : 0 < x)
    simp only [g]
    field_simp
  have hLint := complexLogFourier_finitePart_log_exp_integrable
  have hA : IntegrableOn (fun x ↦ log x * ((x ^ 2)⁻¹ * exp (-x⁻¹))) (Ioi 0) := by
    rw [← integrableOn_congr_fun hg1 measurableSet_Ioi, (complexLogFourier_finitePart_inv_sub g).1,
      integrableOn_congr_fun hg2 measurableSet_Ioi]
    exact hLint.neg
  have hAval : ∫ x in Ioi 0, log x * ((x ^ 2)⁻¹ * exp (-x⁻¹)) = -∫ x in Ioi 0, log x * exp (-x) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi hg1, (complexLogFourier_finitePart_inv_sub g).2,
      setIntegral_congr_fun measurableSet_Ioi hg2, integral_neg]
  have hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt log x⁻¹ x := fun x hx ↦ hasDerivAt_log (ne_of_gt hx)
  have hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun s ↦ exp (-s⁻¹) - 1 + exp (-s))
      ((x ^ 2)⁻¹ * exp (-x⁻¹) - exp (-x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun s ↦ exp (-s⁻¹)) (exp (-x⁻¹) * (-(-(x ^ 2)⁻¹))) x :=
      ((hasDerivAt_inv (ne_of_gt hx)).neg).exp
    have h2 : HasDerivAt (fun s ↦ exp (-s)) (exp (-x) * (-1)) x := (hasDerivAt_neg x).exp
    convert (h1.sub_const 1).add h2 using 1
    ring
  have huv' : IntegrableOn (log * fun x ↦ (x ^ 2)⁻¹ * exp (-x⁻¹) - exp (-x)) (Ioi 0) := by
    refine (hA.sub hLint).congr_fun (fun x _ ↦ ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, Pi.sub_apply]; ring
  have hu'v : IntegrableOn ((fun x : ℝ ↦ x⁻¹) * fun s ↦ exp (-s⁻¹) - 1 + exp (-s)) (Ioi 0) := hint
  have hlim_top : Tendsto (log * fun s ↦ exp (-s⁻¹) - 1 + exp (-s)) atTop (𝓝 0) := by
    have hl : Tendsto (fun s ↦ 2 * (log s / s)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 2
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [eventually_gt_atTop 1] with s hs
    have hs0 : 0 < s := by linarith
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (log_pos hs)]
    have hb := complexLogFourier_finitePart_phi_bound hs0
    have hm : min s s⁻¹ ≤ s⁻¹ := min_le_right _ _
    have := log_pos hs
    calc log s * |exp (-s⁻¹) - 1 + exp (-s)| ≤ log s * (2 * s⁻¹) := by gcongr; linarith
      _ = 2 * (log s / s) := by ring
  have hlim_zero : Tendsto (log * fun s ↦ exp (-s⁻¹) - 1 + exp (-s)) (𝓝[>] 0) (𝓝 0) := by
    have hl : Tendsto (fun s : ℝ ↦ 2 * (log s⁻¹ / s⁻¹)) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun s ↦ 2 * (log s / s)) atTop (𝓝 0) := by
        simpa using (tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).const_mul 2
      exact this.comp tendsto_inv_nhdsGT_zero
    refine squeeze_zero_norm' ?_ hl
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_neg (log_neg hs0 hs1)]
    have hb := complexLogFourier_finitePart_phi_bound hs0
    have hm : min s s⁻¹ ≤ s := min_le_left _ _
    have := log_neg hs0 hs1
    calc -log s * |exp (-s⁻¹) - 1 + exp (-s)| ≤ -log s * (2 * s) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = 2 * (log s⁻¹ / s⁻¹) := by rw [log_inv]; field_simp
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hlim_zero hlim_top
  simp only [sub_zero, zero_sub] at hibp
  have hsplit : ∫ x in Ioi 0, log x * ((x ^ 2)⁻¹ * exp (-x⁻¹) - exp (-x)) =
      (∫ x in Ioi 0, log x * ((x ^ 2)⁻¹ * exp (-x⁻¹))) - ∫ x in Ioi 0, log x * exp (-x) := by
    rw [← integral_sub hA hLint]; congr 1; funext x; ring
  rw [hsplit, hAval] at hibp
  rw [eulerMascheroniConstant_eq_neg_integral_log]
  linarith

open Real in
open scoped FourierTransform in
/-- `∫₀^∞ (e^{-a/s} - 1 + e^{-bs}) ds / s = -2γ - log(ab)`. -/
private theorem complexLogFourier_finitePart_cconst {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun s ↦ s⁻¹ * (exp (-(a * s⁻¹)) - 1 + exp (-(b * s)))) (Ioi 0) ∧
      ∫ s in Ioi 0, s⁻¹ * (exp (-(a * s⁻¹)) - 1 + exp (-(b * s))) =
        -2 * eulerMascheroniConstant - log (a * b) := by
  obtain ⟨hf1, vf1⟩ := complexLogFourier_finitePart_frullani_exp hb one_pos
  obtain ⟨hf2, vf2⟩ := complexLogFourier_finitePart_frullani_exp ha one_pos
  let g : ℝ → ℝ := fun t ↦ exp (-a * t) - exp (-1 * t)
  have h2 : IntegrableOn (fun s ↦ s⁻¹ * g s⁻¹) (Ioi 0) := (complexLogFourier_finitePart_inv_sub g).1.mpr hf2
  have v2 : ∫ s in Ioi 0, s⁻¹ * g s⁻¹ = log (1 / a) := (complexLogFourier_finitePart_inv_sub g).2.trans vf2
  obtain ⟨hk, vk⟩ := complexLogFourier_finitePart_k0
  have he : EqOn (fun s ↦ s⁻¹ * (exp (-(a * s⁻¹)) - 1 + exp (-(b * s))))
      ((fun y ↦ y⁻¹ * (exp (-b * y) - exp (-1 * y))) + (fun s ↦ s⁻¹ * g s⁻¹) +
        fun s ↦ s⁻¹ * (exp (-s⁻¹) - 1 + exp (-s))) (Ioi 0) := by
    intro s _
    simp only [g, Pi.add_apply, neg_mul, one_mul]
    ring
  have hsum := (hf1.add h2).add hk
  refine ⟨hsum.congr_fun he.symm measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_add' (hf1.add h2) hk,
    integral_add' hf1 h2, vf1, v2, vk, log_mul ha.ne' hb.ne', one_div, one_div, log_inv, log_inv]
  ring

open Real in
open scoped FourierTransform in
/-- The Gaussian integral over a disc in the complex plane. -/
private theorem complexLogFourier_finitePart_ball_gauss {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    ∫ x in {x : ℂ | ‖x‖ ^ 2 < ε}, exp (-(s * ‖x‖ ^ 2)) = π / s * (1 - exp (-(s * ε))) := by
  have hmeas : MeasurableSet {x : ℂ | ‖x‖ ^ 2 < ε} := measurableSet_lt (by fun_prop) (by fun_prop)
  let f : ℝ → ℝ := fun r ↦ if r ^ 2 < ε then exp (-(s * r ^ 2)) else 0
  have h1 : ∫ x in {x : ℂ | ‖x‖ ^ 2 < ε}, exp (-(s * ‖x‖ ^ 2)) = ∫ x : ℂ, f ‖x‖ := by
    rw [← integral_indicator hmeas]
    congr 1
  rw [h1, integral_fun_norm_addHaar volume f, Complex.finrank_real_complex]
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = π := by
    simp [Measure.real]
  rw [hball]
  have h2 : ∫ y in Ioi (0 : ℝ), y ^ (2 - 1) • f y = ∫ y in (0 : ℝ)..√ε, y * exp (-(s * y ^ 2)) := by
    rw [intervalIntegral.integral_of_le (sqrt_nonneg _), integral_Ioc_eq_integral_Ioo,
      ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
    congr 1; funext y
    simp only [indicator, mem_Ioi, mem_Ioo, f, smul_eq_mul]
    by_cases hy : 0 < y
    · have : y ^ 2 < ε ↔ y < √ε := by
        rw [lt_sqrt hy.le]
      by_cases hy2 : y ^ 2 < ε
      · simp [hy, hy2, this.mp hy2]
      · simp [hy, hy2, mt this.mpr hy2]
    · simp [hy]
  have h3 : ∫ y in (0 : ℝ)..√ε, y * exp (-(s * y ^ 2)) = (1 - exp (-(s * ε))) / (2 * s) := by
    have hd : ∀ y ∈ uIcc (0 : ℝ) √ε, HasDerivAt (fun y ↦ -exp (-(s * y ^ 2)) / (2 * s))
        (y * exp (-(s * y ^ 2))) y := by
      intro y _
      have := (((hasDerivAt_pow 2 y).const_mul s).neg.exp).neg.div_const (2 * s)
      convert this using 1
      simp only [Pi.neg_apply]
      field_simp
      ring_nf
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((by fun_prop : Continuous fun y : ℝ ↦ y * exp (-(s * y ^ 2))).intervalIntegrable _ _), sq_sqrt hε.le]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, neg_zero,
      exp_zero]
    field_simp
    ring
  rw [h2, h3, smul_eq_mul, nsmul_eq_mul]
  push_cast
  field_simp

open Real in
open scoped FourierTransform in
/-- The Laplace transform of the constant one. -/
private theorem complexLogFourier_finitePart_exp_Ioi {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun s ↦ exp (-(r * s))) (Ioi 0) ∧ ∫ s in Ioi (0 : ℝ), exp (-(r * s)) = r⁻¹ := by
  have h := exp_neg_integrableOn_Ioi 0 hr
  simp only [neg_mul] at h
  refine ⟨h, ?_⟩
  have := integral_exp_mul_Ioi (show -r < 0 by linarith) 0
  simp only [neg_mul, mul_zero, exp_zero] at this
  rw [this]; field_simp

open Real in
open scoped FourierTransform in
/-- Writing `1 / ‖x‖²` as a Laplace integral and exchanging the integrations. -/
private theorem complexLogFourier_finitePart_fubini_gen {w : ℂ → ℂ} (hw : Measurable w) {S : Set ℂ}
    (h0 : ∀ᵐ x ∂(volume.restrict S), x ≠ 0)
    (hi : IntegrableOn (fun x ↦ w x / ((‖x‖ ^ 2 : ℝ) : ℂ)) S) :
    IntegrableOn (fun s ↦ ∫ x in S, w x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) (Ioi 0) ∧
      ∫ s in Ioi (0 : ℝ), ∫ x in S, w x * (exp (-(s * ‖x‖ ^ 2)) : ℂ) =
        ∫ x in S, w x / ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  let Fk : ℂ → ℝ → ℂ := fun x s ↦ w x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)
  have hF : Measurable (Function.uncurry Fk) := by
    unfold Fk Function.uncurry
    exact (hw.comp measurable_fst).mul (by fun_prop)
  have hx (x : ℂ) (hx : x ≠ 0) :
      Integrable (Fk x) (volume.restrict (Ioi 0)) ∧
        ∫ s in Ioi (0 : ℝ), ‖Fk x s‖ = ‖w x / ((‖x‖ ^ 2 : ℝ) : ℂ)‖ ∧
        ∫ s in Ioi (0 : ℝ), Fk x s = w x / ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    have hr : 0 < ‖x‖ ^ 2 := by positivity
    obtain ⟨hI, hV⟩ := complexLogFourier_finitePart_exp_Ioi hr
    have hI' : IntegrableOn (fun s ↦ exp (-(s * ‖x‖ ^ 2))) (Ioi 0) := by
      simpa only [mul_comm] using hI
    have hV' : ∫ s in Ioi (0 : ℝ), exp (-(s * ‖x‖ ^ 2)) = (‖x‖ ^ 2)⁻¹ := by
      simpa only [mul_comm] using hV
    refine ⟨hI'.ofReal.const_mul (w x), ?_, ?_⟩
    · simp only [Fk, norm_mul, Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le]
      rw [integral_const_mul, hV', norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le,
        div_eq_mul_inv]
    · simp only [Fk]
      have hc : ∫ s in Ioi (0 : ℝ), (exp (-(s * ‖x‖ ^ 2)) : ℂ) =
          ((∫ s in Ioi (0 : ℝ), exp (-(s * ‖x‖ ^ 2)) : ℝ) : ℂ) := integral_ofReal
      rw [integral_const_mul, hc, hV', Complex.ofReal_inv, div_eq_mul_inv]
  have hint : Integrable (Function.uncurry Fk) ((volume.restrict S).prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [h0] with x hx0 using (hx x hx0).1
    · refine hi.norm.congr ?_
      filter_upwards [h0] with x hx0 using ((hx x hx0).2.1).symm
  refine ⟨hint.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hint]
  refine integral_congr_ae ?_
  filter_upwards [h0] with x hx0 using (hx x hx0).2.2

open Real in
open scoped FourierTransform in
/-- `1 / ‖x‖` is integrable on discs in the plane. -/
private theorem complexLogFourier_finitePart_inv_norm_ball {r : ℝ} : IntegrableOn (fun x : ℂ ↦ ‖x‖⁻¹) (Metric.ball 0 r) := by
  rw [integrableOn_fun_norm_addHaar (μ := volume) (f := fun y : ℝ ↦ y⁻¹), Complex.finrank_real_complex]
  refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun y (hy : y ∈ Ioo 0 r) ↦ ?_)
    measurableSet_Ioo
  simp [smul_eq_mul, hy.1.ne']

open Real in
open scoped FourierTransform in
/-- The remainder of a Lipschitz-at-zero function over a shrinking disc tends to zero. -/
private theorem complexLogFourier_finitePart_disc_tendsto {g : ℂ → ℂ} (hg : Continuous g) {C : ℝ} (hC : ∀ x, ‖g x - g 0‖ ≤ C * ‖x‖) :
    Tendsto (fun ε : ℝ ↦ ∫ x in {x : ℂ | ‖x‖ ^ 2 < ε}, (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 0) := by
  have hm (ε : ℝ) : MeasurableSet {x : ℂ | ‖x‖ ^ 2 < ε} := measurableSet_lt (by fun_prop) (by fun_prop)
  simp_rw [← integral_indicator (hm _)]
  suffices key : Tendsto (fun ε : ℝ ↦ ∫ x : ℂ, {x : ℂ | ‖x‖ ^ 2 < ε}.indicator
      (fun x ↦ (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ)) x) (𝓝[>] 0) (𝓝 (∫ x : ℂ, (0 : ℂ))) by
    rwa [integral_zero] at key
  refine tendsto_integral_filter_of_dominated_convergence
    ((Metric.ball (0 : ℂ) 1).indicator fun x ↦ |C| * ‖x‖⁻¹) ?_ ?_ ?_ ?_
  · filter_upwards with ε
    refine (Measurable.indicator ?_ (hm ε)).aestronglyMeasurable
    exact ((hg.sub continuous_const).measurable).div (by fun_prop)
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine ae_of_all _ fun x ↦ ?_
    by_cases hx : ‖x‖ ^ 2 < ε
    · have hx1 : x ∈ Metric.ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]
        nlinarith [norm_nonneg x, hε.2]
      rw [indicator_of_mem (show x ∈ {x : ℂ | ‖x‖ ^ 2 < ε} from hx), indicator_of_mem hx1]
      rcases eq_or_ne x 0 with rfl | h0
      · simp
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr h0
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      calc ‖g x - g 0‖ / ‖x‖ ^ 2 ≤ C * ‖x‖ / ‖x‖ ^ 2 := by gcongr; exact hC x
        _ ≤ |C| * ‖x‖ / ‖x‖ ^ 2 := by gcongr; exact le_abs_self C
        _ = |C| * ‖x‖⁻¹ := by field_simp
    · rw [indicator_of_notMem (show x ∉ {x : ℂ | ‖x‖ ^ 2 < ε} from hx), norm_zero]
      exact indicator_nonneg (fun _ _ ↦ by positivity) _
  · exact (integrable_indicator_iff measurableSet_ball).mpr (complexLogFourier_finitePart_inv_norm_ball.const_mul _)
  · filter_upwards [Measure.ae_ne volume (0 : ℂ)] with x hx
    have hn : 0 < ‖x‖ ^ 2 := by positivity
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hn] with ε hε
    rw [indicator_of_notMem]
    simp only [mem_ofPred_eq, not_lt]; exact hε.2.le

open Real in
open scoped FourierTransform in
/-- The logarithmic Fourier pairing as an integral over Gaussian scales. -/
private theorem complexLogFourier_finitePart_fourier_side {g : ℂ → ℂ} (hg : Continuous g) (hgi : Integrable g) (hf : Integrable (𝓕 g))
    (hfc : Continuous (𝓕 g))
    (hlog : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ)) :
    ∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ =
      ∫ y in Ioi (0 : ℝ), ((y⁻¹ : ℝ) : ℂ) * ((exp (-(π ^ 2) * y) : ℂ) * g 0 -
        ((π * y)⁻¹ : ℂ) * ∫ x, g x * Complex.exp (-(‖x‖ ^ 2 / y : ℝ))) := by
  have hπ : 0 < π ^ 2 := by positivity
  let Fk : ℂ → ℝ → ℂ := fun ξ y ↦ ((y⁻¹ * (exp (-(π ^ 2) * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y)) : ℝ) : ℂ) * 𝓕 g ξ
  have hF : Measurable (Function.uncurry Fk) := by
    unfold Fk Function.uncurry
    refine Measurable.mul (by fun_prop) ?_
    exact hfc.measurable.comp measurable_fst
  have hx (ξ : ℂ) (hξ : ξ ≠ 0) :
      Integrable (Fk ξ) (volume.restrict (Ioi 0)) ∧
        ∫ y in Ioi (0 : ℝ), ‖Fk ξ y‖ = ‖(log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ‖ ∧
        ∫ y in Ioi (0 : ℝ), Fk ξ y = (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ := by
    have hβ : 0 < π ^ 2 * ‖ξ‖ ^ 2 := by positivity
    obtain ⟨hI, hV⟩ := complexLogFourier_finitePart_frullani_exp hπ hβ
    have hA := complexLogFourier_finitePart_frullani_abs hπ hβ
    have hq : π ^ 2 * ‖ξ‖ ^ 2 / π ^ 2 = ‖ξ‖ ^ 2 := by field_simp
    rw [hq] at hV hA
    refine ⟨hI.ofReal.mul_const _, ?_, ?_⟩
    · have e : ∀ y, ‖Fk ξ y‖ = |y⁻¹ * (exp (-π ^ 2 * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y))| * ‖𝓕 g ξ‖ :=
        fun y ↦ by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp_rw [e]
      rw [integral_mul_const, hA, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    · have hc : ∫ y in Ioi (0 : ℝ), ((y⁻¹ * (exp (-π ^ 2 * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y)) : ℝ) : ℂ) =
          ((∫ y in Ioi (0 : ℝ), y⁻¹ * (exp (-π ^ 2 * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y)) : ℝ) : ℂ) :=
        integral_ofReal
      simp only [Fk]
      rw [integral_mul_const, hc, hV]
  have hint : Integrable (Function.uncurry Fk) (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ using (hx ξ hξ).1
    · refine hlog.norm.congr ?_
      filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ using ((hx ξ hξ).2.1).symm
  have hL : ∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ = ∫ ξ, ∫ y in Ioi (0 : ℝ), Fk ξ y := by
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ using ((hx ξ hξ).2.2).symm
  rw [hL, integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) ↦ ?_
  -- the inner integral at a fixed scale
  have hmass : ∫ ξ, 𝓕 g ξ = g 0 := by
    have hinv := congrFun (hg.fourierInv_fourier_eq hgi hf) 0
    rw [Real.fourierInv_eq'] at hinv
    simpa using hinv
  have hb : 0 < ((π ^ 2 * y : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; exact mul_pos hπ hy
  set b : ℂ := ((π ^ 2 * y : ℝ) : ℂ) with hbdef
  have hGi : Integrable (fun v : ℂ ↦ Complex.exp (-b * ‖v‖ ^ 2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 0
  have hFG (x : ℂ) : 𝓕 (fun v : ℂ ↦ Complex.exp (-b * ‖v‖ ^ 2)) x =
      ((π * y)⁻¹ : ℂ) * Complex.exp (-(‖x‖ ^ 2 / y : ℝ)) := by
    rw [fourier_gaussian_innerProductSpace hb, Complex.finrank_real_complex]
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hπ' : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
    rw [show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one, hbdef]
    push_cast
    congr 1
    · field_simp
    · congr 1; field_simp
  have hgauss : ∫ ξ, Complex.exp (-b * ‖ξ‖ ^ 2) * 𝓕 g ξ =
      ((π * y)⁻¹ : ℂ) * ∫ x, g x * Complex.exp (-(‖x‖ ^ 2 / y : ℝ)) := by
    have he := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℂ)
      Real.continuous_fourierChar continuous_inner hgi hGi
    rw [flip_innerₗ] at he
    change (∫ ξ, 𝓕 g ξ • Complex.exp (-b * ‖ξ‖ ^ 2)) =
      ∫ x, g x • 𝓕 (fun v : ℂ ↦ Complex.exp (-b * ‖v‖ ^ 2)) x at he
    simp only [smul_eq_mul, hFG] at he
    rw [← integral_const_mul]
    simp only [mul_comm (Complex.exp _) (𝓕 g _)]
    rw [he]
    congr 1; funext x
    ring
  have hGi2 : Integrable (fun ξ : ℂ ↦ Complex.exp (-b * ‖ξ‖ ^ 2) * 𝓕 g ξ) := by
    refine hf.bdd_mul (c := 1) (by fun_prop) (ae_of_all _ fun ξ ↦ ?_)
    have e : -b * (‖ξ‖ : ℂ) ^ 2 = ((-(π ^ 2 * y) * ‖ξ‖ ^ 2 : ℝ) : ℂ) := by
      rw [hbdef]; push_cast; ring
    rw [e, Complex.norm_exp, Complex.ofReal_re, exp_le_one_iff]
    have := mul_pos hπ hy
    nlinarith [sq_nonneg ‖ξ‖]
  have hpt (ξ : ℂ) : ((y⁻¹ * (exp (-π ^ 2 * y) - exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y)) : ℝ) : ℂ) * 𝓕 g ξ =
      ((y⁻¹ : ℝ) : ℂ) * ((exp (-π ^ 2 * y) : ℂ) * 𝓕 g ξ - Complex.exp (-b * ‖ξ‖ ^ 2) * 𝓕 g ξ) := by
    have e : Complex.exp (-b * ‖ξ‖ ^ 2) = ((exp (-(π ^ 2 * ‖ξ‖ ^ 2) * y) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp, hbdef]; push_cast; ring_nf
    rw [e]; push_cast; ring
  simp only [Fk, hpt]
  rw [integral_const_mul, integral_sub (hf.const_mul _) hGi2, integral_const_mul, hmass, hgauss]

open Real in
open scoped FourierTransform in
/-- The planar finite-part identity for the logarithm, for Lebesgue measure and the standard
Fourier transform. -/
private theorem complexLogFourier_finitePart_core {g : ℂ → ℂ} (hg : Continuous g) (hgi : Integrable g) (hf : Integrable (𝓕 g))
    (hfc : Continuous (𝓕 g))
    (hlog : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ))
    {C : ℝ} (hC : ∀ x, ‖g x - g 0‖ ≤ C * ‖x‖) :
    (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) {x | ε ≤ ‖x‖ ^ 2}) ∧
    Tendsto (fun ε : ℝ ↦ (∫ x in {x : ℂ | ε ≤ ‖x‖ ^ 2}, g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) +
        (π : ℂ) * g 0 * (log ε : ℂ)) (𝓝[>] 0)
      (𝓝 (-(π : ℂ) * ((∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ) +
        2 * ((log π + eulerMascheroniConstant : ℝ) : ℂ) * g 0))) := by
  have hπ0 : 0 < π := pi_pos
  have hπC : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  have hmA (ε : ℝ) : MeasurableSet {x : ℂ | ε ≤ ‖x‖ ^ 2} := measurableSet_le (by fun_prop) (by fun_prop)
  have hmB (ε : ℝ) : MeasurableSet {x : ℂ | ‖x‖ ^ 2 < ε} := measurableSet_lt (by fun_prop) (by fun_prop)
  -- integrability on the outer region
  have hA (ε : ℝ) (hε : 0 < ε) : IntegrableOn (fun x ↦ g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) {x | ε ≤ ‖x‖ ^ 2} := by
    refine (hgi.integrableOn.norm.const_mul ε⁻¹).mono' ?_ ?_
    · exact (hg.measurable.div (by fun_prop)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (hmA ε)] with x (hx : ε ≤ ‖x‖ ^ 2)
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity), div_eq_mul_inv, mul_comm]
      gcongr
  refine ⟨hA, ?_⟩
  set I := ∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 g ξ with hIdef
  -- Gaussian averages of the test
  let G : ℝ → ℂ := fun s ↦ ∫ x, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)
  -- the Fourier side after the substitution s = 1/y
  have hIs : I = ∫ s in Ioi (0 : ℝ), (((s⁻¹ * exp (-(π ^ 2 * s⁻¹)) : ℝ) : ℂ) * g 0 -
      (π : ℂ)⁻¹ * G s) := by
    rw [hIdef, complexLogFourier_finitePart_fourier_side hg hgi hf hfc hlog]
    rw [← complexLogFourier_finitePart_inv_subC]
    refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
    simp only [G]
    have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have e : ∀ x : ℂ, Complex.exp (-(‖x‖ ^ 2 / s⁻¹ : ℝ)) = (exp (-(s * ‖x‖ ^ 2)) : ℂ) := by
      intro x; rw [Complex.ofReal_exp]; congr 1; push_cast; field_simp
    simp only [e]
    push_cast
    field_simp
  have key (ε : ℝ) (hε : 0 < ε) :
      (∫ x in {x : ℂ | ε ≤ ‖x‖ ^ 2}, g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) + (π : ℂ) * g 0 * (log ε : ℂ) =
        -(π : ℂ) * (I + 2 * ((log π + eulerMascheroniConstant : ℝ) : ℂ) * g 0) -
          ∫ x in {x : ℂ | ‖x‖ ^ 2 < ε}, (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    set A := {x : ℂ | ε ≤ ‖x‖ ^ 2}
    set B := {x : ℂ | ‖x‖ ^ 2 < ε}
    have hAB : Aᶜ = B := by ext x; simp [A, B, not_le]
    have h0A : ∀ᵐ x ∂(volume.restrict A), x ≠ 0 := by
      filter_upwards [ae_restrict_mem (hmA ε)] with x (hx : ε ≤ ‖x‖ ^ 2)
      rintro rfl; simp at hx; linarith
    have h0B : ∀ᵐ x ∂(volume.restrict B), x ≠ 0 := ae_restrict_of_ae (Measure.ae_ne volume 0)
    have hBball : B ⊆ Metric.ball (0 : ℂ) (√ε + 1) := by
      intro x (hx : ‖x‖ ^ 2 < ε)
      rw [mem_ball_zero_iff]
      have : ‖x‖ < √ε := by rw [lt_sqrt (norm_nonneg _)]; exact hx
      linarith
    have hiB : IntegrableOn (fun x ↦ (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ)) B := by
      refine ((complexLogFourier_finitePart_inv_norm_ball (r := √ε + 1)).mono_set hBball |>.const_mul |C|).mono' ?_ ?_
      · exact ((hg.measurable.sub_const _).div (by fun_prop)).aestronglyMeasurable
      · filter_upwards [h0B] with x hx
        have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        calc ‖g x - g 0‖ / ‖x‖ ^ 2 ≤ C * ‖x‖ / ‖x‖ ^ 2 := by gcongr; exact hC x
          _ ≤ |C| * ‖x‖ / ‖x‖ ^ 2 := by gcongr; exact le_abs_self C
          _ = |C| * ‖x‖⁻¹ := by field_simp
    obtain ⟨hQi, hQv⟩ := complexLogFourier_finitePart_fubini_gen (w := g) hg.measurable h0A (hA ε hε)
    obtain ⟨hEi, hEv⟩ := complexLogFourier_finitePart_fubini_gen (w := fun x ↦ g x - g 0) (hg.measurable.sub_const _) h0B hiB
    obtain ⟨hci, hcv⟩ := complexLogFourier_finitePart_cconst (a := π ^ 2) (b := ε) (by positivity) hε
    have hG (s : ℝ) (hs : 0 < s) : G s = (∫ x in A, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
        (∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
        g 0 * ((π / s * (1 - exp (-(s * ε))) : ℝ) : ℂ) := by
      have hint : Integrable (fun x ↦ g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) := by
        refine hgi.mul_bdd (c := 1) (by fun_prop) (ae_of_all _ fun x ↦ ?_)
        rw [Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, exp_le_one_iff]
        have := sq_nonneg ‖x‖; nlinarith
      have hBe : IntegrableOn (fun x : ℂ ↦ (exp (-(s * ‖x‖ ^ 2)) : ℂ)) B := by
        refine Measure.integrableOn_of_bounded (M := 1) ?_ (by fun_prop) (ae_of_all _ fun x ↦ ?_)
        · exact ((measure_mono hBball).trans_lt measure_ball_lt_top).ne
        · rw [Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, exp_le_one_iff]
          have := sq_nonneg ‖x‖; nlinarith
      have hsplit : (∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) =
          (∫ x in B, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) - g 0 * ∫ x in B, (exp (-(s * ‖x‖ ^ 2)) : ℂ) := by
        simp only [sub_mul]
        rw [integral_sub hint.integrableOn (hBe.const_mul _), integral_const_mul]
      have hball : ∫ x in B, (exp (-(s * ‖x‖ ^ 2)) : ℂ) = ((π / s * (1 - exp (-(s * ε))) : ℝ) : ℂ) := by
        have hc : ∫ x in B, (exp (-(s * ‖x‖ ^ 2)) : ℂ) = ((∫ x in B, exp (-(s * ‖x‖ ^ 2)) : ℝ) : ℂ) :=
          integral_ofReal
        rw [hc, complexLogFourier_finitePart_ball_gauss hs hε]
      rw [hsplit, hball]
      simp only [G]
      rw [← integral_add_compl (hmA ε) hint, hAB]
      ring
    have hpt : EqOn (fun s ↦ ((s⁻¹ * exp (-(π ^ 2 * s⁻¹)) : ℝ) : ℂ) * g 0 - (π : ℂ)⁻¹ * G s)
        (fun s ↦ g 0 * ((s⁻¹ * (exp (-(π ^ 2 * s⁻¹)) - 1 + exp (-(ε * s))) : ℝ) : ℂ) -
          (π : ℂ)⁻¹ * ((∫ x in A, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
            ∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ))) (Ioi 0) := by
      intro s (hs : 0 < s)
      simp only
      rw [hG s hs, mul_comm ε s]
      have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      push_cast
      field_simp
      ring
    have hc : ∫ s in Ioi (0 : ℝ), ((s⁻¹ * (exp (-(π ^ 2 * s⁻¹)) - 1 + exp (-(ε * s))) : ℝ) : ℂ) =
        ((∫ s in Ioi (0 : ℝ), s⁻¹ * (exp (-(π ^ 2 * s⁻¹)) - 1 + exp (-(ε * s))) : ℝ) : ℂ) :=
      integral_ofReal
    have h1 : IntegrableOn (fun s ↦ g 0 *
        ((s⁻¹ * (exp (-(π ^ 2 * s⁻¹)) - 1 + exp (-(ε * s))) : ℝ) : ℂ)) (Ioi 0) :=
      (hci.ofReal (𝕜 := ℂ)).const_mul (g 0)
    have h2 : IntegrableOn (fun s ↦ (π : ℂ)⁻¹ * ((∫ x in A, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
        ∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ))) (Ioi 0) :=
      (hQi.add hEi).const_mul _
    have hsum : ∫ s in Ioi (0 : ℝ), ((∫ x in A, g x * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) +
        ∫ x in B, (g x - g 0) * (exp (-(s * ‖x‖ ^ 2)) : ℂ)) =
        (∫ x in A, g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) + ∫ x in B, (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ) := by
      rw [integral_add hQi hEi, hQv, hEv]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub h1 h2, integral_const_mul,
      integral_const_mul, hsum, hc, hcv] at hIs
    have hlog2 : log (π ^ 2 * ε) = 2 * log π + log ε := by
      rw [log_mul (by positivity) hε.ne', log_pow]; push_cast; ring
    rw [hlog2] at hIs
    have hπI : (π : ℂ) * I = (π : ℂ) * (g 0 * ((-2 * eulerMascheroniConstant - (2 * log π + log ε) : ℝ) : ℂ)) -
        ((∫ x in A, g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) + ∫ x in B, (g x - g 0) / ((‖x‖ ^ 2 : ℝ) : ℂ)) := by
      rw [hIs]; field_simp
    push_cast at hπI ⊢
    linear_combination hπI
  have hT := (tendsto_const_nhds (x := -(π : ℂ) * (I + 2 * ((log π + eulerMascheroniConstant : ℝ) : ℂ) * g 0))).sub
    (complexLogFourier_finitePart_disc_tendsto hg hC)
  rw [sub_zero] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (key ε hε).symm

open Real in
open scoped FourierTransform in
/-- Fourier inversion at the origin. -/
private theorem complexLogFourier_finitePart_mass (g : 𝓢(ℂ, ℂ)) : ∫ ξ, 𝓕 (g : ℂ → ℂ) ξ = g 0 := by
  have hf : Integrable (𝓕 (g : ℂ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 g).integrable
  have hinv := congrFun (g.continuous.fourierInv_fourier_eq g.integrable hf) 0
  rw [Real.fourierInv_eq'] at hinv
  simpa using hinv

open Real in
open scoped FourierTransform in
/-- The logarithm of the squared norm is integrable against Schwartz functions on the plane. -/
private theorem complexLogFourier_finitePart_logint (g : 𝓢(ℂ, ℂ)) : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * g ξ) := by
  have h := integrable_abs_log_norm_div_one_add_norm_pow (volume : Measure ℂ) (by simp)
  simp only [Complex.finrank_real_complex] at h
  obtain ⟨Λ, hΛ⟩ := RiemannMasullo.SchwartzMap.exists_strongDual_integral_mul (volume : Measure ℂ)
    (fun t ↦ (log (‖t‖ ^ 2) : ℂ))
    ((Complex.measurable_ofReal.comp (measurable_norm.pow_const 2).log).aestronglyMeasurable) 4
    ((h.const_mul 2).congr (ae_of_all _ fun t ↦ by
      simp only [Complex.norm_real, Real.norm_eq_abs, Real.log_pow]
      push_cast
      rw [abs_mul, abs_two]; ring))
  exact (hΛ g).1

open Real in
open scoped FourierTransform in
/-- The logarithmic pairing in the normalization of the complex completion, after the
change of variables `ξ = 2 conj t`. -/
private theorem complexLogFourier_finitePart_pairing (g : 𝓢(ℂ, ℂ)) :
    Integrable (fun t : ℂ ↦ (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t))) ∧
    ∫ t, (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t)) ∂(2 • volume) =
      (∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) - (log 4 : ℂ) * g 0 := by
  have hf : Integrable (𝓕 (g : ℂ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 g).integrable
  have hlog : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) := by
    simpa only [SchwartzMap.fourier_coe] using complexLogFourier_finitePart_logint (𝓕 g)
  let h : ℂ → ℂ := fun ξ ↦ (log (‖ξ‖ ^ 2 / 4) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ
  have hh (t : ℂ) : (log (‖t‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t) = h ((2 : ℝ) • star t) := by
    simp only [h, norm_smul, Real.norm_two, norm_star]
    congr 3; ring
  have hconj := (Complex.conjLIE.measurePreserving).integral_comp
    Complex.conjLIE.toHomeomorph.measurableEmbedding (fun u ↦ h ((2 : ℝ) • u))
  have hsc := Measure.integral_comp_smul (volume : Measure ℂ) h 2
  have hval : ∫ ξ, h ξ = (∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) - (log 4 : ℂ) * g 0 := by
    rw [← complexLogFourier_finitePart_mass g, ← integral_const_mul, ← integral_sub hlog (hf.const_mul _)]
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ
    simp only [h]
    rw [log_div (by positivity) (by norm_num)]
    push_cast; ring
  have hhi : Integrable h := by
    refine (hlog.sub (hf.const_mul (log 4 : ℂ))).congr ?_
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with ξ hξ
    simp only [h, Pi.sub_apply]
    rw [log_div (by positivity) (by norm_num)]
    push_cast; ring
  have hcj (t : ℂ) : h ((2 : ℝ) • Complex.conjLIE t) = h ((2 : ℝ) • star t) := by
    rw [Complex.conjLIE_apply]; rfl
  have hi : Integrable (fun t : ℂ ↦ (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t))) := by
    have h1 : Integrable (fun u : ℂ ↦ h ((2 : ℝ) • u)) := hhi.comp_smul two_ne_zero
    have h2 : Integrable ((fun u : ℂ ↦ h ((2 : ℝ) • u)) ∘ Complex.conjLIE) :=
      ((Complex.conjLIE.measurePreserving).integrable_comp_emb (g := fun u : ℂ ↦ h ((2 : ℝ) • u))
        Complex.conjLIE.toHomeomorph.measurableEmbedding).mpr h1
    refine (h2.const_mul 2).congr (ae_of_all _ fun t ↦ ?_)
    change 2 * h ((2 : ℝ) • Complex.conjLIE t) = _
    rw [hcj, ← hh t]; ring
  refine ⟨hi, ?_⟩
  rw [show (2 • volume : Measure ℂ) = volume + volume from two_smul ℕ _,
    integral_add_measure hi hi]
  have hone : ∫ t, (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t)) =
      2 * ∫ t, h ((2 : ℝ) • Complex.conjLIE t) := by
    rw [← integral_const_mul]; congr 1; funext t
    rw [hcj, ← hh t]; ring
  rw [hone, hconj, hsc, ← hval, Complex.finrank_real_complex]
  norm_num
  ring

open Real in
open scoped FourierTransform in
/-- The planar finite-part identity in the normalization of the complex completion. -/
private theorem complexLogFourier_finitePart_final (g : 𝓢(ℂ, ℂ)) :
    Integrable (fun t : ℂ ↦ (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t)))
      (2 • volume) ∧
    (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ g x / ((‖x‖ ^ 2 : ℝ) : ℂ)) {x | ε ≤ ‖x‖ ^ 2}
      (2 • volume)) ∧
    Tendsto (fun ε : ℝ ↦ (∫ x in {x : ℂ | ε ≤ ‖x‖ ^ 2}, g x / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂(2 • volume)) +
        ((2 * π : ℝ) : ℂ) * g 0 * (log ε : ℂ)) (𝓝[>] 0)
      (𝓝 (-((2 * π : ℝ) : ℂ) * ((∫ t, (log (‖t‖ ^ 2) : ℂ) * (2 * 𝓕 (g : ℂ → ℂ) ((2 : ℝ) • star t))
        ∂(2 • volume)) + ((2 * (log (2 * π) + eulerMascheroniConstant) : ℝ) : ℂ) * g 0))) := by
  have hf : Integrable (𝓕 (g : ℂ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 g).integrable
  have hfc : Continuous (𝓕 (g : ℂ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 g).continuous
  have hlog : Integrable (fun ξ : ℂ ↦ (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) := by
    simpa only [SchwartzMap.fourier_coe] using complexLogFourier_finitePart_logint (𝓕 g)
  obtain ⟨C, -, hC⟩ := g.decay 0 1
  have hC' (x : ℂ) : ‖g x - g 0‖ ≤ C * ‖x‖ := by
    have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := (g : ℂ → ℂ))
      (fun y _ ↦ g.differentiableAt) (fun y _ ↦ by
        have := hC y
        simpa [norm_iteratedFDeriv_one] using this) (mem_univ 0) (mem_univ x)
    simpa using this
  obtain ⟨hA, hT⟩ := complexLogFourier_finitePart_core g.continuous g.integrable hf hfc hlog hC'
  -- the measure 2 • volume
  have h2 : (2 • (volume : Measure ℂ)) = volume + volume := two_smul ℕ _
  -- the change of variables in the logarithmic pairing
  obtain ⟨hi, hJ⟩ := complexLogFourier_finitePart_pairing g
  have h2v : (2 • volume : Measure ℂ) = volume + volume := two_smul ℕ _
  refine ⟨by rw [h2v]; exact hi.add_measure hi, fun ε hε ↦ ?_, ?_⟩
  · rw [h2v]; exact (hA ε hε).add_measure (hA ε hε)
  rw [hJ]
  have l4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; push_cast; ring
  have l2π : log (2 * π) = log 2 + log π := log_mul two_ne_zero pi_ne_zero
  have hlim : -((2 * π : ℝ) : ℂ) * (((∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) - (log 4 : ℂ) * g 0) +
      ((2 * (log (2 * π) + eulerMascheroniConstant) : ℝ) : ℂ) * g 0) =
      2 * (-(π : ℂ) * ((∫ ξ, (log (‖ξ‖ ^ 2) : ℂ) * 𝓕 (g : ℂ → ℂ) ξ) +
        2 * ((log π + eulerMascheroniConstant : ℝ) : ℂ) * g 0)) := by
    rw [l4, l2π]; push_cast; ring
  rw [hlim]
  refine (hT.const_mul (2 : ℂ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [h2v, Measure.restrict_add, integral_add_measure (hA ε hε) (hA ε hε)]
  push_cast; ring

/-- Paper: Proposition B.4.3.2(2), p. 619. The complex Fourier pairing
equals minus the finite part divided by 2π, with the squared module in the cutoff.
Deviation: Divides the printed distribution by 2π. -/
theorem complexLogFourier_finitePart (w : InfinitePlace F) (_hw : w.IsComplex)
    (f : 𝒮ₐ(w.Completion)) :
    let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
    Integrable K ν∞(w) ∧
      (∀ ε > (0 : ℝ), IntegrableOn (fun x ↦ addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ))
        {x : w.Completion | ε ≤ ‖x‖ ^ 2} ν∞(w)) ∧
      Tendsto (fun ε : ℝ ↦ (∫ x in {x : w.Completion | ε ≤ ‖x‖ ^ 2},
        addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂ν∞(w)) +
        (2 * Real.pi : ℝ) * addTest(f) 0 * (Real.log ε : ℂ))
        (𝓝[>] 0) (𝓝 (-(2 * Real.pi : ℝ) *
          ((∫ y, K y ∂ν∞(w)) + (2 * eulerLogConstant : ℝ) * addTest(f) 0))) := by
  intro K
  let : BorelSpace w.Completion := ⟨rfl⟩
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex _hw
  let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex _hw
  let m := j.symm.toHomeomorph.toMeasurableEquiv
  have hμ : ν∞(w) = (2 • (volume : Measure ℂ)).map m :=
    dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr _hw)
  have hem (t : ℂ) : e (m t) = t := e.apply_symm_apply t
  have hnorm (t : ℂ) : ‖m t‖ = ‖t‖ := by
    change ‖j.symm t‖ = ‖t‖
    rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
      show j.symm 0 = 0 from map_zero e.symm]
  obtain ⟨g, hg⟩ := complexModelSchwartz w _hw f
  have hf : addTest(f) = fun x ↦ g (e x) := by
    funext x
    rw [hg]
    exact congrArg (fun y ↦ addTest(f) y) (e.symm_apply_apply x).symm
  have hK (t : ℂ) : K (m t) =
      (Real.log (‖t‖ ^ 2) : ℂ) * (2 * FourierTransform.fourier (g : ℂ → ℂ) ((2 : ℝ) • star t)) := by
    change (Real.log (‖m t‖ ^ w.mult) : ℂ) * tamagawaFourier ν∞(w) ψ∞(w) addTest(f) (m t) = _
    rw [_hw.mult_eq_two, hnorm, hf, complexModelFourier w _hw, hem]
  have hf' (x : w.Completion) : f (Multiplicative.ofAdd x) = g (e x) := congrFun hf x
  obtain ⟨hint, hcut, hlim⟩ := complexLogFourier_finitePart_final g
  simp only [hμ, integrable_map_equiv, integrableOn_map_equiv, setIntegral_map_equiv,
    integral_map_equiv, Function.comp_def, preimage_ofPred_eq, hK, hnorm, hf', hem, map_zero]
  exact ⟨hint, hcut, hlim⟩

end LocalFourier

section PrincipalValues

local notation "scaledMeasure(" v ", " a ")" =>
  (ENNReal.ofReal (Real.sqrt ‖(a : (HeightOneSpectrum.adicCompletion F v)ˣ).val‖) • ν𝔭(v))
local notation "scaledChar(" v ", " a ")" => (fun x ↦ ψ𝔭(v) (Units.val a * x))
local notation "zeroExtend(" f ")" => (Function.extend Units.val (f : _ → ℂ) (fun _ ↦ 0))
local notation "weightedTranslate(" abs ", " f ")" =>
  (fun x ↦ zeroExtend(f) (1 + x) / (Real.sqrt (abs (1 + x)) : ℂ))

/-- The finite Fourier transform is additive and homogeneous on continuous compactly
supported functions. -/
private theorem exists_finiteConnesPrincipalValue_fourier_linear (v : Primes(F)) (c : ℂ)
    (u w : v.adicCompletion F → ℂ) (hu : Continuous u) (hu' : HasCompactSupport u)
    (hw : Continuous w) (hw' : HasCompactSupport w) (y : v.adicCompletion F) :
    tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ u x + w x) y =
        tamagawaFourier ν𝔭(v) ψ𝔭(v) u y + tamagawaFourier ν𝔭(v) ψ𝔭(v) w y ∧
      tamagawaFourier ν𝔭(v) ψ𝔭(v) (fun x ↦ c * u x) y =
        c * tamagawaFourier ν𝔭(v) ψ𝔭(v) u y := by
  let : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  let : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  have hHaar := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hψ0 := finiteLocalStandardCharacter_exists_continuousMonoidHom F v
  have hψ : Continuous (finiteLocalStandardCharacter F v) :=
    (hψ0.choose.continuous.comp continuous_ofAdd).congr hψ0.choose_spec.1
  have hχ : Continuous fun x : v.adicCompletion F ↦ star (ψ𝔭(v) (x * y) : ℂ) :=
    continuous_star.comp (continuous_subtype_val.comp (hψ.comp (continuous_id.mul continuous_const)))
  have hi (z : v.adicCompletion F → ℂ) (hz : Continuous z) (hz' : HasCompactSupport z) :
      Integrable (fun x ↦ z x * star (ψ𝔭(v) (x * y) : ℂ)) ν𝔭(v) :=
    (hz.mul hχ).integrable_of_hasCompactSupport hz'.mul_right
  unfold tamagawaFourier
  refine ⟨?_, ?_⟩
  · rw [← integral_add (hi u hu hu') (hi w hw hw')]
    exact integral_congr_ae (ae_of_all _ fun x ↦ add_mul _ _ _)
  · rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x ↦ mul_assoc _ _ _)

/-- Every additive and homogeneous functional on the additive tests of a finite completion is
continuous, since their topology is the finest locally convex one. -/
private theorem exists_finiteConnesPrincipalValue_ofLinear (v : Primes(F))
    (L : 𝒮ₐ(v.adicCompletion F) → ℂ) (hadd : ∀ f g, L (f + g) = L f + L g)
    (hsmul : ∀ (c : ℂ) f, L (c • f) = c * L f) (P : 𝒮ₐ(v.adicCompletion F) → ℂ → Prop)
    (hP : ∀ f, P f (L f)) :
    ∃ T : StrongDual ℂ (𝒮ₐ(v.adicCompletion F)), ∀ f, P f (T f) := by
  let ℓ : 𝒮ₐ(v.adicCompletion F) →ₗ[ℂ] ℂ :=
    { toFun := L
      map_add' := hadd
      map_smul' := hsmul }
  have h := continuous_of_finestLocallyConvex (𝒮ₐ(v.adicCompletion F)) (M := ℂ) ℓ
  exact ⟨⟨ℓ, (congrArg (fun t ↦ @Continuous _ ℂ t _ ℓ)
    (finitePlaceSchwartz_finestTopology F v)).mpr h⟩, hP⟩

/-- The logarithm pairs integrably with the dilated Fourier transform of an additive test. -/
private theorem exists_finiteConnesPrincipalValue_integrable (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒮ₐ(v.adicCompletion F)) :
    Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)) ν𝔭(v) := by
  obtain ⟨g, hg⟩ := finiteLocal_exists_fourier_test v f
  have hint : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v) :=
    (finiteLog_integrable_mul_test v g).congr (ae_of_all _ fun y ↦ by
      simp only [hg])
  exact (finiteLogFourier_comp_mul v f a hint).1

/-- The pairing of the logarithm with the dilated Fourier transform is additive. -/
private theorem exists_finiteConnesPrincipalValue_add (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f g : 𝒮ₐ(v.adicCompletion F)) :
    ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f + g) (a.val * y) ∂ν𝔭(v) =
      (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) ∂ν𝔭(v)) +
        ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) (a.val * y)
          ∂ν𝔭(v) := by
  have hreg (f : 𝒮ₐ(v.adicCompletion F)) :
      Continuous (fun x : v.adicCompletion F ↦ f (Multiplicative.ofAdd x)) ∧
        HasCompactSupport (fun x : v.adicCompletion F ↦ f (Multiplicative.ofAdd x)) :=
    ⟨(schwartzBruhat_continuous f).comp continuous_ofAdd,
      ((mem_finitePlaceSchwartz_iff F v _).1 ⟨f, fun _ ↦ rfl⟩).2⟩
  refine Eq.trans ?_ (integral_add (exists_finiteConnesPrincipalValue_integrable v a f)
    (exists_finiteConnesPrincipalValue_integrable v a g))
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  have h : tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f + g) (a.val * y) =
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) +
        tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(g) (a.val * y) :=
    (exists_finiteConnesPrincipalValue_fourier_linear v 1 _ _ (hreg f).1 (hreg f).2
      (hreg g).1 (hreg g).2 (a.val * y)).1
  exact (congrArg (((J𝔭(v) y : ℝ) : ℂ) * ·) h).trans (mul_add _ _ _)

/-- The pairing of the logarithm with the dilated Fourier transform is homogeneous. -/
private theorem exists_finiteConnesPrincipalValue_smul (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (c : ℂ) (f : 𝒮ₐ(v.adicCompletion F)) :
    ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(c • f) (a.val * y) ∂ν𝔭(v) =
      c * ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)
        ∂ν𝔭(v) := by
  have hreg : Continuous (fun x : v.adicCompletion F ↦ f (Multiplicative.ofAdd x)) ∧
      HasCompactSupport (fun x : v.adicCompletion F ↦ f (Multiplicative.ofAdd x)) :=
    ⟨(schwartzBruhat_continuous f).comp continuous_ofAdd,
      ((mem_finitePlaceSchwartz_iff F v _).1 ⟨f, fun _ ↦ rfl⟩).2⟩
  refine Eq.trans ?_ (integral_const_mul c _)
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  have h : tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(c • f) (a.val * y) =
      c * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) :=
    (exists_finiteConnesPrincipalValue_fourier_linear v c _ _ hreg.1 hreg.2
      hreg.1 hreg.2 (a.val * y)).2
  exact (congrArg (((J𝔭(v) y : ℝ) : ℂ) * ·) h).trans (mul_left_comm _ _ _)

/-- The scaled pairing is `√‖a‖` times the dilated pairing, and integrable. -/
private theorem exists_finiteConnesPrincipalValue_scale (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒮ₐ(v.adicCompletion F)) :
    Integrable (logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v), addTest(f)))
        scaledMeasure(v, a) ∧
      -(V𝔭(v) : ℂ) * ((√‖a.val‖ * √‖a.val‖ : ℝ) : ℂ) *
          ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)
            ∂ν𝔭(v) =
        -(V𝔭(v) : ℂ) * ∫ y, logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v),
          addTest(f)) y ∂scaledMeasure(v, a) := by
  have hc : (ENNReal.ofReal √‖a.val‖).toReal = √‖a.val‖ :=
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
  -- Changing the character and the measure dilates the transform and scales it by `√‖a‖`.
  have hF (y : v.adicCompletion F) :
      tamagawaFourier (ENNReal.ofReal √‖a.val‖ • ν𝔭(v)) (fun x ↦ ψ𝔭(v) (a.val * x))
        addTest(f) y = (√‖a.val‖ : ℝ) • tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) := by
    unfold tamagawaFourier
    rw [integral_smul_measure, hc]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [mul_left_comm a.val x y]
  have hK : logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v), addTest(f)) =
      fun y ↦ ((√‖a.val‖ : ℝ) : ℂ) * (((J𝔭(v) y : ℝ) : ℂ) *
        tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y)) := by
    funext y
    rw [hF, Complex.real_smul]
    ring
  rw [hK]
  refine ⟨((exists_finiteConnesPrincipalValue_integrable v a f).const_mul _).smul_measure
    ENNReal.ofReal_ne_top, ?_⟩
  rw [integral_smul_measure, hc, integral_const_mul, Complex.real_smul]
  push_cast
  ring

/-- Paper: Definition B.4.4.1(1), p. 619. The scaled finite Fourier
pairing defines a continuous linear functional on additive tests.
Deviation: The additive character is allowed to be any translate of the standard character
by a nonzero field multiplier, with the corresponding self-dual measure. -/
theorem exists_finiteConnesPrincipalValue (v : Primes(F)) (a : (v.adicCompletion F)ˣ) :
    ∃ T : StrongDual ℂ (𝒮ₐ(v.adicCompletion F)),
      ∀ f : 𝒮ₐ(v.adicCompletion F),
        let ν := scaledMeasure(v, a)
        let K : v.adicCompletion F → ℂ := logFourierIntegrand(ν, scaledChar(v, a), J𝔭(v), addTest(f))
        Integrable K ν ∧ T f = -(V𝔭(v) : ℂ) * ∫ y, K y ∂ν :=
  exists_finiteConnesPrincipalValue_ofLinear v (fun f ↦
    -(V𝔭(v) : ℂ) * ((√‖a.val‖ * √‖a.val‖ : ℝ) : ℂ) *
      ∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) ∂ν𝔭(v))
    (fun f g ↦ by rw [exists_finiteConnesPrincipalValue_add, mul_add])
    (fun c f ↦ by rw [exists_finiteConnesPrincipalValue_smul, mul_left_comm])
    (fun f z ↦ Integrable (logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v),
        addTest(f))) scaledMeasure(v, a) ∧
      z = -(V𝔭(v) : ℂ) * ∫ y, logFourierIntegrand(scaledMeasure(v, a), scaledChar(v, a), J𝔭(v),
        addTest(f)) y ∂scaledMeasure(v, a))
    (exists_finiteConnesPrincipalValue_scale v a)

/-- Paper: Definition B.4.4.1(1), p. 619. Connes's finite additive
principal value pairs the Fourier-transformed test with the normalized logarithm.
Deviation: The nonzero multiplier specifies the character as in (B.4.4.12). -/
def finiteConnesPrincipalValue (v : Primes(F)) (a : (v.adicCompletion F)ˣ) :
    StrongDual ℂ (𝒮ₐ(v.adicCompletion F)) := (exists_finiteConnesPrincipalValue v a).choose

/-- Paper: Definition B.4.4.1(1), p. 619. Outside the singularity, the finite
additive principal value for the standard character is ordinary multiplicative integration. -/
theorem finiteConnesPrincipalValue_one_of_apply_zero (v : Primes(F))
    (f : 𝒮ₐ(v.adicCompletion F)) (_hf : addTest(f) 0 = 0) :
    finiteConnesPrincipalValue v 1 f =
      ∫ u : (v.adicCompletion F)ˣ, addTest(f) u.val ∂μ𝔭(v) := by
  have hT := ((exists_finiteConnesPrincipalValue v 1).choose_spec f).2
  have hK := (finiteLogFourier_eq_neg_haar v f _hf).2.2
  have hV : V𝔭(v) ≠ 0 := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_integerUnits, ENNReal.toReal_ne_zero]
    refine ⟨ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top, ENNReal.inv_ne_top.mpr ?_⟩
    refine (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne'
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).trans' zero_lt_one
  change finiteConnesPrincipalValue v 1 f = _ at hT
  simp only [Units.val_one, norm_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul,
    one_mul] at hT
  rw [hT, hK, mul_div, neg_mul_neg]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hV)

/-- The elementary Schwartz space of a real vector group is the usual Schwartz space. -/
private theorem exists_infiniteConnesPrincipalValue_elementaryEquiv (d : ℕ) :
    ∃ e : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) ≃L[ℂ] ElementarySchwartz d 0 0 PUnit,
      ∀ f x, e f x = f x.1 := by
  let E := EuclideanSpace ℝ (Fin d)
  let X := 𝓢(E, ℂ)
  let Y := ElementarySchwartz d 0 0 PUnit
  let L : X →ₗ[ℂ] Y :=
    { toFun := fun f ↦ ⟨fun x ↦ f x.1, (elementarySchwartzSubmodule_real_iff _).mpr ⟨f, rfl⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hL (f : X) (x : ElementaryLieGroup d 0 0 PUnit) : L f x = f x.1 := rfl
  have hbij : Bijective L := by
    constructor
    · intro f g h
      ext x
      exact congrArg (fun s : Y ↦ s (x, 0, 0, 0)) h
    · intro g
      let f (x : E) := g (x, 0, 0, 0)
      have heq : (fun x : ElementaryLieGroup d 0 0 PUnit ↦ f x.1) = g.val := by
        funext x
        exact congrArg g (Prod.ext rfl (Subsingleton.elim _ _))
      have hmem := (elementarySchwartzSubmodule_real_iff f).mp (heq ▸ g.property)
      obtain ⟨s, hs⟩ := hmem
      refine ⟨s, Subtype.ext ?_⟩
      change (fun x : ElementaryLieGroup d 0 0 PUnit ↦ s x.1) = g.val
      rw [← heq]
      exact congrArg (fun u : E → ℂ ↦ fun x : ElementaryLieGroup d 0 0 PUnit ↦ u x.1) hs
  have hX : IsFrechetTVS X := euclideanSchwartz_frechet d
  have : BarrelledSpace ℂ X := isFrechetTVS_barrelled hX
  have hc : Continuous L := by
    apply continuous_toElementarySchwartz_of_eval
    intro g
    exact ⟨(BoundedContinuousFunction.evalCLM ℂ g.1).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ E ℂ), fun _ ↦ rfl⟩
  obtain ⟨hTX, -, hMX, hCX⟩ := hX
  obtain ⟨hTY, -, hMY, hCY⟩ := elementarySchwartz_isFrechet (m := d) (n := 0) (r := 0) (F := PUnit)
  let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup X := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace X := hCX
  have : CompleteSpace Y := hCY
  have : (uniformity Y).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero Y]
    infer_instance
  have : BaireSpace Y := BaireSpace.of_completelyPseudoMetrizable
  let A : X →L[ℂ] Y := ⟨L, hc⟩
  have hopen : IsOpenMap A := by
    apply isOpenMap_of_not_isMeagre_range A
    change ¬ IsMeagre (range L)
    rw [hbij.surjective.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  let e := LinearEquiv.ofBijective L hbij
  refine ⟨{ e with continuous_toFun := hc, continuous_invFun := ?_ }, hL⟩
  exact e.toEquiv.continuous_symm_iff.mpr hopen

/-- A real vector coordinate gives a largest structural pair, with whole open subgroup,
presented by the real vector group. -/
private theorem exists_infiniteConnesPrincipalValue_presentation {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {d : ℕ}
    (c : G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin d))) :
    ∃ a : BruhatStructuralPair G, (∀ b, b ≤ a) ∧ ∃ (hm : ∀ x : G, x ∈ a.val.1)
        (w : a.quotient ≃ₜ* Multiplicative (ElementaryLieGroup d 0 0 PUnit)),
        ∀ x : G, (w (QuotientGroup.mk ⟨x, hm x⟩)).toAdd.1 = (c x).toAdd := by
  have : ConnectedSpace (Multiplicative (EuclideanSpace ℝ (Fin d))) :=
    inferInstanceAs (ConnectedSpace (EuclideanSpace ℝ (Fin d)))
  have : ConnectedSpace G := c.symm.surjective.connectedSpace c.symm.continuous
  let chart : EuclideanSpace ℝ (Fin d) ≃ₜ G := c.symm.toHomeomorph
  have hgood : IsBruhatGoodSubgroup (⊥ : Subgroup G) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨d, ⟨chart.chartedSpace⟩⟩
  let H : Subgroup G := ⊤
  let i : G ≃ₜ* H :=
    ⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩
  have htop : IsOpen (H : Set G) := isOpen_univ
  let : ConnectedSpace H := i.surjective.connectedSpace i.continuous
  let : LocallyCompactSpace H := htop.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hgen : IsCompactlyGeneratedGroup H := by
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : H)
    have hOpen : IsOpen (Subgroup.closure U : Set H) :=
      Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hU Subgroup.subset_closure)
    exact ⟨U, hU, hUc, SetLike.coe_injective
      ((OpenSubgroup.isClopen ⟨Subgroup.closure U, hOpen⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩
  let a : BruhatStructuralPair G := ⟨(H, OrderDual.toDual ⊥), htop, hgen, hgood, bot_le⟩
  have hmem (x : G) : x ∈ a.val.1 := Subgroup.mem_top x
  let p := (QuotientGroup.mk' _ : H →* a.quotient).comp i.toMulEquiv.toMonoidHom
  have hp : IsOpenQuotientMap p :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.toHomeomorph.isOpenQuotientMap
  have hinj : Injective p := (MonoidHom.ker_eq_bot_iff p).mp (le_antisymm (fun x hx ↦ by
    change (QuotientGroup.mk (i x) : a.quotient) = 1 at hx
    exact (a.quotient_mk_eq_one (i x)).mp hx) bot_le)
  let q := (MulEquiv.ofBijective p ⟨hinj, hp.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hp.isQuotientMap.isOpen_preimage)
  let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit) := uniqueOfSubsingleton 0
  let w : Multiplicative (ElementaryLieGroup d 0 0 PUnit) ≃ₜ*
      Multiplicative (EuclideanSpace ℝ (Fin d)) :=
    ContinuousMulEquiv.mk' (Homeomorph.prodUnique _ _) (fun _ _ ↦ rfl)
  have ha (b : BruhatStructuralPair G) : b ≤ a := by
    change b.val.1 ≤ ⊤ ∧ (⊥ : Subgroup G) ≤ OrderDual.ofDual b.val.2
    exact ⟨le_top, bot_le⟩
  refine ⟨a, ha, hmem, q.symm.trans (c.trans w.symm), fun x ↦ ?_⟩
  change (w (w.symm (c (q.symm (q x))))).toAdd = _
  rw [q.symm_apply_apply, w.apply_symm_apply]

/-- In real vector coordinates, the Schwartz–Bruhat space carries the usual Schwartz
topology. -/
private theorem exists_infiniteConnesPrincipalValue_coordinate {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {d : ℕ}
    (c : G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin d))) :
    ∃ e : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) ≃L[ℂ] SchwartzBruhat G,
      ∀ f x, e f x = f (c x).toAdd := by
  have : SecondCountableTopology (Multiplicative (EuclideanSpace ℝ (Fin d))) :=
    inferInstanceAs (SecondCountableTopology (EuclideanSpace ℝ (Fin d)))
  have : SecondCountableTopology G := c.toHomeomorph.isEmbedding.secondCountableTopology
  refine (exists_infiniteConnesPrincipalValue_presentation c).elim fun a hp ↦ ?_
  refine hp.2.elim fun hm hm' ↦ hm'.elim fun w hw ↦ ?_
  have ha := hp.1
  let e : ElementaryLCAPresentation a.quotient := ⟨d, 0, 0, PUnit, w⟩
  let J : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a e
  have hJ : Topology.IsEmbedding J := schwartzBruhatStage_isEmbedding a e
  have hs : Surjective J := schwartzBruhat_maxStage_surjective a ha e
  let A := LinearEquiv.ofBijective J ⟨hJ.injective, hs⟩
  let B := ContinuousLinearEquiv.ofIsHomeomorph A
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hJ, hs⟩)
  refine (exists_infiniteConnesPrincipalValue_elementaryEquiv d).elim fun T hT ↦ ?_
  refine ⟨T.trans B, fun f x ↦ ?_⟩
  change (show SchwartzBruhat G from schwartzBruhatStageInclusion a e (T f)) x = _
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (hm x), hT]
  exact congrArg f (hw x)

/-- If, in a model of the completion, the logarithmic Fourier integrand is a weight of
polynomial growth times a Schwartz function depending continuously on the test, then
its integral is a continuous linear functional. -/
private theorem exists_infiniteConnesPrincipalValue_ofModel (w : InfinitePlace F)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] (m : V ≃ᵐ w.Completion) (μ : Measure V)
    (hμ : ν∞(w) = μ.map m) (Q : 𝒮ₐ(w.Completion) →L[ℂ] 𝓢(V, ℂ)) (L : V → ℂ)
    (hL : AEStronglyMeasurable L μ) (k : ℕ)
    (hk : Integrable (fun t ↦ ‖L t‖ / (1 + ‖t‖) ^ k) μ)
    (hK : ∀ (f : 𝒮ₐ(w.Completion)) (t : V),
      logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f)) (m t) = L t * Q f t) :
    ∃ T : StrongDual ℂ (𝒮ₐ(w.Completion)), ∀ f : 𝒮ₐ(w.Completion),
      let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
      Integrable K ν∞(w) ∧ T f = -(∫ y, K y ∂ν∞(w)) := by
  obtain ⟨Λ, hΛ⟩ := SchwartzMap.exists_strongDual_integral_mul μ L hL k hk
  refine ⟨-(Λ.comp Q), fun f ↦ ?_⟩
  intro K
  have hKm : K ∘ m = fun t ↦ L t * Q f t := funext (hK f)
  rw [hμ, integrable_map_equiv, integral_map_equiv]
  refine ⟨hKm ▸ (hΛ (Q f)).1, ?_⟩
  change -(Λ (Q f)) = -(∫ t, (K ∘ m) t ∂μ)
  rw [hKm, (hΛ (Q f)).2]

/-- Paper: Definition B.4.4.1(1), p. 619. The archimedean Fourier pairing
defines a continuous linear functional on additive tests. -/
theorem exists_infiniteConnesPrincipalValue (w : InfinitePlace F) :
    ∃ T : StrongDual ℂ (𝒮ₐ(w.Completion)), ∀ f : 𝒮ₐ(w.Completion),
      let K : w.Completion → ℂ := logFourierIntegrand(ν∞(w), ψ∞(w), J∞(w), addTest(f))
      Integrable K ν∞(w) ∧ T f = -(∫ y, K y ∂ν∞(w)) := by
  let : BorelSpace w.Completion := ⟨rfl⟩
  by_cases hw : w.IsReal
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    let j := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let m := j.symm.toHomeomorph.toMeasurableEquiv
    have hμ : ν∞(w) = (volume : Measure ℝ).map m := dite_eq_left hw
    have hem (t : ℝ) : e (m t) = t := e.apply_symm_apply t
    have hnorm (t : ℝ) : ‖m t‖ = ‖t‖ := by
      change ‖j.symm t‖ = ‖t‖
      rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
        show j.symm 0 = 0 from map_zero e.symm]
    let c : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
      { toMulEquiv := e.toAddEquiv.toMultiplicative
        continuous_toFun := j.continuous
        continuous_invFun := j.symm.continuous }
    obtain ⟨E, hE⟩ := schwartzBruhat_realCoordinate_equiv c
    have hP (f : 𝒮ₐ(w.Completion)) : addTest(f) = fun x ↦ E.symm f (e x) := by
      funext x
      conv_lhs => rw [← E.apply_symm_apply f]
      exact hE _ _
    refine exists_infiniteConnesPrincipalValue_ofModel w m volume hμ
      ((SchwartzMap.fourierTransformCLM ℂ).comp E.symm.toContinuousLinearMap)
      (fun t ↦ (Real.log ‖t‖ : ℂ))
      (Complex.measurable_ofReal.comp measurable_norm.log).aestronglyMeasurable 3 ?_
      fun f t ↦ ?_
    · have h := integrable_abs_log_norm_div_one_add_norm_pow (volume : Measure ℝ)
        (by simp)
      simp only [Module.finrank_self] at h
      simpa only [Complex.norm_real, Real.norm_eq_abs] using h
    · change (Real.log (‖m t‖ ^ w.mult) : ℂ) * tamagawaFourier ν∞(w) ψ∞(w) addTest(f) (m t) = _
      rw [hw.mult_eq_one, pow_one, hnorm, hP f, realModelFourier w hw, hem]
      rfl
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hc
    let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    let m := j.symm.toHomeomorph.toMeasurableEquiv
    have hμ : ν∞(w) = (2 • (volume : Measure ℂ)).map m := dite_eq_right hw
    have hem (t : ℂ) : e (m t) = t := e.apply_symm_apply t
    have hnorm (t : ℂ) : ‖m t‖ = ‖t‖ := by
      change ‖j.symm t‖ = ‖t‖
      rw [← dist_zero_right, ← dist_zero_right t, ← j.symm.dist_eq t 0,
        show j.symm 0 = 0 from map_zero e.symm]
    let LE : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      (LinearEquiv.ofFinrankEq ℂ (EuclideanSpace ℝ (Fin 2)) (by simp)).toContinuousLinearEquiv
    let c₀ : w.Completion ≃ₜ EuclideanSpace ℝ (Fin 2) := j.toHomeomorph.trans LE.toHomeomorph
    let c : Multiplicative w.Completion ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin 2)) :=
      ContinuousMulEquiv.mk' c₀ (fun x y ↦ by
        change LE (e (x.toAdd + y.toAdd)) = LE (e x.toAdd) + LE (e y.toAdd)
        rw [map_add, map_add])
    obtain ⟨E, hE⟩ := exists_infiniteConnesPrincipalValue_coordinate c
    let P : 𝒮ₐ(w.Completion) →L[ℂ] 𝓢(ℂ, ℂ) :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ LE).comp E.symm.toContinuousLinearMap
    have hP (f : 𝒮ₐ(w.Completion)) : addTest(f) = fun x ↦ P f (e x) := by
      funext x
      conv_lhs => rw [← E.apply_symm_apply f]
      exact hE _ _
    let A : ℂ ≃L[ℝ] ℂ := Complex.conjCLE.trans
      (LinearEquiv.smulOfNeZero ℝ ℂ (2 : ℝ) two_ne_zero).toContinuousLinearEquiv
    have hA (z : ℂ) : A z = (2 : ℝ) • star z := rfl
    refine exists_infiniteConnesPrincipalValue_ofModel w m (2 • volume) hμ
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A).comp
        ((SchwartzMap.fourierTransformCLM ℂ).comp P))
      (fun t ↦ (Real.log (‖t‖ ^ 2) : ℂ) * 2)
      ((Complex.measurable_ofReal.comp (measurable_norm.pow_const 2).log).mul_const
        _).aestronglyMeasurable 4 ?_ fun f t ↦ ?_
    · have h := integrable_abs_log_norm_div_one_add_norm_pow (volume : Measure ℂ)
        (by simp)
      simp only [Complex.finrank_real_complex] at h
      have h' : Integrable (fun t : ℂ ↦ ‖(Real.log (‖t‖ ^ 2) : ℂ) * 2‖ / (1 + ‖t‖) ^ 4)
          volume := by
        refine (h.const_mul 4).congr (ae_of_all _ fun t ↦ ?_)
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.log_pow]
        norm_num [abs_mul]
        ring
      rw [two_smul]
      exact h'.add_measure h'
    · change (Real.log (‖m t‖ ^ w.mult) : ℂ) * tamagawaFourier ν∞(w) ψ∞(w) addTest(f) (m t) = _
      rw [hc.mult_eq_two, hnorm, hP f, complexModelFourier w hc, hem]
      change _ = _ * FourierTransform.fourier (P f : ℂ → ℂ) (A t)
      rw [hA]
      ring

/-- Paper: Definition B.4.4.1(1), p. 619. Connes's archimedean additive
principal value is minus the Fourier transform of the logarithm distribution. -/
def infiniteConnesPrincipalValue (w : InfinitePlace F) :
    StrongDual ℂ (𝒮ₐ(w.Completion)) := (exists_infiniteConnesPrincipalValue w).choose

/-- Paper: Definition B.4.4.1(1), p. 619. On real tests vanishing at
zero, the additive principal value is integration against half of the weighted additive measure.
Deviation: The factor one half is the real case of the correction to Proposition B.4.3.2. -/
theorem realConnesPrincipalValue_of_apply_zero (w : InfinitePlace F) (_hw : w.IsReal)
    (f : 𝒮ₐ(w.Completion)) (_hf : addTest(f) 0 = 0) :
    infiniteConnesPrincipalValue w f =
      (1 / 2 : ℂ) * ∫ x, addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w) := by
  have hT := ((exists_infiniteConnesPrincipalValue w).choose_spec f).2
  change infiniteConnesPrincipalValue w f = _ at hT
  have hL := (realLogFourier_finitePart w _hw f).2.2
  simp only [_hf, mul_zero, zero_mul, add_zero] at hL
  let : BorelSpace w.Completion := ⟨rfl⟩
  -- Real coordinates turn the test into a classical Schwartz function vanishing at zero.
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal _hw
  let c : Multiplicative w.Completion ≃ₜ* Multiplicative ℝ :=
    { toMulEquiv := (InfinitePlace.Completion.ringEquivRealOfIsReal _hw).toAddEquiv.toMultiplicative
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have hc := schwartzBruhat_realCoordinate_equiv c
  have hE := hc.choose_spec
  let s := hc.choose.symm f
  have hs (t : ℝ) : s t = addTest(f) (e.symm t) := by
    have := hE s (Multiplicative.ofAdd (e.symm t))
    rw [ContinuousLinearEquiv.apply_symm_apply] at this
    refine Eq.trans ?_ this.symm
    exact congrArg s (e.apply_symm_apply t).symm
  have h0 : e.symm 0 = 0 := map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal _hw).symm
  have hnorm (t : ℝ) : ‖e.symm t‖ = ‖t‖ := by
    rw [← dist_zero_right, ← dist_zero_right t, ← e.symm.dist_eq t 0, h0]
  have hs0 : s 0 = 0 := by rw [hs, h0]; exact _hf
  -- The weighted test is integrable on the real line: Lipschitz near zero, decaying at infinity.
  let C := SchwartzMap.seminorm ℝ 0 1 s
  have hlip (t : ℝ) : ‖s t‖ ≤ C * ‖t‖ := by
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := s) (s := univ) (C := C)
      (fun x _ ↦ s.differentiableAt) (fun x _ ↦ ?_) convex_univ (mem_univ 0) (mem_univ t)
    · simpa [hs0] using this
    · rw [← norm_iteratedFDeriv_one]
      exact s.norm_iteratedFDeriv_le_seminorm ℝ 1 x
  have hR : Integrable (fun t : ℝ ↦ s t / ((‖t‖ : ℝ) : ℂ)) := by
    refine Integrable.mono' (g := fun t ↦ (Icc (-1 : ℝ) 1).indicator (fun _ ↦ C) t + ‖s t‖)
      ((continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc).add
        s.integrable.norm)
      (s.continuous.measurable.div
        (Complex.measurable_ofReal.comp measurable_norm)).aestronglyMeasurable
      (Eventually.of_forall fun t ↦ ?_)
    rw [norm_div, Complex.norm_real, norm_norm]
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem ht]
      rcases eq_or_ne t 0 with rfl | ht0
      · simp [hs0, C]
      · have : ‖s t‖ / ‖t‖ ≤ C := (div_le_iff₀ (norm_pos_iff.mpr ht0)).mpr (hlip t)
        linarith [norm_nonneg (s t)]
    · rw [indicator_of_notMem ht, zero_add]
      have h1 : 1 ≤ ‖t‖ := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rw [Real.norm_eq_abs]
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      exact div_le_self (norm_nonneg _) h1
  have hG : Integrable (fun x : w.Completion ↦ addTest(f) x / ((‖x‖ : ℝ) : ℂ)) ν∞(w) := by
    rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left _hw]
    let m := e.symm.toHomeomorph.toMeasurableEquiv
    rw [show ((InfinitePlace.Completion.ringEquivRealOfIsReal _hw).symm : ℝ → w.Completion) = m
      from rfl, integrable_map_equiv]
    refine hR.congr (Eventually.of_forall fun t ↦ ?_)
    change s t / ((‖t‖ : ℝ) : ℂ) = addTest(f) (e.symm t) / ((‖e.symm t‖ : ℝ) : ℂ)
    rw [hs, hnorm]
  -- Dominated convergence removes the cutoff.
  have hmeas (ε : ℝ) : MeasurableSet {x : w.Completion | ε ≤ ‖x‖} :=
    measurableSet_le measurable_const measurable_norm
  have hlim : Tendsto (fun ε : ℝ ↦ ∫ x in {x : w.Completion | ε ≤ ‖x‖},
      addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w)) (𝓝[>] 0)
      (𝓝 (∫ x, addTest(f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w))) := by
    simp_rw [← integral_indicator (hmeas _)]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ ‖addTest(f) x / ((‖x‖ : ℝ) : ℂ)‖)
      (Eventually.of_forall fun ε ↦ hG.aestronglyMeasurable.indicator (hmeas ε))
      (Eventually.of_forall fun ε ↦ Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _)
      hG.norm (Eventually.of_forall fun x ↦ ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Set.indicator_apply]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds (norm_pos_iff.mpr hx))] with ε hε
      rw [indicator_of_mem (show ε ≤ ‖x‖ from hε.le)]
  rw [hT, tendsto_nhds_unique hlim hL]
  ring

/-- Good subgroups of the units of a finite completion are open, because the dual
quotient is locally connected and totally disconnected. -/
private theorem finiteUnits_goodSubgroup_isOpen (v : Primes(F))
    (k : Subgroup (v.adicCompletion F)ˣ) (hk : IsBruhatGoodSubgroup k) :
    IsOpen (k : Set (v.adicCompletion F)ˣ) := by
  let G := (v.adicCompletion F)ˣ
  let A : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator k, hk.2⟩
  obtain ⟨γ, _, hγ, hker, _⟩ := lca_dualSubgroup_quotient A
  let Q := PontryaginDual A.val
  let : LocallyCompactSpace A.val := A.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨n, ⟨charts⟩⟩ := isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mp A.property.2
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q := charts
  let : LocallyConnectedSpace Q := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) Q
  let B : OpenSubgroup G :=
    ⟨(v.adicCompletionIntegers F).units, Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)⟩
  let : CompactSpace B.toSubgroup := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let j : B.toSubgroup → v.adicCompletion F := Units.val ∘ Subtype.val
  have hj : Topology.IsEmbedding j :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).comp Topology.IsEmbedding.subtypeVal
  let η : B.toSubgroup →ₜ* Q := γ.comp ⟨B.toSubgroup.subtype, continuous_subtype_val⟩
  have hη : Continuous η := η.continuous
  have hηOpen : IsOpenMap η := hγ.isOpenMap.comp B.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hSmall (U : Set Q) (hU : U ∈ 𝓝 (1 : Q)) : ∃ V : OpenSubgroup Q, (V : Set Q) ⊆ U := by
    have hpre : η ⁻¹' U ∈ 𝓝 (1 : B.toSubgroup) :=
      hη.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU)
    rw [hj.isInducing.nhds_eq_comap] at hpre
    obtain ⟨S, hS, hSsub⟩ := mem_comap.mp hpre
    let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨r, hr⟩ := (Valued.mem_nhds (Γ₀ := WithZero (Multiplicative ℤ))).mp hS
    let W := (fun x : B.toSubgroup ↦ j x - j 1) ⁻¹' {y | ν.restrict y < r.val}
    have hW : IsClopen W :=
      (Valued.isClopen_ball (v.adicCompletion F) r.val).preimage
        (hj.continuous.sub continuous_const)
    have h1W : (1 : B.toSubgroup) ∈ W := by
      change ν.restrict (j 1 - j 1) < r.val
      rw [sub_self, map_zero]
      exact pos_iff_ne_zero.mpr r.ne_zero
    obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1W
    refine ⟨⟨V.toSubgroup.map η.toMonoidHom, hηOpen _ V.isOpen⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hSsub (hr (hV hx))
  have hComponent : connectedComponent (1 : Q) = {1} := by
    refine subset_antisymm ?_ (singleton_subset_iff.mpr mem_connectedComponent)
    intro y hy
    by_contra hne
    have h1y : (1 : Q) ∈ ({y} : Set Q)ᶜ :=
      fun h ↦ hne (mem_singleton_iff.mpr (mem_singleton_iff.mp h).symm)
    obtain ⟨V, hV⟩ := hSmall _ (isOpen_compl_singleton.mem_nhds h1y)
    have hyV := isPreconnected_connectedComponent.subset_isClopen V.isClopen
      ⟨1, mem_connectedComponent, V.one_mem⟩ hy
    exact (hV hyV) (mem_singleton y)
  have hOne : IsOpen ({1} : Set Q) := hComponent ▸ isOpen_connectedComponent
  rw [← lcaDualAnnihilator_annihilator k hk.1, ← hker]
  exact hOne.preimage γ.continuous

/-- A test function on the units of a finite completion is locally constant. -/
private theorem finiteUnits_test_isLocallyConstant (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)) : IsLocallyConstant f.val := by
  have hf : IsBruhatSmooth f.val := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1
  obtain ⟨k, hk, hInv, _⟩ := hf 0
  have hkOpen := finiteUnits_goodSubgroup_isOpen v k hk
  refine (IsLocallyConstant.iff_exists_open _).2 fun x ↦ ?_
  refine ⟨(fun y ↦ y * x⁻¹) ⁻¹' (k : Set _),
    hkOpen.preimage (by fun_prop : Continuous fun y : (v.adicCompletion F)ˣ ↦ y * x⁻¹), by simp [k.one_mem], fun y hy ↦ ?_⟩
  simpa using hInv ⟨_, hy⟩ x

/-- The norm on the units of a finite completion is locally constant. -/
private theorem finiteUnits_norm_isLocallyConstant (v : Primes(F)) :
    IsLocallyConstant (fun u : (v.adicCompletion F)ˣ ↦ ‖u.val‖) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun u ↦ ?_
  refine ⟨(fun w : (v.adicCompletion F)ˣ ↦ w.val) ⁻¹' {y | ‖y - u.val‖ < ‖u.val‖},
    (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).preimage
      Units.continuous_val, ?_, fun w hw ↦ ?_⟩
  · change ‖u.val - u.val‖ < ‖u.val‖
    rw [sub_self, norm_zero]
    exact norm_pos_iff.mpr u.ne_zero
  have hw' : ‖w.val - u.val‖ < ‖u.val‖ := hw
  have hne : ‖w.val - u.val‖ ≠ ‖u.val‖ := hw'.ne
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [sub_add_cancel, max_eq_right hw'.le] at h
  exact h

/-- The zero extension of a locally constant compactly supported function on the units
of a finite completion is locally constant and compactly supported. -/
private theorem finiteUnits_extend_regular (v : Primes(F)) (h : (v.adicCompletion F)ˣ → ℂ)
    (hl : IsLocallyConstant h) (hc : HasCompactSupport h) :
    IsLocallyConstant (Function.extend Units.val h (fun _ ↦ (0 : ℂ))) ∧
      HasCompactSupport (Function.extend Units.val h (fun _ ↦ (0 : ℂ))) := by
  have he : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) :=
    Units.isOpenEmbedding_val
  let E : v.adicCompletion F → ℂ := Function.extend Units.val h (fun _ ↦ (0 : ℂ))
  have hEu (u : (v.adicCompletion F)ˣ) : E u.val = h u := Units.val_injective.extend_apply h _ u
  let T := Units.val '' tsupport h
  have hT : IsCompact T := hc.image he.continuous
  have hE0 (y : v.adicCompletion F) (hy : y ∉ T) : E y = 0 := by
    by_cases hr : ∃ u : (v.adicCompletion F)ˣ, u.val = y
    · obtain ⟨u, rfl⟩ := hr
      rw [hEu]
      exact image_eq_zero_of_notMem_tsupport (fun hu ↦ hy ⟨u, hu, rfl⟩)
    · exact extend_apply' _ _ _ hr
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun y ↦ ?_,
    HasCompactSupport.of_support_subset_isCompact hT fun y hy ↦ by_contra fun h' ↦ hy (hE0 y h')⟩
  by_cases hy : y ∈ T
  · obtain ⟨u, -, rfl⟩ := hy
    obtain ⟨U, hU, huU, hconst⟩ := (IsLocallyConstant.iff_exists_open _).1 hl u
    refine ⟨Units.val '' U, he.isOpenMap _ hU, ⟨u, huU, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    change E w.val = E u.val
    rw [hEu, hEu]
    exact hconst w hw
  · refine ⟨Tᶜ, hT.isClosed.isOpen_compl, hy, fun z hz ↦ ?_⟩
    change E z = E y
    rw [hE0 z hz, hE0 y hy]

/-- A fixed-support stage is finite-dimensional when the good subgroup of its structural
pair is open: the compact support then meets finitely many of its cosets. -/
private theorem bruhatCompactSupportStage_finiteDimensional_of_isOpen {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts G) (hk : IsOpen ((OrderDual.ofDual a.val.2 : Subgroup G) : Set G)) :
    FiniteDimensional ℂ (bruhatCompactSupportStage a e C) := by
  classical
  let k := OrderDual.ofDual a.val.2
  let R := schwartzBruhatStageRealization a e
  have hinv (s : SchwartzBruhatStage e) (h : G) (hh : h ∈ k) (x : G) : R s (h * x) = R s x :=
    stage_realization_mul_kernel a e s hh x
  have hRinj (s : SchwartzBruhatStage e) (hs : ∀ x, R s x = 0) : s = 0 := by
    let s' : elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank e.finiteFactor := s
    change s' = 0
    refine Subtype.ext (funext fun p ↦ ?_)
    let q : a.quotient := e.equiv.symm (Multiplicative.ofAdd p)
    let x : a.val.1 := q.out
    have hxq : (QuotientGroup.mk x : a.quotient) = q := QuotientGroup.out_eq' q
    have h0 : R s x.val = 0 := hs x.val
    rw [schwartzBruhatStageRealization_apply, dite_eq_left x.property] at h0
    change s (Multiplicative.toAdd (e.equiv (QuotientGroup.mk x))) = 0 at h0
    have h1 := congrArg (fun r : a.quotient ↦ s (Multiplicative.toAdd (e.equiv r))) hxq
    have h2 : e.equiv q = Multiplicative.ofAdd p := e.equiv.apply_symm_apply _
    simp only [h2] at h1
    rw [Submodule.coe_zero]
    exact h1.symm.trans h0
  have hcov : (C : Set G) ⊆ ⋃ y : G, (fun z ↦ z * y⁻¹) ⁻¹' (k : Set G) := fun z _ ↦
    mem_iUnion.mpr ⟨z, show z * z⁻¹ ∈ k by rw [mul_inv_cancel]; exact k.one_mem⟩
  have hfin := C.isCompact.elim_finite_subcover
    (fun y : G ↦ (fun z ↦ z * y⁻¹) ⁻¹' (k : Set G))
    (fun y ↦ hk.preimage (continuous_id.mul continuous_const)) hcov
  let t := hfin.choose
  have ht := hfin.choose_spec
  let X := bruhatCompactSupportStage a e C
  let Ψ : bruhatCompactSupportStage a e C →ₗ[ℂ] (t → ℂ) :=
    LinearMap.pi fun y ↦ (LinearMap.proj y.val).comp (R.comp (bruhatCompactSupportStage a e C).subtype)
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro s hs
    refine Subtype.ext ((hRinj s.val fun x ↦ ?_).trans (Submodule.coe_zero (p := X)).symm)
    by_cases hxC : x ∈ (C : Set G)
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hxC)
      have h0 : R s.val y = 0 := congrFun hs ⟨y, hy⟩
      have h1 := hinv s.val (x * y⁻¹) hxy y
      rw [inv_mul_cancel_right] at h1
      rw [h1, h0]
    · exact image_eq_zero_of_notMem_tsupport fun h ↦
        hxC ((mem_bruhatCompactSupportStage_iff a e C s.val).1 s.property h)
  exact Module.Finite.of_injective Ψ hΨ

/-- A fixed-support stage of test functions on the units of a finite completion is
finite-dimensional, since good subgroups of the units are open. -/
private theorem finiteUnits_stage_finiteDimensional (v : Primes(F))
    (a : BruhatStructuralPair (v.adicCompletion F)ˣ) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts (v.adicCompletion F)ˣ) :
    FiniteDimensional ℂ (bruhatCompactSupportStage a e C) :=
  bruhatCompactSupportStage_finiteDimensional_of_isOpen a e C
    (finiteUnits_goodSubgroup_isOpen v _ a.property.2.2.1)

/-- Paper: Definition B.4.4.1(2), p. 620. Translation of the zero-extended
test after inverse square-root weighting gives a continuous linear map to additive tests. -/
theorem exists_finiteWeilTestMap (v : Primes(F)) :
    ∃ A : 𝒟((v.adicCompletion F)ˣ) →L[ℂ] 𝒮ₐ(v.adicCompletion F),
      ∀ (f : 𝒟((v.adicCompletion F)ˣ)) (x : v.adicCompletion F),
        addTest(A f) x = weightedTranslate(norm, f.val) x := by
  let K := v.adicCompletion F
  let G := Kˣ
  let wt (f : 𝒟(G)) : G → ℂ := fun u ↦ f.val u / (Real.sqrt ‖u.val‖ : ℂ)
  let Φ (f : 𝒟(G)) : K → ℂ := fun x ↦ Function.extend Units.val (wt f) (fun _ ↦ (0 : ℂ)) (1 + x)
  have hΦ (f : 𝒟(G)) (x : K) : Φ f x = weightedTranslate(norm, f.val) x := by
    change Function.extend Units.val (wt f) (fun _ ↦ (0 : ℂ)) (1 + x) =
      Function.extend Units.val f.val (fun _ ↦ (0 : ℂ)) (1 + x) / (Real.sqrt ‖1 + x‖ : ℂ)
    by_cases hr : ∃ u : G, u.val = 1 + x
    · obtain ⟨u, hu⟩ := hr
      rw [← hu, Units.val_injective.extend_apply, Units.val_injective.extend_apply]
    · rw [extend_apply' _ _ _ hr, extend_apply' _ _ _ hr, zero_div]
  have hreg (f : 𝒟(G)) : IsLocallyConstant (Φ f) ∧ HasCompactSupport (Φ f) := by
    have hl : IsLocallyConstant (wt f) := (finiteUnits_test_isLocallyConstant v f).comp₂
      ((finiteUnits_norm_isLocallyConstant v).comp fun t ↦ ((Real.sqrt t : ℝ) : ℂ)) (· / ·)
    have hc : HasCompactSupport (wt f) := HasCompactSupport.mono f.property.2 fun u hu h0 ↦ hu (by
      change f.val u / _ = 0
      rw [h0, zero_div])
    obtain ⟨hEl, hEc⟩ := finiteUnits_extend_regular v (wt f) hl hc
    exact ⟨hEl.comp_continuous (continuous_const.add continuous_id),
      hEc.comp_homeomorph (Homeomorph.addLeft (1 : K))⟩
  have hmem (f : 𝒟(G)) : (fun y : Multiplicative K ↦ Φ f y.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative K) := by
    obtain ⟨g, hg⟩ := (mem_finitePlaceSchwartz_iff F v (Φ f)).mpr (hreg f)
    have hgf : (fun y : Multiplicative K ↦ Φ f y.toAdd) = (g : Multiplicative K → ℂ) :=
      funext fun y ↦ (hg y.toAdd).symm
    rw [hgf]
    exact (show schwartzBruhatSubmodule (Multiplicative K) from g).property
  have hadd (f g : 𝒟(G)) (x : K) : Φ (f + g) x = Φ f x + Φ g x := by
    by_cases hr : ∃ u : G, u.val = 1 + x
    · obtain ⟨u, hu⟩ := hr
      simp only [Φ, ← hu, Units.val_injective.extend_apply]
      exact add_div _ _ _
    · simp only [Φ, extend_apply' _ _ _ hr, add_zero]
  have hsmul (c : ℂ) (f : 𝒟(G)) (x : K) : Φ (c • f) x = c • Φ f x := by
    by_cases hr : ∃ u : G, u.val = 1 + x
    · obtain ⟨u, hu⟩ := hr
      simp only [Φ, ← hu, Units.val_injective.extend_apply]
      exact mul_div_assoc _ _ _
    · simp only [Φ, extend_apply' _ _ _ hr, smul_zero]
  let Φlin : 𝒟(G) →ₗ[ℂ] (Multiplicative K → ℂ) :=
    { toFun := fun f y ↦ Φ f y.toAdd
      map_add' := fun f g ↦ funext fun y ↦ hadd f g y.toAdd
      map_smul' := fun c f ↦ funext fun y ↦ hsmul c f y.toAdd }
  let L : 𝒟(G) →ₗ[ℂ] 𝒮ₐ(K) := Φlin.codRestrict _ hmem
  have hcont : Continuous L := by
    let P := {q : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
        (C : TopologicalSpace.Compacts G), Continuous (q ∘ bruhatCompactSupportStageInclusion a e C)}
    refine (PolynormableSpace.withSeminorms ℂ (𝒮ₐ(K))).continuous_of_continuous_comp L fun p ↦
      (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm
        (⟨p.val.comp L, ?_⟩ : P)
    intro a e C
    let X := bruhatCompactSupportStage a e C
    let : FiniteDimensional ℂ X := finiteUnits_stage_finiteDimensional v a e C
    let : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
    let : ContinuousSMul ℂ (SchwartzBruhatStage e) :=
      elementarySchwartz_withSeminorms.continuousSMul
    let : ContinuousSMul ℂ 𝒮ₐ(K) := (PolynormableSpace.withSeminorms ℂ _).continuousSMul
    let M : X →ₗ[ℂ] 𝒮ₐ(K) :=
      L.comp (show X →ₗ[ℂ] 𝒟(G) from bruhatCompactSupportStageInclusion a e C)
    exact p.property.comp M.continuous_of_finiteDimensional
  exact ⟨⟨L, hcont⟩, fun f x ↦ hΦ f x⟩

/-- Closed graph theorem from a closed subspace of a Fréchet space to a Fréchet space. -/
private theorem weilTest_continuous_of_isClosed_graph {E Y : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
    [ContinuousSMul ℂ Y]
    (hE : IsFrechetTVS E) (hY : IsFrechetTVS Y) (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    (T : S →ₗ[ℂ] Y) (hT : IsClosed (T.graph : Set (S × Y))) : Continuous T := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : UniformSpace Y := IsTopologicalAddGroup.rightUniformSpace Y
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have : IsUniformAddGroup Y := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace E := hE.2.2.2
  have : CompleteSpace Y := hY.2.2.2
  have : TopologicalSpace.MetrizableSpace E := hE.2.2.1
  have : TopologicalSpace.MetrizableSpace Y := hY.2.2.1
  have : CompleteSpace S := completeSpace_coe_iff_isComplete.mpr hS.isComplete
  have : IsUniformAddGroup S := S.toAddSubgroup.isUniformAddGroup
  let Γ := T.graph
  have : CompleteSpace Γ := completeSpace_coe_iff_isComplete.mpr hT.isComplete
  have : IsUniformAddGroup Γ := Γ.toAddSubgroup.isUniformAddGroup
  have : TopologicalSpace.MetrizableSpace S :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (S : Set E))
  have : TopologicalSpace.MetrizableSpace (S × Y) := inferInstance
  have : TopologicalSpace.MetrizableSpace Γ :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Γ : Set (S × Y)))
  have : FirstCountableTopology Γ := inferInstance
  have : FirstCountableTopology S := inferInstance
  have : (uniformity S).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : BaireSpace S := BaireSpace.of_completelyPseudoMetrizable
  let P : Γ →L[ℂ] S := (ContinuousLinearMap.fst ℂ S Y).comp Γ.subtypeL
  have hmem (x : S) : (x, T x) ∈ Γ := (LinearMap.mem_graph_iff _ _).mpr rfl
  have hval (p : Γ) : p.val.2 = T p.val.1 := (LinearMap.mem_graph_iff _ _).mp p.property
  have hinj : Injective P := fun p q h ↦ by
    have h1 : p.val.1 = q.val.1 := h
    exact Subtype.ext (Prod.ext h1 (by rw [hval, hval, h1]))
  have hsurj : Surjective P := fun x ↦ ⟨⟨(x, T x), hmem x⟩, rfl⟩
  have ho : IsOpenMap P := by
    apply isOpenMap_of_not_isMeagre_range P
    rw [hsurj.range_eq]
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
  let h : Γ ≃ₜ S :=
    (Equiv.ofBijective P ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen P.continuous ho
  refine (continuous_snd.comp (continuous_subtype_val.comp h.symm.continuous)).congr fun x ↦ ?_
  have h1 : (h.symm x).val.1 = x := h.apply_symm_apply x
  change (h.symm x).val.2 = T x
  rw [hval, h1]

/-- A real vector coordinate gives a structural pair with trivial kernel and whole
open subgroup, presented by the real vector group. -/
private theorem weilTest_vectorPresentation {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {d : ℕ}
    (c : G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin d))) :
    ∃ a : BruhatStructuralPair G, ∃ (hm : ∀ x : G, x ∈ a.val.1)
        (w : a.quotient ≃ₜ* Multiplicative (ElementaryLieGroup d 0 0 PUnit)),
        ∀ x : G, (w (QuotientGroup.mk ⟨x, hm x⟩)).toAdd.1 = (c x).toAdd := by
  have : ConnectedSpace (Multiplicative (EuclideanSpace ℝ (Fin d))) :=
    inferInstanceAs (ConnectedSpace (EuclideanSpace ℝ (Fin d)))
  have : ConnectedSpace G := c.symm.surjective.connectedSpace c.symm.continuous
  let chart : EuclideanSpace ℝ (Fin d) ≃ₜ G := c.symm.toHomeomorph
  have hgood : IsBruhatGoodSubgroup (⊥ : Subgroup G) :=
    isBruhatGoodSubgroup_bot_iff.mpr ⟨d, ⟨chart.chartedSpace⟩⟩
  let H : Subgroup G := ⊤
  let i : G ≃ₜ* H :=
    ⟨Subgroup.topEquiv.symm, continuous_id.subtype_mk _, continuous_subtype_val⟩
  have htop : IsOpen (H : Set G) := isOpen_univ
  let : ConnectedSpace H := i.surjective.connectedSpace i.continuous
  let : LocallyCompactSpace H := htop.isOpenEmbedding_subtypeVal.locallyCompactSpace
  have hgen : IsCompactlyGeneratedGroup H := by
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds (1 : H)
    have hOpen : IsOpen (Subgroup.closure U : Set H) :=
      Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hU Subgroup.subset_closure)
    exact ⟨U, hU, hUc, SetLike.coe_injective
      ((OpenSubgroup.isClopen ⟨Subgroup.closure U, hOpen⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩
  let a : BruhatStructuralPair G := ⟨(H, OrderDual.toDual ⊥), htop, hgen, hgood, bot_le⟩
  have hmem (x : G) : x ∈ a.val.1 := Subgroup.mem_top x
  let p := (QuotientGroup.mk' _ : H →* a.quotient).comp i.toMulEquiv.toMonoidHom
  have hp : IsOpenQuotientMap p :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.toHomeomorph.isOpenQuotientMap
  have hinj : Injective p := (MonoidHom.ker_eq_bot_iff p).mp (le_antisymm (fun x hx ↦ by
    change (QuotientGroup.mk (i x) : a.quotient) = 1 at hx
    exact (a.quotient_mk_eq_one (i x)).mp hx) bot_le)
  let q := (MulEquiv.ofBijective p ⟨hinj, hp.surjective⟩).toContinuousMulEquiv
    (fun _ ↦ hp.isQuotientMap.isOpen_preimage)
  let : Unique ((Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × PUnit) := uniqueOfSubsingleton 0
  let w : Multiplicative (ElementaryLieGroup d 0 0 PUnit) ≃ₜ*
      Multiplicative (EuclideanSpace ℝ (Fin d)) :=
    ContinuousMulEquiv.mk' (Homeomorph.prodUnique _ _) (fun _ _ ↦ rfl)
  refine ⟨a, hmem, q.symm.trans (c.trans w.symm), fun x ↦ ?_⟩
  change (w (w.symm (c (q.symm (q x))))).toAdd = _
  rw [q.symm_apply_apply, w.apply_symm_apply]

/-- Extension by zero from the units evaluates the function off zero. -/
private theorem weilTest_zeroExtend_apply {K : Type*} [GroupWithZero K] (f : Kˣ → ℂ) (x : K) :
    Function.extend Units.val f (fun _ ↦ (0 : ℂ)) x =
      if hx : x = 0 then 0 else f (Units.mk0 x hx) := by
  split_ifs with hx
  · subst hx
    exact Function.extend_apply' _ _ _ fun ⟨u, hu⟩ ↦ u.ne_zero hu
  · exact Units.val_injective.extend_apply f (fun _ ↦ (0 : ℂ)) (Units.mk0 x hx)


/-- An exponential-type map with identity derivative has a smooth local inverse at one. -/
private theorem weilTest_localLog {𝕂 : Type*} [RCLike 𝕂] (E : 𝕂 → 𝕂) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0) :
    ∃ Λ : 𝕂 → 𝕂, ContDiffAt ℝ (⊤ : ℕ∞) Λ 1 ∧ ∀ᶠ y in 𝓝 1, E (Λ y) = y := by
  have hn0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hEc : ContDiffAt ℝ (⊤ : ℕ∞) E 0 := hEs.contDiffAt
  have hS := ContDiffAt.hasStrictFDerivAt hEc hEd hn0
  have h0 : (hS.toOpenPartialHomeomorph E).symm (E 0) = 0 := hS.localInverse_apply_image
  have hΛ : ContDiffAt ℝ (⊤ : ℕ∞) (hS.toOpenPartialHomeomorph E).symm (E 0) :=
    (hS.toOpenPartialHomeomorph E).contDiffAt_symm hS.image_mem_toOpenPartialHomeomorph_target
      (by rw [h0]; exact hEd) (by rw [h0]; exact hEc)
  have hright : ∀ᶠ y in 𝓝 (E 0), E ((hS.toOpenPartialHomeomorph E).symm y) = y :=
    hS.eventually_right_inverse
  rw [hE00] at hΛ hright
  exact ⟨_, hΛ, hright⟩


/-- On an elementary presentation, a function smooth on the covers stays smooth along a
continuous one-parameter family of translates given by an additive map from a real vector
space. -/
private theorem weilTest_elementary_curve {Q : Type*} [CommGroup Q] [TopologicalSpace Q]
    {𝕂 : Type*} [RCLike 𝕂] {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (e : ElementaryLCAPresentation Q) (f₀ : Q → ℂ) {N : ℕ∞}
    (hsm : ∀ (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor), ContDiff ℝ (N : WithTop ℕ∞)
      (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd (elementaryCover xt z b)))))
    (θ : 𝕂 →+ ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)
    (hθ : Continuous θ) (q₀ : Q) :
    ContDiff ℝ (N : WithTop ℕ∞)
      (fun v ↦ f₀ (e.equiv.symm (e.equiv q₀ * Multiplicative.ofAdd (θ v)))) := by
  obtain ⟨A, hA, hAv⟩ : ∃ A : ElementaryLieGroup d 0 0 PUnit.{1} →+
      ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor,
      Continuous A ∧ ∀ x, A x = θ (L.symm x.1) :=
    ⟨θ.comp ((L.symm.toLinearMap.toAddMonoidHom).comp (AddMonoidHom.fst _ _)),
      hθ.comp (L.symm.continuous.comp continuous_fst), fun _ ↦ rfl⟩
  obtain ⟨θ₀, hθ₀⟩ : ∃ θ₀ : ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor,
      Multiplicative.ofAdd θ₀ = e.equiv q₀ := ⟨_, rfl⟩
  obtain ⟨f', hf'v⟩ : ∃ f' : ElementaryLieGroup e.realDim e.torusDim e.latticeRank
      e.finiteFactor → ℂ, ∀ y, f' y = f₀ (e.equiv.symm (Multiplicative.ofAdd (θ₀ + y))) :=
    ⟨_, fun _ ↦ rfl⟩
  have hf' (z : Fin e.latticeRank → ℤ) (b : e.finiteFactor) :
      ContDiff ℝ (N : WithTop ℕ∞) (fun u ↦ f' (elementaryCover u z b)) := by
    obtain ⟨t, ht⟩ := elementaryCover_surjective θ₀.2.2.1 θ₀.2.2.2 θ₀.1 θ₀.2.1
    have hθ : θ₀ = elementaryCover (θ₀.1, t) θ₀.2.2.1 θ₀.2.2.2 := ht.symm
    have hshift (u : EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)) :
        θ₀ + elementaryCover u z b =
          elementaryCover ((θ₀.1, t) + u) (θ₀.2.2.1 + z) (θ₀.2.2.2 + b) := by
      calc θ₀ + elementaryCover u z b
          = elementaryCover (θ₀.1, t) θ₀.2.2.1 θ₀.2.2.2 + elementaryCover u z b :=
            congrArg (· + elementaryCover u z b) hθ
        _ = _ := by
          simp only [elementaryCover, Prod.mk_add_mk, Prod.fst_add, Prod.snd_add,
            PiLp.add_apply, AddCircle.coe_add]
          rfl
    simp only [hf'v, hshift]
    exact (hsm _ _).comp (contDiff_const.add contDiff_id)
  have hG := (contDiff_comp_elementaryHom A hA hf' 0 0).comp
    (L.contDiff.prodMk (contDiff_const (c := (0 : EuclideanSpace ℝ (Fin 0)))))
  have heq : ∀ v : 𝕂, f₀ (e.equiv.symm (e.equiv q₀ * Multiplicative.ofAdd (θ v))) =
      f' (A (elementaryCover (m := d) (n := 0) (r := 0) (F := PUnit.{1})
        (L v, (0 : EuclideanSpace ℝ (Fin 0))) 0 0)) := by
    intro v
    rw [hAv]
    change _ = f' (θ (L.symm (L v)))
    rw [L.symm_apply_apply, hf'v, ofAdd_add, hθ₀]
  simp_rw [heq]
  exact hG

/-- A Bruhat smooth function on the units is smooth along every exponential curve. -/
private theorem weilTest_units_curve (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφs : Continuous φ.symm)
    {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEc : Continuous E) (f : w.Completionˣ → ℂ) (hf : IsBruhatSmooth f)
    (u₀ : w.Completionˣ) (n : ℕ) :
    ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun v : 𝕂 ↦
      Function.extend Units.val f (fun _ ↦ (0 : ℂ)) ((u₀ : w.Completion) * φ.symm (E v))) := by
  have hne (y : 𝕂) (hy : y ≠ 0) : φ.symm y ≠ 0 := (map_ne_zero φ.symm).mpr hy
  obtain ⟨k, hk, -, hdesc⟩ := hf n
  have hkC : IsCompact (k : Set w.Completionˣ) := (lcaDualAnnihilator_annihilator k hk.1) ▸
    isCompact_lcaDualAnnihilator (lcaAnnihilator k) hk.2.1
  obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains
    ((isCompact_singleton (x := u₀)).union hkC)
  obtain ⟨a, haH, hak⟩ : ∃ a : BruhatStructuralPair w.Completionˣ, a.val.1 = H.val ∧
      OrderDual.ofDual a.val.2 = k :=
    ⟨⟨(H.val, OrderDual.toDual k), H.property.1, H.property.2, hk, fun _ hx ↦ hH (Or.inr hx)⟩,
      rfl, rfl⟩
  obtain ⟨f₀, hf₀, hsm⟩ := hdesc a hak
  obtain ⟨e⟩ := a.elementary
  have hu₀ : u₀ ∈ a.val.1 := haH ▸ hH (Or.inl rfl)
  -- The exponential lands in the identity component, hence in the open subgroup.
  obtain ⟨Eu, hEuv⟩ : ∃ Eu : Multiplicative 𝕂 →* w.Completionˣ,
      ∀ v, (Eu v : w.Completion) = φ.symm (E v.toAdd) :=
    ⟨{ toFun := fun v ↦ Units.mk0 (φ.symm (E v.toAdd)) (hne _ (hE0 _))
       map_one' := Units.ext (by simp [hE00])
       map_mul' := fun a b ↦ Units.ext (by simp [hEadd]) }, fun _ ↦ rfl⟩
  have hEu : Continuous Eu := Units.isEmbedding_val₀.continuous_iff.mpr
    ((hφs.comp (hEc.comp continuous_toAdd)).congr fun v ↦ (hEuv v).symm)
  have hEH (v : Multiplicative 𝕂) : Eu v ∈ a.val.1 := by
    have hcl : IsClopen (a.val.1 : Set w.Completionˣ) :=
      ⟨a.val.1.isClosed_of_isOpen a.property.1, a.property.1⟩
    have : PreconnectedSpace (Multiplicative 𝕂) := inferInstanceAs (PreconnectedSpace 𝕂)
    exact (isPreconnected_range hEu).subset_isClopen hcl ⟨1, ⟨1, map_one Eu⟩, a.val.1.one_mem⟩
      ⟨v, rfl⟩
  obtain ⟨θ, hθc, hθv⟩ : ∃ θ : 𝕂 →+ ElementaryLieGroup e.realDim e.torusDim e.latticeRank
      e.finiteFactor, Continuous θ ∧ ∀ v, Multiplicative.ofAdd (θ v) =
        e.equiv (QuotientGroup.mk ⟨Eu (Multiplicative.ofAdd v), hEH _⟩) := by
    let θm : Multiplicative 𝕂 →* Multiplicative
        (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
      e.equiv.toMulEquiv.toMonoidHom.comp ((QuotientGroup.mk' _).comp (Eu.codRestrict _ hEH))
    have hθm : Continuous θm := e.equiv.continuous.comp (QuotientGroup.continuous_mk.comp
      (hEu.subtype_mk _))
    exact ⟨AddMonoidHom.toMultiplicative.symm θm, hθm, fun _ ↦ rfl⟩
  have hc := weilTest_elementary_curve L e f₀ (hsm e) θ hθc (QuotientGroup.mk ⟨u₀, hu₀⟩)
  have heq (v : 𝕂) : Function.extend Units.val f (fun _ ↦ (0 : ℂ))
      ((u₀ : w.Completion) * φ.symm (E v)) =
      f₀ (e.equiv.symm (e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩) *
        Multiplicative.ofAdd (θ v))) := by
    have hmem : u₀ * Eu (Multiplicative.ofAdd v) ∈ a.val.1 := mul_mem hu₀ (hEH _)
    have hval : (u₀ : w.Completion) * φ.symm (E v) = ((u₀ * Eu (Multiplicative.ofAdd v) :
        w.Completionˣ) : w.Completion) := by
      rw [Units.val_mul, hEuv, toAdd_ofAdd]
    have hmul : e.equiv (QuotientGroup.mk ⟨u₀ * Eu (Multiplicative.ofAdd v), hmem⟩) =
        e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩) * Multiplicative.ofAdd (θ v) :=
      calc e.equiv (QuotientGroup.mk ⟨u₀ * Eu (Multiplicative.ofAdd v), hmem⟩)
          = e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩ *
              QuotientGroup.mk ⟨Eu (Multiplicative.ofAdd v), hEH _⟩) := rfl
        _ = e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩) *
              e.equiv (QuotientGroup.mk ⟨Eu (Multiplicative.ofAdd v), hEH _⟩) :=
            map_mul e.equiv _ _
        _ = _ := congrArg (e.equiv (QuotientGroup.mk ⟨u₀, hu₀⟩) * ·) (hθv v).symm
    calc Function.extend Units.val f (fun _ ↦ (0 : ℂ)) ((u₀ : w.Completion) * φ.symm (E v))
        = Function.extend Units.val f (fun _ ↦ (0 : ℂ))
            ((u₀ * Eu (Multiplicative.ofAdd v) : w.Completionˣ) : w.Completion) :=
          congrArg _ hval
      _ = f (u₀ * Eu (Multiplicative.ofAdd v)) := Units.val_injective.extend_apply _ _ _
      _ = f₀ (QuotientGroup.mk ⟨_, hmem⟩) := (hf₀ ⟨_, hmem⟩).symm
      _ = _ := congrArg f₀ ((e.equiv.symm_apply_eq.mpr hmul.symm).symm)
  simp_rw [heq]
  exact hc

/-- A Bruhat smooth function on the units of an archimedean completion, extended by
zero, is smooth at every nonzero point in a real coordinate. -/
private theorem weilTest_source_contDiffAt (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφs : Continuous φ.symm)
    {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0)
    (f : w.Completionˣ → ℂ) (hf : IsBruhatSmooth f)
    (y₀ : 𝕂) (hy₀ : y₀ ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : 𝕂 ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ)) (φ.symm y)) y₀ := by
  rw [contDiffAt_infty]
  intro n
  obtain ⟨u₀, hu₀v⟩ : ∃ u : w.Completionˣ, (u : w.Completion) = φ.symm y₀ :=
    ⟨Units.mk0 _ ((map_ne_zero φ.symm).mpr hy₀), rfl⟩
  have hcurve := weilTest_units_curve w φ hφs L E hEadd hE0 hE00 hEs.continuous f hf u₀ n
  -- A local logarithm straightens the exponential curve near `y₀`.
  obtain ⟨Λ, hΛ, hright⟩ := weilTest_localLog E hE00 hEs hEd
  have hdiv : ContDiff ℝ (⊤ : ℕ∞) (fun y : 𝕂 ↦ y * y₀⁻¹) := contDiff_id.mul contDiff_const
  have hlim : Tendsto (fun y : 𝕂 ↦ y * y₀⁻¹) (𝓝 y₀) (𝓝 1) := by
    have := hdiv.continuous.tendsto y₀
    rwa [mul_inv_cancel₀ hy₀] at this
  have hle : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have hloc : ContDiffAt ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun y ↦ Function.extend Units.val f
      (fun _ ↦ (0 : ℂ)) ((u₀ : w.Completion) * φ.symm (E (Λ (y * y₀⁻¹))))) y₀ := by
    have hΛ' : ContDiffAt ℝ ((n : ℕ∞) : WithTop ℕ∞) Λ (y₀ * y₀⁻¹) := by
      rw [mul_inv_cancel₀ hy₀]
      exact hΛ.of_le hle
    exact hcurve.contDiffAt.comp y₀ (hΛ'.comp y₀ (hdiv.contDiffAt.of_le hle))
  refine hloc.congr_of_eventuallyEq ?_
  filter_upwards [hlim.eventually hright] with y hy
  rw [hu₀v, hy, ← map_mul, mul_left_comm, mul_inv_cancel₀ hy₀, mul_one]

/-- The weighted translate of a test on the units is smooth with compact support in a
real coordinate on the completion. -/
private theorem weilTest_target_contDiff (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφ : Continuous φ) (hφs : Continuous φ.symm)
    (hnorm : ∀ x, ‖φ x‖ = ‖x‖) {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0)
    (m : ℕ) (hW : ∀ z : 𝕂, z ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z : 𝕂 ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)) z)
    (f : w.Completionˣ → ℂ) (hf : IsBruhatSmooth f) (hfc : HasCompactSupport f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : 𝕂 ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ))
        (1 + φ.symm y) / ((Real.sqrt (‖1 + φ.symm y‖ ^ m) : ℝ) : ℂ)) ∧
      HasCompactSupport (fun y : 𝕂 ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ))
        (1 + φ.symm y) / ((Real.sqrt (‖1 + φ.symm y‖ ^ m) : ℝ) : ℂ)) := by
  let h : 𝕂 → ℂ := fun y ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ)) (φ.symm y)
  let W : 𝕂 → ℂ := fun z ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)
  have hns (z : 𝕂) : ‖φ.symm z‖ = ‖z‖ := by rw [← hnorm, RingEquiv.apply_symm_apply]
  have hfun : (fun y : 𝕂 ↦ Function.extend Units.val f (fun _ ↦ (0 : ℂ))
      (1 + φ.symm y) / ((Real.sqrt (‖1 + φ.symm y‖ ^ m) : ℝ) : ℂ)) =
      fun y ↦ h (1 + y) / W (1 + y) := by
    funext y
    have h1 : 1 + φ.symm y = φ.symm (1 + y) := by rw [map_add, map_one]
    simp only [h, W, h1, hns]
  rw [hfun]
  let Z : Set 𝕂 := φ '' (Units.val '' tsupport f)
  have hZ : IsCompact Z := (hfc.image Units.continuous_val).image hφ
  have hzero (z : 𝕂) (hz : z ∉ Z) : h z = 0 := by
    simp only [h]
    rw [weilTest_zeroExtend_apply]
    split_ifs with h0
    · rfl
    · refine image_eq_zero_of_notMem_tsupport fun hm ↦ hz ⟨_, ⟨_, hm, rfl⟩, ?_⟩
      simp
  have hWne (z : 𝕂) (hz : z ≠ 0) : W z ≠ 0 := by
    simp only [W, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (pow_pos (norm_pos_iff.mpr hz) m)).ne'
  have h0Z : (0 : 𝕂) ∉ Z := by
    rintro ⟨_, ⟨u, -, rfl⟩, hu⟩
    exact u.ne_zero ((map_eq_zero_iff φ φ.injective).mp hu)
  have htr : Continuous (fun y : 𝕂 ↦ 1 + y) := continuous_const.add continuous_id
  refine ⟨contDiff_iff_contDiffAt.mpr fun y ↦ ?_, ?_⟩
  · by_cases hy : 1 + y ∈ Z
    · have hy0 : 1 + y ≠ 0 := fun h ↦ h0Z (h ▸ hy)
      have hs := weilTest_source_contDiffAt w φ hφs L E hEadd hE0 hE00 hEs hEd f
        hf (1 + y) hy0
      have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : 𝕂 ↦ 1 + y) y := contDiffAt_const.add contDiffAt_id
      have hs' : ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ h (1 + y)) y := hs.comp y hc
      have hW' : ContDiffAt ℝ (⊤ : ℕ∞) (fun y ↦ W (1 + y)) y := (hW (1 + y) hy0).comp y hc
      convert hs'.mul (hW'.inv (hWne _ hy0)) using 1
      funext y
      simp [div_eq_mul_inv]
    · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [(htr.tendsto y).eventually (hZ.isClosed.isOpen_compl.mem_nhds hy)]
        with y' hy'
      simp [hzero _ hy']
  · refine HasCompactSupport.intro (hZ.image (continuous_id.sub
      (continuous_const (y := (1 : 𝕂))))) fun y hy ↦ ?_
    have : 1 + y ∉ Z := fun h ↦ hy ⟨1 + y, h, by simp⟩
    simp [hzero _ this]


/-- The weighted translate is additive in the test. -/
private theorem weilTest_weighted_add (w : InfinitePlace F) (m : ℕ)
    (f f' : BruhatCompactSupport w.Completionˣ) (x : w.Completion) :
    Function.extend Units.val ((f + f').val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
        ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) =
      Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
          ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) +
        Function.extend Units.val (f'.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
          ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) := by
  simp only [weilTest_zeroExtend_apply]
  by_cases h0 : 1 + x = 0
  · simp only [h0, dite_true, zero_div, add_zero]
  · simp only [h0, dite_false]
    have hadd : (f + f').val (Units.mk0 (1 + x) h0) =
        f.val (Units.mk0 (1 + x) h0) + f'.val (Units.mk0 (1 + x) h0) := rfl
    exact (congrArg (· / ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ)) hadd).trans (add_div _ _ _)

/-- The weighted translate is homogeneous in the test. -/
private theorem weilTest_weighted_smul (w : InfinitePlace F) (m : ℕ) (c : ℂ)
    (f : BruhatCompactSupport w.Completionˣ) (x : w.Completion) :
    Function.extend Units.val ((c • f).val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
        ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) =
      c * (Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ)) (1 + x) /
          ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ)) := by
  simp only [weilTest_zeroExtend_apply]
  by_cases h0 : 1 + x = 0
  · simp only [h0, dite_true, zero_div, mul_zero]
  · simp only [h0, dite_false]
    have hsmul : (c • f).val (Units.mk0 (1 + x) h0) = c * f.val (Units.mk0 (1 + x) h0) := rfl
    exact (congrArg (· / ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ)) hsmul).trans (mul_div_assoc _ _ _)

/-- The weighted translate, read in real coordinates, defines a linear map into the
elementary Schwartz space of the real vector group. -/
private theorem weilTest_exists_linear (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφ : Continuous φ) (hφs : Continuous φ.symm)
    (hnorm : ∀ x, ‖φ x‖ = ‖x‖) {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0)
    (m : ℕ) (hW : ∀ z : 𝕂, z ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z : 𝕂 ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)) z) :
    ∃ T : BruhatCompactSupport w.Completionˣ →ₗ[ℂ] ElementarySchwartz d 0 0 PUnit.{1},
      ∀ f g, T f g = Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ))
        (1 + φ.symm (L.symm g.1)) / ((Real.sqrt (‖1 + φ.symm (L.symm g.1)‖ ^ m) : ℝ) : ℂ) := by
  have hψ (f : BruhatCompactSupport w.Completionˣ) :=
    weilTest_target_contDiff w φ hφ hφs hnorm L E hEadd hE0 hE00 hEs hEd m hW
      f.val ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1) f.property.2
  have hψ' (f : BruhatCompactSupport w.Completionˣ) :=
    And.intro ((hψ f).1.comp L.symm.contDiff)
      ((hψ f).2.comp_isClosedEmbedding L.symm.toHomeomorph.isClosedEmbedding)
  let toY (f : BruhatCompactSupport w.Completionˣ) : ElementarySchwartz d 0 0 PUnit.{1} :=
    ⟨fun g ↦ (hψ' f).2.toSchwartzMap (hψ' f).1 g.1,
      (elementarySchwartzSubmodule_real_iff _).mpr ⟨(hψ' f).2.toSchwartzMap (hψ' f).1, rfl⟩⟩
  refine ⟨{ toFun := toY
            map_add' := fun f f' ↦ Subtype.ext (funext fun g ↦
              weilTest_weighted_add w m f f' (φ.symm (L.symm g.1)))
            map_smul' := fun c f ↦ Subtype.ext (funext fun g ↦
              weilTest_weighted_smul w m c f (φ.symm (L.symm g.1))) }, fun f g ↦ rfl⟩


/-- Elementary Schwartz functions with the same values are equal. -/
private theorem weilTest_elementarySchwartz_ext {d : ℕ}
    {s t : ElementarySchwartz d 0 0 PUnit.{1}} (h : ∀ g, s g = t g) : s = t :=
  Subtype.ext (funext h)

/-- Evaluation of elementary Schwartz functions on the real vector group is continuous. -/
private theorem weilTest_elementarySchwartz_eval {d : ℕ} (g : ElementaryLieGroup d 0 0 PUnit.{1}) :
    Continuous (fun t : ElementarySchwartz d 0 0 PUnit.{1} ↦ t g) := by
  obtain ⟨Lg, hLg⟩ := elementarySchwartz_eval_continuousLinear (d := d) (t := 0) (r := 0)
    (F := PUnit.{1}) g
  exact Lg.continuous.congr hLg

/-- On a fixed-support stage, the weighted translate is continuous by the closed graph
theorem. -/
private theorem weilTest_stage_continuous (w : InfinitePlace F) {d : ℕ} (m : ℕ)
    (ρ : ElementaryLieGroup d 0 0 PUnit.{1} → w.Completion)
    (T : BruhatCompactSupport w.Completionˣ →ₗ[ℂ] ElementarySchwartz d 0 0 PUnit.{1})
    (hT : ∀ f g, T f g = Function.extend Units.val (f.val : w.Completionˣ → ℂ)
      (fun _ ↦ (0 : ℂ)) (1 + ρ g) / ((Real.sqrt (‖1 + ρ g‖ ^ m) : ℝ) : ℂ))
    (a : BruhatStructuralPair w.Completionˣ) (e : ElementaryLCAPresentation a.quotient)
    (C : TopologicalSpace.Compacts w.Completionˣ) :
    Continuous (T ∘ bruhatCompactSupportStageInclusion a e C) := by
  let G := w.Completionˣ
  let Y := ElementarySchwartz d 0 0 PUnit.{1}
  let X := bruhatCompactSupportStage a e C
  let i : X →ₗ[ℂ] bruhatCompactSupportSubmodule G := bruhatCompactSupportStageInclusion a e C
  let J : SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G := schwartzBruhatStageInclusion a e
  have hJ : Continuous J :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ (fun p ↦ p.2 a e)
  have hev (x : G) :
      Continuous (fun s : SchwartzBruhatStage e ↦ schwartzBruhatStageRealization a e s x) :=
    (continuous_schwartzBruhat_eval_forEndpoints x).comp hJ
  have hX : IsClosed (X : Set (SchwartzBruhatStage e)) := by
    simp only [X, bruhatCompactSupportStage, Submodule.coe_iInf]
    exact isClosed_iInter fun x ↦ isClosed_singleton.preimage (hev x.val)
  let T' : X →ₗ[ℂ] Y := T.comp i
  have hval (z : w.Completion) : Continuous (fun s : X ↦ Function.extend Units.val
      ((i s : BruhatCompactSupport G).val : G → ℂ) (fun _ ↦ (0 : ℂ)) z) := by
    simp only [weilTest_zeroExtend_apply]
    by_cases h0 : z = 0
    · simp only [h0, dite_true]
      exact continuous_const
    · simp only [h0, dite_false]
      exact (hev _).comp continuous_subtype_val
  have hgraph : IsClosed (T'.graph : Set (X × Y)) := by
    have heq : (T'.graph : Set (X × Y)) = ⋂ g : ElementaryLieGroup d 0 0 PUnit.{1},
        {p | p.2 g = Function.extend Units.val ((i p.1 : BruhatCompactSupport G).val : G → ℂ)
          (fun _ ↦ (0 : ℂ)) (1 + ρ g) / ((Real.sqrt (‖1 + ρ g‖ ^ m) : ℝ) : ℂ)} := by
      ext p
      refine ⟨fun h ↦ mem_iInter.mpr fun g ↦ ?_, fun h ↦ ?_⟩
      · have h' : p.2 = T' p.1 := (LinearMap.mem_graph_iff _ _).mp h
        exact (congrArg (fun t : Y ↦ t g) h').trans (hT _ g)
      · have hfun : ∀ g, p.2 g = T' p.1 g := fun g ↦ (mem_iInter.mp h g).trans (hT (i p.1) g).symm
        exact (LinearMap.mem_graph_iff _ _).mpr (weilTest_elementarySchwartz_ext hfun)
    have hc : IsClosed (⋂ g : ElementaryLieGroup d 0 0 PUnit.{1},
        {p : X × Y | p.2 g = Function.extend Units.val
          ((i p.1 : BruhatCompactSupport G).val : G → ℂ)
          (fun _ ↦ (0 : ℂ)) (1 + ρ g) / ((Real.sqrt (‖1 + ρ g‖ ^ m) : ℝ) : ℂ)}) := by
      refine isClosed_iInter fun g ↦ isClosed_eq ?_
        (((hval _).div_const _).comp continuous_fst)
      exact (weilTest_elementarySchwartz_eval g).comp continuous_snd
    exact (congrArg IsClosed heq).mpr hc
  have : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
  exact weilTest_continuous_of_isClosed_graph elementarySchwartz_isFrechet
    elementarySchwartz_isFrechet X hX T' hgraph

/-- A linear map from tests on the units to an elementary Schwartz space is continuous
when each value is the weighted translate at a point given by a fixed function. -/
private theorem weilTest_continuous_linear (w : InfinitePlace F) {d : ℕ} (m : ℕ)
    (ρ : ElementaryLieGroup d 0 0 PUnit.{1} → w.Completion)
    (T : BruhatCompactSupport w.Completionˣ →ₗ[ℂ] ElementarySchwartz d 0 0 PUnit.{1})
    (hT : ∀ f g, T f g = Function.extend Units.val (f.val : w.Completionˣ → ℂ)
      (fun _ ↦ (0 : ℂ)) (1 + ρ g) / ((Real.sqrt (‖1 + ρ g‖ ^ m) : ℝ) : ℂ)) :
    Continuous T := by
  let G := w.Completionˣ
  let Y := ElementarySchwartz d 0 0 PUnit.{1}
  have hstage := weilTest_stage_continuous w m ρ T hT
  refine (elementarySchwartz_withSeminorms (m := d) (n := 0) (r := 0)
    (F := PUnit.{1})).continuous_of_continuous_comp T fun j ↦ ?_
  let P := {q : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (C : TopologicalSpace.Compacts G),
      Continuous (q ∘ bruhatCompactSupportStageInclusion a e C)}
  exact (withGeneratingSeminorms_spec _ (Subtype.val : P → _)).continuous_seminorm
    (⟨(elementarySchwartzSeminorm j).comp T, fun a e C ↦
      (elementarySchwartz_withSeminorms.continuous_seminorm j).comp (hstage a e C)⟩ : P)


/-- In real coordinates on an archimedean completion, translation of the zero-extended
test after weighting is a continuous linear map to additive Schwartz–Bruhat tests. -/
private theorem weilTest_exists_map (w : InfinitePlace F) {𝕂 : Type*} [RCLike 𝕂]
    (φ : w.Completion ≃+* 𝕂) (hφ : Continuous φ) (hφs : Continuous φ.symm)
    (hnorm : ∀ x, ‖φ x‖ = ‖x‖) {d : ℕ} (L : 𝕂 ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (E : 𝕂 → 𝕂) (hEadd : ∀ a b, E (a + b) = E a * E b) (hE0 : ∀ a, E a ≠ 0) (hE00 : E 0 = 1)
    (hEs : ContDiff ℝ (⊤ : ℕ∞) E)
    (hEd : HasFDerivAt E ((ContinuousLinearEquiv.refl ℝ 𝕂 : 𝕂 ≃L[ℝ] 𝕂) : 𝕂 →L[ℝ] 𝕂) 0)
    (m : ℕ) (hW : ∀ z : 𝕂, z ≠ 0 →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z : 𝕂 ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)) z) :
    ∃ A : BruhatCompactSupport w.Completionˣ →L[ℂ]
        SchwartzBruhat (Multiplicative w.Completion),
      ∀ (f : BruhatCompactSupport w.Completionˣ) (x : w.Completion),
        A f (Multiplicative.ofAdd x) = Function.extend Units.val (f.val : w.Completionˣ → ℂ)
          (fun _ ↦ (0 : ℂ)) (1 + x) / ((Real.sqrt (‖1 + x‖ ^ m) : ℝ) : ℂ) := by
  have hex := weilTest_exists_linear w φ hφ hφs hnorm L E hEadd hE0 hE00 hEs hEd m hW
  refine hex.elim fun T hT ↦ ?_
  have hTc := weilTest_continuous_linear w m (fun g ↦ φ.symm (L.symm g.1)) T hT
  -- The completion is presented by its real coordinates.
  let c₀ : w.Completion ≃ₜ EuclideanSpace ℝ (Fin d) :=
    (Homeomorph.mk φ.toEquiv hφ hφs).trans L.toHomeomorph
  let c : Multiplicative w.Completion ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin d)) :=
    ContinuousMulEquiv.mk' c₀ (fun x y ↦ by
      change L (φ (x.toAdd + y.toAdd)) = L (φ x.toAdd) + L (φ y.toAdd)
      rw [map_add, map_add])
  refine (weilTest_vectorPresentation c).elim fun a₁ h₁ ↦ h₁.elim fun hm₁ h₂ ↦
    h₂.elim fun w₁ hw₁ ↦ ?_
  let e₁ : ElementaryLCAPresentation a₁.quotient := ⟨d, 0, 0, PUnit, w₁⟩
  let J₁ : SchwartzBruhatStage e₁ →ₗ[ℂ] SchwartzBruhat (Multiplicative w.Completion) :=
    schwartzBruhatStageInclusion a₁ e₁
  have hJ₁ : Continuous J₁ :=
    (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp _ (fun p ↦ p.2 a₁ e₁)
  refine ⟨⟨J₁.comp T, hJ₁.comp hTc⟩, fun f x ↦ ?_⟩
  change (show SchwartzBruhat (Multiplicative w.Completion) from
    schwartzBruhatStageInclusion a₁ e₁ (T f)) (Multiplicative.ofAdd x) = _
  rw [schwartzBruhatStageInclusion_apply, schwartzBruhatStageRealization_apply,
    dite_eq_left (hm₁ _)]
  refine (hT f _).trans ?_
  have hx : (w₁ (QuotientGroup.mk ⟨Multiplicative.ofAdd x, hm₁ _⟩)).toAdd.1 = L (φ x) :=
    hw₁ (Multiplicative.ofAdd x)
  change Function.extend Units.val (f.val : w.Completionˣ → ℂ) (fun _ ↦ (0 : ℂ))
      (1 + φ.symm (L.symm (w₁ (QuotientGroup.mk ⟨Multiplicative.ofAdd x, hm₁ _⟩)).toAdd.1)) /
        ((Real.sqrt (‖1 + φ.symm (L.symm
          (w₁ (QuotientGroup.mk ⟨Multiplicative.ofAdd x, hm₁ _⟩)).toAdd.1)‖ ^ m) : ℝ) : ℂ) = _
  rw [hx, L.symm_apply_apply, RingEquiv.symm_apply_apply]


/-- The inverse square-root weight is smooth away from zero. -/
private theorem weilTest_weight_contDiffAt {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (m : ℕ) (z : V) (hz : z ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : V ↦ ((Real.sqrt (‖z‖ ^ m) : ℝ) : ℂ)) z := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : V ↦ ‖z‖ ^ m) z := (contDiffAt_norm ℝ hz).pow m
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : V ↦ Real.sqrt (‖z‖ ^ m)) z :=
    (Real.contDiffAt_sqrt (pow_ne_zero m (norm_ne_zero_iff.mpr hz))).comp z h1
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp z h2

/-- Paper: Definition B.4.4.1(2), p. 620. The weighted translate of a
multiplicative test at an infinite place is an additive test, continuously in the original test. -/
theorem exists_infiniteWeilTestMap (w : InfinitePlace F) :
    ∃ A : 𝒟(w.Completionˣ) →L[ℂ] 𝒮ₐ(w.Completion),
      ∀ (f : 𝒟(w.Completionˣ)) (x : w.Completion),
        addTest(A f) x = weightedTranslate((fun y : w.Completion ↦ ‖y‖ ^ w.mult), f.val) x := by
  by_cases hw : w.IsReal
  · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let L : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
      (LinearEquiv.ofFinrankEq ℝ (EuclideanSpace ℝ (Fin 1)) (by simp)).toContinuousLinearEquiv
    have hEd : HasFDerivAt Real.exp
        ((ContinuousLinearEquiv.refl ℝ ℝ : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) 0 :=
      (Real.hasDerivAt_exp 0).hasFDerivAt.congr_fderiv (by ext; simp)
    have hex := weilTest_exists_map w (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      e.continuous e.symm.continuous (fun x ↦ e.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw)) x) L
      Real.exp Real.exp_add (fun a ↦ (Real.exp_pos a).ne') Real.exp_zero Real.contDiff_exp hEd
      w.mult (weilTest_weight_contDiffAt w.mult)
    exact hex.elim fun A hA ↦ ⟨A, fun f x ↦ hA f x⟩
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc
    let L : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      (LinearEquiv.ofFinrankEq ℂ (EuclideanSpace ℝ (Fin 2)) (by simp)).toContinuousLinearEquiv
    have hEd : HasFDerivAt Complex.exp
        ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) 0 :=
      (Complex.hasDerivAt_exp 0).complexToReal_fderiv.congr_fderiv (by ext; simp)
    have hex := weilTest_exists_map w (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)
      e.continuous e.symm.continuous (fun x ↦ e.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)) x) L
      Complex.exp Complex.exp_add Complex.exp_ne_zero Complex.exp_zero
      (Complex.contDiff_exp (𝕜 := ℝ)) hEd w.mult (weilTest_weight_contDiffAt w.mult)
    exact hex.elim fun A hA ↦ ⟨A, fun f x ↦ hA f x⟩

/-- Paper: Definition B.4.4.1(2), p. 620. The finite multiplicative
principal value applies Connes's functional to the weighted translated test.
Deviation: The multiplier parametrizes the additive character used by Lemma B.4.4.4. -/
def finiteConnesWeilPrincipalValue (v : Primes(F)) (a : (v.adicCompletion F)ˣ) :
    StrongDual ℂ (𝒟((v.adicCompletion F)ˣ)) :=
  (finiteConnesPrincipalValue v a).comp (exists_finiteWeilTestMap v).choose

/-- Paper: Definition B.4.4.1(2), p. 620. The infinite multiplicative
principal value applies Connes's functional to the weighted translated test. -/
def infiniteConnesWeilPrincipalValue (w : InfinitePlace F) :
    StrongDual ℂ (𝒟(w.Completionˣ)) :=
  (infiniteConnesPrincipalValue w).comp (exists_infiniteWeilTestMap w).choose

/-- Paper: Definition B.4.4.1(2), p. 620. At a real place a test vanishing
at one has its principal value given by the canonical ordinary integral. -/
theorem realConnesWeilPrincipalValue_of_apply_one_zero (w : InfinitePlace F)
    (_hw : w.IsReal) (f : 𝒟(w.Completionˣ)) (_hf : f.val 1 = 0) :
    let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
    (infiniteConnesWeilPrincipalValue w) f =
      (1 / 2 : ℂ) * ∫ u : w.Completionˣ,
        f.val u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ) ∂μ := by
  intro μ
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let r := InfinitePlace.Completion.ringEquivRealOfIsReal _hw
  let e := InfinitePlace.Completion.isometryEquivRealOfIsReal _hw
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hA := (exists_infiniteWeilTestMap w).choose_spec f
  have hmult : w.mult = 1 := by simp [InfinitePlace.mult, _hw]
  let Fz : w.Completion → ℂ := Function.extend Units.val (f.val : _ → ℂ) (fun _ ↦ 0)
  have hFu (u : w.Completionˣ) : Fz u.val = f.val u := Units.val_injective.extend_apply _ _ u
  have hFz (y : w.Completion) (hy : y ∉ range (Units.val : w.Completionˣ → w.Completion)) :
      Fz y = 0 := by
    simp only [Fz, Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ ↦ hy ⟨u, hu⟩)]
  have h0 : addTest((exists_infiniteWeilTestMap w).choose f) 0 = 0 := by
    rw [hA]
    change Fz (1 + 0) / _ = 0
    rw [add_zero, ← Units.val_one, hFu, _hf, zero_div]
  change infiniteConnesPrincipalValue w ((exists_infiniteWeilTestMap w).choose f) = _
  rw [realConnesPrincipalValue_of_apply_zero w _hw _ h0]
  congr 1
  let G : w.Completion → ℂ := fun y ↦ Fz y / (Real.sqrt ‖y‖ : ℂ) / ((‖y - 1‖ : ℝ) : ℂ)
  -- Translation invariance moves the singularity from zero to one.
  have htr : ∫ x, addTest((exists_infiniteWeilTestMap w).choose f) x / ((‖x‖ : ℝ) : ℂ) ∂ν∞(w) =
      ∫ y, G y ∂ν∞(w) := by
    have hG : (fun x ↦ addTest((exists_infiniteWeilTestMap w).choose f) x / ((‖x‖ : ℝ) : ℂ)) =
        fun x ↦ G (1 + x) := by
      funext x
      rw [hA]
      change Fz (1 + x) / ((Real.sqrt (‖1 + x‖ ^ w.mult) : ℂ)) / _ =
        Fz (1 + x) / (Real.sqrt ‖1 + x‖ : ℂ) / ((‖1 + x - 1‖ : ℝ) : ℂ)
      rw [hmult, pow_one, add_sub_cancel_left]
    rw [hG, infiniteLocalAdditiveTamagawaMeasure, dite_eq_left _hw]
    let m := e.symm.toHomeomorph.toMeasurableEquiv
    rw [show (r.symm : ℝ → w.Completion) = m from rfl, integral_map_equiv, integral_map_equiv]
    have hm (t : ℝ) : 1 + m t = m (1 + t) := by
      change 1 + r.symm t = r.symm (1 + t)
      rw [map_add, map_one]
    simp_rw [hm]
    exact integral_add_left_eq_self (fun t ↦ G (m t)) 1
  rw [htr]
  -- The multiplicative measure is the additive one with density `1 / ‖y‖` on units.
  let d : w.Completion → ENNReal := fun x ↦ (↑(‖x‖₊ ^ w.mult) : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  simp only [← hFu]
  change _ = ∫ u, _ ∂(ν∞(w).withDensity d).comap Units.val
  rw [← hval.integral_map (g := fun y ↦ Fz y * (Real.sqrt ‖y‖ : ℂ) / ((‖1 - y‖ : ℝ) : ℂ)),
    hval.map_comap, setIntegral_withDensity_eq_setIntegral_toReal_smul hd ?_ _
      hval.measurableSet_range,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range Units.val)
      (fun y hy ↦ by simp only [G, hFz y hy, zero_div])]
  · refine setIntegral_congr_fun hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr (hu ▸ u.ne_zero)
    simp only [G, d, hmult, pow_one]
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm, Complex.real_smul, norm_sub_rev]
    have hs : (Real.sqrt ‖y‖ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
    have hsq : (‖y‖ : ℂ) = (Real.sqrt ‖y‖ : ℂ) * (Real.sqrt ‖y‖ : ℂ) := by
      exact_mod_cast (Real.mul_self_sqrt hn.le).symm
    push_cast
    rw [hsq]
    field_simp
  · refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    simp only [d, hmult, pow_one]
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])

local notation "finiteWeilIntegrand(" v ", " f ")" =>
  (fun u : (HeightOneSpectrum.adicCompletion F v)ˣ ↦
    f u * (Real.sqrt ‖u.val‖ : ℂ) / ((‖1 - u.val‖ : ℝ) : ℂ))

/-- Paper: Remark B.4.4.2, p. 620. For the finite local norm the canonical
multiplicative Haar measure gives an integer-unit shell mass equal to the log prime norm. -/
theorem finiteCanonicalHaar_eq_smul_tamagawa (v : Primes(F)) :
    letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
    letI : SecondCountableTopology (v.adicCompletion F)ˣ :=
      (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).secondCountableTopology
    letI : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
    let m : (v.adicCompletion F)ˣ →ₜ* ℝ≥0ˣ :=
      ⟨Units.map nnNormHom.toMonoidHom, continuous_finiteLocalModule v⟩
    ∃ hm : IsModulation m, canonicalModulatedHaar m hm =
      ENNReal.ofReal (Real.log q(v) / V𝔭(v)) • μ𝔭(v) := by
  classical
  intro m
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : SecondCountableTopology Kˣ := (Units.isEmbedding_val₀ (G₀ := K)).secondCountableTopology
  let : BorelSpace Kˣ := ⟨rfl⟩
  let q : ℝ≥0ˣ := Units.mk0 (v.asIdeal.absNorm : ℝ≥0)
    (by exact_mod_cast (zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v)).ne')
  have hq : 1 < (q.val : ℝ) := by
    change 1 < (v.asIdeal.absNorm : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  let val : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let p : Kˣ := Units.mk0 (π : K) hπ.ne_zero
  have hp : ‖p.val‖ = q(v)⁻¹ := norm_uniformizer_adicCompletion v _ hπ
  have hgen : m p⁻¹ = q := by
    apply Units.ext
    apply NNReal.eq
    change ‖(p⁻¹).val‖ = q(v)
    rw [Units.val_inv_eq_inv_val, norm_inv, hp, inv_inv]
  have hm : IsModulation m := by
    constructor
    · change IsProperMap (Units.map nnNormHom.toMonoidHom : Kˣ →* ℝ≥0ˣ)
      have h := isProperMap_units_nnNorm_pow (K := K) 1 one_ne_zero
      simpa only [MonoidHom.pow_apply, pow_one] using h
    · refine ⟨p⁻¹, fun he ↦ hq.ne' ?_⟩
      exact congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (hgen.symm.trans he)
  -- The inverse uniformizer generates the range of the normalized absolute value.
  have hrange : m.toMonoidHom.range = Subgroup.zpowers q := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      refine Subgroup.mem_zpowers_iff.mpr ⟨WithZero.log (Valued.v u.val), ?_⟩
      apply Units.ext
      apply NNReal.eq
      change (((q ^ _).val : ℝ≥0) : ℝ) = ‖u.val‖
      rw [Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, FinitePlace.norm_def,
        WithZeroMulInt.toNNReal_neg_apply _ (Valued.v.ne_zero_iff.mpr u.ne_zero)]
      simp [q]
    · exact Subgroup.zpowers_le.mpr ⟨p⁻¹, hgen⟩
  have hker : (m.toMonoidHom.ker : Set Kˣ) = (O(v)).units := by
    ext u
    change m u = 1 ↔ u ∈ (O(v)).units
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      ← Valued.toNormedField.norm_eq_one_iff, ← Units.val_inj, ← NNReal.coe_inj]
    rfl
  let : (μ𝔭(v)).IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar F v
  refine ⟨hm, (existsUnique_canonicalModulatedHaar m hm).unique
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists) ?_⟩
  have hqval : (q.val : ℝ) = q(v) := by simp [q]
  simpa only [hker, hqval] using haar_logGrowth_of_cyclic_range m hm hq hrange μ𝔭(v)

/-- Paper: Remark B.4.4.2, p. 620. For the infinite local module, dividing
Tamagawa measure by two at a real place or by two pi at a complex place gives canonical Haar measure. -/
theorem infiniteCanonicalHaar_eq_smul_tamagawa (w : InfinitePlace F) :
    letI : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    letI : SecondCountableTopology w.Completionˣ :=
      (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
    letI : BorelSpace w.Completion := ⟨rfl⟩
    letI : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
    let m : w.Completionˣ →ₜ* ℝ≥0ˣ :=
      ⟨(Units.map nnNormHom.toMonoidHom) ^ w.mult, continuous_infiniteLocalModule w⟩
    ∃ hm : IsModulation m, canonicalModulatedHaar m hm =
      ENNReal.ofReal ((if w.IsReal then 2 else 2 * Real.pi)⁻¹) •
        infiniteLocalMultiplicativeTamagawaMeasure F w := by
  intro m
  let : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology w.Completionˣ :=
    (Units.isEmbedding_val₀ (G₀ := w.Completion)).secondCountableTopology
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : BorelSpace w.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let μ := infiniteLocalMultiplicativeTamagawaMeasure F w
  let : μ.IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_haar F w
  have hi := InfinitePlace.Completion.isometry_extensionEmbedding w
  let : ProperSpace w.Completion :=
    LipschitzWith.properSpace hi.isClosedEmbedding.isProperMap hi.lipschitzWith
  have h2 : ‖(2 : w.Completion)‖ = 2 := by
    rw [← hi.norm_map_of_map_zero (map_zero _) (2 : w.Completion), map_ofNat]
    norm_num
  have hmval (g : w.Completionˣ) : ((m g).val : ℝ) = ‖g.val‖ ^ w.mult := by
    change (((Units.map nnNormHom.toMonoidHom g) ^ w.mult : ℝ≥0ˣ).val : ℝ) = _
    rw [Units.val_pow_eq_pow_val, NNReal.coe_pow]
    rfl
  have hm : IsModulation m := by
    refine ⟨isProperMap_units_nnNorm_pow w.mult w.mult_ne_zero, ⟨Units.mk0 2 (by rw [← norm_ne_zero_iff, h2]; norm_num), ?_⟩⟩
    intro h
    have h2' := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
    simp only [hmval, Units.val_one, NNReal.coe_one] at h2'
    rw [Units.val_mk0, h2] at h2'
    exact absurd ((pow_eq_one_iff_of_nonneg zero_le_two w.mult_ne_zero).mp h2') (by norm_num)
  let c : ℝ := if w.IsReal then 2 else 2 * Real.pi
  have hc : 0 < c := by unfold c; split_ifs <;> positivity
  refine ⟨hm, (existsUnique_canonicalModulatedHaar m hm).unique
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists)
    ⟨Measure.IsHaarMeasure.smul _ (ENNReal.ofReal_pos.mpr (inv_pos.mpr hc)).ne'
      ENNReal.ofReal_ne_top, ?_⟩⟩
  refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with Λ hΛ
  let S : Set w.Completionˣ := {g | ((m g).val : ℝ) ∈ Icc Λ⁻¹ Λ}
  have hS : MeasurableSet S := by
    have : Continuous fun g : w.Completionˣ ↦ ((m g).val : ℝ) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
    exact this.measurable measurableSet_Icc
  let φ : ℝ → ℂ := fun r ↦ (((Icc Λ⁻¹ Λ).indicator 1 (r ^ w.mult) : ℝ) : ℂ)
  have h1 : ((μ.real S : ℝ) : ℂ) = ∫ u, φ ‖u.val‖ ∂μ := by
    rw [← integral_indicator_one hS, ← integral_complex_ofReal]
    refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
    simp only [φ, S, indicator, mem_ofPred_eq, hmval, Pi.one_apply]
  have hrad {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
      (hφ : ∀ r, 0 < r → φ r = (Icc a b).indicator (fun _ ↦ (1 : ℂ)) r) :
      ∫ r in Ioi (0 : ℝ), r⁻¹ • φ r = (Real.log (b / a) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := (Icc a b).indicator
      (fun r : ℝ ↦ ((r⁻¹ : ℝ) : ℂ))) (fun r hr ↦ by
        rw [hφ r hr]
        by_cases h : r ∈ Icc a b <;> simp [h, indicator, Complex.real_smul])]
    rw [setIntegral_indicator measurableSet_Icc,
      inter_eq_right.mpr (fun r (hr : r ∈ Icc a b) ↦ ha.trans_le hr.1),
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_ofReal,
      integral_inv_of_pos ha (ha.trans_le hab)]
  have hΛpos : 0 < Λ := zero_lt_one.trans_le hΛ
  have hval : μ.real S = 2 * c * Real.log Λ := by
    apply Complex.ofReal_injective
    rw [h1, localUnit_radial F w φ]
    by_cases hw : w.IsReal
    · rw [hrad (inv_pos.mpr hΛpos) (inv_le_one_of_one_le₀ hΛ |>.trans hΛ) (fun r _ ↦ by
        simp only [φ, hw.mult_eq_one, pow_one, indicator]
        split_ifs <;> simp)]
      simp only [c, hw, ↓reduceIte, div_inv_eq_mul, Real.log_mul hΛpos.ne' hΛpos.ne',
        Complex.real_smul]
      push_cast; ring
    · have hw' := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hs := Real.sqrt_pos.mpr hΛpos
      rw [hrad (inv_pos.mpr hs) ((inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hΛ)).trans
        (Real.one_le_sqrt.mpr hΛ)) (fun r hr ↦ by
          have : r ^ 2 ∈ Icc Λ⁻¹ Λ ↔ r ∈ Icc (√Λ)⁻¹ √Λ := by
            rw [mem_Icc, mem_Icc, ← Real.sqrt_inv, Real.sqrt_le_iff, Real.le_sqrt' hr]
            simp [hr.le]
          simp only [φ, hw'.mult_eq_two]
          by_cases h : r ∈ Icc (√Λ)⁻¹ √Λ <;>
            simp only [indicator, this, h, ↓reduceIte, Pi.one_apply, Complex.ofReal_one,
              Complex.ofReal_zero])]
      simp only [c, hw, ↓reduceIte, div_inv_eq_mul, Real.mul_self_sqrt hΛpos.le,
        Complex.real_smul]
      push_cast; ring
  rw [eq_comm]
  change ((ENNReal.ofReal c⁻¹ • μ) S).toReal - 2 * Real.log Λ = 0
  rw [smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_pos.mpr hc).le, ← measureReal_def, hval]
  field_simp
  ring

/-- Paper: Lemma B.4.4.3, p. 620. If the locally constant test vanishes
at one, the finite principal value is the ordinary integrable local term. -/
theorem finiteConnesWeilPrincipalValue_of_apply_one_zero (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)) (_hf : f.val 1 = 0) :
    Integrable (finiteWeilIntegrand(v, f.val)) μ𝔭(v) ∧
      finiteConnesWeilPrincipalValue v 1 f =
        ∫ u, finiteWeilIntegrand(v, f.val) u ∂μ𝔭(v) := by
  let K := v.adicCompletion F
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  let c : ENNReal := (↑v.asIdeal.absNorm / (↑v.asIdeal.absNorm - 1) : ENNReal)
  let d : K → ENNReal := fun x ↦ (↑‖x‖₊ : ENNReal)⁻¹
  have hd : Measurable d := by fun_prop
  have hdlt : ∀ᵐ y ∂(ν𝔭(v).restrict (range (Units.val : Kˣ → K))), d y < ⊤ := by
    refine ae_restrict_of_forall_mem hval.measurableSet_range fun y ⟨u, hu⟩ ↦ ?_
    exact ENNReal.inv_lt_top.mpr (by simp [← hu])
  have hdy (y : K) : (d y).toReal = ‖y‖⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.coe_toReal, coe_nnNorm]
  have hq : (1 : ENNReal) < v.asIdeal.absNorm := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hc0 : c ≠ 0 :=
    (ENNReal.div_pos (zero_lt_one.trans hq).ne' (ENNReal.sub_ne_top (ENNReal.natCast_ne_top _))).ne'
  have hct : c ≠ ⊤ :=
    (ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (tsub_pos_of_lt hq).ne').ne
  have := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hsupp (g : K → ℂ) : support (fun y ↦ ‖y‖⁻¹ • g y) ⊆ range (Units.val : Kˣ → K) := by
    intro y hy
    have : y ≠ 0 := by rintro rfl; simp at hy
    exact ⟨Units.mk0 y this, rfl⟩
  -- Multiplicative integration is additive integration against `c / ‖y‖`.
  have key (g : K → ℂ) :
      (Integrable (fun u : Kˣ ↦ g u.val) μ𝔭(v) ↔ Integrable (fun y ↦ ‖y‖⁻¹ • g y) ν𝔭(v)) ∧
        ∫ u : Kˣ, g u.val ∂μ𝔭(v) = c.toReal • ∫ y, ‖y‖⁻¹ • g y ∂ν𝔭(v) := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity]
    refine ⟨?_, ?_⟩
    · rw [integrable_smul_measure hc0 hct, show (fun u : Kˣ ↦ g u.val) = g ∘ Units.val from rfl,
        ← hval.integrable_map_iff (g := g), hval.map_comap,
        restrict_withDensity hval.measurableSet_range,
        integrable_withDensity_iff_integrable_smul' hd hdlt,
        ← integrableOn_iff_integrable_of_support_subset (hsupp g)]
      simp_rw [hdy]
      rfl
    · rw [integral_smul_measure]
      congr 1
      rw [← hval.integral_map (g := g), hval.map_comap,
        setIntegral_withDensity_eq_setIntegral_toReal_smul hd ?_ _ hval.measurableSet_range,
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range Units.val)
          (fun y hy ↦ Function.notMem_support.mp (fun h ↦ hy (hsupp g h)))]
      · simp_rw [hdy]
      · exact hdlt
  let A := (exists_finiteWeilTestMap v).choose
  have hA := (exists_finiteWeilTestMap v).choose_spec f
  let Fz : K → ℂ := Function.extend Units.val (f.val : _ → ℂ) (fun _ ↦ 0)
  have hFu (u : Kˣ) : Fz u.val = f.val u := Units.val_injective.extend_apply _ _ u
  have h0 : addTest(A f) 0 = 0 := by
    rw [hA]
    change Fz (1 + 0) / _ = 0
    rw [add_zero, ← Units.val_one, hFu, _hf, zero_div]
  let Q : K → ℂ := fun y ↦ Fz y * (Real.sqrt ‖y‖ : ℂ) / ((‖1 - y‖ : ℝ) : ℂ)
  have hQ (u : Kˣ) : Q u.val = finiteWeilIntegrand(v, f.val) u := by
    change Fz u.val * _ / _ = _
    rw [hFu]
  let H : K → ℂ := fun y ↦ ‖y‖⁻¹ • Q y
  -- After the translation `y = 1 + x`, the two weighted integrands agree.
  have hPH (x : K) : ‖x‖⁻¹ • addTest(A f) x = H (1 + x) := by
    rw [hA]
    change ‖x‖⁻¹ • (Fz (1 + x) / (Real.sqrt ‖1 + x‖ : ℂ)) =
      ‖1 + x‖⁻¹ • (Fz (1 + x) * (Real.sqrt ‖1 + x‖ : ℂ) / ((‖1 - (1 + x)‖ : ℝ) : ℂ))
    rw [sub_add_cancel_left, norm_neg, Complex.real_smul, Complex.real_smul]
    rcases (norm_nonneg (1 + x)).eq_or_lt with hn | hn
    · simp [← hn]
    have hs : (Real.sqrt ‖1 + x‖ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hn).ne'
    have hsq : (‖1 + x‖ : ℂ) = (Real.sqrt ‖1 + x‖ : ℂ) * (Real.sqrt ‖1 + x‖ : ℂ) := by
      exact_mod_cast (Real.mul_self_sqrt hn.le).symm
    push_cast
    rw [hsq]
    field_simp
  have hPI := (finiteLogFourier_eq_neg_haar v (A f) h0).2.1
  have hPH' : (fun x ↦ ‖x‖⁻¹ • addTest(A f) x) = fun x ↦ H (1 + x) := funext hPH
  have hHI : Integrable H ν𝔭(v) := by
    have h1 := (key addTest(A f)).1.mp hPI
    rw [hPH'] at h1
    refine (h1.comp_add_left (-1)).congr (ae_of_all _ fun x ↦ ?_)
    exact congrArg H (add_neg_cancel_left 1 x)
  have e1 : finiteConnesWeilPrincipalValue v 1 f = ∫ u : Kˣ, addTest(A f) u.val ∂μ𝔭(v) :=
    finiteConnesPrincipalValue_one_of_apply_zero v (A f) h0
  have e2 : ∫ u : Kˣ, addTest(A f) u.val ∂μ𝔭(v) = ∫ u : Kˣ, Q u.val ∂μ𝔭(v) :=
    calc ∫ u : Kˣ, addTest(A f) u.val ∂μ𝔭(v)
        = c.toReal • ∫ y, ‖y‖⁻¹ • addTest(A f) y ∂ν𝔭(v) := (key addTest(A f)).2
      _ = c.toReal • ∫ y, H (1 + y) ∂ν𝔭(v) :=
        congrArg (c.toReal • ·) (congrArg (fun φ ↦ ∫ y, φ y ∂ν𝔭(v)) hPH')
      _ = c.toReal • ∫ y, H y ∂ν𝔭(v) := congrArg _ (integral_add_left_eq_self H 1)
      _ = ∫ u : Kˣ, Q u.val ∂μ𝔭(v) := ((key Q).2).symm
  have e3 : ∫ u : Kˣ, Q u.val ∂μ𝔭(v) = ∫ u, finiteWeilIntegrand(v, f.val) u ∂μ𝔭(v) :=
    integral_congr_ae (ae_of_all _ hQ)
  exact ⟨((key Q).1.mpr hHI).congr (ae_of_all _ hQ), e1.trans (e2.trans e3)⟩

-- TODO(paper-gap): Equation (B.4.4.6) gives the wrong sign and scale for
-- the restriction of T, and Fourier transformation requires an additive test space.

/-- Paper: Lemma B.4.4.3, pp. 620–621. The translated Fourier
distribution is normalized on the Fourier transform of the integer-unit indicator.
It evaluates the finite multiplicative principal value on inverse square-root weighted tests.
Deviation: The distribution is on the full additive test space. Its restriction away
from one is minus the specified density divided by the mass of the integer units.
The evaluation identity extends to all multiplicative tests by the weighted translation. -/
theorem existsUnique_finiteWeilFourierDistribution (v : Primes(F)) :
    let normalized := fun T : StrongDual ℂ (𝒮ₐ(v.adicCompletion F)) ↦
      (∀ f : 𝒮ₐ(v.adicCompletion F), addTest(f) 1 = 0 →
        T f = -((q(v) / (q(v) - 1) / V𝔭(v) : ℝ) : ℂ) *
          ∫ x, addTest(f) x / ((‖1 - x‖ : ℝ) : ℂ) ∂ν𝔭(v)) ∧
      (∃ g : 𝒮ₐ(v.adicCompletion F),
        addTest(g) = tamagawaFourier ν𝔭(v) ψ𝔭(v)
          (indicator {x : v.adicCompletion F | ‖x‖ = 1} (fun _ ↦ 1)) ∧ T g = 0)
    ∃ T, normalized T ∧ (∀ S, normalized S → S = T) ∧
      (∀ f : 𝒟((v.adicCompletion F)ˣ), ∃ g : 𝒮ₐ(v.adicCompletion F),
        (∀ x, addTest(g) x = zeroExtend(f.val) x / (Real.sqrt ‖x‖ : ℂ)) ∧
        finiteConnesWeilPrincipalValue v 1 f = -(V𝔭(v) : ℂ) * T g) := by sorry

/-- Paper: Lemma B.4.4.4(1), p. 622. Changing the finite additive
character by a multiplier adds a multiple of evaluation at zero to Connes's principal value. -/
theorem finiteConnesPrincipalValue_changeCharacter (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒮ₐ(v.adicCompletion F)) :
    finiteConnesPrincipalValue v a f = finiteConnesPrincipalValue v 1 f +
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * addTest(f) 0 := by
  have ha := ((exists_finiteConnesPrincipalValue v a).choose_spec f).2
  change finiteConnesPrincipalValue v a f = _ at ha
  have h1 := (exists_finiteConnesPrincipalValue v 1).choose_spec f
  have h1E := h1.2
  change finiteConnesPrincipalValue v 1 f = _ at h1E
  have h1I := h1.1
  simp only [Units.val_one, norm_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul,
    one_mul] at h1I h1E
  have h1I' : Integrable (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) *
      tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) y) ν𝔭(v) := h1I
  have hcE := (finiteLogFourier_comp_mul v f a h1I').2
  have hc : (ENNReal.ofReal √‖a.val‖).toReal = √‖a.val‖ :=
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
  -- Changing the character and the measure dilates the transform and scales it by `√‖a‖`.
  have hF (y : v.adicCompletion F) :
      tamagawaFourier (ENNReal.ofReal √‖a.val‖ • ν𝔭(v)) (fun x ↦ ψ𝔭(v) (a.val * x))
        addTest(f) y = (√‖a.val‖ : ℝ) • tamagawaFourier ν𝔭(v) ψ𝔭(v) addTest(f) (a.val * y) := by
    unfold tamagawaFourier
    rw [integral_smul_measure, hc]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    simp only [mul_left_comm a.val x y]
  beta_reduce at ha
  refine ha.trans (Eq.trans ?_ (congrArg (· + _) h1E.symm))
  rw [integral_smul_measure, hc]
  simp only [hF, mul_smul_comm]
  rw [integral_smul, hcE, smul_smul, mul_smul_comm, smul_smul, ← mul_assoc,
    Real.mul_self_sqrt (norm_nonneg _), mul_inv_cancel₀ (norm_ne_zero_iff.mpr a.ne_zero),
    one_smul]
  push_cast
  ring

/-- Paper: Lemma B.4.4.4(2), p. 622. The same change of character
adds a multiple of evaluation at one to the multiplicative principal value. -/
theorem finiteConnesWeilPrincipalValue_changeCharacter (v : Primes(F))
    (a : (v.adicCompletion F)ˣ) (f : 𝒟((v.adicCompletion F)ˣ)) :
    finiteConnesWeilPrincipalValue v a f = finiteConnesWeilPrincipalValue v 1 f +
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * f.val 1 := by
  let A := (exists_finiteWeilTestMap v).choose
  have hunit := Units.val_injective.extend_apply f.val (fun _ ↦ 0)
    (1 : (v.adicCompletion F)ˣ)
  have hzero : addTest(A f) 0 = f.val 1 := by
    have h := (exists_finiteWeilTestMap v).choose_spec f 0
    simp only [add_zero, norm_one, Real.sqrt_one, Complex.ofReal_one, div_one] at h
    exact h.trans hunit
  exact (finiteConnesPrincipalValue_changeCharacter v a (A f)).trans
    (congrArg (fun z : ℂ ↦ finiteConnesWeilPrincipalValue v 1 f +
      ((V𝔭(v) * Real.log ‖a.val‖ / Real.log q(v) : ℝ) : ℂ) * z) hzero)

-- TODO(paper-gap): In the proof on p. 623 (footnote 24), the annihilator of
-- the maximal ideal is the inverse maximal ideal times the inverse different.
-- The second indicator in the printed display uses the different itself.

local notation "differentExp(" v ")" =>
  multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))


/-- The integral of the normalized logarithm over a closed ball changes under dilation by a
unit as the ball and the logarithm do. -/
private theorem finiteConnesWeilPrincipalValue_unitsIndicator_scale (v : Primes(F))
    (u : (v.adicCompletion F)ˣ) (R : ℝ) :
    (‖u.val‖⁻¹ : ℝ) * ∫ y, {y : v.adicCompletion F | ‖y‖ ≤ R}.indicator
        (fun y ↦ (J𝔭(v) y : ℂ)) y ∂ν𝔭(v) =
      (∫ z, {z : v.adicCompletion F | ‖z‖ ≤ R / ‖u.val‖}.indicator
        (fun z ↦ (J𝔭(v) z : ℂ)) z ∂ν𝔭(v)) +
        (J𝔭(v) u.val : ℂ) * ((ν𝔭(v) {z | ‖z‖ ≤ R / ‖u.val‖}).toReal : ℂ) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have hu : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hL : Real.log q(v) ≠ 0 := (Real.log_pos hq).ne'
  let B : Set K := {z | ‖z‖ ≤ R / ‖u.val‖}
  have hB : MeasurableSet B := measurableSet_le measurable_norm measurable_const
  have hint : IntegrableOn (fun z : K ↦ (J𝔭(v) z : ℂ)) B ν𝔭(v) := by
    have h := (finiteLog_abs_integrableOn_closedBall v (R / ‖u.val‖)).div_const (Real.log q(v))
    refine Integrable.mono' h ?_ (ae_of_all _ fun z ↦ ?_)
    · exact (Complex.measurable_ofReal.comp ((Real.measurable_log.comp measurable_norm).div_const
        _)).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (Real.log_pos hq)]
  have hfin : ν𝔭(v) B ≠ ⊤ := by
    have : B = Metric.closedBall (0 : K) (R / ‖u.val‖) := by ext z; simp [B]
    rw [this]
    exact (isCompact_closedBall (0 : K) _).measure_lt_top.ne
  have hpt : (fun y ↦ {y : K | ‖y‖ ≤ R}.indicator (fun y ↦ (J𝔭(v) y : ℂ)) (u.val * y)) =ᵐ[ν𝔭(v)]
      fun z ↦ B.indicator (fun z ↦ (J𝔭(v) z : ℂ) + (J𝔭(v) u.val : ℂ)) z := by
    have : ∀ᵐ z ∂ν𝔭(v), z ≠ 0 := by
      have : (𝓝[≠] (0 : K)).NeBot := by
        let := Valued.toNontriviallyNormedField (v.adicCompletion F) _
        exact NormedField.nhdsNE_neBot 0
      rw [ae_iff]
      simp
    filter_upwards [this] with z hz
    have hmem : (‖u.val * z‖ ≤ R) ↔ ‖z‖ ≤ R / ‖u.val‖ := by
      rw [norm_mul, le_div_iff₀ hu, mul_comm]
    by_cases h : ‖z‖ ≤ R / ‖u.val‖
    · rw [indicator_of_mem (show u.val * z ∈ {y : K | ‖y‖ ≤ R} from hmem.mpr h),
        indicator_of_mem (show z ∈ B from h)]
      simp only [norm_mul]
      rw [Real.log_mul hu.ne' (norm_pos_iff.mpr hz).ne']
      push_cast
      field_simp
      ring
    · rw [indicator_of_notMem (show u.val * z ∉ {y : K | ‖y‖ ≤ R} from fun h' ↦ h (hmem.mp h')),
        indicator_of_notMem (show z ∉ B from h)]
  have key := finiteLocalAdditive_integral_comp_mul v u
    (fun y ↦ {y : K | ‖y‖ ≤ R}.indicator (fun y ↦ (J𝔭(v) y : ℂ)) y)
  rw [integral_congr_ae hpt, integral_indicator hB, integral_add hint
    (integrableOn_const hfin), setIntegral_const, ← integral_indicator hB] at key
  simp only [RCLike.real_smul_eq_coe_mul, Measure.real] at key
  linear_combination -key

/-- A uniformizer of the completion, as a unit of norm `q⁻¹`. -/
private theorem finiteConnesWeilPrincipalValue_unitsIndicator_unif (v : Primes(F)) :
    ∃ π : (v.adicCompletion F)ˣ, ‖π.val‖ = q(v)⁻¹ := by
  let hunif := (Valued.v : Valuation (v.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨Units.mk0 hunif.choose hunif.choose_spec.ne_zero,
    norm_uniformizer_adicCompletion v _ hunif.choose_spec⟩

/-- The integral of the normalized logarithm over the integers. -/
private theorem finiteConnesWeilPrincipalValue_unitsIndicator_integers (v : Primes(F)) :
    (∫ y, {y : v.adicCompletion F | ‖y‖ ≤ 1}.indicator (fun y ↦ (J𝔭(v) y : ℂ)) y ∂ν𝔭(v)) =
      -((ν𝔭(v) {z | ‖z‖ ≤ 1}).toReal : ℂ) / ((q(v) : ℂ) - 1) := by
  obtain ⟨π, hπ⟩ := finiteConnesWeilPrincipalValue_unitsIndicator_unif v
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < q(v) := zero_lt_one.trans hq
  have hs := finiteConnesWeilPrincipalValue_unitsIndicator_scale v π q(v)⁻¹
  rw [hπ, inv_inv, div_self (inv_ne_zero hq0.ne')] at hs
  have hJπ : J𝔭(v) π.val = -1 := by
    simp only [hπ, Real.log_inv]
    field_simp [(Real.log_pos hq).ne']
  have hsame : {y : v.adicCompletion F | ‖y‖ ≤ q(v)⁻¹}.indicator (fun y ↦ (J𝔭(v) y : ℂ)) =
      {y : v.adicCompletion F | ‖y‖ ≤ 1}.indicator (fun y ↦ (J𝔭(v) y : ℂ)) := by
    funext y
    by_cases h1 : ‖y‖ ≤ q(v)⁻¹
    · rw [indicator_of_mem (show y ∈ {y : v.adicCompletion F | ‖y‖ ≤ q(v)⁻¹} from h1),
        indicator_of_mem (show y ∈ {y : v.adicCompletion F | ‖y‖ ≤ 1} from
          h1.trans (inv_le_one_of_one_le₀ hq.le))]
    · rw [indicator_of_notMem (show y ∉ {y : v.adicCompletion F | ‖y‖ ≤ q(v)⁻¹} from h1)]
      by_cases h2 : ‖y‖ ≤ 1
      · rw [indicator_of_mem (show y ∈ {y : v.adicCompletion F | ‖y‖ ≤ 1} from h2)]
        have := finiteLogFourier_eq_neg_haar_norm_eq_one v y h2 (lt_of_not_ge h1)
        simp [this]
      · rw [indicator_of_notMem (show y ∉ {y : v.adicCompletion F | ‖y‖ ≤ 1} from h2)]
  rw [hsame, hJπ] at hs
  have hq1 : (q(v) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hq.ne'
  set I := (∫ y, {y : v.adicCompletion F | ‖y‖ ≤ 1}.indicator (fun y ↦ (J𝔭(v) y : ℂ)) y
    ∂ν𝔭(v)) with hI
  set m := (ν𝔭(v) {z : v.adicCompletion F | ‖z‖ ≤ 1}).toReal with hm
  push_cast at hs
  rw [eq_div_iff hq1]
  linear_combination hs

/-- The integral of the normalized logarithm over the ball of radius `q^d`. -/
private theorem finiteConnesWeilPrincipalValue_unitsIndicator_ball (v : Primes(F)) (d : ℕ) :
    (∫ y, {y : v.adicCompletion F | ‖y‖ ≤ q(v) ^ d}.indicator (fun y ↦ (J𝔭(v) y : ℂ)) y
        ∂ν𝔭(v)) =
      (q(v) : ℂ) ^ d * ((ν𝔭(v) {z | ‖z‖ ≤ 1}).toReal : ℂ) * (d - 1 / ((q(v) : ℂ) - 1)) := by
  obtain ⟨π, hπ⟩ := finiteConnesWeilPrincipalValue_unitsIndicator_unif v
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < q(v) := zero_lt_one.trans hq
  have hn : ‖(π⁻¹ ^ d).val‖ = q(v) ^ d := by
    rw [Units.val_pow_eq_pow_val, norm_pow, Units.val_inv_eq_inv_val, norm_inv, hπ, inv_inv]
  have hs := finiteConnesWeilPrincipalValue_unitsIndicator_scale v (π⁻¹ ^ d) (q(v) ^ d)
  rw [hn, div_self (pow_ne_zero _ hq0.ne')] at hs
  have hJ : J𝔭(v) (π⁻¹ ^ d).val = d := by
    simp only [hn, Real.log_pow]
    field_simp [(Real.log_pos hq).ne']
  rw [hJ, finiteConnesWeilPrincipalValue_unitsIndicator_integers] at hs
  have hq1 : (q(v) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hq.ne'
  set I := (∫ y, {y : v.adicCompletion F | ‖y‖ ≤ q(v) ^ d}.indicator (fun y ↦ (J𝔭(v) y : ℂ)) y
    ∂ν𝔭(v)) with hI
  set m := (ν𝔭(v) {z : v.adicCompletion F | ‖z‖ ≤ 1}).toReal with hm
  push_cast at hs hq1 ⊢
  have hqd : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ d ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hq0.ne')
  rw [← mul_inv_cancel_left₀ hqd I, hs]
  field_simp
  ring

/-- The local integers are the closed unit ball. -/
private theorem finiteConnesWeilPrincipalValue_unitsIndicator_integers_eq (v : Primes(F)) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = {z | ‖z‖ ≤ 1} := by
  ext z
  change z ∈ v.adicCompletionIntegers F ↔ ‖z‖ ≤ 1
  rw [HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v]
  exact Valued.toNormedField.norm_le_one_iff.symm

/-- The normalized logarithm against the Fourier transform of the integer indicator. -/
private theorem finiteConnesWeilPrincipalValue_unitsIndicator_fourierIntegers (v : Primes(F)) :
    (∫ y, ((J𝔭(v) y : ℝ) : ℂ) * tamagawaFourier ν𝔭(v) ψ𝔭(v)
      ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ ↦ (1 : ℂ))) y
        ∂ν𝔭(v)) = (differentExp(v) : ℂ) - 1 / ((q(v) : ℂ) - 1) := by
  rw [finiteLocalTamagawaFourier_integers]
  set c : ℝ := ((ENNReal.ofReal (Real.sqrt (q(v) ^ differentExp(v))))⁻¹).toReal with hc
  have hm : (ν𝔭(v) {z : v.adicCompletion F | ‖z‖ ≤ 1}).toReal = c := by
    rw [← finiteConnesWeilPrincipalValue_unitsIndicator_integers_eq,
      finiteLocalAdditiveTamagawaMeasure_integers]
  have hc' : c = (Real.sqrt (q(v) ^ differentExp(v)))⁻¹ := by
    rw [hc, ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have hfun : (fun y ↦ ((J𝔭(v) y : ℝ) : ℂ) * ((c : ℂ) •
        {x : v.adicCompletion F | ‖x‖ ≤ q(v) ^ differentExp(v)}.indicator (fun _ ↦ (1 : ℂ))) y) =
      fun y ↦ (c : ℂ) * {x : v.adicCompletion F | ‖x‖ ≤ q(v) ^ differentExp(v)}.indicator
        (fun y ↦ (J𝔭(v) y : ℂ)) y := by
    funext y
    by_cases h : ‖y‖ ≤ q(v) ^ differentExp(v)
    · simp [indicator_of_mem (show y ∈ {x : v.adicCompletion F | ‖x‖ ≤ q(v) ^ differentExp(v)}
        from h), mul_comm]
    · simp [indicator_of_notMem (show y ∉ {x : v.adicCompletion F |
        ‖x‖ ≤ q(v) ^ differentExp(v)} from h)]
  refine (integral_congr_ae (ae_of_all _ fun y ↦ congrFun hfun y)).trans ?_
  rw [integral_const_mul, finiteConnesWeilPrincipalValue_unitsIndicator_ball, hm]
  have hq0 : (0 : ℝ) < q(v) := by
    exact_mod_cast zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)
  have hsq : c * c * q(v) ^ differentExp(v) = 1 := by
    have hp : (0 : ℝ) < q(v) ^ differentExp(v) := pow_pos hq0 _
    rw [hc', ← mul_inv, Real.mul_self_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  have hsqC : (c : ℂ) * c * (q(v) : ℂ) ^ differentExp(v) = 1 := by exact_mod_cast hsq
  linear_combination ((differentExp(v) : ℂ) - 1 / ((q(v) : ℂ) - 1)) * hsqC

/-- The multiplicative mass of the units near `-1` is the mass of the integer units divided by
`q - 1`. -/
private theorem finiteConnesWeilPrincipalValue_unitsIndicator_measure (v : Primes(F)) :
    (μ𝔭(v) (Units.val ⁻¹' {x : v.adicCompletion F | ‖1 + x‖ < 1})).toReal =
      (μ𝔭(v) ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ)).toReal /
        (q(v) - 1) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : (ν𝔭(v)).IsAddHaarMeasure := finiteLocalAdditiveTamagawaMeasure_isAddHaar F v
  have he := (IsOpenUnits.isOpenEmbedding_unitsVal (M := K)).measurableEmbedding
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < q(v) := zero_lt_one.trans hq
  obtain ⟨π, hπ⟩ := finiteConnesWeilPrincipalValue_unitsIndicator_unif v
  let A : Set K := {x | ‖1 + x‖ < 1}
  have hA : MeasurableSet A :=
    measurableSet_lt (measurable_const.add measurable_id).norm measurable_const
  have hA1 (x : K) (hx : x ∈ A) : ‖x‖ = 1 := by
    have h : ‖(1 + x) + (-1 : K)‖ = max ‖1 + x‖ ‖(-1 : K)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact hx.ne)
    rw [norm_neg, norm_one, max_eq_right hx.le] at h
    simpa using h
  have hsub : A ⊆ range (Units.val : Kˣ → K) := fun x hx ↦
    ⟨Units.mk0 x (fun h ↦ by have := hA1 x hx; simp [h] at this), rfl⟩
  have hμA : μ𝔭(v) (Units.val ⁻¹' A) =
      (↑(Ideal.absNorm v.asIdeal) / (↑(Ideal.absNorm v.asIdeal) - 1) : ENNReal) * ν𝔭(v) A := by
    rw [finiteLocalMultiplicativeTamagawaMeasure_eq_withDensity, smul_apply, smul_eq_mul,
      he.comap_apply, image_preimage_eq_of_subset hsub, withDensity_apply _ hA]
    congr 1
    rw [setLIntegral_congr_fun hA (g := fun _ ↦ (1 : ENNReal)) (fun x hx ↦ by
      rw [show ‖x‖₊ = 1 from NNReal.eq (by simpa using hA1 x hx)]; simp), setLIntegral_const,
      one_mul]
  have hνA : ν𝔭(v) A = ENNReal.ofReal q(v)⁻¹ * ν𝔭(v) {z : K | ‖z‖ ≤ 1} := by
    have h1 : A = (fun x ↦ 1 + x) ⁻¹' {y : K | ‖y‖ < 1} := rfl
    have h2 : {y : K | ‖y‖ < 1} = ((π⁻¹).val * ·) ⁻¹' {z : K | ‖z‖ ≤ 1} := by
      ext y
      have hn : ‖(π⁻¹).val * y‖ = q(v) * ‖y‖ := by
        rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv, hπ, inv_inv]
      change ‖y‖ < 1 ↔ ‖(π⁻¹).val * y‖ ≤ 1
      rw [hn]
      constructor
      · intro hy
        by_cases h : ‖y‖ ≤ q(v)⁻¹
        · calc q(v) * ‖y‖ ≤ q(v) * q(v)⁻¹ := mul_le_mul_of_nonneg_left h hq0.le
            _ = 1 := mul_inv_cancel₀ hq0.ne'
        · exact absurd (finiteLogFourier_eq_neg_haar_norm_eq_one v y hy.le (lt_of_not_ge h))
            hy.ne
      · intro hy
        calc ‖y‖ = q(v)⁻¹ * (q(v) * ‖y‖) := by field_simp
          _ ≤ q(v)⁻¹ * 1 := mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hq0.le)
          _ < 1 := by rw [mul_one]; exact inv_lt_one_of_one_lt₀ hq
    rw [h1, measure_preimage_add, h2, ← Measure.map_apply (measurable_const_mul _)
      (measurableSet_le measurable_norm measurable_const), finiteLocalAdditive_map_mul,
      smul_apply, smul_eq_mul, Units.val_inv_eq_inv_val, norm_inv, hπ, inv_inv]
  rw [hμA, hνA, ← finiteConnesWeilPrincipalValue_unitsIndicator_integers_eq,
    finiteLocalAdditiveTamagawaMeasure_integers,
    finiteLocalMultiplicativeTamagawaMeasure_integerUnits]
  have hq1 : q(v) - 1 ≠ 0 := (sub_pos.mpr hq).ne'
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_sub_of_le (by exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le)
      (ENNReal.natCast_ne_top _), ENNReal.toReal_natCast, ENNReal.toReal_one,
    ENNReal.toReal_ofReal (inv_nonneg.mpr hq0.le)]
  field_simp

/-- The indicator of a compact open subgroup is a compactly supported Bruhat test. -/
private theorem finiteConnesWeilPrincipalValue_unitsIndicator_test {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) :
    ∃ f : BruhatCompactSupport G, f.val = (U : Set G).indicator (fun _ ↦ 1) := by
  classical
  let g : G → ℂ := (U : Set G).indicator (fun _ ↦ 1)
  let : CompactSpace (lcaAnnihilator U) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator U hU)
  have hClosed : IsClosed (U : Set G) := U.isClosed_of_isOpen hU
  have hSmooth : IsBruhatSmooth g := by
    intro p
    refine ⟨U, ⟨hClosed, isOpen_lcaAnnihilator U hUc, isCompactlyGeneratedGroup_of_compact⟩,
      ?_, ?_⟩
    · intro h x
      have hmem : h.val * x ∈ (U : Set G) ↔ x ∈ (U : Set G) := by
        refine ⟨fun hx ↦ ?_, U.mul_mem h.property⟩
        change x ∈ U
        simpa only [inv_mul_cancel_left] using U.mul_mem (U.inv_mem h.property) hx
      simp only [g, indicator_apply, hmem]
    · intro a ha
      let f₀ : a.quotient → ℂ := ({1} : Set a.quotient).indicator (fun _ ↦ 1)
      refine ⟨f₀, fun x ↦ ?_, ?_⟩
      · simp only [f₀, g, indicator_apply, mem_singleton_iff, a.quotient_mk_eq_one, ha]
        rfl
      · intro e z b
        let : DiscreteTopology a.quotient := QuotientGroup.discreteTopology (by
          rw [ha]
          exact hU.preimage continuous_subtype_val)
        let X := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
        let q : X → a.quotient := fun x ↦
          e.equiv.symm (Multiplicative.ofAdd (elementaryCover x z b))
        have hq : Continuous q := e.equiv.symm.continuous.comp
          (continuous_fst.prodMk ((continuous_pi fun j ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
            ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).prodMk continuous_const))
        change ContDiff ℝ (p : ℕ∞) (fun x ↦ f₀ (q x))
        have heq : (fun x ↦ f₀ (q x)) = fun _ : X ↦ f₀ (q 0) :=
          funext fun x ↦ congrArg f₀ (TotallyDisconnectedSpace.eq_of_continuous q hq x 0)
        rw [heq]
        exact contDiff_const
  have hSub : Function.support g ⊆ (U : Set G) := support_indicator_subset
  have hSupport : HasCompactSupport g :=
    hUc.of_isClosed_subset isClosed_closure (closure_minimal hSub hClosed)
  exact ⟨⟨g, (mem_bruhatSmoothSubmodule_iff _).mpr hSmooth, hSupport⟩, rfl⟩

/-- Paper: Lemma B.4.4.5, p. 622, in the one remaining case `f = 1_{O_v^×}`.
The rescaled principal value of the integer-unit indicator is minus the local
different contribution. The two integrals of the unit-subtracted finite part
vanish on this test, so this is exactly the constant by which
`finiteConnesWeilPrincipalValue_eq_finitePart` fails for a general test.
It is the calculation of pp. 622--623: the Fourier transform of the indicator
of `-1 + O_v^×` against the normalized logarithm, whose printed form carries the
footnote "the right side should be double-checked"; see the `TODO(paper-gap)`
note directly above. -/
theorem finiteConnesWeilPrincipalValue_unitsIndicator (v : Primes(F)) :
    ∃ b : 𝒟((v.adicCompletion F)ˣ),
      b.val = indicator ((O(v)).units : Set (v.adicCompletion F)ˣ) (fun _ ↦ 1) ∧
      finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 b =
        -(((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ) := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let : BorelSpace K := ⟨rfl⟩
  let : BorelSpace Kˣ := ⟨rfl⟩
  let U : Subgroup Kˣ := (v.adicCompletionIntegers F).units
  have hU : IsOpen (U : Set Kˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact (U : Set Kˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  obtain ⟨b, hb⟩ := finiteConnesWeilPrincipalValue_unitsIndicator_test U hU hUc
  refine ⟨b, hb, ?_⟩
  have hq : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < q(v) := zero_lt_one.trans hq
  have hmemU (u : Kˣ) : u ∈ U ↔ ‖u.val‖ = 1 := by
    change u ∈ (v.adicCompletionIntegers F).units ↔ _
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      Valued.toNormedField.norm_eq_one_iff]
  -- The weighted translate of the units indicator.
  let A := (exists_finiteWeilTestMap v).choose
  have hA (x : K) : A b (Multiplicative.ofAdd x) = if ‖1 + x‖ = 1 then 1 else 0 := by
    refine ((exists_finiteWeilTestMap v).choose_spec b x).trans ?_
    show Function.extend Units.val (b.val : Kˣ → ℂ) (fun _ ↦ 0) (1 + x) /
      (Real.sqrt ‖1 + x‖ : ℂ) = _
    by_cases h0 : 1 + x = 0
    · have hnr : (1 + x) ∉ range (Units.val : Kˣ → K) := by
        rintro ⟨u, hu⟩; exact u.ne_zero (hu.trans h0)
      rw [Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ ↦ hnr ⟨u, hu⟩)]
      simp [h0]
    · have he : Function.extend Units.val (b.val : Kˣ → ℂ) (fun _ ↦ 0) (1 + x) =
          b.val (Units.mk0 (1 + x) h0) :=
        Units.val_injective.extend_apply (b.val : Kˣ → ℂ) _ (Units.mk0 (1 + x) h0)
      rw [he, hb]
      by_cases h1 : ‖1 + x‖ = 1
      · have hm : Units.mk0 (1 + x) h0 ∈ (U : Set Kˣ) :=
          SetLike.mem_coe.mpr ((hmemU (Units.mk0 (1 + x) h0)).mpr h1)
        rw [indicator_of_mem hm, h1, Real.sqrt_one, Complex.ofReal_one, div_one]
        simp
      · have hm : Units.mk0 (1 + x) h0 ∉ (U : Set Kˣ) :=
          fun h ↦ h1 ((hmemU (Units.mk0 (1 + x) h0)).mp (SetLike.mem_coe.mp h))
        rw [indicator_of_notMem hm, zero_div]
        exact (ite_eq_right_iff.mpr fun h ↦ absurd h h1).symm
  -- The integer indicator as an additive test.
  obtain ⟨t, ht⟩ := (mem_finitePlaceSchwartz_iff F v
    ((v.adicCompletionIntegers F : Set K).indicator (fun _ ↦ (1 : ℂ)))).mpr (by
      have hOo : IsOpen (v.adicCompletionIntegers F : Set K) := Valued.isOpen_valuationSubring _
      have hOc : IsCompact (v.adicCompletionIntegers F : Set K) :=
        isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
      have hOcl : IsClosed (v.adicCompletionIntegers F : Set K) := hOc.isClosed
      have hcl : IsClopen (v.adicCompletionIntegers F : Set K) := ⟨hOcl, hOo⟩
      have hlc : IsLocallyConstant ⇑(LocallyConstant.charFn ℂ hcl) :=
        (LocallyConstant.charFn ℂ hcl).isLocallyConstant
      rw [LocallyConstant.coe_charFn] at hlc
      exact ⟨hlc,
        hOc.of_isClosed_subset isClosed_closure (closure_minimal support_indicator_subset hOcl)⟩)
  -- The remainder vanishes at zero.
  let h : SchwartzBruhat (Multiplicative K) := A b - t
  have hA1 (x : K) (hx : ‖1 + x‖ < 1) : ‖x‖ = 1 := by
    have h' : ‖(1 + x) + (-1 : K)‖ = max ‖1 + x‖ ‖(-1 : K)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact hx.ne)
    rw [norm_neg, norm_one, max_eq_right hx.le] at h'
    simpa using h'
  have hh (x : K) : h (Multiplicative.ofAdd x) =
      -({y : K | ‖1 + y‖ < 1}.indicator (fun _ ↦ (1 : ℂ)) x) := by
    change A b (Multiplicative.ofAdd x) - t (Multiplicative.ofAdd x) = _
    rw [hA, ht, finiteConnesWeilPrincipalValue_unitsIndicator_integers_eq]
    rcases lt_trichotomy ‖1 + x‖ 1 with hlt | heq | hgt
    · rw [indicator_of_mem (show x ∈ {y : K | ‖1 + y‖ < 1} from hlt),
        indicator_of_mem (show x ∈ {z : K | ‖z‖ ≤ 1} from (hA1 x hlt).le)]
      simp [hlt.ne]
    · have hx : ‖x‖ ≤ 1 := by
        have h' := IsUltrametricDist.norm_add_le_max (1 + x) (-1 : K)
        rw [heq, norm_neg, norm_one, max_self] at h'
        simpa using h'
      rw [indicator_of_notMem (show x ∉ {y : K | ‖1 + y‖ < 1} from
          fun h' ↦ absurd heq (ne_of_lt h')),
        indicator_of_mem (show x ∈ {z : K | ‖z‖ ≤ 1} from hx)]
      simp [heq]
    · have hx : ‖x‖ = ‖1 + x‖ := by
        have h' : ‖(1 + x) + (-1 : K)‖ = max ‖1 + x‖ ‖(-1 : K)‖ :=
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
            (by rw [norm_neg, norm_one]; exact hgt.ne')
        rw [norm_neg, norm_one, max_eq_left hgt.le] at h'
        simpa using h'
      rw [indicator_of_notMem (show x ∉ {y : K | ‖1 + y‖ < 1} from
          fun h' ↦ absurd (lt_trans hgt h') (lt_irrefl _)),
        indicator_of_notMem (show x ∉ {z : K | ‖z‖ ≤ 1} from fun h' ↦ by
          rw [mem_ofPred_eq, hx] at h'; exact absurd h' (not_le.mpr hgt))]
      simp [hgt.ne']
  have h0 : h (Multiplicative.ofAdd 0) = 0 := by
    rw [hh, indicator_of_notMem (show (0 : K) ∉ {y : K | ‖1 + y‖ < 1} by simp), neg_zero]
  -- The principal value splits at zero.
  change _ * finiteConnesPrincipalValue v 1 (A b) = _
  have hsplit : A b = t + h := by simp [h]
  rw [hsplit, map_add]
  set V := (μ𝔭(v) (v.adicCompletionIntegers F).units).toReal with hV
  have hPt : finiteConnesPrincipalValue v 1 t =
      -(V : ℂ) * ((differentExp(v) : ℂ) - 1 / ((q(v) : ℂ) - 1)) := by
    have h1 := ((exists_finiteConnesPrincipalValue v 1).choose_spec t).2
    change finiteConnesPrincipalValue v 1 t = _ at h1
    simp only [Units.val_one, norm_one, Real.sqrt_one, ENNReal.ofReal_one, one_smul,
      one_mul] at h1
    have hft : (fun x ↦ t (Multiplicative.ofAdd x)) =
        (v.adicCompletionIntegers F : Set K).indicator (fun _ ↦ (1 : ℂ)) := funext ht
    rw [h1, hft, finiteConnesWeilPrincipalValue_unitsIndicator_fourierIntegers]
  have hPh : finiteConnesPrincipalValue v 1 h = -((V / (q(v) - 1) : ℝ) : ℂ) := by
    rw [finiteConnesPrincipalValue_one_of_apply_zero v h h0]
    have hmeas : MeasurableSet (Units.val ⁻¹' {y : K | ‖1 + y‖ < 1} : Set Kˣ) :=
      ((isOpen_lt (continuous_const.add continuous_id).norm continuous_const).preimage
        Units.continuous_val).measurableSet
    have hfun : (fun u : Kˣ ↦ h (Multiplicative.ofAdd u.val)) =
        fun u ↦ -((Units.val ⁻¹' {y : K | ‖1 + y‖ < 1}).indicator (fun _ ↦ (1 : ℂ)) u) := by
      funext u
      rw [hh]
      rfl
    refine (integral_congr_ae (ae_of_all _ (congrFun hfun))).trans ?_
    rw [integral_neg, integral_indicator_const _ hmeas, Measure.real,
      finiteConnesWeilPrincipalValue_unitsIndicator_measure, ← hV]
    simp
  rw [hPt, hPh]
  have hV0 : V ≠ 0 := by
    rw [hV, finiteLocalMultiplicativeTamagawaMeasure_integerUnits]
    refine (ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr
        (Real.sqrt_pos.mpr (pow_pos ?_ _))).ne')).ne'
    exact_mod_cast hq0
  have hq1 : (q(v) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast hq.ne'
  have hL : (Real.log q(v) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  have hV0' : (V : ℂ) ≠ 0 := by exact_mod_cast hV0
  push_cast
  field_simp
  ring

/-- Paper: Lemma B.4.4.5, p. 622. The rescaled finite principal value is
the unit-subtracted finite part with the different correction. -/
theorem finiteConnesWeilPrincipalValue_eq_finitePart (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)) :
    let units : Set (v.adicCompletion F)ˣ := (O(v)).units
    let outside := finiteWeilIntegrand(v, f.val)
    let inside := finiteWeilIntegrand(v, (fun u ↦ f.val u - f.val 1))
    IntegrableOn outside unitsᶜ μ𝔭(v) ∧ IntegrableOn inside units μ𝔭(v) ∧
      finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f =
        finiteWeilScale(v) * ((∫ u in unitsᶜ, outside u ∂μ𝔭(v)) +
          (∫ u in units, inside u ∂μ𝔭(v))) -
        ((differentExp(v) : ℝ) * Real.log q(v) : ℝ) * f.val 1 := by
  obtain ⟨b, hbval, hbscale⟩ := finiteConnesWeilPrincipalValue_unitsIndicator v
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have hU : IsOpen ((O(v)).units : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUmeas : MeasurableSet ((O(v)).units : Set (v.adicCompletion F)ˣ) := hU.measurableSet
  have hb1 : b.val 1 = 1 := by
    rw [hbval]
    exact Set.indicator_of_mem (Subgroup.one_mem _) _
  set c : ℂ := f.val 1 with hc
  set g : 𝒟((v.adicCompletion F)ˣ) := f - c • b with hg
  have hgval (u : (v.adicCompletion F)ˣ) : g.val u = f.val u - c * b.val u := by
    rw [hg]
    rfl
  have hg1 : g.val 1 = 0 := by
    rw [hgval, hb1, hc]
    ring
  -- The test `g` vanishes at one, so the ordinary integral computes its principal value.
  obtain ⟨hintg, hPg0⟩ := finiteConnesWeilPrincipalValue_of_apply_one_zero v g hg1
  have hPg : finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 g =
      finiteWeilScale(v) * ∫ u, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v) := by rw [hPg0]
  -- The principal value is linear, so the correction is the one of the indicator.
  have hfe : f = g + c • b := by
    rw [hg]
    abel
  have hP : finiteConnesWeilPrincipalValue v 1 f =
      finiteConnesWeilPrincipalValue v 1 g + c * finiteConnesWeilPrincipalValue v 1 b := by
    rw [hfe, map_add, map_smul, smul_eq_mul]
  -- Off the integer units the subtracted test agrees with the original one,
  -- and on them the unit-subtracted integrands agree.
  have hout (u : (v.adicCompletion F)ˣ) (hu : u ∉ (O(v)).units) :
      finiteWeilIntegrand(v, f.val) u = finiteWeilIntegrand(v, g.val) u := by
    have hbu : b.val u = 0 := by
      rw [hbval]
      exact Set.indicator_of_notMem hu _
    have hgu : g.val u = f.val u := by rw [hgval, hbu, mul_zero, sub_zero]
    exact (congrArg (fun t : ℂ ↦ t * (Real.sqrt ‖u.val‖ : ℂ) /
      ((‖1 - u.val‖ : ℝ) : ℂ)) hgu).symm
  have hin (u : (v.adicCompletion F)ˣ) (hu : u ∈ (O(v)).units) :
      finiteWeilIntegrand(v, (fun u ↦ f.val u - f.val 1)) u =
        finiteWeilIntegrand(v, g.val) u := by
    have hbu : b.val u = 1 := by
      rw [hbval]
      exact Set.indicator_of_mem hu _
    have hgu : g.val u = f.val u - f.val 1 := by rw [hgval, hbu, mul_one]
    exact (congrArg (fun t : ℂ ↦ t * (Real.sqrt ‖u.val‖ : ℂ) /
      ((‖1 - u.val‖ : ℝ) : ℂ)) hgu).symm
  have houtI : (∫ u in ((O(v)).units)ᶜ, finiteWeilIntegrand(v, f.val) u ∂μ𝔭(v)) =
      ∫ u in ((O(v)).units)ᶜ, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v) :=
    setIntegral_congr_fun hUmeas.compl (fun u hu ↦ hout u hu)
  have hinI :
      (∫ u in ((O(v)).units), finiteWeilIntegrand(v, (fun u ↦ f.val u - f.val 1)) u ∂μ𝔭(v)) =
        ∫ u in ((O(v)).units), finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v) :=
    setIntegral_congr_fun hUmeas (fun u hu ↦ hin u hu)
  have hsum : (∫ u in ((O(v)).units)ᶜ, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v)) +
      (∫ u in ((O(v)).units), finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v)) =
      ∫ u, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v) := by
    rw [add_comm]
    exact integral_add_compl hUmeas hintg
  have hkey : finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f =
      finiteWeilScale(v) * (∫ u, finiteWeilIntegrand(v, g.val) u ∂μ𝔭(v)) +
        c * (-(((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ)) := by
    have e1 : finiteWeilScale(v) * (c * finiteConnesWeilPrincipalValue v 1 b) =
        c * (finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 b) := by ring
    rw [hP, mul_add, hPg, e1, hbscale]
  refine ⟨hintg.integrableOn.congr_fun (fun u hu ↦ (hout u hu).symm) hUmeas.compl,
    hintg.integrableOn.congr_fun (fun u hu ↦ (hin u hu).symm) hUmeas, ?_⟩
  dsimp only
  rw [houtI, hinI, hsum, hkey]
  ring

/-- Evaluating the finite part on a compact open subgroup indicator gives the correction term. -/
private theorem finiteConnesWeilPrincipalValue_integerUnits_test
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G))
    (μ : Measure G) (num den : G → ℂ) (eval : 𝒟(G) → ℂ) (scale correction : ℂ)
    (heval : ∀ f : 𝒟(G), eval f =
      scale * ((∫ u in (U : Set G)ᶜ, f.val u * num u / den u ∂μ) +
        (∫ u in (U : Set G), (f.val u - f.val 1) * num u / den u ∂μ)) -
      correction * f.val 1) :
    ∃ f : 𝒟(G), f.val = (U : Set G).indicator (fun _ ↦ 1) ∧ eval f = -correction := by
  classical
  let g : G → ℂ := (U : Set G).indicator (fun _ ↦ 1)
  let : CompactSpace (lcaAnnihilator U) :=
    isCompact_iff_compactSpace.mp (isCompact_lcaAnnihilator U hU)
  have hClosed : IsClosed (U : Set G) := U.isClosed_of_isOpen hU
  have hSmooth : IsBruhatSmooth g := by
    intro p
    refine ⟨U, ⟨hClosed, isOpen_lcaAnnihilator U hUc, isCompactlyGeneratedGroup_of_compact⟩,
      ?_, ?_⟩
    · intro h x
      have hmem : h.val * x ∈ (U : Set G) ↔ x ∈ (U : Set G) := by
        refine ⟨fun hx ↦ ?_, U.mul_mem h.property⟩
        change x ∈ U
        simpa only [inv_mul_cancel_left] using U.mul_mem (U.inv_mem h.property) hx
      simp only [g, indicator_apply, hmem]
    · intro a ha
      let f₀ : a.quotient → ℂ := ({1} : Set a.quotient).indicator (fun _ ↦ 1)
      refine ⟨f₀, fun x ↦ ?_, ?_⟩
      · simp only [f₀, g, indicator_apply, mem_singleton_iff, a.quotient_mk_eq_one, ha]
        rfl
      · intro e z b
        let : DiscreteTopology a.quotient := QuotientGroup.discreteTopology (by
          rw [ha]
          exact hU.preimage continuous_subtype_val)
        let X := EuclideanSpace ℝ (Fin e.realDim) × EuclideanSpace ℝ (Fin e.torusDim)
        let q : X → a.quotient := fun x ↦ e.equiv.symm (Multiplicative.ofAdd (elementaryCover x z b))
        have hq : Continuous q := e.equiv.symm.continuous.comp
          (continuous_fst.prodMk ((continuous_pi fun j ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
            ((PiLp.continuous_apply 2 _ j).comp continuous_snd)).prodMk continuous_const))
        change ContDiff ℝ (p : ℕ∞) (fun x ↦ f₀ (q x))
        have heq : (fun x ↦ f₀ (q x)) = fun _ : X ↦ f₀ (q 0) :=
          funext fun x ↦ congrArg f₀ (TotallyDisconnectedSpace.eq_of_continuous q hq x 0)
        rw [heq]
        exact contDiff_const
  have hSub : Function.support g ⊆ (U : Set G) := support_indicator_subset
  have hSupport : HasCompactSupport g :=
    hUc.of_isClosed_subset isClosed_closure (closure_minimal hSub hClosed)
  let f : 𝒟(G) := ⟨g, (mem_bruhatSmoothSubmodule_iff _).mpr hSmooth, hSupport⟩
  have hOne : g 1 = 1 := indicator_of_mem U.one_mem (fun _ : G ↦ (1 : ℂ))
  have hOut : (∫ u in (U : Set G)ᶜ, f.val u * num u / den u ∂μ) = 0 := by
    change (∫ u in (U : Set G)ᶜ, g u * num u / den u ∂μ) = 0
    calc
      _ = ∫ _u in (U : Set G)ᶜ, (0 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hU.measurableSet.compl
        intro u hu
        have hgu : g u = 0 := indicator_of_notMem hu _
        simp only [hgu, zero_mul, zero_div]
      _ = 0 := by simp
  have hIn : (∫ u in (U : Set G), (f.val u - f.val 1) * num u / den u ∂μ) = 0 := by
    change (∫ u in (U : Set G), (g u - g 1) * num u / den u ∂μ) = 0
    calc
      _ = ∫ _u in (U : Set G), (0 : ℂ) ∂μ := by
        apply setIntegral_congr_fun hU.measurableSet
        intro u hu
        have hgu : g u = 1 := indicator_of_mem hu (fun _ : G ↦ (1 : ℂ))
        simp only [hgu, hOne, sub_self, zero_mul, zero_div]
      _ = 0 := by simp
  refine ⟨f, rfl, ?_⟩
  have hValue := heval f
  have hfOne : f.val 1 = 1 := hOne
  rw [hOut, hIn, hfOne, add_zero, mul_zero, zero_sub, mul_one] at hValue
  exact hValue

/-- Paper: Lemma B.4.4.5, p. 622. The integer-unit indicator detects
the different contribution to the Fourier-defined principal value. The
unit-subtracted finite part is zero on this test. -/
theorem finiteConnesWeilPrincipalValue_integerUnits (v : Primes(F)) :
    ∃ f : 𝒟((v.adicCompletion F)ˣ),
      f.val = indicator ((O(v)).units : Set (v.adicCompletion F)ˣ) (fun _ ↦ 1) ∧
      finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f =
        -(((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ) := by
  let U : Subgroup (v.adicCompletion F)ˣ := (O(v)).units
  have hU : IsOpen (U : Set (v.adicCompletion F)ˣ) :=
    Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)
  have hUc : IsCompact (U : Set (v.adicCompletion F)ˣ) := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  exact finiteConnesWeilPrincipalValue_integerUnits_test U hU hUc (μ𝔭(v))
    (fun u : (v.adicCompletion F)ˣ ↦ (Real.sqrt ‖u.val‖ : ℂ))
    (fun u : (v.adicCompletion F)ˣ ↦ ((‖1 - u.val‖ : ℝ) : ℂ))
    (fun f ↦ finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 f)
    finiteWeilScale(v) (((differentExp(v) : ℝ) * Real.log q(v) : ℝ) : ℂ)
    (fun f ↦ (finiteConnesWeilPrincipalValue_eq_finitePart v f).2.2)

/-- Paper: Remark B.4.4.6, p. 623. A finite local test agrees with its value at
one on a neighborhood of one, so the unit-subtracted integrand vanishes there. -/
theorem finiteWeilTest_eventually_eq_at_one (v : Primes(F)) (f : 𝒟((v.adicCompletion F)ˣ)) :
    ∀ᶠ u in 𝓝 (1 : (v.adicCompletion F)ˣ), f.val u = f.val 1 := by
  let G := (v.adicCompletion F)ˣ
  have hf : IsBruhatSmooth f.val := (mem_bruhatSmoothSubmodule_iff _).mp f.property.1
  obtain ⟨k, hk, hInv, _⟩ := hf 0
  let A : OpenCompactlyGeneratedSubgroups (PontryaginDual G) := ⟨lcaAnnihilator k, hk.2⟩
  obtain ⟨γ, _, hγ, hker, _⟩ := lca_dualSubgroup_quotient A
  let Q := PontryaginDual A.val
  let : LocallyCompactSpace A.val := A.property.1.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨n, ⟨charts⟩⟩ := isCompactlyGeneratedGroup_iff_dual_locallyEuclidean.mp A.property.2
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q := charts
  let : LocallyConnectedSpace Q := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) Q
  let B : OpenSubgroup G :=
    ⟨(v.adicCompletionIntegers F).units, Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)⟩
  let : CompactSpace B.toSubgroup := isCompact_iff_compactSpace.mp
    (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  let j : B.toSubgroup → v.adicCompletion F := Units.val ∘ Subtype.val
  have hj : Topology.IsEmbedding j :=
    (Units.isEmbedding_val₀ (G₀ := v.adicCompletion F)).comp Topology.IsEmbedding.subtypeVal
  let η : B.toSubgroup →ₜ* Q := γ.comp ⟨B.toSubgroup.subtype, continuous_subtype_val⟩
  have hη : Continuous η := η.continuous
  have hηOpen : IsOpenMap η := hγ.isOpenMap.comp B.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hSmall (U : Set Q) (hU : U ∈ 𝓝 (1 : Q)) : ∃ V : OpenSubgroup Q, (V : Set Q) ⊆ U := by
    have hpre : η ⁻¹' U ∈ 𝓝 (1 : B.toSubgroup) :=
      hη.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU)
    rw [hj.isInducing.nhds_eq_comap] at hpre
    obtain ⟨S, hS, hSsub⟩ := mem_comap.mp hpre
    let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨r, hr⟩ := (Valued.mem_nhds (Γ₀ := WithZero (Multiplicative ℤ))).mp hS
    let W := (fun x : B.toSubgroup ↦ j x - j 1) ⁻¹' {y | ν.restrict y < r.val}
    have hW : IsClopen W :=
      (Valued.isClopen_ball (v.adicCompletion F) r.val).preimage
        (hj.continuous.sub continuous_const)
    have h1W : (1 : B.toSubgroup) ∈ W := by
      change ν.restrict (j 1 - j 1) < r.val
      rw [sub_self, map_zero]
      exact pos_iff_ne_zero.mpr r.ne_zero
    obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1W
    refine ⟨⟨V.toSubgroup.map η.toMonoidHom, hηOpen _ V.isOpen⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hSsub (hr (hV hx))
  have hComponent : connectedComponent (1 : Q) = {1} := by
    refine subset_antisymm ?_ (singleton_subset_iff.mpr mem_connectedComponent)
    intro y hy
    by_contra hne
    have h1y : (1 : Q) ∈ ({y} : Set Q)ᶜ :=
      fun h ↦ hne (mem_singleton_iff.mpr (mem_singleton_iff.mp h).symm)
    obtain ⟨V, hV⟩ := hSmall _ (isOpen_compl_singleton.mem_nhds h1y)
    have hyV := isPreconnected_connectedComponent.subset_isClopen V.isClopen
      ⟨1, mem_connectedComponent, V.one_mem⟩ hy
    exact (hV hyV) (mem_singleton y)
  have hOne : IsOpen ({1} : Set Q) := hComponent ▸ isOpen_connectedComponent
  have hkOpen : IsOpen (k : Set G) := by
    rw [← lcaDualAnnihilator_annihilator k hk.1, ← hker]
    exact hOne.preimage γ.continuous
  filter_upwards [hkOpen.mem_nhds k.one_mem] with u hu
  simpa only [mul_one] using hInv ⟨u, hu⟩ 1

end PrincipalValues

section IdelicExplicitFormula

/-- Paper: Theorem B.4.4.7, p. 623. Use the meromorphic continuation
from §3.2 to read off each zero's multiplicity in its norm-twist coordinate. -/
def explicitFormulaCompletedHeckeL (χ : U[F]) : ℂ → ℂ :=
  (completedHeckeL_exists_continuation χ).choose

/-- Paper: Theorem B.4.4.7, p. 623. The continued function is in
meromorphic normal form and agrees with the completed Euler product on the right half-plane. -/
theorem explicitFormulaCompletedHeckeL_spec (χ : U[F]) :
    MeromorphicNFOn (explicitFormulaCompletedHeckeL χ) univ ∧
      ∀ s : halfPlane, explicitFormulaCompletedHeckeL χ s = completedHeckeL χ s :=
  (completedHeckeL_exists_continuation χ).choose_spec

local notation "chartZeros(" τ ")" =>
  {z : {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL z.1.val) univ z.2}
local notation "zeroMultiplicity(" z ")" =>
  (MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (z).val.1.val) univ (z).val.2 : ℂ)
local notation "zeroCharacter(" z ")" => ideleClassNormTwist (z).val.1.val (z).val.2
local notation "classVolume" => (normOneIdeleClassTamagawaMeasure F univ).toReal
local notation "classMeasure" => ideleClassTamagawaMeasure F
local notation "classWeight(" g ", " a ")" =>
  ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (a : ℂ))
local notation "classMellinIntegrand(" f ", " c ", " a ")" =>
  (fun g : C[F] ↦ (f).val g * c g * classWeight(g, a))
local notation "finiteClassMap(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "infiniteClassMap(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w

-- TODO(paper-gap): The printed sum omits zero multiplicity. In (B.4.4.16)
-- the corrected archimedean Fourier pairing is already canonically normalized.
-- The proof on p. 625 also needs the norm-one volume divisor in D(φ) and
-- a comparison of the Mellin local terms with the principal values (footnote 27).
-- For (B.4.4.22), compact norm support handles nonunit shells at large primes.
-- Invariance under the local units at almost every prime makes the unit-shell test constant.

/-- Paper: Theorem B.4.4.7, pp. 623–626. The sum over completed Hecke zeros
equals the pole distributions minus the local principal value distributions.
The zero and finite-place series converge in the strong dual of the test space.
Deviation: A norm section indexes each quasi-character once, the signed formula
counts zero multiplicity, and the archimedean pairing already uses canonical
Haar normalization. -/
theorem idelicExplicitFormula (τ : ℝ≥0ˣ →ₜ* C[F]) (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ (spectral : chartZeros(τ) → StrongDual ℂ (𝒟(C[F])))
      (poles : StrongDual ℂ (𝒟(C[F])))
      (arch : InfinitePlace F → StrongDual ℂ (𝒟(C[F])))
      (finite : Primes(F) → StrongDual ℂ (𝒟(C[F]))),
      (∀ z f, spectral z f = zeroMultiplicity(z) / (classVolume : ℂ) *
        ∫ g, classMellinIntegrand(f, zeroCharacter(z), -1 / 2) g ∂classMeasure) ∧
      (∀ f, poles f =
        ((∫ g, f.val g * classWeight(g, -1 / 2) ∂classMeasure) +
          (∫ g, f.val g * classWeight(g, 1 / 2) ∂classMeasure)) / (classVolume : ℂ)) ∧
      (∀ w f, ∃ test : 𝒟(w.Completionˣ),
        (∀ u, test.val u = f.val (infiniteClassMap(w) u)) ∧
        arch w f = infiniteConnesWeilPrincipalValue w test) ∧
      (∀ v f, ∃ test : 𝒟((v.adicCompletion F)ˣ),
        (∀ u, test.val u = f.val (finiteClassMap(v) u)) ∧
        finite v f = finiteWeilScale(v) * finiteConnesWeilPrincipalValue v 1 test) ∧
      (∀ f, Summable (fun z ↦ ‖spectral z f‖)) ∧
      (∀ f, (Function.support (fun v ↦ finite v f)).Finite) ∧
      Summable finite ∧
      HasSum spectral (poles - (∑ w, arch w) - (∑' v, finite v)) := by sorry

-- TODO(paper-gap): Discreteness in each component imposes no bound on
-- the number of points in consecutive height intervals, even for G = ℝ₊ˣ.
-- In (B.4.4.18), c(τ(t)) already equals t^s. Use this radial character once.

section BruhatMellinPolynomialCount

/-- The model series `1/1^2 + 1/2^2 + ...` has partial sums bounded by two. -/
private theorem summable_bruhatMellin_of_polynomialCount_sum_inv_sq_range (n : ℕ) :
    ∑ t ∈ Finset.range n, (((t : ℝ) + 1) ^ 2)⁻¹ ≤ 2 := by
  have key : ∀ m : ℕ,
      ∑ t ∈ Finset.range m, (((t : ℝ) + 1) ^ 2)⁻¹ ≤ 2 - (m : ℝ)⁻¹ := by
    intro m
    induction m with
    | zero => norm_num
    | succ p ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos p with hp0 | hp
      · subst hp0
        norm_num
      · have hstep : (((p : ℝ) + 1) ^ 2)⁻¹ ≤ (p : ℝ)⁻¹ - ((p : ℝ) + 1)⁻¹ := by
          have h1 : (p : ℝ) ≠ 0 := by positivity
          have h2 : (p : ℝ) + 1 ≠ 0 := by positivity
          field_simp
          nlinarith
        have hcast : ((p + 1 : ℕ) : ℝ)⁻¹ = ((p : ℝ) + 1)⁻¹ := by
          push_cast
          ring
        rw [hcast]
        linarith
  exact (key n).trans (by
    have : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    linarith)

/-- Absorbing polynomial growth into the quadratic decay. -/
private theorem summable_bruhatMellin_of_polynomialCount_pow_add_div_pow (x : ℝ) (hx : 1 ≤ x)
    (k : ℕ) : (x + 1) ^ k / x ^ (k + 2) ≤ (2 : ℝ) ^ k / x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have habs : (x + 1) ^ k ≤ (2 : ℝ) ^ k * x ^ k := by
    have hle : x + 1 ≤ 2 * x := by linarith
    calc (x + 1) ^ k ≤ (2 * x) ^ k := pow_le_pow_left₀ (by linarith) hle k
      _ = (2 : ℝ) ^ k * x ^ k := mul_pow _ _ _
  have hxp : (0 : ℝ) < x ^ (k + 2) := pow_pos hx0 _
  have hx2 : (0 : ℝ) < x ^ 2 := pow_pos hx0 2
  rw [div_le_div_iff₀ hxp hx2]
  calc (x + 1) ^ k * x ^ 2 ≤ ((2 : ℝ) ^ k * x ^ k) * x ^ 2 :=
        mul_le_mul_of_nonneg_right habs (le_of_lt hx2)
    _ = (2 : ℝ) ^ k * x ^ (k + 2) := by rw [pow_add]; ring

/-- An inverse power decreases when the base increases. -/
private theorem summable_bruhatMellin_of_polynomialCount_mul_inv_pow_le {K x t : ℝ} (hK : 0 ≤ K)
    (ht : 0 < t) (htx : t ≤ x) (k : ℕ) : K / x ^ (k + 1) ≤ K / t ^ (k + 1) := by
  have hx : (0 : ℝ) < x := lt_of_lt_of_le ht htx
  have hmono : t ^ (k + 1) ≤ x ^ (k + 1) := pow_le_pow_left₀ (le_of_lt ht) htx _
  have htp : (0 : ℝ) < t ^ (k + 1) := pow_pos ht _
  have hxp : (0 : ℝ) < x ^ (k + 1) := pow_pos hx _
  rw [div_le_div_iff₀ hxp htp]
  calc K * t ^ (k + 1) ≤ K * x ^ (k + 1) := mul_le_mul_of_nonneg_left hmono hK
    _ = K * x ^ (k + 1) := rfl

/-- Paper: Lemma B.4.4.8, p. 624. Counting the level sets of the height
`max |Im s| (max_j |n_j|)` polynomially and having quadratic decay in that height
forces summability. This is the combinatorial half of Lemma B.4.4.8. -/
private theorem summable_bruhatMellin_of_polynomialCount_of_polyCount_decay
    {ι : Type*} (m : ι → ℝ) (hm : ∀ z, 0 ≤ m z) (C k : ℕ) (K : ℝ) (hK : 0 ≤ K)
    (g : ι → ℝ)
    (hcount : ∀ T : ℕ, {z : ι | m z ≤ (T : ℝ)}.encard ≤ ((C * (T + 1) ^ k : ℕ) : ℕ∞))
    (hdecay : ∀ z, ‖g z‖ ≤ K / (1 + m z) ^ (k + 2)) :
    Summable g := by
  classical
  set S : ι → ℕ := fun z => Nat.ceil (m z) with hSdef
  have hSle (z : ι) : m z ≤ (S z : ℝ) := Nat.le_ceil (m z)
  have hmzle : ∀ {z : ι} {t : ℕ}, S z = t → m z ≤ (t : ℝ) := by
    intro z t hz
    calc m z ≤ (S z : ℝ) := hSle z
      _ = (t : ℝ) := by rw [hz]
  have hfin : ∀ T : ℕ, {z : ι | S z ≤ T}.Finite := by
    intro T
    exact Set.finite_of_encard_le_coe
      ((Set.encard_mono fun z hz => (hSle z).trans (by exact_mod_cast hz)).trans (hcount T))
  have hcard : ∀ t : ℕ, {z : ι | S z = t}.encard ≤ ((C * (t + 1) ^ k : ℕ) : ℕ∞) := by
    intro t
    have hsub : {z : ι | S z = t} ⊆ {z : ι | m z ≤ (t : ℝ)} := by
      intro z hz
      exact hmzle hz
    exact (Set.encard_mono hsub).trans (hcount t)
  have hfibercard : ∀ (t : ℕ) (u : Finset ι), (∀ z ∈ u, S z = t) →
      (u.card : ℝ) ≤ (C : ℝ) * (t + 1) ^ k := by
    intro t u hu
    have hcoe : ((u.card : ℕ) : ℕ∞) = (u : Set ι).encard :=
      (Set.encard_coe_eq_coe_finsetCard u).symm
    have hle : (u : Set ι).encard ≤ {z : ι | S z = t}.encard :=
      Set.encard_mono fun z hz => hu z hz
    have hnat : u.card ≤ C * (t + 1) ^ k := by
      have : ((u.card : ℕ) : ℕ∞) ≤ ((C * (t + 1) ^ k : ℕ) : ℕ∞) := by
        rw [hcoe]
        exact hle.trans (hcard t)
      exact_mod_cast this
    exact_mod_cast hnat
  -- decay of one term, with the level value in the base
  have hterm : ∀ (t : ℕ) (z : ι), S z = t → ‖g z‖ ≤ K / (max (t : ℝ) 1) ^ (k + 2) := by
    intro t z hz
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · have hmz : m z = 0 := le_antisymm (by simpa [ht0] using hmzle hz) (hm z)
      have hmax : max (t : ℝ) 1 = 1 := by simp [ht0]
      have hthis := hdecay z
      rw [hmax] at ⊢
      simp only [hmz, add_zero, one_pow, div_one] at hthis ⊢
      exact hthis
    · have ht1 : (1 : ℝ) ≤ (t : ℝ) := by
        exact_mod_cast htpos
      have hmax : max (t : ℝ) 1 = (t : ℝ) := max_eq_left ht1
      have hmet : ((t : ℝ) - 1) < m z := by
        by_contra hcon
        have hcon' : m z ≤ (t : ℝ) - 1 := not_lt.mp hcon
        have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
          push_cast [show 1 ≤ t from htpos]
          ring
        have hle : S z ≤ t - 1 := by
          rw [hSdef]
          exact Nat.ceil_le.mpr (by rw [hcast]; exact hcon')
        omega
      have htm : (t : ℝ) ≤ 1 + m z := by linarith
      have htpos' : (0 : ℝ) < (t : ℝ) := by linarith
      rw [hmax]
      exact (hdecay z).trans
        (summable_bruhatMellin_of_polynomialCount_mul_inv_pow_le hK htpos' htm (k + 1))
  -- the contribution of one level
  have hshell : ∀ (t : ℕ) (u : Finset ι), (∀ z ∈ u, S z = t) →
      ∑ z ∈ u, ‖g z‖ ≤ (C : ℝ) * K * (2 : ℝ) ^ k * 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by
    intro t u hu
    have hcard' := hfibercard t u hu
    have hC : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg _
    have hCK : (0 : ℝ) ≤ (C : ℝ) * K := mul_nonneg hC hK
    have hnn : (0 : ℝ) ≤ K / (max (t : ℝ) 1) ^ (k + 2) :=
      div_nonneg hK (by positivity)
    have hsum : ∑ z ∈ u, ‖g z‖ ≤ (u.card : ℝ) * (K / (max (t : ℝ) 1) ^ (k + 2)) := by
      calc ∑ z ∈ u, ‖g z‖ ≤ ∑ _z ∈ u, (K / (max (t : ℝ) 1) ^ (k + 2)) :=
            Finset.sum_le_sum (fun z hz => hterm t z (hu z hz))
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos t with ht0 | htpos
    · have hmax : max (t : ℝ) 1 = 1 := by simp [ht0]
      have hcard0 : (u.card : ℝ) ≤ (C : ℝ) := by simpa [ht0] using hcard'
      have h1 : ∑ z ∈ u, ‖g z‖ ≤ (C : ℝ) * K := by
        calc ∑ z ∈ u, ‖g z‖ ≤ (u.card : ℝ) * (K / (max (t : ℝ) 1) ^ (k + 2)) := hsum
          _ = (u.card : ℝ) * K := by rw [hmax]; norm_num
          _ ≤ (C : ℝ) * K := mul_le_mul_of_nonneg_right hcard0 hK
      refine h1.trans ?_
      rw [show (C : ℝ) * K * (2 : ℝ) ^ k * 4 * (((t : ℝ) + 1) ^ 2)⁻¹
          = (C : ℝ) * K * ((2 : ℝ) ^ k * 4) by rw [ht0]; ring]
      have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ k * 4 := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        linarith
      calc (C : ℝ) * K = (C : ℝ) * K * 1 := by ring
        _ ≤ (C : ℝ) * K * ((2 : ℝ) ^ k * 4) := mul_le_mul_of_nonneg_left h4 hCK
    · have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast htpos
      have hmax : max (t : ℝ) 1 = (t : ℝ) := max_eq_left ht1
      have hstep : ((t : ℝ) + 1) ^ k / (t : ℝ) ^ (k + 2) ≤ (2 : ℝ) ^ k / (t : ℝ) ^ 2 :=
        summable_bruhatMellin_of_polynomialCount_pow_add_div_pow (t : ℝ) ht1 k
      have h4 : ((t : ℝ) ^ 2)⁻¹ ≤ 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by
        have h1 : ((t : ℝ) + 1) ^ 2 * ((t : ℝ) ^ 2)⁻¹ ≤ 4 := by
          rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg ((t : ℝ) - 1)]
        have hq' : (0 : ℝ) ≤ (((t : ℝ) + 1) ^ 2)⁻¹ := by positivity
        calc ((t : ℝ) ^ 2)⁻¹
            = (((t : ℝ) + 1) ^ 2)⁻¹ * (((t : ℝ) + 1) ^ 2 * ((t : ℝ) ^ 2)⁻¹) := by
              field_simp
          _ ≤ (((t : ℝ) + 1) ^ 2)⁻¹ * 4 := mul_le_mul_of_nonneg_left h1 hq'
          _ = 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by ring
      have hnn' : (0 : ℝ) ≤ K / (t : ℝ) ^ (k + 2) :=
        div_nonneg hK (by positivity)
      calc ∑ z ∈ u, ‖g z‖ ≤ (u.card : ℝ) * (K / (max (t : ℝ) 1) ^ (k + 2)) := hsum
        _ = (u.card : ℝ) * (K / (t : ℝ) ^ (k + 2)) := by rw [hmax]
        _ ≤ ((C : ℝ) * ((t : ℝ) + 1) ^ k) * (K / (t : ℝ) ^ (k + 2)) :=
            mul_le_mul_of_nonneg_right hcard' hnn'
        _ = (C : ℝ) * K * (((t : ℝ) + 1) ^ k / (t : ℝ) ^ (k + 2)) := by ring
        _ ≤ (C : ℝ) * K * ((2 : ℝ) ^ k / (t : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hstep hCK
        _ = (C : ℝ) * K * (2 : ℝ) ^ k * ((t : ℝ) ^ 2)⁻¹ := by
            rw [div_eq_mul_inv]
            ring
        _ ≤ (C : ℝ) * K * (2 : ℝ) ^ k * (4 * (((t : ℝ) + 1) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = (C : ℝ) * K * (2 : ℝ) ^ k * 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by ring
  -- assemble
  have hbound : ∀ u : Finset ι, ∑ z ∈ u, ‖g z‖ ≤ (C : ℝ) * K * (2 : ℝ) ^ k * 8 := by
    intro u
    set T := u.sup S with hTdef
    have hTu : ∀ z ∈ u, S z ≤ T := fun z hz => Finset.le_sup (f := S) hz
    have hbox : u ⊆ (hfin T).toFinset := by
      intro z hz
      rw [Set.Finite.mem_toFinset]
      exact hTu z hz
    have hmaps : ∀ z ∈ (hfin T).toFinset, S z ∈ Finset.range (T + 1) := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le hz
    have step1 : ∑ z ∈ u, ‖g z‖ ≤ ∑ z ∈ (hfin T).toFinset, ‖g z‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hbox (fun _ _ _ => norm_nonneg _)
    have step2 : ∑ z ∈ (hfin T).toFinset, ‖g z‖
        = ∑ t ∈ Finset.range (T + 1),
            ∑ z ∈ (hfin T).toFinset.filter (fun z => S z = t), ‖g z‖ :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    have step3 : ∑ t ∈ Finset.range (T + 1),
          ∑ z ∈ (hfin T).toFinset.filter (fun z => S z = t), ‖g z‖
        ≤ ∑ t ∈ Finset.range (T + 1),
            (C : ℝ) * K * (2 : ℝ) ^ k * 4 * (((t : ℝ) + 1) ^ 2)⁻¹ := by
      refine Finset.sum_le_sum (fun t _ => ?_)
      exact hshell t _ (fun z hz => (Finset.mem_filter.mp hz).2)
    refine (step1.trans (step2.le.trans step3)).trans ?_
    rw [← Finset.mul_sum]
    have h0 : (0 : ℝ) ≤ (C : ℝ) * K * (2 : ℝ) ^ k * 4 := by positivity
    calc (C : ℝ) * K * (2 : ℝ) ^ k * 4 *
          ∑ t ∈ Finset.range (T + 1), (((t : ℝ) + 1) ^ 2)⁻¹
        ≤ (C : ℝ) * K * (2 : ℝ) ^ k * 4 * 2 :=
          mul_le_mul_of_nonneg_left
            (summable_bruhatMellin_of_polynomialCount_sum_inv_sq_range (T + 1)) h0
      _ = (C : ℝ) * K * (2 : ℝ) ^ k * 8 := by ring
  exact Summable.of_norm (summable_of_sum_le (fun z => norm_nonneg _) hbound)

/-- Paper: Lemma B.4.4.8, p. 624. On a bounded vertical strip, the Mellin evaluation of
compactly supported Bruhat test is dominated by any inverse power of the joint height
`max |Im s| (max_j |n_j|)`, with a constant that depends on the test and on the strip.
This is the analytic half of Lemma B.4.4.8: it is the standard smoothing estimate for the
Mellin transform of a compactly supported test, applied in the `t` coordinate and in each
torus coordinate of the product presentation `e`, and it carries no counting hypothesis. -/
private theorem summable_bruhatMellin_of_polynomialCount_decay
    {G A : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {d : ℕ} (e : G ≃ₜ* (ℝ≥0ˣ × (Fin d → Circle) × A))
    (μ : Measure G) [μ.IsHaarMeasure]
    (a b : ℝ) (N : ℕ) (f : 𝒟(G)) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ × (Fin d → ℤ) × PontryaginDual A, z.1.re ∈ Icc a b →
      ‖∫ g, f.val g *
        (((e g).1.val : ℝ) : ℂ) ^ z.1 *
        (∏ j : Fin d, (((e g).2.1 j : Circle) : ℂ) ^ z.2.1 j) *
        (z.2.2 (e g).2.2 : ℂ) ∂μ‖ ≤
      K / (1 + max |z.1.im|
        ((Finset.univ.sup (fun j : Fin d => (z.2.1 j).natAbs) : ℕ) : ℝ)) ^ N := by
  sorry

end BruhatMellinPolynomialCount

/-- Paper: Lemma B.4.4.8, p. 624. Compactly supported Bruhat tests have
absolutely summable Mellin evaluations on polynomially counted samples in
a bounded strip of the quasi-character space of a real-modulated abelian Lie group.
Deviation: The joint counting bound includes both vertical height and torus
frequency, and uses a common strip. A product coordinate displays the compact
kernel as a torus times a finite abelian group. -/
theorem summable_bruhatMellin_of_polynomialCount
    {G A : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [CommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    {d : ℕ} (e : G ≃ₜ* (ℝ≥0ˣ × (Fin d → Circle) × A))
    (μ : Measure G) [μ.IsHaarMeasure]
    (Z : Set (ℂ × (Fin d → ℤ) × PontryaginDual A))
    (a b : ℝ) (_hStrip : ∀ z ∈ Z, z.1.re ∈ Icc a b)
    (_hCount : ∃ C k : ℕ, ∀ T : ℕ,
      {z ∈ Z | |z.1.im| ≤ T ∧ ∀ j, (z.2.1 j).natAbs ≤ T}.encard ≤
        ((C * (T + 1) ^ k : ℕ) : ℕ∞))
    (f : 𝒟(G)) :
    Summable (fun z : Z ↦ ‖∫ g, f.val g *
      (((e g).1.val : ℝ) : ℂ) ^ z.val.1 *
      (∏ j : Fin d, (((e g).2.1 j : Circle) : ℂ) ^ z.val.2.1 j) *
      (z.val.2.2 (e g).2.2 : ℂ) ∂μ‖) := by
  obtain ⟨C, k, hCount⟩ := _hCount
  obtain ⟨K, hK, hDecay⟩ :=
    summable_bruhatMellin_of_polynomialCount_decay e μ a b (k + 2) f
  set m : Z → ℝ := fun z => max |z.val.1.im|
    ((Finset.univ.sup (fun j : Fin d => (z.val.2.1 j).natAbs) : ℕ) : ℝ) with hmdef
  have hm : ∀ z : Z, 0 ≤ m z := by
    intro z
    rw [hmdef]
    exact (abs_nonneg _).trans (le_max_left _ _)
  refine summable_bruhatMellin_of_polynomialCount_of_polyCount_decay
    (g := fun z : Z => ‖∫ g, f.val g *
      (((e g).1.val : ℝ) : ℂ) ^ z.val.1 *
      (∏ j : Fin d, (((e g).2.1 j : Circle) : ℂ) ^ z.val.2.1 j) *
      (z.val.2.2 (e g).2.2 : ℂ) ∂μ‖)
    m hm C k K hK.le ?_ (hdecay := fun z => by
      rw [hmdef]
      simpa using hDecay z.val (_hStrip z.val z.2))
  intro T
  have hset : Subtype.val '' {z : Z | m z ≤ (T : ℝ)} =
      {p : ℂ × (Fin d → ℤ) × PontryaginDual A |
        p ∈ Z ∧ |p.1.im| ≤ (T : ℝ) ∧ ∀ j, (p.2.1 j).natAbs ≤ T} := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, (le_max_left _ _).trans hz, fun j => ?_⟩
      have h2 : ((Finset.univ.sup (fun j : Fin d => (z.val.2.1 j).natAbs) : ℕ) : ℝ) ≤ (T : ℝ) :=
        (le_max_right _ _).trans hz
      have h3 : (Finset.univ.sup (fun j : Fin d => (z.val.2.1 j).natAbs) : ℕ) ≤ T :=
        by exact_mod_cast h2
      exact (Finset.le_sup (f := fun j : Fin d => (z.val.2.1 j).natAbs)
        (Finset.mem_univ j)).trans h3
    · rintro ⟨hpZ, him, hn⟩
      refine ⟨⟨p, hpZ⟩, ?_, rfl⟩
      change max |p.1.im| ((Finset.univ.sup (fun j : Fin d => (p.2.1 j).natAbs) : ℕ) : ℝ)
        ≤ (T : ℝ)
      rw [max_le_iff]
      refine ⟨him, ?_⟩
      have h3 : (Finset.univ.sup (fun j : Fin d => (p.2.1 j).natAbs) : ℕ) ≤ T :=
        Finset.sup_le fun j _ => hn j
      exact_mod_cast h3
  calc {z : Z | m z ≤ (T : ℝ)}.encard
      = (Subtype.val '' {z : Z | m z ≤ (T : ℝ)}).encard :=
        (Subtype.val_injective.injOn.encard_image).symm
    _ = {p : ℂ × (Fin d → ℤ) × PontryaginDual A |
          p ∈ Z ∧ |p.1.im| ≤ (T : ℝ) ∧ ∀ j, (p.2.1 j).natAbs ≤ T}.encard := by rw [hset]
    _ = {z ∈ Z | |z.1.im| ≤ T ∧ ∀ j, (z.2.1 j).natAbs ≤ T}.encard := by congr 1
    _ ≤ _ := hCount T

private theorem summable_ideleClassMellin_completedHeckeZeros_weight
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (f : 𝒟(G)) (b : ℝ) :
    ∃ f' : 𝒟(G), ∀ g, f'.val g = (((m g).val : ℝ) : ℂ) ^ (b : ℂ) * f.val g := by
  have hS : modulationWeight m b f.val ∈ schwartzBruhatSubmodule G :=
    modulationWeight_mem_schwartzBruhat m univ ⟨b, mem_univ _⟩
      ⟨f.val, bruhatCompactSupport_le_modulatedExponentialDecay m univ hm hms f.property⟩
  refine ⟨⟨modulationWeight m b f.val, (mem_bruhatSmoothSubmodule_iff _).2
    (schwartzBruhat_isBruhatSmooth (G := G) ⟨_, hS⟩), f.property.2.mul_left⟩, ?_⟩
  intro g
  change ((((m g).val : ℝ) ^ b : ℝ) : ℂ) * f.val g = _
  rw [Complex.ofReal_cpow (m g).val.coe_nonneg]

-- TODO(paper-gap): On p. 625, passing to a Lie quotient eliminates other kernel
-- characters. A uniform zero count with multiplicity for the remaining characters
-- is still needed to apply the corrected Lemma B.4.4.8.

/-- Paper: Lemma B.4.4.9, pp. 624–625. Mellin evaluations on any subset
of the completed Hecke zeros are absolutely summable after a real norm twist.
Deviation: Norm-section coordinates list the zeros once, and the weight also
counts their multiplicities as needed in the explicit formula. -/
theorem summable_ideleClassMellin_completedHeckeZeros (τ : ℝ≥0ˣ →ₜ* C[F])
    (_hτ : RightInverse τ (ideleClassNorm F)) (Z : Set (chartZeros(τ)))
    (f : 𝒟(C[F])) (a : ℝ) :
    Summable (fun z : Z ↦ ‖zeroMultiplicity(z.val) *
      ∫ g, classMellinIntegrand(f, zeroCharacter(z.val), (a : ℂ)) g ∂classMeasure‖) := by
  -- Absorb the shift from the centered exponent of the idelic explicit formula into the test.
  obtain ⟨m, hmNorm, hm, hms⟩ := exists_ideleClassModulation F
  obtain ⟨f', h'⟩ := summable_ideleClassMellin_completedHeckeZeros_weight
    (G := C[F]) m hm hms f (a + 1 / 2)
  have hw (g : C[F]) : f'.val g * classWeight(g, -1 / 2) = f.val g * classWeight(g, (a : ℂ)) := by
    have hx : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    rw [h', show m g = ideleClassNorm F g from DFunLike.congr_fun hmNorm g, mul_comm _ (f.val g),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    push_cast
    ring_nf
  have hvol : 0 < classVolume := by
    rw [normOneIdeleClassTamagawaMeasure_volume]
    have := NumberField.classNumber_pos F
    have := NumberField.Units.regulator_pos F
    have := NumberField.Units.torsionOrder_pos F
    have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
    rw [ENNReal.toReal_ofReal (by positivity)]
    positivity
  -- Restrict the absolutely summable spectral family and undo its volume normalization.
  obtain ⟨S, _, _, _, hSval, _, _, _, hsum, _⟩ := idelicExplicitFormula τ _hτ
  refine (((hsum f').subtype (fun z ↦ z ∈ Z)).mul_left ‖(classVolume : ℂ)‖).congr fun z ↦ ?_
  change ‖(classVolume : ℂ)‖ * ‖S z.val f'‖ = _
  rw [← norm_mul, hSval]
  congr 1
  rw [← mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hvol.ne')]
  congr 1
  apply integral_congr_ae
  filter_upwards with g
  calc _ = (f'.val g * classWeight(g, -1 / 2)) * zeroCharacter(z.val) g := by ring
       _ = _ := by rw [hw]; ring

end IdelicExplicitFormula

end RiemannMasullo
