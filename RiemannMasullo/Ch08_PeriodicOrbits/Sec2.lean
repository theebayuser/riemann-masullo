module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Separation.GDelta
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # §8.2. Stack-theoretic periodic orbits and fixed points

The parameter `S` records the finite part of the paper's set of places. Every
infinite place is already included in `SAdeleRing`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain NumberField TopologicalSpace Topology
open scoped NNReal NumberField.AdeleRing

variable (F : Type*) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Aₛ" => SAdeleRing F S
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)
local notation "N₁" => MonoidHom.ker (ideleNorm F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point $e_v$ has zero at $v$
and one elsewhere. The index `none` denotes the ordinary base point 1. -/
def adeleOrbitBasepoint : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)) → 𝔸[F]
  | none => 1
  | some (.inl v) => AdeleRing.ofCompletion (𝓞 F) F v 0
  | some (.inr v) => AdeleRing.ofAdicCompletion (𝓞 F) F v 0

/-- Paper: Definition 8.2.0.1(1), p. 384. Coordinate formulas for the global base points. -/
theorem adeleOrbitBasepoint_coordinates :
    adeleOrbitBasepoint F none = 1 ∧
      (∀ v : InfinitePlace F,
        (adeleOrbitBasepoint F (some (.inl v))).1 v = 0 ∧
        (∀ w : InfinitePlace F, w ≠ v → (adeleOrbitBasepoint F (some (.inl v))).1 w = 1) ∧
        (adeleOrbitBasepoint F (some (.inl v))).2 = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
        (adeleOrbitBasepoint F (some (.inr v))).1 = 1 ∧
        (adeleOrbitBasepoint F (some (.inr v))).2 v = 0 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
          (adeleOrbitBasepoint F (some (.inr v))).2 w = 1) := by
  classical
  refine ⟨rfl, ?_, ?_⟩
  · intro v
    refine ⟨?_, ?_, rfl⟩
    · show Pi.mulSingle v (0 : v.Completion) v = 0
      exact Pi.mulSingle_eq_same v 0
    · intro w hw
      show Pi.mulSingle v (0 : v.Completion) w = 1
      exact Pi.mulSingle_eq_of_ne hw 0
  · intro v
    refine ⟨rfl, ?_, ?_⟩
    · show Pi.mulSingle v (0 : v.adicCompletion F) v = 0
      exact Pi.mulSingle_eq_same v 0
    · intro w hw
      show Pi.mulSingle v (0 : v.adicCompletion F) w = 1
      exact Pi.mulSingle_eq_of_ne hw 0

/-- Paper: Definition 8.2.0.1(1), p. 384. The S-local base points keep all infinite
places and the finite places in S. -/
def sAdeleOrbitBasepoint (i : Option (InfinitePlace F ⊕ S)) : Aₛ :=
  adeleProjection F S (adeleOrbitBasepoint F (i.map (Sum.map id Subtype.val)))

/-- Paper: Definition 8.2.0.1(1), p. 384. The base point at a selected finite place
has zero at that place, including after projection to the S-adeles. -/
theorem sAdeleOrbitBasepoint_finite (v : S) :
    (sAdeleOrbitBasepoint F S (some (.inr v))).2 v = 0 := by
  exact ((adeleOrbitBasepoint_coordinates F).2.2 v.val).2.1

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_{F,S}$ in (8.2.0.1)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def sAdeleOrbitBasepoints : Set Aₛ :=
  Set.range (sAdeleOrbitBasepoint F S)

/-- The index `none` gives the ordinary base point, since the projection is a ring hom. -/
private theorem sAdeleOrbitBasepoint_none : sAdeleOrbitBasepoint F S none = 1 := by
  simp [sAdeleOrbitBasepoint, adeleOrbitBasepoint]

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_{F,S}$. -/
theorem one_mem_sAdeleOrbitBasepoints : 1 ∈ sAdeleOrbitBasepoints F S :=
  ⟨none, sAdeleOrbitBasepoint_none F S⟩

/-- Paper: Definition 8.2.0.1(1), p. 384. The set $Z_F$ in (8.2.0.2)
consists of 1 and the single-zero base points, with the adelic subspace topology. -/
def adeleOrbitBasepoints : Set 𝔸[F] :=
  Set.range (adeleOrbitBasepoint F)

/-- Paper: Definition 8.2.0.1(1), p. 384. The ordinary base point lies in $Z_F$. -/
theorem one_mem_adeleOrbitBasepoints : 1 ∈ adeleOrbitBasepoints F := by
  sorry

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.3) consists of the
S-local full-idele orbits with their adelic subspace topologies. -/
def sAdeleFullOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit 𝕀ₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary S-local orbit consists of
the $S$-adeles that are units. -/
theorem mem_sAdeleFullOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbit F S none ↔ IsUnit x := by
  rw [sAdeleFullOrbit, sAdeleOrbitBasepoint_none F S, MulAction.mem_orbit_iff]
  simp only [Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩

/-- Paper: Definition 8.2.0.1(2), p. 384. The family in (8.2.0.4) consists of the
global full-idele orbits with their adelic subspace topologies. -/
def adeleFullOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) : Set 𝔸[F] :=
  MulAction.orbit 𝔸[F]ˣ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.1(2), p. 384. The ordinary global orbit consists of
the adeles that are units. -/
theorem mem_adeleFullOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbit F none ↔ IsUnit x := by
  have h1 : adeleOrbitBasepoint F none = 1 := rfl
  rw [adeleFullOrbit, h1, MulAction.mem_orbit_iff]
  simp only [Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, hu⟩

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local set $D_{F,S}$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def sAdeleFullOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleFullOrbit F S i

/-- Paper: Definition 8.2.0.1(3), p. 385. The S-local full-orbit union is the
set of translates of the special S-adeles by full ideles. -/
theorem mem_sAdeleFullOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleFullOrbitUnion F S ↔
      ∃ (g : 𝕀ₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  simp only [sAdeleFullOrbitUnion, Set.mem_iUnion, sAdeleFullOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

/-- Paper: Definition 8.2.0.1(3), p. 385. The global set $D_F$ in (8.2.0.5)
is the union of the full-idele orbits with the adelic subspace topology. -/
def adeleFullOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleFullOrbit F i

/-- Paper: Definition 8.2.0.1(3), p. 385. The global full-orbit union is the
set of translates of the special adeles by full ideles. -/
theorem mem_adeleFullOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleFullOrbitUnion F ↔
      ∃ (g : 𝔸[F]ˣ) (z : adeleOrbitBasepoints F), g • z.val = x := by
  simp only [adeleFullOrbitUnion, Set.mem_iUnion, adeleFullOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

-- Read the full-group stability sentence on p. 385 with (8.2.0.3)–(8.2.0.5).
-- The norm-one orbits in (8.2.0.6)–(8.2.0.8) are stable under the norm kernel.

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.6) consists of the
S-local norm-one orbits with their adelic subspace topologies. -/
def sAdeleNormOneOrbit (i : Option (InfinitePlace F ⊕ S)) : Set Aₛ :=
  MulAction.orbit Nₛ (sAdeleOrbitBasepoint F S i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary S-local norm-one orbit
is the image of the norm kernel in the S-adeles. -/
theorem mem_sAdeleNormOneOrbit_none_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbit F S none ↔
      ∃ g : 𝕀ₛ, sIdeleNorm F S g = 1 ∧ g.val = x := by
  rw [sAdeleNormOneOrbit, sAdeleOrbitBasepoint_none F S, MulAction.mem_orbit_iff]
  simp only [MulAction.subgroup_smul_def, Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, MonoidHom.mem_ker.mp g.property, hg⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, MonoidHom.mem_ker.mpr hg⟩, rfl⟩

/-- Paper: Definition 8.2.0.2(1), p. 385. The family in (8.2.0.7) consists of the
global norm-one orbits with their adelic subspace topologies. -/
def adeleNormOneOrbit (i : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) :
    Set 𝔸[F] :=
  MulAction.orbit N₁ (adeleOrbitBasepoint F i)

/-- Paper: Definition 8.2.0.2(1), p. 385. The ordinary global norm-one orbit is the
image of the norm kernel in the adeles. -/
theorem mem_adeleNormOneOrbit_none_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbit F none ↔ ∃ g : 𝔸[F]ˣ, ideleNorm F g = 1 ∧ g.val = x := by
  have h1 : adeleOrbitBasepoint F none = 1 := rfl
  rw [adeleNormOneOrbit, h1, MulAction.mem_orbit_iff]
  simp only [MulAction.subgroup_smul_def, Units.smul_def, smul_eq_mul, mul_one]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, MonoidHom.mem_ker.mp g.property, hg⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, MonoidHom.mem_ker.mpr hg⟩, rfl⟩

/-- Paper: Definition 8.2.0.2(2), p. 385. The S-local set $D^1_{F,S}$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def sAdeleNormOneOrbitUnion : Set Aₛ :=
  ⋃ i, sAdeleNormOneOrbit F S i

/-- Paper: Definition 8.2.0.2(2), p. 385. An S-adele lies in the union exactly when
it is a norm-one translate of a special S-adele. -/
theorem mem_sAdeleNormOneOrbitUnion_iff (x : Aₛ) :
    x ∈ sAdeleNormOneOrbitUnion F S ↔
      ∃ (g : Nₛ) (z : sAdeleOrbitBasepoints F S), g • z.val = x := by
  simp only [sAdeleNormOneOrbitUnion, Set.mem_iUnion, sAdeleNormOneOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

/-- Paper: Definition 8.2.0.2(2), p. 385. The global set $D^1_F$ in (8.2.0.8)
is the union of the norm-one orbits with the adelic subspace topology. -/
def adeleNormOneOrbitUnion : Set 𝔸[F] :=
  ⋃ i, adeleNormOneOrbit F i

/-- Paper: Definition 8.2.0.2(2), p. 385. An adele lies in the union exactly when
it is a norm-one translate of a special adele. -/
theorem mem_adeleNormOneOrbitUnion_iff (x : 𝔸[F]) :
    x ∈ adeleNormOneOrbitUnion F ↔
      ∃ (g : N₁) (z : adeleOrbitBasepoints F), g • z.val = x := by
  simp only [adeleNormOneOrbitUnion, Set.mem_iUnion, adeleNormOneOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨i, g, hg⟩
    exact ⟨g, ⟨_, i, rfl⟩, hg⟩
  · rintro ⟨g, ⟨_, i, rfl⟩, hg⟩
    exact ⟨i, g, hg⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The S-local orbit map applies the norm-one
idele to the given special S-adele. -/
def sAdeleNormOneOrbitMap (gz : Nₛ × sAdeleOrbitBasepoints F S) :
    sAdeleNormOneOrbitUnion F S :=
  ⟨gz.1 • gz.2.val, (mem_sAdeleNormOneOrbitUnion_iff F S _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(1), p. 385. The underlying S-adele of the orbit map
is given by the norm-one action. -/
theorem sAdeleNormOneOrbitMap_val (g : Nₛ) (z : sAdeleOrbitBasepoints F S) :
    (sAdeleNormOneOrbitMap F S (g, z)).val = g • z.val := by
  rfl

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map applies the norm-one
idele to the given special adele. -/
def adeleNormOneOrbitMap (gz : N₁ × adeleOrbitBasepoints F) : adeleNormOneOrbitUnion F :=
  ⟨gz.1 • gz.2.val, (mem_adeleNormOneOrbitUnion_iff F _).mpr ⟨gz.1, gz.2, rfl⟩⟩

/-- Paper: Lemma 8.2.0.3(2), p. 385. The underlying adele of the orbit map is
given by the norm-one action. -/
theorem adeleNormOneOrbitMap_val (g : N₁) (z : adeleOrbitBasepoints F) :
    (adeleNormOneOrbitMap F (g, z)).val = g • z.val := by
  rfl

/-- Paper: Lemma 8.2.0.3(1), p. 385. The adelic subspace topology on the S-local
norm-one orbit union is the quotient topology of the S-local orbit map. -/
theorem sAdeleNormOneOrbitMap_isQuotientMap : IsQuotientMap (sAdeleNormOneOrbitMap F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is continuous for the
adelic subspace topology on the target.
Deviation: The adelic subspace topology is coarser than the quotient topology.
The equality of topologies fails by ERRATA R12. -/
theorem adeleNormOneOrbitMap_continuous : Continuous (adeleNormOneOrbitMap F) := by
  refine Continuous.subtype_mk ?_ _
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

/-- Paper: Lemma 8.2.0.3(2), p. 385. Every point in the global norm-one orbit union
has a preimage under the orbit map. -/
theorem adeleNormOneOrbitMap_surjective : Surjective (adeleNormOneOrbitMap F) := by
  rintro ⟨x, hx⟩
  simp only [adeleNormOneOrbitUnion, Set.mem_iUnion] at hx
  obtain ⟨i, hi⟩ := hx
  simp only [adeleNormOneOrbit, MulAction.mem_orbit_iff] at hi
  obtain ⟨g, hg⟩ := hi
  exact ⟨(g, ⟨adeleOrbitBasepoint F i, Set.mem_range_self i⟩), Subtype.ext hg⟩

/-- The coordinates of a unit adele are nonzero. -/
private theorem adeleNormOneOrbitMap_isOpenQuotientMap_ne_zero (u : 𝔸[F]ˣ) :
    (∀ w : InfinitePlace F, u.val.1 w ≠ 0) ∧ ∀ w : HeightOneSpectrum (𝓞 F), u.val.2 w ≠ 0 := by
  constructor
  · intro w h
    have hc : u.val.1 w * u.inv.1 w = 1 := congrArg (fun a : 𝔸[F] ↦ a.1 w) u.val_inv
    rw [h, zero_mul] at hc
    exact zero_ne_one hc
  · intro w h
    have hc : u.val.2 w * u.inv.2 w = 1 := congrArg (fun a : 𝔸[F] ↦ a.2 w) u.val_inv
    rw [h, zero_mul] at hc
    exact zero_ne_one hc

/-- The coordinates of a base point are zero at its own place and one elsewhere. -/
private theorem adeleNormOneOrbitMap_isOpenQuotientMap_coord
    (k : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F))) :
    (∀ w : InfinitePlace F, (k = some (.inl w) → (adeleOrbitBasepoint F k).1 w = 0) ∧
      (k ≠ some (.inl w) → (adeleOrbitBasepoint F k).1 w = 1)) ∧
    ∀ w : HeightOneSpectrum (𝓞 F), (k = some (.inr w) → (adeleOrbitBasepoint F k).2 w = 0) ∧
      (k ≠ some (.inr w) → (adeleOrbitBasepoint F k).2 w = 1) := by
  classical
  rcases k with _ | v | v
  · exact ⟨fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩, fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩⟩
  · refine ⟨fun w ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩, fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩⟩
    · cases h
      exact Pi.mulSingle_eq_same (M := fun u : InfinitePlace F ↦ u.Completion) _ _
    · have hvw : w ≠ v := fun e ↦ h (e ▸ rfl)
      exact Pi.mulSingle_eq_of_ne (M := fun u : InfinitePlace F ↦ u.Completion) hvw _
  · refine ⟨fun w ↦ ⟨fun h ↦ (by cases h), fun _ ↦ rfl⟩, fun w ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
    · cases h
      exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v 0 v).trans (Pi.mulSingle_eq_same _ _)
    · have hvw : w ≠ v := fun e ↦ h (e ▸ rfl)
      exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v 0 w).trans
        (Pi.mulSingle_eq_of_ne hvw _)

/-- Two base points in the same idele orbit are equal. -/
private theorem adeleNormOneOrbitMap_isOpenQuotientMap_eq (u : 𝔸[F]ˣ)
    (i j : Option (InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)))
    (h : u • adeleOrbitBasepoint F i = adeleOrbitBasepoint F j) : i = j := by
  obtain ⟨hu1, hu2⟩ := adeleNormOneOrbitMap_isOpenQuotientMap_ne_zero F u
  have hco := adeleNormOneOrbitMap_isOpenQuotientMap_coord F
  have k1 : ∀ w, (adeleOrbitBasepoint F j).1 w = u.val.1 w * (adeleOrbitBasepoint F i).1 w :=
    fun w ↦ by rw [← h]; rfl
  have k2 : ∀ w, (adeleOrbitBasepoint F j).2 w = u.val.2 w * (adeleOrbitBasepoint F i).2 w :=
    fun w ↦ by rw [← h]; rfl
  rcases j with _ | w | w
  · rcases i with _ | v | v
    · rfl
    · exfalso
      have hc := k1 v
      rw [((hco none).1 v).2 (by simp), ((hco _).1 v).1 rfl, mul_zero] at hc
      exact one_ne_zero hc
    · exfalso
      have hc := k2 v
      rw [((hco none).2 v).2 (by simp), ((hco _).2 v).1 rfl, mul_zero] at hc
      exact one_ne_zero hc
  · have hc := k1 w
    rw [((hco _).1 w).1 rfl] at hc
    by_contra hne
    rw [((hco i).1 w).2 hne, mul_one] at hc
    exact hu1 w hc.symm
  · have hc := k2 w
    rw [((hco _).2 w).1 rfl] at hc
    by_contra hne
    rw [((hco i).2 w).2 hne, mul_one] at hc
    exact hu2 w hc.symm

/-- The saturation of an open set under the norm-one orbit relation is open. -/
private theorem adeleNormOneOrbitMap_isOpenQuotientMap_sat (U : Set (N₁ × adeleOrbitBasepoints F))
    (hU : IsOpen U) :
    IsOpen {p : N₁ × adeleOrbitBasepoints F | ∃ q ∈ U, q.1 • q.2.val = p.1 • p.2.val} := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨q, hqU, hqp⟩
  obtain ⟨i, hi⟩ := p.2.prop
  obtain ⟨j, hj⟩ := q.2.prop
  have hk : (p.1.val⁻¹ * q.1.val) • q.2.val = p.2.val := by
    rw [mul_smul]
    change p.1.val⁻¹ • (q.1 • q.2.val) = _
    rw [hqp]
    exact inv_smul_smul p.1.val _
  have hji : j = i := adeleNormOneOrbitMap_isOpenQuotientMap_eq F _ j i (by rw [hj, hi]; exact hk)
  have hq2 : q.2 = p.2 := Subtype.ext (by rw [← hj, ← hi, hji])
  have hfix := hk
  rw [hq2] at hfix
  rcases i with _ | pl
  · have h1 : ((p.1.val⁻¹ * q.1.val : 𝔸[F]ˣ) : 𝔸[F]) * 1 = 1 := by
      rw [← hi] at hfix
      exact hfix
    rw [mul_one] at h1
    have hpq : q = p := Prod.ext (Subtype.ext (inv_mul_eq_one.mp (Units.ext h1)).symm) hq2
    exact Filter.mem_of_superset (hU.mem_nhds (hpq ▸ hqU)) fun u hu ↦ ⟨u, hu, rfl⟩
  · obtain ⟨O, hOo, hpO, hOu⟩ : ∃ O : Set 𝔸[F], IsOpen O ∧ p.2.val ∈ O ∧
        ∀ y : adeleOrbitBasepoints F, y.val ∈ O → y = p.2 := by
      rcases pl with w | w
      · refine ⟨{y | y.1 w ≠ 1},
          isOpen_ne_fun ((continuous_apply w).comp continuous_fst) continuous_const, ?_, ?_⟩
        · show (p.2.val).1 w ≠ 1
          rw [← hi, ((adeleNormOneOrbitMap_isOpenQuotientMap_coord F _).1 w).1 rfl]
          exact zero_ne_one
        · intro y hy
          obtain ⟨k, hk⟩ := y.prop
          have hy' : (adeleOrbitBasepoint F k).1 w ≠ 1 := by
            rw [hk]
            exact hy
          have hkw : k = some (.inl w) := by
            by_contra hne
            exact hy' (((adeleNormOneOrbitMap_isOpenQuotientMap_coord F k).1 w).2 hne)
          exact Subtype.ext (by rw [← hk, ← hi, hkw])
      · refine ⟨{y | y.2 w ≠ 1}, isOpen_ne_fun
          ((RestrictedProduct.continuous_eval w).comp continuous_snd) continuous_const, ?_, ?_⟩
        · show (p.2.val).2 w ≠ 1
          rw [← hi, ((adeleNormOneOrbitMap_isOpenQuotientMap_coord F _).2 w).1 rfl]
          exact zero_ne_one
        · intro y hy
          obtain ⟨k, hk⟩ := y.prop
          have hy' : (adeleOrbitBasepoint F k).2 w ≠ 1 := by
            rw [hk]
            exact hy
          have hkw : k = some (.inr w) := by
            by_contra hne
            exact hy' (((adeleNormOneOrbitMap_isOpenQuotientMap_coord F k).2 w).2 hne)
          exact Subtype.ext (by rw [← hk, ← hi, hkw])
    let k : N₁ := p.1⁻¹ * q.1
    have hcont : Continuous fun x : N₁ × adeleOrbitBasepoints F ↦ (x.1 * k, x.2) := by
      refine Continuous.prodMk ?_ continuous_snd
      refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
      show Continuous fun x : N₁ × adeleOrbitBasepoints F ↦ x.1.val * k.val
      exact (continuous_subtype_val.comp continuous_fst).mul continuous_const
    have hV : IsOpen ((fun x : N₁ × adeleOrbitBasepoints F ↦ (x.1 * k, x.2)) ⁻¹' U ∩
        {x | x.2.val ∈ O}) :=
      (hU.preimage hcont).inter (hOo.preimage (continuous_subtype_val.comp continuous_snd))
    refine Filter.mem_of_superset (hV.mem_nhds ⟨?_, hpO⟩) ?_
    · show (p.1 * k, p.2) ∈ U
      rw [show p.1 * k = q.1 from mul_inv_cancel_left p.1 q.1, ← hq2]
      exact hqU
    · rintro x ⟨hxU, hxO⟩
      have hx2 : x.2 = p.2 := hOu x.2 hxO
      refine ⟨(x.1 * k, x.2), hxU, ?_⟩
      change (x.1.val * k.val) • x.2.val = x.1.val • x.2.val
      rw [mul_smul, hx2, show (k : 𝔸[F]ˣ) • p.2.val = p.2.val from hfix]

/-- Paper: Lemma 8.2.0.3(2), p. 385. The global orbit map is an open quotient map
for its coinduced topology.
Deviation: The target carries the quotient topology of the global orbit map.
ERRATA R12 distinguishes this topology from the adelic subspace topology. -/
theorem adeleNormOneOrbitMap_isOpenQuotientMap :
    @IsOpenQuotientMap _ _ inferInstance
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance)
      (adeleNormOneOrbitMap F) := by
  refine @IsOpenQuotientMap.mk _ _ _
    (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance) (adeleNormOneOrbitMap F)
    (adeleNormOneOrbitMap_surjective F) continuous_coinduced_rng fun U hU ↦ ?_
  rw [isOpen_coinduced]
  convert adeleNormOneOrbitMap_isOpenQuotientMap_sat F U hU using 1
  ext p
  constructor
  · rintro ⟨q, hq, hqp⟩
    exact ⟨q, hq, congrArg Subtype.val hqp⟩
  · rintro ⟨q, hq, hqp⟩
    exact ⟨q, hq, Subtype.ext hqp⟩

/-- The S-adele ring is Hausdorff: it is a product of Hausdorff completions of `F`.
The instance has to be routed through the definition, exactly as in
`AppA_AlgebraicNT/Sec1.lean` (`adeleHausdorff_ideleLocallyCompact`). -/
private theorem t2Space_sAdeleRing : T2Space (SAdeleRing F S) := by
  change T2Space (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is Hausdorff. -/
theorem sAdeleNormOneOrbitUnion_t2Space : T2Space (sAdeleNormOneOrbitUnion F S) := by
  have := t2Space_sAdeleRing F S
  infer_instance

/-- The adele ring is Hausdorff: a product of the infinite part with the restricted
product of the finite part. The restricted product instance only fires after unfolding,
so it is written out (`Πʳ` is not in scope in this file). -/
private theorem t2Space_adeleRing : T2Space 𝔸[F] :=
  inferInstanceAs (T2Space (((w : InfinitePlace F) → w.Completion) ×
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite))

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is Hausdorff. -/
theorem adeleNormOneOrbitUnion_t2Space : T2Space (adeleNormOneOrbitUnion F) := by
  have := t2Space_adeleRing F
  infer_instance

/-- The S-adele ring is metrizable: a finite product of metrizable completions of `F`,
routed through the definition as for `t2Space_sAdeleRing`. -/
private theorem metrizableSpace_sAdeleRing : MetrizableSpace (SAdeleRing F S) := by
  change MetrizableSpace (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is metrizable. -/
theorem sAdeleNormOneOrbitUnion_metrizableSpace :
    MetrizableSpace (sAdeleNormOneOrbitUnion F S) := by
  have := metrizableSpace_sAdeleRing F S
  infer_instance

/-- The nonzero prime ideals of the ring of integers form a countable type: the ring is
countable, its ideals are finitely generated, and a height-one spectrum element is
determined by its underlying ideal. -/
private theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  haveI : Countable (𝓞 F) := RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact HeightOneSpectrum.asIdeal_injective.countable

/-- A restricted product over a countable index type, with open distinguished subsets,
is second countable: the pieces where the coordinates lie in the distinguished subsets
outside a fixed finite set form a countable open cover by second countable subspaces. -/
private theorem secondCountableTopology_restrictedProduct_cofinite
    {ι : Type*} [Countable ι] (R : ι → Type*) [∀ i, TopologicalSpace (R i)]
    [∀ i, SecondCountableTopology (R i)] (A : ∀ i, Set (R i))
    (hA : ∀ i, IsOpen (A i)) :
    SecondCountableTopology (RestrictedProduct R A Filter.cofinite) := by
  have hS (T : Finset ι) : Filter.cofinite ≤ Filter.principal ((T : Set ι)ᶜ) :=
    Filter.le_principal_iff.2 (T.finite_toSet.compl_mem_cofinite)
  haveI (T : Finset ι) : SecondCountableTopology
      (RestrictedProduct R A (Filter.principal ((T : Set ι)ᶜ))) :=
    RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  have he (T : Finset ι) : IsOpenEmbedding (RestrictedProduct.inclusion R A (hS T)) :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS T)
  haveI (T : Finset ι) : SecondCountableTopology
      (Set.range (RestrictedProduct.inclusion R A (hS T))) :=
    (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine secondCountableTopology_of_countable_cover (fun T => (he T).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hx : {i | ¬ x i ∈ A i}.Finite := Filter.eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, ?_⟩
  refine RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS _) ?_
  intro i hi
  by_contra h
  exact hi (by simpa [Set.Finite.mem_toFinset] using h)

/-- The finite adele ring is second countable: the local completions are proper metric
spaces, hence second countable, and the restricted product is taken over a countable
index with open integer subrings. -/
private theorem secondCountableTopology_finiteAdeleRing :
    SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Countable (HeightOneSpectrum (𝓞 F)) := countable_heightOneSpectrum F
  haveI (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) :=
    properSpace_adicCompletion v
  change SecondCountableTopology (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    Filter.cofinite)
  exact secondCountableTopology_restrictedProduct_cofinite
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun _ ↦ Valued.isOpen_valuationSubring _)

/-- The adele ring is metrizable. The infinite part is a finite product of metrizable
completions. The finite part is second countable and weakly locally compact (the integer
subrings are compact open), hence regular; with T0 this gives T3, and Urysohn's
metrization theorem applies. -/
private theorem metrizableSpace_adeleRing : MetrizableSpace 𝔸[F] := by
  haveI (v : HeightOneSpectrum (𝓞 F)) : ProperSpace (v.adicCompletion F) :=
    properSpace_adicCompletion v
  haveI (v : HeightOneSpectrum (𝓞 F)) : CompactSpace (v.adicCompletionIntegers F) :=
    compactSpace_adicCompletionIntegers v
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  haveI : SecondCountableTopology (RestrictedProduct
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite) :=
    secondCountableTopology_finiteAdeleRing F
  exact inferInstanceAs (MetrizableSpace (((w : InfinitePlace F) → w.Completion) ×
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) Filter.cofinite))

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is metrizable. -/
theorem adeleNormOneOrbitUnion_metrizableSpace : MetrizableSpace (adeleNormOneOrbitUnion F) := by
  have := metrizableSpace_adeleRing F
  infer_instance

/-- The S-adele ring is second countable: the archimedean completions embed isometrically
into `ℂ`, and the finite completions in `S` are proper metric spaces. -/
private theorem secondCountableTopology_sAdeleRing :
    SecondCountableTopology (SAdeleRing F S) := by
  change SecondCountableTopology (((w : InfinitePlace F) → w.Completion) × ((v : S) → (v.val.adicCompletion F)))
  haveI (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  haveI (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is second-countable. -/
theorem sAdeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (sAdeleNormOneOrbitUnion F S) := by
  have := secondCountableTopology_sAdeleRing F S
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is second-countable. -/
theorem adeleNormOneOrbitUnion_secondCountable :
    SecondCountableTopology (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is perfectly normal. -/
theorem sAdeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is perfectly normal. -/
theorem adeleNormOneOrbitUnion_perfectlyNormal :
    PerfectlyNormalSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is separable. -/
theorem sAdeleNormOneOrbitUnion_separableSpace : SeparableSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is separable. -/
theorem adeleNormOneOrbitUnion_separableSpace : SeparableSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is locally compact. -/
theorem sAdeleNormOneOrbitUnion_locallyCompactSpace :
    LocallyCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- The finite base points tend to `1` along the cofinite filter. They lie in the image
of the integral finite adeles, where the restricted product carries the product topology. -/
private theorem adeleNormOneOrbitUnion_locallyCompactSpace_tendsto :
    Filter.Tendsto (fun v ↦ adeleOrbitBasepoint F (some (.inr v))) Filter.cofinite (𝓝 1) := by
  classical
  have hx (v u : HeightOneSpectrum (𝓞 F)) :
      Pi.mulSingle (M := fun u : HeightOneSpectrum (𝓞 F) ↦ u.adicCompletion F) v 0 u ∈
        u.adicCompletionIntegers F := by
    by_cases h : u = v
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact zero_mem _
    · rw [Pi.mulSingle_eq_of_ne h]
      exact one_mem _
  let x : HeightOneSpectrum (𝓞 F) → (u : HeightOneSpectrum (𝓞 F)) →
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)) := fun v u ↦ ⟨_, hx v u⟩
  let x₁ : (u : HeightOneSpectrum (𝓞 F)) →
      (u.adicCompletionIntegers F : Set (u.adicCompletion F)) := fun u ↦ ⟨1, one_mem _⟩
  have hxt : Filter.Tendsto x Filter.cofinite (𝓝 x₁) := by
    refine tendsto_pi_nhds.mpr fun u ↦ tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_cofinite_ne u] with v hv
    exact Subtype.ext (Pi.mulSingle_eq_of_ne (Ne.symm hv) _).symm
  have hs := RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) ↦ v.adicCompletion F)
    (A := fun v ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)
  exact Prod.tendsto_iff _ _ |>.mpr ⟨tendsto_const_nhds, (hs.continuous.tendsto x₁).comp hxt⟩

/-- The set of base points is locally compact. It is compact, because the finite base
points tend to `1` and there are only finitely many infinite places. -/
private theorem adeleNormOneOrbitUnion_locallyCompactSpace_basepoints :
    LocallyCompactSpace (adeleOrbitBasepoints F) := by
  have := t2Space_adeleRing F
  have h1 :=
    (adeleNormOneOrbitUnion_locallyCompactSpace_tendsto F).isCompact_insert_range_of_cofinite
  have h2 :
      IsCompact (Set.range fun w : InfinitePlace F ↦ adeleOrbitBasepoint F (some (.inl w))) :=
    (Set.finite_range _).isCompact
  have hc : IsCompact (adeleOrbitBasepoints F) := by
    convert h1.union h2 using 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rcases i with _ | w | v
      · exact Or.inl (Set.mem_insert _ _)
      · exact Or.inr ⟨w, rfl⟩
      · exact Or.inl (Set.mem_insert_of_mem _ ⟨v, rfl⟩)
    · rintro ((rfl | ⟨v, rfl⟩) | ⟨w, rfl⟩)
      · exact ⟨none, rfl⟩
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  have := isCompact_iff_compactSpace.mp hc
  infer_instance

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is locally compact
in the quotient topology of the orbit map.
Deviation: The adelic subspace topology fails to be locally compact by ERRATA R13. -/
theorem adeleNormOneOrbitUnion_locallyCompactSpace :
    @LocallyCompactSpace (adeleNormOneOrbitUnion F)
      (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance) := by
  have := (ideleGroup_topology F).2.1
  have : LocallyCompactSpace N₁ := (ideleGroup_topology F).2.2.2.2.2.locallyCompactSpace
  have := adeleNormOneOrbitUnion_locallyCompactSpace_basepoints F
  exact @IsOpenQuotientMap.locallyCompactSpace _ _ _
    (TopologicalSpace.coinduced (adeleNormOneOrbitMap F) inferInstance) _ _
    (adeleNormOneOrbitMap_isOpenQuotientMap F)

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is σ-compact. -/
theorem sAdeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is σ-compact
in the adelic subspace topology. -/
theorem adeleNormOneOrbitUnion_sigmaCompactSpace :
    SigmaCompactSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The S-local norm-one orbit union is paracompact. -/
theorem sAdeleNormOneOrbitUnion_paracompactSpace :
    ParacompactSpace (sAdeleNormOneOrbitUnion F S) := by
  sorry

/-- Paper: Lemma 8.2.0.3, p. 385. The global norm-one orbit union is paracompact. -/
theorem adeleNormOneOrbitUnion_paracompactSpace : ParacompactSpace (adeleNormOneOrbitUnion F) := by
  sorry

/-- Paper: Proposition 8.2.0.4, p. 386. The subgroup of global ideles obtained by
inserting the units of the local valuation ring at the specified finite place. -/
def embeddedFiniteLocalUnits (v : HeightOneSpectrum (𝓞 F)) : Subgroup 𝔸[F]ˣ :=
  ((IdeleGroup.ofAdicCompletion (𝓞 F) F v).comp
    (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom)).range

/-- Paper: Proposition 8.2.0.4, p. 386. The inserted local units have norm one at
the specified place and value one at all other places. -/
theorem mem_embeddedFiniteLocalUnits_iff (v : HeightOneSpectrum (𝓞 F)) (g : 𝔸[F]ˣ) :
    g ∈ embeddedFiniteLocalUnits F v ↔
      g.val.1 = 1 ∧ ‖g.val.2 v‖ = 1 ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → g.val.2 w = 1 := by
  classical
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · change (AdeleRing.ofAdicCompletion (𝓞 F) F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val).1 = 1
      rw [AdeleRing.ofAdicCompletion_apply]
    · have h := FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val v
      have hval := h.trans (Pi.mulSingle_eq_same v _)
      refine (congrArg norm hval).trans ?_
      rw [Valued.toNormedField.norm_eq_one_iff]
      exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
        (K := F) (v := v)).mp u.isUnit
    · exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val w).trans
        (Pi.mulSingle_eq_of_ne (i := v) (i' := w) hw _)
  · rintro ⟨h1, h2, h3⟩
    let x : v.adicCompletion F := g.val.2 v
    have hxval : Valued.v x = 1 := Valued.toNormedField.norm_eq_one_iff.mp h2
    have hxne : x ≠ 0 :=
      (Valuation.ne_zero_iff Valued.v).mp (by rw [hxval]; exact one_ne_zero)
    have hxm : x ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hxval]
    have hxim : x⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hxval, inv_one]
    let u : (v.adicCompletionIntegers F)ˣ :=
      Units.mk ⟨x, hxm⟩ ⟨x⁻¹, hxim⟩
        (Subtype.ext (mul_inv_cancel₀ hxne)) (Subtype.ext (inv_mul_cancel₀ hxne))
    refine ⟨u, Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext F fun w => ?_))⟩
    · change (AdeleRing.ofAdicCompletion (𝓞 F) F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val).1 = g.val.1
      rw [AdeleRing.ofAdicCompletion_apply, h1]
    · refine (FiniteAdeleRing.ofAdicCompletion_apply_coe F v
        (Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u).val w).trans ?_
      obtain rfl | hw := eq_or_ne w v
      · exact Pi.mulSingle_eq_same _ _
      · rw [Pi.mulSingle_eq_of_ne hw, h3 w hw]

/-- Paper: Equation (8.2.0.9), p. 386. The S-local section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def sAdeleFiniteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) : Set Aₛ :=
  (fun t : ℝ≥0ˣ ↦ τ t • sAdeleOrbitBasepoint F S (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.val.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.9), p. 386. The included left endpoint gives the S-local
single-zero base point. -/
theorem sAdeleOrbitBasepoint_mem_finiteOrbitSection (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) :
    sAdeleOrbitBasepoint F S (some (.inr v)) ∈ sAdeleFiniteOrbitSection F S v τ := by
  sorry

/-- Paper: Equation (8.2.0.10), p. 386. The global section at a finite place takes
parameters in the half-open interval from 1 to the absolute prime ideal norm. -/
def adeleFiniteOrbitSection (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    Set 𝔸[F] :=
  (fun t : ℝ≥0ˣ ↦ τ t • adeleOrbitBasepoint F (some (.inr v))) ''
    {t | t.val ∈ Set.Ico 1 (v.asIdeal.absNorm : ℝ≥0)}

/-- Paper: Equation (8.2.0.10), p. 386. The included left endpoint gives the global
single-zero base point. -/
theorem adeleOrbitBasepoint_mem_finiteOrbitSection (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) :
    adeleOrbitBasepoint F (some (.inr v)) ∈ adeleFiniteOrbitSection F v τ := by
  sorry

/-- A uniformizer at a finite place, as a unit, with norm the reciprocal of the absolute norm. -/
private theorem sAdeleFiniteOrbit_transporter_uniformizer (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : (v.adicCompletion F)ˣ, ‖(π : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  exact ⟨Units.mk0 (π : v.adicCompletion F) hπ.ne_zero, norm_uniformizer_adicCompletion v _ hπ⟩

/-- The norm of a unit at a finite place is an integer power of the absolute norm. -/
private theorem sAdeleFiniteOrbit_transporter_norm_zpow (v : HeightOneSpectrum (𝓞 F))
    (y : (v.adicCompletion F)ˣ) :
    ∃ m : ℤ, ‖(y : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ) ^ m := by
  obtain ⟨π, hπ⟩ := sAdeleFiniteOrbit_transporter_uniformizer F v
  obtain ⟨e, he1, he2⟩ := finitePlace_unitDecomposition v π hπ
  let ι := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom
  have hy : y = π ^ (e y).1.toAdd * ι (e y).2 := by
    apply e.injective
    rw [map_mul, map_zpow, he1, he2]
    apply Prod.ext
    · show (e y).1 = Multiplicative.ofAdd (1 : ℤ) ^ (e y).1.toAdd * 1
      rw [mul_one, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
    · simp
  obtain ⟨m, u, hmu⟩ : ∃ (m : ℤ) (u : (v.adicCompletionIntegers F)ˣ), y = π ^ m * ι u :=
    ⟨_, _, hy⟩
  refine ⟨-m, ?_⟩
  have hu : ‖((ι u : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = 1 := by
    rw [Valued.toNormedField.norm_eq_one_iff]
    exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
      (K := F) (v := v)).mp u.isUnit
  rw [hmu, Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow, hπ, hu, mul_one,
    inv_zpow, zpow_neg]

/-- The idele inserted at a finite place has the norm of the inserted unit. -/
private theorem sAdeleFiniteOrbit_transporter_ideleNorm (v : HeightOneSpectrum (𝓞 F))
    (w : (v.adicCompletion F)ˣ) :
    ((ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v w) : ℝ≥0) : ℝ) =
      ‖(w : v.adicCompletion F)‖ := by
  classical
  rw [((ideleNorm_spec F).1 _).2]
  change (∏ u : InfinitePlace F, ‖(1 : u.Completion)‖ ^ u.mult) *
    (∏ᶠ u : HeightOneSpectrum (𝓞 F), ‖FiniteAdeleRing.ofAdicCompletion F v w.val u‖) = _
  simp only [norm_one, one_pow, Finset.prod_const_one, one_mul]
  rw [finprod_eq_single _ v (fun u hu ↦ by
    rw [show FiniteAdeleRing.ofAdicCompletion F v w.val u = 1 from
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ u).trans (Pi.mulSingle_eq_of_ne hu _),
      norm_one])]
  rw [show FiniteAdeleRing.ofAdicCompletion F v w.val v = w.val from
    (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ v).trans (Pi.mulSingle_eq_same _ _)]

/-- An S-idele fixes the S-local base point at a finite place of S exactly when it is the
projection of an idele inserted at that place. -/
private theorem sAdeleFiniteOrbit_transporter_smul (v : S) (g : (SAdeleRing F S)ˣ) :
    g • sAdeleOrbitBasepoint F S (some (.inr v)) = sAdeleOrbitBasepoint F S (some (.inr v)) ↔
      ∃ w : (v.val.adicCompletion F)ˣ, g = Units.map (adeleProjection F S).toMonoidHom
        (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w) := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    have h1 : g.val.1 = 1 := by
      have hc := congrArg Prod.fst h
      change g.val.1 * 1 = 1 at hc
      rwa [mul_one] at hc
    have h2 : ∀ u : S, u ≠ v → g.val.2 u = 1 := by
      intro u hu
      have hb : (sAdeleOrbitBasepoint F S (some (.inr v))).2 u = 1 :=
        (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val 0 u.val).trans
          (Pi.mulSingle_eq_of_ne (fun h ↦ hu (Subtype.ext h)) _)
      have hc : g.val.2 u * (sAdeleOrbitBasepoint F S (some (.inr v))).2 u =
          (sAdeleOrbitBasepoint F S (some (.inr v))).2 u :=
        congrArg (fun a : SAdeleRing F S ↦ a.2 u) h
      rwa [hb, mul_one] at hc
    let w : (v.val.adicCompletion F)ˣ := ⟨g.val.2 v, g.inv.2 v,
      congrArg (fun a : SAdeleRing F S ↦ a.2 v) g.val_inv,
      congrArg (fun a : SAdeleRing F S ↦ a.2 v) g.inv_val⟩
    refine ⟨w, Units.ext (Prod.ext h1 (funext fun u ↦ ?_))⟩
    refine Eq.trans ?_ (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val (g.val.2 v) u.val).symm
    obtain rfl | hu := eq_or_ne u v
    · rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne (fun h ↦ hu (Subtype.ext h)), h2 u hu]
  · rintro ⟨w, rfl⟩
    rw [Units.smul_def]
    change adeleProjection F S (AdeleRing.ofAdicCompletion (𝓞 F) F v.val w.val) *
        adeleProjection F S (AdeleRing.ofAdicCompletion (𝓞 F) F v.val 0) =
      adeleProjection F S (AdeleRing.ofAdicCompletion (𝓞 F) F v.val 0)
    rw [← map_mul, ← map_mul, mul_zero]

/-- The projection of an idele inserted at a finite place of S has the same S-norm as
global norm. -/
private theorem sAdeleFiniteOrbit_transporter_sIdeleNorm (v : S) (w : (v.val.adicCompletion F)ˣ) :
    sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom
      (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w)) =
      ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w) := by
  classical
  let A := integralAdelesOutside F S
  let s := IdeleGroup.ofAdicCompletion (𝓞 F) F v.val
  have hmem (y : (v.val.adicCompletion F)ˣ) : (s y).val ∈ A := by
    change (s y).val ∈ integralAdelesOutside F S
    delta integralAdelesOutside
    rw [Subring.mem_iInf]
    intro u
    rw [Subring.mem_iInf]
    intro hu
    have h1 : FiniteAdeleRing.ofAdicCompletion F v.val y.val u = 1 :=
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val _ u).trans
        (Pi.mulSingle_eq_of_ne (by rintro rfl; exact hu v.prop) _)
    change FiniteAdeleRing.ofAdicCompletion F v.val y.val u ∈ u.adicCompletionIntegers F
    rw [h1]
    exact (u.adicCompletionIntegers F).one_mem
  have ht : s w ∈ A.toSubmonoid.units :=
    ⟨hmem w, by
      change ((s w)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem w⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s w, ht⟩
  exact ((sIdeleNorm_spec F S).1 g).symm

/-- Two S-local norm-one transporters into the half-open section differ by the projection
of an embedded local unit. -/
private theorem sAdeleFiniteOrbit_transporter_unique (v : S) (τ : ℝ≥0ˣ →* (SAdeleRing F S)ˣ)
    (hsection : RightInverse τ (sIdeleNorm F S)) (x : SAdeleRing F S) (g h : Nₛ)
    (hg : g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ)
    (hh : h⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ) :
    g.val⁻¹ * h.val ∈ (embeddedFiniteLocalUnits F v.val).map
      (Units.map (adeleProjection F S).toMonoidHom) := by
  classical
  obtain ⟨t, ht, hgt⟩ := hg
  obtain ⟨t', ht', hht⟩ := hh
  dsimp only at hgt hht
  have e1 : (g.val * τ t) • sAdeleOrbitBasepoint F S (some (.inr v)) = x := by
    rw [mul_smul]
    change g.val • (τ t • sAdeleOrbitBasepoint F S (some (.inr v))) = x
    rw [hgt]
    exact smul_inv_smul g.val x
  have e2 : (h.val * τ t') • sAdeleOrbitBasepoint F S (some (.inr v)) = x := by
    rw [mul_smul]
    change h.val • (τ t' • sAdeleOrbitBasepoint F S (some (.inr v))) = x
    rw [hht]
    exact smul_inv_smul h.val x
  have hfix : ((g.val * τ t)⁻¹ * (h.val * τ t')) • sAdeleOrbitBasepoint F S (some (.inr v)) =
      sAdeleOrbitBasepoint F S (some (.inr v)) := by
    rw [mul_smul, e2, ← e1, inv_smul_smul]
  obtain ⟨w, hw⟩ := (sAdeleFiniteOrbit_transporter_smul F S v _).mp hfix
  have hgn : sIdeleNorm F S g.val = 1 := g.prop
  have hhn : sIdeleNorm F S h.val = 1 := h.prop
  have hN : ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w) = t⁻¹ * t' := by
    rw [← sAdeleFiniteOrbit_transporter_sIdeleNorm F S v w, ← hw, map_mul, map_inv, map_mul,
      map_mul, hgn, hhn, hsection t, hsection t', one_mul, one_mul]
  have hwn : ‖(w : v.val.adicCompletion F)‖ = ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := by
    rw [← sAdeleFiniteOrbit_transporter_ideleNorm F v.val w, hN, Units.val_mul,
      Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv, inv_mul_eq_div]
  have hq : (1 : ℝ) < v.val.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have ha1 : (1 : ℝ) ≤ ((t : ℝ≥0) : ℝ) := by exact_mod_cast ht.1
  have ha2 : ((t : ℝ≥0) : ℝ) < v.val.asIdeal.absNorm := by exact_mod_cast ht.2
  have hb1 : (1 : ℝ) ≤ ((t' : ℝ≥0) : ℝ) := by exact_mod_cast ht'.1
  have hb2 : ((t' : ℝ≥0) : ℝ) < v.val.asIdeal.absNorm := by exact_mod_cast ht'.2
  have ha0 : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := by linarith
  obtain ⟨m, hm⟩ := sAdeleFiniteOrbit_transporter_norm_zpow F v.val w
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hlt | heq | hgt'
    · exfalso
      have h1 : (v.val.asIdeal.absNorm : ℝ) ^ m ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_neg_one] at h1
      have h2 : (v.val.asIdeal.absNorm : ℝ)⁻¹ < ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) :=
        calc (v.val.asIdeal.absNorm : ℝ)⁻¹ = 1 / (v.val.asIdeal.absNorm : ℝ) := (one_div _).symm
          _ < 1 / ((t : ℝ≥0) : ℝ) := one_div_lt_one_div_of_lt ha0 ha2
          _ ≤ ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := div_le_div_of_nonneg_right hb1 ha0.le
      rw [← hwn, hm] at h2
      linarith
    · exact heq
    · exfalso
      have h1 : (v.val.asIdeal.absNorm : ℝ) ^ (1 : ℤ) ≤ (v.val.asIdeal.absNorm : ℝ) ^ m :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_one] at h1
      have h2 : ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) < v.val.asIdeal.absNorm :=
        lt_of_le_of_lt (div_le_self (by linarith) ha1) hb2
      rw [← hwn, hm] at h2
      linarith
  have hw1 : ‖(w : v.val.adicCompletion F)‖ = 1 := by rw [hm, hm0, zpow_zero]
  have htt : t' = t := by
    rw [hwn, div_eq_one_iff_eq ha0.ne'] at hw1
    exact Units.ext (NNReal.eq hw1)
  subst htt
  have hgh : g.val⁻¹ * h.val = Units.map (adeleProjection F S).toMonoidHom
      (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w) := by
    rw [← hw, mul_inv, mul_mul_mul_comm, inv_mul_cancel, mul_one]
  rw [hgh]
  refine ⟨IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_embeddedFiniteLocalUnits_iff]
  refine ⟨rfl, ?_, fun w' hw' ↦ ?_⟩
  · rw [show (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val w).val.2 v.val = w.val from
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val _ v.val).trans
        (Pi.mulSingle_eq_same _ _)]
    exact hw1
  · exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v.val _ w').trans
      (Pi.mulSingle_eq_of_ne hw' _)

/-- Every point of the full S-local orbit has a norm-one transporter into the half-open
section. -/
private theorem sAdeleFiniteOrbit_transporter_exists (v : S) (τ : ℝ≥0ˣ →* (SAdeleRing F S)ˣ)
    (hsection : RightInverse τ (sIdeleNorm F S)) (x : SAdeleRing F S)
    (hx : x ∈ sAdeleFullOrbit F S (some (.inr v))) :
    ∃ g : Nₛ, g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨π, hπ⟩ := sAdeleFiniteOrbit_transporter_uniformizer F v.val
  have hq : (1 : ℝ) < v.val.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hq0 : (0 : ℝ) < v.val.asIdeal.absNorm := by linarith
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (x := ((sIdeleNorm F S a : ℝ≥0) : ℝ))
    (y := (v.val.asIdeal.absNorm : ℝ))
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (sIdeleNorm F S a).ne_zero)) hq
  let s := Units.map (adeleProjection F S).toMonoidHom
    (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val (π ^ j))
  let t := sIdeleNorm F S (a * s)
  have hs : s⁻¹ • sAdeleOrbitBasepoint F S (some (.inr v)) =
      sAdeleOrbitBasepoint F S (some (.inr v)) :=
    (sAdeleFiniteOrbit_transporter_smul F S v s⁻¹).mpr ⟨(π ^ j)⁻¹, by rw [map_inv, map_inv]⟩
  refine ⟨⟨a * s * (τ t)⁻¹, ?_⟩, t, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hsection t]
    exact mul_inv_cancel _
  · have htv : ((t : ℝ≥0) : ℝ) =
        ((sIdeleNorm F S a : ℝ≥0) : ℝ) * (v.val.asIdeal.absNorm : ℝ) ^ (-j) := by
      change ((sIdeleNorm F S (a * s) : ℝ≥0) : ℝ) = _
      rw [map_mul, Units.val_mul, NNReal.coe_mul, sAdeleFiniteOrbit_transporter_sIdeleNorm,
        sAdeleFiniteOrbit_transporter_ideleNorm, Units.val_zpow_eq_zpow_val, norm_zpow, hπ,
        inv_zpow, zpow_neg]
    change (t : ℝ≥0) ∈ Set.Ico 1 (v.val.asIdeal.absNorm : ℝ≥0)
    rw [Set.mem_Ico, ← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, htv, NNReal.coe_one,
      NNReal.coe_natCast, zpow_neg, ← div_eq_mul_inv]
    constructor
    · rw [le_div_iff₀ (zpow_pos hq0 j), one_mul]
      exact hj.1
    · rw [div_lt_iff₀ (zpow_pos hq0 j), mul_comm, ← zpow_add_one₀ hq0.ne']
      exact hj.2
  · change τ t • sAdeleOrbitBasepoint F S (some (.inr v)) =
      (a * s * (τ t)⁻¹)⁻¹ • a • sAdeleOrbitBasepoint F S (some (.inr v))
    rw [← mul_smul, show (a * s * (τ t)⁻¹)⁻¹ * a = τ t * s⁻¹ by group, mul_smul, hs]

/-- Paper: Proposition 8.2.0.4(1), p. 386. Every point in the full S-local finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem sAdeleFiniteOrbit_transporter (v : S) (τ : ℝ≥0ˣ →* 𝕀ₛ) (hτ : Continuous τ)
    (hsection : RightInverse τ (sIdeleNorm F S)) (x : Aₛ)
    (hx : x ∈ sAdeleFullOrbit F S (some (.inr v))) :
    ∃ g : Nₛ, g⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ ∧
      ∀ h : Nₛ, h⁻¹ • x ∈ sAdeleFiniteOrbitSection F S v τ →
        g.val⁻¹ * h.val ∈ (embeddedFiniteLocalUnits F v.val).map
          (Units.map (adeleProjection F S).toMonoidHom) := by
  obtain ⟨g, hg⟩ := sAdeleFiniteOrbit_transporter_exists F S v τ hsection x hx
  exact ⟨g, hg, fun h hh ↦ sAdeleFiniteOrbit_transporter_unique F S v τ hsection x g h hg hh⟩

/-- A global idele fixes the base point at a finite place exactly when it is inserted
at that place. -/
private theorem adeleFiniteOrbit_transporter_smul (v : HeightOneSpectrum (𝓞 F)) (g : 𝔸[F]ˣ) :
    g • adeleOrbitBasepoint F (some (.inr v)) = adeleOrbitBasepoint F (some (.inr v)) ↔
      ∃ w : (v.adicCompletion F)ˣ, g = IdeleGroup.ofAdicCompletion (𝓞 F) F v w := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    change g.val * AdeleRing.ofAdicCompletion (𝓞 F) F v 0 =
      AdeleRing.ofAdicCompletion (𝓞 F) F v 0 at h
    have h1 : g.val.1 = 1 := by
      have hc := congrArg Prod.fst h
      change g.val.1 * 1 = 1 at hc
      rwa [mul_one] at hc
    have h2 : ∀ w, w ≠ v → g.val.2 w = 1 := by
      intro w hw
      have hb : (AdeleRing.ofAdicCompletion (𝓞 F) F v 0).2 w = 1 :=
        (FiniteAdeleRing.ofAdicCompletion_apply_coe F v 0 w).trans (Pi.mulSingle_eq_of_ne hw _)
      have hc : g.val.2 w * (AdeleRing.ofAdicCompletion (𝓞 F) F v 0).2 w =
          (AdeleRing.ofAdicCompletion (𝓞 F) F v 0).2 w := congrArg (fun a : 𝔸[F] ↦ a.2 w) h
      rwa [hb, mul_one] at hc
    let u : (v.adicCompletion F)ˣ := ⟨g.val.2 v, g.inv.2 v,
      congrArg (fun a : 𝔸[F] ↦ a.2 v) g.val_inv, congrArg (fun a : 𝔸[F] ↦ a.2 v) g.inv_val⟩
    refine ⟨u, Units.ext (Prod.ext h1 (FiniteAdeleRing.ext F fun w ↦ ?_))⟩
    refine Eq.trans ?_ (FiniteAdeleRing.ofAdicCompletion_apply_coe F v (g.val.2 v) w).symm
    obtain rfl | hw := eq_or_ne w v
    · rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hw, h2 w hw]
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change AdeleRing.ofAdicCompletion (𝓞 F) F v u.val * AdeleRing.ofAdicCompletion (𝓞 F) F v 0 =
      AdeleRing.ofAdicCompletion (𝓞 F) F v 0
    rw [← map_mul, mul_zero]

/-- Two norm-one transporters into the half-open section differ by an embedded local unit. -/
private theorem adeleFiniteOrbit_transporter_unique (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F]) (g h : N₁)
    (hg : g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ)
    (hh : h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ) :
    g.val⁻¹ * h.val ∈ embeddedFiniteLocalUnits F v := by
  classical
  obtain ⟨t, ht, hgt⟩ := hg
  obtain ⟨t', ht', hht⟩ := hh
  dsimp only at hgt hht
  have e1 : (g.val * τ t) • adeleOrbitBasepoint F (some (.inr v)) = x := by
    rw [mul_smul]
    change g.val • (τ t • adeleOrbitBasepoint F (some (.inr v))) = x
    rw [hgt]
    exact smul_inv_smul g.val x
  have e2 : (h.val * τ t') • adeleOrbitBasepoint F (some (.inr v)) = x := by
    rw [mul_smul]
    change h.val • (τ t' • adeleOrbitBasepoint F (some (.inr v))) = x
    rw [hht]
    exact smul_inv_smul h.val x
  have hfix : ((g.val * τ t)⁻¹ * (h.val * τ t')) • adeleOrbitBasepoint F (some (.inr v)) =
      adeleOrbitBasepoint F (some (.inr v)) := by
    rw [mul_smul, e2, ← e1, inv_smul_smul]
  obtain ⟨w, hw⟩ := (adeleFiniteOrbit_transporter_smul F v _).mp hfix
  have hgn : ideleNorm F g.val = 1 := g.prop
  have hhn : ideleNorm F h.val = 1 := h.prop
  have hN : ideleNorm F (IdeleGroup.ofAdicCompletion (𝓞 F) F v w) = t⁻¹ * t' := by
    rw [← hw, map_mul, map_inv, map_mul, map_mul, hgn, hhn, hsection t, hsection t', one_mul,
      one_mul]
  have hwn : ‖(w : v.adicCompletion F)‖ = ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := by
    rw [← sAdeleFiniteOrbit_transporter_ideleNorm F v w, hN, Units.val_mul,
      Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv, inv_mul_eq_div]
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have ha1 : (1 : ℝ) ≤ ((t : ℝ≥0) : ℝ) := by exact_mod_cast ht.1
  have ha2 : ((t : ℝ≥0) : ℝ) < v.asIdeal.absNorm := by exact_mod_cast ht.2
  have hb1 : (1 : ℝ) ≤ ((t' : ℝ≥0) : ℝ) := by exact_mod_cast ht'.1
  have hb2 : ((t' : ℝ≥0) : ℝ) < v.asIdeal.absNorm := by exact_mod_cast ht'.2
  have ha0 : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := by linarith
  obtain ⟨m, hm⟩ := sAdeleFiniteOrbit_transporter_norm_zpow F v w
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hlt | heq | hgt'
    · exfalso
      have h1 : (v.asIdeal.absNorm : ℝ) ^ m ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_neg_one] at h1
      have h2 : (v.asIdeal.absNorm : ℝ)⁻¹ < ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) :=
        calc (v.asIdeal.absNorm : ℝ)⁻¹ = 1 / (v.asIdeal.absNorm : ℝ) := (one_div _).symm
          _ < 1 / ((t : ℝ≥0) : ℝ) := one_div_lt_one_div_of_lt ha0 ha2
          _ ≤ ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) := div_le_div_of_nonneg_right hb1 ha0.le
      rw [← hwn, hm] at h2
      linarith
    · exact heq
    · exfalso
      have h1 : (v.asIdeal.absNorm : ℝ) ^ (1 : ℤ) ≤ (v.asIdeal.absNorm : ℝ) ^ m :=
        zpow_le_zpow_right₀ hq.le (by omega)
      rw [zpow_one] at h1
      have h2 : ((t' : ℝ≥0) : ℝ) / ((t : ℝ≥0) : ℝ) < v.asIdeal.absNorm :=
        lt_of_le_of_lt (div_le_self (by linarith) ha1) hb2
      rw [← hwn, hm] at h2
      linarith
  have hw1 : ‖(w : v.adicCompletion F)‖ = 1 := by rw [hm, hm0, zpow_zero]
  have htt : t' = t := by
    rw [hwn, div_eq_one_iff_eq ha0.ne'] at hw1
    exact Units.ext (NNReal.eq hw1)
  subst htt
  have hgh : g.val⁻¹ * h.val = IdeleGroup.ofAdicCompletion (𝓞 F) F v w := by
    rw [← hw, mul_inv, mul_mul_mul_comm, inv_mul_cancel, mul_one]
  rw [hgh, mem_embeddedFiniteLocalUnits_iff]
  refine ⟨rfl, ?_, fun w' hw' ↦ ?_⟩
  · rw [show (IdeleGroup.ofAdicCompletion (𝓞 F) F v w).val.2 v = w.val from
      (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ v).trans (Pi.mulSingle_eq_same _ _)]
    exact hw1
  · exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v _ w').trans
      (Pi.mulSingle_eq_of_ne hw' _)

/-- Every point of the full orbit has a norm-one transporter into the half-open section. -/
private theorem adeleFiniteOrbit_transporter_exists (v : HeightOneSpectrum (𝓞 F))
    (τ : ℝ≥0ˣ →* 𝔸[F]ˣ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F])
    (hx : x ∈ adeleFullOrbit F (some (.inr v))) :
    ∃ g : N₁, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨π, hπ⟩ := sAdeleFiniteOrbit_transporter_uniformizer F v
  have hq : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hq0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (x := ((ideleNorm F a : ℝ≥0) : ℝ))
    (y := (v.asIdeal.absNorm : ℝ))
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleNorm F a).ne_zero)) hq
  let s := IdeleGroup.ofAdicCompletion (𝓞 F) F v (π ^ j)
  let t := ideleNorm F (a * s)
  have hs : s⁻¹ • adeleOrbitBasepoint F (some (.inr v)) = adeleOrbitBasepoint F (some (.inr v)) :=
    (adeleFiniteOrbit_transporter_smul F v s⁻¹).mpr ⟨(π ^ j)⁻¹, by rw [map_inv]⟩
  refine ⟨⟨a * s * (τ t)⁻¹, ?_⟩, t, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, map_mul, map_inv, hsection t]
    exact mul_inv_cancel _
  · have htv : ((t : ℝ≥0) : ℝ) =
        ((ideleNorm F a : ℝ≥0) : ℝ) * (v.asIdeal.absNorm : ℝ) ^ (-j) := by
      change ((ideleNorm F (a * s) : ℝ≥0) : ℝ) = _
      rw [map_mul, Units.val_mul, NNReal.coe_mul, sAdeleFiniteOrbit_transporter_ideleNorm,
        Units.val_zpow_eq_zpow_val, norm_zpow, hπ, inv_zpow, zpow_neg]
    change (t : ℝ≥0) ∈ Set.Ico 1 (v.asIdeal.absNorm : ℝ≥0)
    rw [Set.mem_Ico, ← NNReal.coe_le_coe, ← NNReal.coe_lt_coe, htv, NNReal.coe_one,
      NNReal.coe_natCast, zpow_neg, ← div_eq_mul_inv]
    constructor
    · rw [le_div_iff₀ (zpow_pos hq0 j), one_mul]
      exact hj.1
    · rw [div_lt_iff₀ (zpow_pos hq0 j), mul_comm, ← zpow_add_one₀ hq0.ne']
      exact hj.2
  · change τ t • adeleOrbitBasepoint F (some (.inr v)) =
      (a * s * (τ t)⁻¹)⁻¹ • a • adeleOrbitBasepoint F (some (.inr v))
    rw [← mul_smul, show (a * s * (τ t)⁻¹)⁻¹ * a = τ t * s⁻¹ by group, mul_smul, hs]

/-- Paper: Proposition 8.2.0.4(2), p. 386. Every point in the full global finite-place
orbit can be moved into the half-open section by a norm-one idele. The transporter
is unique up to the embedded local units.
Deviation: The transporter lies in the norm-one subgroup, correcting ERRATA R1. -/
theorem adeleFiniteOrbit_transporter (v : HeightOneSpectrum (𝓞 F)) (τ : ℝ≥0ˣ →* 𝔸[F]ˣ)
    (hτ : Continuous τ) (hsection : RightInverse τ (ideleNorm F)) (x : 𝔸[F])
    (hx : x ∈ adeleFullOrbit F (some (.inr v))) :
    ∃ g : N₁, g⁻¹ • x ∈ adeleFiniteOrbitSection F v τ ∧
      ∀ h : N₁, h⁻¹ • x ∈ adeleFiniteOrbitSection F v τ →
        g.val⁻¹ * h.val ∈ embeddedFiniteLocalUnits F v := by
  obtain ⟨g, hg⟩ := adeleFiniteOrbit_transporter_exists F v τ hsection x hx
  exact ⟨g, hg, fun h hh ↦ adeleFiniteOrbit_transporter_unique F v τ hsection x g h hg hh⟩

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full S-local orbit is
already the norm-one orbit of the distinguished base point. -/
theorem sAdeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    sAdeleNormOneOrbit F S (some (.inl v)) = sAdeleFullOrbit F S (some (.inl v)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro ⟨g, rfl⟩
    let s := singlePlaceIdeleNormSection F v
    let p := Units.map (adeleProjection F S).toMonoidHom
    have hτ (t : ℝ≥0ˣ) : sIdeleNorm F S (p (s t)) = t := by
      let A := integralAdelesOutside F S
      have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
        change (s u).val ∈ integralAdelesOutside F S
        delta integralAdelesOutside
        rw [Subring.mem_iInf]
        intro w
        rw [Subring.mem_iInf]
        intro _
        exact (w.adicCompletionIntegers F).one_mem
      have ht : s t ∈ A.toSubmonoid.units :=
        ⟨hmem t, by
          change ((s t)⁻¹).val ∈ A
          rw [← map_inv]
          exact hmem t⁻¹⟩
      let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
      exact ((sIdeleNorm_spec F S).1 g).symm.trans
        (singlePlaceIdeleNormSection_rightInverse F v t)
    let c := p (s (sIdeleNorm F S g)⁻¹)
    have hfix : c • sAdeleOrbitBasepoint F S (some (.inl v)) =
        sAdeleOrbitBasepoint F S (some (.inl v)) := by
      rw [Units.smul_def]
      change adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v
          (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ (sIdeleNorm F S g)⁻¹).val) *
          adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0) =
        adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0)
      rw [← map_mul, ← map_mul, mul_zero]
    refine ⟨⟨g * c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hτ, mul_inv_cancel]
    · change (g * c) • sAdeleOrbitBasepoint F S (some (.inl v)) = g • _
      rw [mul_smul, hfix]

/-- Paper: Proposition 8.2.0.5, p. 386. At an infinite place the full global orbit is
already the norm-one orbit of the distinguished base point. -/
theorem adeleNormOneOrbit_infinite_eq_full (v : InfinitePlace F) :
    adeleNormOneOrbit F (some (.inl v)) = adeleFullOrbit F (some (.inl v)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro ⟨g, rfl⟩
    let c := singlePlaceIdeleNormSection F v (ideleNorm F g)⁻¹
    have hc : ideleNorm F c = (ideleNorm F g)⁻¹ :=
      singlePlaceIdeleNormSection_rightInverse F v _
    have hfix : c • adeleOrbitBasepoint F (some (.inl v)) =
        adeleOrbitBasepoint F (some (.inl v)) := by
      rw [Units.smul_def]
      change AdeleRing.ofCompletion (𝓞 F) F v
          (infinitePlaceRealPower F v (v.mult : ℝ)⁻¹ (ideleNorm F g)⁻¹).val *
          AdeleRing.ofCompletion (𝓞 F) F v 0 = AdeleRing.ofCompletion (𝓞 F) F v 0
      rw [← map_mul, mul_zero]
    refine ⟨⟨g * c, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, hc, mul_inv_cancel]
    · change (g * c) • adeleOrbitBasepoint F (some (.inl v)) = g • _
      rw [mul_smul, hfix]

/-- The idele inserted at an infinite place has norm one exactly when the inserted
unit has norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm (v : InfinitePlace F)
    (u : v.Completionˣ) :
    ideleNorm F (IdeleGroup.ofCompletion (𝓞 F) F v u) = 1 ↔ ‖(u : v.Completion)‖ = 1 := by
  classical
  rw [Units.ext_iff, Units.val_one, ← NNReal.coe_eq_one, ((ideleNorm_spec F).1 _).2]
  change (∏ w : InfinitePlace F, ‖Pi.mulSingle v (u : v.Completion) w‖ ^ w.mult) *
    (∏ᶠ w : HeightOneSpectrum (𝓞 F), ‖(1 : w.adicCompletion F)‖) = 1 ↔ _
  simp only [norm_one, finprod_one, mul_one]
  rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ _), Pi.mulSingle_eq_same]
  · exact pow_eq_one_iff_of_nonneg (norm_nonneg _) InfinitePlace.mult_pos.ne'
  · intro w _ hw
    simp only [Pi.mulSingle_eq_of_ne hw, norm_one, one_pow]

/-- At a real place the units of norm one are the two signs. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_unit (v : InfinitePlace F)
    (hv : v.IsReal) (u : v.Completionˣ) : ‖u.val‖ = 1 ↔ (u.val = 1 ∨ u.val = -1) := by
  let φ := InfinitePlace.Completion.extensionEmbeddingOfIsReal hv
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv
  rw [← hiso.norm_map_of_map_zero (map_zero φ) u.val, Real.norm_eq_abs, abs_eq zero_le_one]
  constructor
  · rintro (h | h)
    · exact Or.inl (hiso.injective (h.trans (map_one φ).symm))
    · exact Or.inr (hiso.injective (h.trans (by rw [map_neg, map_one])))
  · rintro (h | h)
    · exact Or.inl (by rw [h, map_one])
    · exact Or.inr (by rw [h, map_neg, map_one])

/-- An S-idele fixes the S-local base point at an infinite place exactly when it is the
projection of an idele inserted at that place. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_smul (v : InfinitePlace F)
    (g : (SAdeleRing F S)ˣ) :
    g • sAdeleOrbitBasepoint F S (some (.inl v)) = sAdeleOrbitBasepoint F S (some (.inl v)) ↔
      ∃ u : v.Completionˣ, g = Units.map (adeleProjection F S).toMonoidHom
        (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    have h1 : ∀ w, w ≠ v → g.val.1 w = 1 := by
      intro w hw
      have hc := congrFun (congrArg Prod.fst h) w
      change g.val.1 w * Pi.mulSingle v 0 w = Pi.mulSingle v 0 w at hc
      rwa [Pi.mulSingle_eq_of_ne hw, mul_one] at hc
    have h2 : ∀ w : S, g.val.2 w = 1 := by
      intro w
      have hc := congrFun (congrArg Prod.snd h) w
      change g.val.2 w * 1 = 1 at hc
      rwa [mul_one] at hc
    let u : v.Completionˣ := ⟨g.val.1 v, g.inv.1 v, congrFun (congrArg Prod.fst g.val_inv) v,
      congrFun (congrArg Prod.fst g.inv_val) v⟩
    refine ⟨u, Units.ext (Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_))⟩
    · change g.val.1 w = Pi.mulSingle v (g.val.1 v) w
      obtain rfl | hw := eq_or_ne w v
      · rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hw, h1 w hw]
    · change g.val.2 w = 1
      exact h2 w
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v u.val) *
        adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0) =
      adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v 0)
    rw [← map_mul, ← map_mul, mul_zero]

/-- The projected idele inserted at an infinite place has S-norm one exactly when the
inserted unit has norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm (v : InfinitePlace F)
    (u : v.Completionˣ) :
    sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom
      (IdeleGroup.ofCompletion (𝓞 F) F v u)) = 1 ↔ ‖(u : v.Completion)‖ = 1 := by
  let A := integralAdelesOutside F S
  let s := IdeleGroup.ofCompletion (𝓞 F) F v
  have hmem (y : v.Completionˣ) : (s y).val ∈ A := by
    change (s y).val ∈ integralAdelesOutside F S
    delta integralAdelesOutside
    rw [Subring.mem_iInf]
    intro w
    rw [Subring.mem_iInf]
    intro _
    exact (w.adicCompletionIntegers F).one_mem
  have ht : s u ∈ A.toSubmonoid.units :=
    ⟨hmem u, by
      change ((s u)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem u⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s u, ht⟩
  have hg : sIdeleNorm F S (Units.map (adeleProjection F S).toMonoidHom (s u)) =
      ideleNorm F (s u) := ((sIdeleNorm_spec F S).1 g).symm
  rw [hg]
  exact sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u

/-- At an infinite place the S-local norm-one stabilizer of an orbit point consists of
the projected ideles inserted at that place with a unit of norm one. -/
private theorem sAdeleFullOrbit_real_normOne_stabilizer_iff_aux (v : InfinitePlace F)
    (x : SAdeleRing F S) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v)))
    (g : (SAdeleRing F S)ˣ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  obtain ⟨h, rfl⟩ := hx
  change sIdeleNorm F S g = 1 ∧ g • h • sAdeleOrbitBasepoint F S (some (.inl v)) =
    h • sAdeleOrbitBasepoint F S (some (.inl v)) ↔ _
  rw [← mul_smul, mul_comm g h, mul_smul, smul_left_cancel_iff,
    sAdeleFullOrbit_real_normOne_stabilizer_iff_smul]
  constructor
  · rintro ⟨hn, u, rfl⟩
    exact ⟨u, (sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm F S v u).mp hn, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(sAdeleFullOrbit_real_normOne_stabilizer_iff_sIdeleNorm F S v u).mpr hu, u, rfl⟩

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the S-local orbit is the image of the two local signs. -/
theorem sAdeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  rw [sAdeleFullOrbit_real_normOne_stabilizer_iff_aux F S v x hx g]
  exact exists_congr fun u ↦
    and_congr (sAdeleFullOrbit_real_normOne_stabilizer_iff_unit F v hv u) Iff.rfl

/-- A global idele fixes the base point at an infinite place exactly when it is inserted
at that place. -/
private theorem adeleFullOrbit_real_normOne_stabilizer_iff_smul (v : InfinitePlace F)
    (g : 𝔸[F]ˣ) :
    g • adeleOrbitBasepoint F (some (.inl v)) = adeleOrbitBasepoint F (some (.inl v)) ↔
      ∃ u : v.Completionˣ, g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  classical
  constructor
  · intro h
    rw [Units.smul_def] at h
    change g.val * AdeleRing.ofCompletion (𝓞 F) F v 0 = AdeleRing.ofCompletion (𝓞 F) F v 0 at h
    have h1 : ∀ w, w ≠ v → g.val.1 w = 1 := by
      intro w hw
      have hc := congrFun (congrArg Prod.fst h) w
      change g.val.1 w * Pi.mulSingle v 0 w = Pi.mulSingle v 0 w at hc
      rwa [Pi.mulSingle_eq_of_ne hw, mul_one] at hc
    have h2 : g.val.2 = 1 := by
      have hc := congrArg Prod.snd h
      change g.val.2 * 1 = 1 at hc
      rwa [mul_one] at hc
    let u : v.Completionˣ := ⟨g.val.1 v, g.inv.1 v, congrFun (congrArg Prod.fst g.val_inv) v,
      congrFun (congrArg Prod.fst g.inv_val) v⟩
    refine ⟨u, Units.ext (Prod.ext (funext fun w ↦ ?_) h2)⟩
    change g.val.1 w = Pi.mulSingle v (g.val.1 v) w
    obtain rfl | hw := eq_or_ne w v
    · rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hw, h1 w hw]
  · rintro ⟨u, rfl⟩
    rw [Units.smul_def]
    change AdeleRing.ofCompletion (𝓞 F) F v u.val * AdeleRing.ofCompletion (𝓞 F) F v 0 =
      AdeleRing.ofCompletion (𝓞 F) F v 0
    rw [← map_mul, mul_zero]

/-- At an infinite place the global norm-one stabilizer of an orbit point consists of
the ideles inserted at that place with a unit of norm one. -/
private theorem adeleFullOrbit_real_normOne_stabilizer_iff_aux (v : InfinitePlace F)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧ g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  obtain ⟨h, rfl⟩ := hx
  change ideleNorm F g = 1 ∧ g • h • adeleOrbitBasepoint F (some (.inl v)) =
    h • adeleOrbitBasepoint F (some (.inl v)) ↔ _
  rw [← mul_smul, mul_comm g h, mul_smul, smul_left_cancel_iff,
    adeleFullOrbit_real_normOne_stabilizer_iff_smul]
  constructor
  · rintro ⟨hn, u, rfl⟩
    exact ⟨u, (sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u).mp hn, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨(sAdeleFullOrbit_real_normOne_stabilizer_iff_ideleNorm F v u).mpr hu, u, rfl⟩

/-- Paper: Proposition 8.2.0.5(1), p. 386. At a real place the norm-one
stabilizer of every point of the global orbit is the image of the two local signs. -/
theorem adeleFullOrbit_real_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsReal)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, (u.val = 1 ∨ u.val = -1) ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  rw [adeleFullOrbit_real_normOne_stabilizer_iff_aux F v x hx g]
  exact exists_congr fun u ↦
    and_congr (sAdeleFullOrbit_real_normOne_stabilizer_iff_unit F v hv u) Iff.rfl

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the S-local orbit is the image of the local unit circle. -/
theorem sAdeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : Aₛ) (hx : x ∈ sAdeleFullOrbit F S (some (.inl v))) (g : 𝕀ₛ) :
    (sIdeleNorm F S g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.ofCompletion (𝓞 F) F v u) := by
  exact sAdeleFullOrbit_real_normOne_stabilizer_iff_aux F S v x hx g

/-- Paper: Proposition 8.2.0.5(2), p. 387. At a complex place the norm-one
stabilizer of every point of the global orbit is the image of the local unit circle. -/
theorem adeleFullOrbit_complex_normOne_stabilizer_iff (v : InfinitePlace F) (hv : v.IsComplex)
    (x : 𝔸[F]) (hx : x ∈ adeleFullOrbit F (some (.inl v))) (g : 𝔸[F]ˣ) :
    (ideleNorm F g = 1 ∧ g • x = x) ↔
      ∃ u : v.Completionˣ, ‖u.val‖ = 1 ∧
        g = IdeleGroup.ofCompletion (𝓞 F) F v u := by
  exact adeleFullOrbit_real_normOne_stabilizer_iff_aux F v x hx g

/-- Paper: Proposition 8.2.0.6(1), p. 387. The closure of the positive section ray
relative to the S-local full-orbit union adds the single-zero base point. -/
theorem sAdeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set Aₛ := Set.range fun t : ℝ≥0ˣ ↦
      adeleProjection F S (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ sAdeleFullOrbitUnion F S =
      ray ∪ {sAdeleOrbitBasepoint F S (some (.inl v))} := by
  classical
  intro ray
  let ψ := InfinitePlace.Completion.extensionEmbedding v
  have hψ : Isometry ψ := InfinitePlace.Completion.isometry_extensionEmbedding v
  let φ : v.Completion → SAdeleRing F S := fun x ↦
    adeleProjection F S (AdeleRing.ofCompletion (𝓞 F) F v x)
  have hp : Continuous (adeleProjection F S) :=
    continuous_fst.prodMk (continuous_pi fun u : S ↦
      (RestrictedProduct.continuous_eval u.val).comp continuous_snd)
  have hφ0 : Continuous fun x : v.Completion ↦ AdeleRing.ofCompletion (𝓞 F) F v x :=
    (continuous_mulSingle (A := InfinitePlace.Completion) v).prodMk continuous_const
  have hφ : Continuous φ := hp.comp hφ0
  let e : ℝ := (v.mult : ℝ)⁻¹
  have he0 : 0 < e := inv_pos.mpr (by exact_mod_cast InfinitePlace.mult_pos)
  let r : ℝ≥0ˣ → v.Completion := fun t ↦ (infinitePlaceRealPower F v e t).val
  have hray : ∀ t, adeleProjection F S (singlePlaceIdeleNormSection F v t).val = φ (r t) :=
    fun t ↦ rfl
  have hψr : ∀ t, ψ (r t) = (((t.val : ℝ) ^ e : ℝ) : ℂ) := fun t ↦
    infinitePlaceRealPower_apply F v e t
  let K : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}
  have hK : IsClosed K :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  let C : Set (SAdeleRing F S) :=
    {y | y.2 = 1} ∩ (⋂ w ∈ ({v}ᶜ : Set (InfinitePlace F)), {y | y.1 w = 1}) ∩
      {y | ψ (y.1 v) ∈ K}
  have hC0 : IsClosed {y : SAdeleRing F S | y.2 = 1} := isClosed_eq continuous_snd continuous_const
  have hC1 : IsClosed (⋂ w ∈ ({v}ᶜ : Set (InfinitePlace F)), {y : SAdeleRing F S | y.1 w = 1}) :=
    isClosed_biInter fun w _ ↦
      isClosed_eq ((continuous_apply w).comp continuous_fst) continuous_const
  have hC2 : IsClosed {y : SAdeleRing F S | ψ (y.1 v) ∈ K} :=
    hK.preimage (hψ.continuous.comp ((continuous_apply v).comp continuous_fst))
  have hC : IsClosed C := (hC0.inter hC1).inter hC2
  have hrayC : ray ⊆ C := by
    rintro _ ⟨t, rfl⟩
    change adeleProjection F S (singlePlaceIdeleNormSection F v t).val ∈ C
    rw [hray]
    refine ⟨⟨rfl, Set.mem_iInter₂.mpr fun w hw ↦ ?_⟩, ?_⟩
    · exact Pi.mulSingle_eq_of_ne hw _
    · change ψ (Pi.mulSingle v (r t) v) ∈ K
      rw [Pi.mulSingle_eq_same, hψr]
      exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩
  have hbase : sAdeleOrbitBasepoint F S (some (.inl v)) ∈ closure ray := by
    let tn : ℕ → ℝ≥0ˣ := fun n ↦ Units.mk0 ((n : ℝ≥0) + 1)⁻¹ (by positivity)
    have hn : ∀ n : ℕ, ‖r (tn n)‖ = ((n : ℝ) + 1)⁻¹ ^ e := by
      intro n
      rw [← hψ.norm_map_of_map_zero (map_zero ψ), hψr, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      simp [tn]
    have hlim : Filter.Tendsto (fun n ↦ r (tn n)) Filter.atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [hn]
      have h1 : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ one_div _
      have h0 : (0 : ℝ) ^ e = 0 := Real.zero_rpow he0.ne'
      rw [← h0]
      exact (Real.continuousAt_rpow_const 0 e (Or.inr he0.le)).tendsto.comp h1
    have hlim' : Filter.Tendsto
        (fun n ↦ adeleProjection F S (singlePlaceIdeleNormSection F v (tn n)).val)
        Filter.atTop (𝓝 (sAdeleOrbitBasepoint F S (some (.inl v)))) := by
      simp_rw [hray]
      exact (hφ.tendsto 0).comp hlim
    exact mem_closure_of_tendsto hlim' (Filter.Eventually.of_forall fun n ↦ ⟨tn n, rfl⟩)
  ext y
  constructor
  · rintro ⟨hy, -⟩
    obtain ⟨⟨h2, h1⟩, him, hre⟩ := closure_minimal hrayC hC hy
    have hyφ : y = φ (y.1 v) := by
      refine Prod.ext (funext fun w ↦ ?_) h2
      change y.1 w = Pi.mulSingle v (y.1 v) w
      obtain rfl | hw := eq_or_ne w v
      · rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hw]
        exact Set.mem_iInter₂.mp h1 w hw
    have hψy : ψ (y.1 v) = (((ψ (y.1 v)).re : ℝ) : ℂ) := Complex.ext rfl (by simpa using him)
    rcases hre.eq_or_lt with h0 | hpos
    · right
      have hy0 : y.1 v = 0 := by
        apply hψ.injective
        rw [hψy, ← h0, Complex.ofReal_zero, map_zero]
      rw [Set.mem_singleton_iff, hyφ, hy0]
      rfl
    · left
      set s := (ψ (y.1 v)).re with hs
      let t : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (s ^ (v.mult : ℝ))) (by
        rw [ne_eq, Real.toNNReal_eq_zero, not_le]
        positivity)
      have ht : r t = y.1 v := by
        apply hψ.injective
        rw [hψr, hψy]
        congr 1
        change ((Real.toNNReal (s ^ (v.mult : ℝ)) : ℝ)) ^ e = s
        rw [Real.coe_toNNReal _ (by positivity), Real.rpow_rpow_inv hpos.le
          (by exact_mod_cast InfinitePlace.mult_pos.ne')]
      exact ⟨t, by
        change adeleProjection F S (singlePlaceIdeleNormSection F v t).val = y
        rw [hray, ht, ← hyφ]⟩
  · rintro (⟨t, rfl⟩ | hy)
    · refine ⟨subset_closure ⟨t, rfl⟩, Set.mem_iUnion.mpr ⟨none,
        Units.map (adeleProjection F S).toMonoidHom (singlePlaceIdeleNormSection F v t), ?_⟩⟩
      change _ • adeleProjection F S (1 : 𝔸[F]) = _
      rw [map_one, Units.smul_def, smul_eq_mul, mul_one]
      rfl
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hbase, Set.mem_iUnion.mpr ⟨some (.inl v), MulAction.mem_orbit_self _⟩⟩

/-- Paper: Proposition 8.2.0.6(2), p. 387. The closure of the positive section ray
relative to the global full-orbit union adds the single-zero base point. -/
theorem adeleFullOrbitUnion_closure_sectionRay (v : InfinitePlace F) :
    let ray : Set 𝔸[F] := Set.range fun t : ℝ≥0ˣ ↦ (singlePlaceIdeleNormSection F v t).val
    closure ray ∩ adeleFullOrbitUnion F = ray ∪ {adeleOrbitBasepoint F (some (.inl v))} := by
  classical
  intro ray
  let ψ := InfinitePlace.Completion.extensionEmbedding v
  have hψ : Isometry ψ := InfinitePlace.Completion.isometry_extensionEmbedding v
  let φ : v.Completion → 𝔸[F] := fun x ↦ AdeleRing.ofCompletion (𝓞 F) F v x
  have hφ : Continuous φ :=
    (continuous_mulSingle (A := InfinitePlace.Completion) v).prodMk continuous_const
  let e : ℝ := (v.mult : ℝ)⁻¹
  have he0 : 0 < e := inv_pos.mpr (by exact_mod_cast InfinitePlace.mult_pos)
  let r : ℝ≥0ˣ → v.Completion := fun t ↦ (infinitePlaceRealPower F v e t).val
  have hray : ∀ t, (singlePlaceIdeleNormSection F v t).val = φ (r t) := fun t ↦ rfl
  have hψr : ∀ t, ψ (r t) = (((t.val : ℝ) ^ e : ℝ) : ℂ) := fun t ↦
    infinitePlaceRealPower_apply F v e t
  let K : Set ℂ := {z | z.im = 0 ∧ 0 ≤ z.re}
  have hK : IsClosed K :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  let C : Set 𝔸[F] :=
    (⋂ w : HeightOneSpectrum (𝓞 F), {y | y.2 w = 1}) ∩
      (⋂ w ∈ ({v}ᶜ : Set (InfinitePlace F)), {y | y.1 w = 1}) ∩ {y | ψ (y.1 v) ∈ K}
  have hC0 : IsClosed (⋂ w : HeightOneSpectrum (𝓞 F), {y : 𝔸[F] | y.2 w = 1}) :=
    isClosed_iInter fun w ↦
      isClosed_eq ((RestrictedProduct.continuous_eval w).comp continuous_snd) continuous_const
  have hC1 : IsClosed (⋂ w ∈ ({v}ᶜ : Set (InfinitePlace F)), {y : 𝔸[F] | y.1 w = 1}) :=
    isClosed_biInter fun w _ ↦
      isClosed_eq ((continuous_apply w).comp continuous_fst) continuous_const
  have hC2 : IsClosed {y : 𝔸[F] | ψ (y.1 v) ∈ K} :=
    hK.preimage (hψ.continuous.comp ((continuous_apply v).comp continuous_fst))
  have hC : IsClosed C := (hC0.inter hC1).inter hC2
  have hrayC : ray ⊆ C := by
    rintro _ ⟨t, rfl⟩
    change (singlePlaceIdeleNormSection F v t).val ∈ C
    rw [hray]
    refine ⟨⟨Set.mem_iInter.mpr fun w ↦ ?_, Set.mem_iInter₂.mpr fun w hw ↦ ?_⟩, ?_⟩
    · rfl
    · exact Pi.mulSingle_eq_of_ne hw _
    · change ψ (Pi.mulSingle v (r t) v) ∈ K
      rw [Pi.mulSingle_eq_same, hψr]
      exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; positivity⟩
  have hbase : adeleOrbitBasepoint F (some (.inl v)) ∈ closure ray := by
    let tn : ℕ → ℝ≥0ˣ := fun n ↦ Units.mk0 ((n : ℝ≥0) + 1)⁻¹ (by positivity)
    have hn : ∀ n : ℕ, ‖r (tn n)‖ = ((n : ℝ) + 1)⁻¹ ^ e := by
      intro n
      rw [← hψ.norm_map_of_map_zero (map_zero ψ), hψr, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      simp [tn]
    have hlim : Filter.Tendsto (fun n ↦ r (tn n)) Filter.atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp_rw [hn]
      have h1 : Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ one_div _
      have h0 : (0 : ℝ) ^ e = 0 := Real.zero_rpow he0.ne'
      rw [← h0]
      exact (Real.continuousAt_rpow_const 0 e (Or.inr he0.le)).tendsto.comp h1
    have hlim' : Filter.Tendsto (fun n ↦ (singlePlaceIdeleNormSection F v (tn n)).val) Filter.atTop
        (𝓝 (adeleOrbitBasepoint F (some (.inl v)))) := by
      simp_rw [hray]
      exact (hφ.tendsto 0).comp hlim
    exact mem_closure_of_tendsto hlim' (Filter.Eventually.of_forall fun n ↦ ⟨tn n, rfl⟩)
  ext y
  constructor
  · rintro ⟨hy, -⟩
    obtain ⟨⟨h2', h1⟩, him, hre⟩ := closure_minimal hrayC hC hy
    have h2 : y.2 = 1 := FiniteAdeleRing.ext F fun w ↦ Set.mem_iInter.mp h2' w
    have hyφ : y = φ (y.1 v) := by
      refine Prod.ext (funext fun w ↦ ?_) h2
      change y.1 w = Pi.mulSingle v (y.1 v) w
      obtain rfl | hw := eq_or_ne w v
      · rw [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne hw]
        exact Set.mem_iInter₂.mp h1 w hw
    have hψy : ψ (y.1 v) = (((ψ (y.1 v)).re : ℝ) : ℂ) := Complex.ext rfl (by simpa using him)
    rcases hre.eq_or_lt with h0 | hpos
    · right
      have hy0 : y.1 v = 0 := by
        apply hψ.injective
        rw [hψy, ← h0, Complex.ofReal_zero, map_zero]
      rw [Set.mem_singleton_iff, hyφ, hy0]
      rfl
    · left
      set s := (ψ (y.1 v)).re with hs
      let t : ℝ≥0ˣ := Units.mk0 (Real.toNNReal (s ^ (v.mult : ℝ))) (by
        rw [ne_eq, Real.toNNReal_eq_zero, not_le]
        positivity)
      have ht : r t = y.1 v := by
        apply hψ.injective
        rw [hψr, hψy]
        congr 1
        change ((Real.toNNReal (s ^ (v.mult : ℝ)) : ℝ)) ^ e = s
        rw [Real.coe_toNNReal _ (by positivity), Real.rpow_rpow_inv hpos.le
          (by exact_mod_cast InfinitePlace.mult_pos.ne')]
      exact ⟨t, by
        change (singlePlaceIdeleNormSection F v t).val = y
        rw [hray, ht, ← hyφ]⟩
  · rintro (⟨t, rfl⟩ | hy)
    · refine ⟨subset_closure ⟨t, rfl⟩,
        Set.mem_iUnion.mpr ⟨none, singlePlaceIdeleNormSection F v t, ?_⟩⟩
      change singlePlaceIdeleNormSection F v t • (1 : 𝔸[F]) = _
      rw [Units.smul_def, smul_eq_mul, mul_one]
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨hbase, Set.mem_iUnion.mpr ⟨some (.inl v), MulAction.mem_orbit_self _⟩⟩

end RiemannMasullo
