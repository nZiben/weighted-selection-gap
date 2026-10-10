import Mathlib

/- Fresh formalization of the scalar relaxation only.
   This file does not formalize the frame geometry or the regression bridge. -/

open scoped BigOperators
noncomputable section
namespace WeightedSelectionScalar

def x (d : ℝ) : ℝ := 1 + 3 / 10 * d
def y (d : ℝ) : ℝ := 1 - 3 / 10 * d
def P (d : ℝ) : ℝ := x d * y d
def Q (d : ℝ) : ℝ := 7 / 3 - 21 / 100 * d ^ 2
def h (d a b : ℝ) : ℝ := P d - a * y d - b * x d
def F (d a b : ℝ) : ℝ :=
  (a + b) ^ 2 + 4 / 3 * (a + b) - d * (a - b) - 7 / 3 - d ^ 2
def g (r a b : ℝ) : ℝ :=
  (a + b) / 2 +
    (r * (1 - r) + ((1 - r) * a + r * b) / 2) / (1 + (a + b) / 2)

theorem certificate_identity (d a b : ℝ) :
    P d * F d a b =
      -(121 / 100 : ℝ) * d ^ 2 * P d -
      h d a b * (Q d + a * x d + b * y d) - a * b * (x d - y d) ^ 2 := by
  dsimp [P, F, h, Q, x, y]
  ring

theorem certificate_implies (d a b : ℝ)
    (hdlo : -1 ≤ d) (hdhi : d ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h d a b) : F d a b ≤ 0 := by
  have hd2 : d ^ 2 ≤ 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ d + 1) (by linarith : 0 ≤ 1 - d)]
  have hx : 0 < x d := by unfold x; linarith
  have hy : 0 < y d := by unfold y; linarith
  have hp : 0 < P d := mul_pos hx hy
  have hq : 0 < Q d := by unfold Q; nlinarith
  have ht1 : 0 ≤ (121 / 100 : ℝ) * d ^ 2 * P d := by positivity
  have ht2 : 0 ≤ h d a b * (Q d + a * x d + b * y d) := by positivity
  have ht3 : 0 ≤ a * b * (x d - y d) ^ 2 := by positivity
  have hi := certificate_identity d a b
  nlinarith

theorem cost_identity (r a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    4 * (1 + (a + b) / 2) * (g r a b - 5 / 6) = F (2 * r - 1) a b := by
  have hden : 1 + (a + b) / 2 ≠ 0 := by positivity
  unfold g F
  field_simp
  ring

theorem certificate_cost_bound (r a b : ℝ)
    (hrlo : 0 ≤ r) (hrhi : r ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h (2 * r - 1) a b) :
    g r a b ≤ 5 / 6 := by
  have hf := certificate_implies (2 * r - 1) a b (by linarith) (by linarith) ha hb hh
  have hi := cost_identity r a b ha hb
  have hden : 0 < 1 + (a + b) / 2 := by positivity
  nlinarith

theorem weighted_nonnegative_witness {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hf : 0 ≤ ∑ i, p i * f i) : ∃ i, 0 < p i ∧ 0 ≤ f i := by
  classical
  have hpossum : (∑ _i : ι, (0 : ℝ)) < ∑ i, p i := by simp [hsum]
  obtain ⟨k, _, hk⟩ := Finset.exists_lt_of_sum_lt hpossum
  by_contra hn
  push Not at hn
  have hall : ∀ i ∈ (Finset.univ : Finset ι), p i * f i ≤ 0 := by
    intro i _
    by_cases hi : 0 < p i
    · exact le_of_lt (mul_neg_of_pos_of_neg hi (hn i hi))
    · have hz : p i = 0 := le_antisymm (le_of_not_gt hi) (hp i)
      simp [hz]
  have hstrict : ∃ i ∈ (Finset.univ : Finset ι), p i * f i < (0 : ℝ) :=
    ⟨k, Finset.mem_univ k, mul_neg_of_pos_of_neg hk (hn k hk)⟩
  have hbad := Finset.sum_lt_sum hall hstrict
  simp only [Finset.sum_const_zero] at hbad
  linarith

theorem certificate_mean {ι : Type*} [Fintype ι]
    (p a b : ι → ℝ) (r : ℝ)
    (hsum : ∑ i, p i = 1) (ha : ∑ i, p i * a i = r)
    (hb : ∑ i, p i * b i = 1 - r) :
    (∑ i, p i * h (2 * r - 1) (a i) (b i)) =
      (21 / 100 : ℝ) * (2 * r - 1) ^ 2 := by
  have hexpand : ∀ i, p i * h (2 * r - 1) (a i) (b i) =
      p i * P (2 * r - 1) - (p i * a i) * y (2 * r - 1) -
      (p i * b i) * x (2 * r - 1) := by
    intro i
    unfold h
    ring
  simp_rw [hexpand, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hsum, ha, hb]
  unfold P x y
  ring

theorem scalar_moment_selection {ι : Type*} [Fintype ι]
    (p a b : ι → ℝ) (r : ℝ)
    (hp : ∀ i, 0 ≤ p i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsum : ∑ i, p i = 1) (hrlo : 0 ≤ r) (hrhi : r ≤ 1)
    (hamean : ∑ i, p i * a i = r) (hbmean : ∑ i, p i * b i = 1 - r) :
    ∃ i, 0 < p i ∧ g r (a i) (b i) ≤ 5 / 6 := by
  have hm := certificate_mean p a b r hsum hamean hbmean
  have hnonneg : 0 ≤ ∑ i, p i * h (2 * r - 1) (a i) (b i) := by
    rw [hm]
    positivity
  obtain ⟨i, hpi, hhi⟩ := weighted_nonnegative_witness p
    (fun i => h (2 * r - 1) (a i) (b i)) hp hsum hnonneg
  exact ⟨i, hpi, certificate_cost_bound r (a i) (b i) hrlo hrhi (ha i) (hb i) hhi⟩

theorem isotropic_scalar_obstruction : g (1 / 2) (1 / 2) (1 / 2) = 5 / 6 := by
  unfold g
  norm_num

/- Any universal scalar bound of the same form is at least 5/6.
   Only a one-atom scalar distribution is needed for the obstruction. -/
theorem scalar_bound_necessary (c : ℝ)
    (H : ∀ (p a b : Fin 1 → ℝ) (r : ℝ),
      (∀ i, 0 ≤ p i) → (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
      (∑ i, p i = 1) → 0 ≤ r → r ≤ 1 →
      (∑ i, p i * a i = r) → (∑ i, p i * b i = 1 - r) →
      ∃ i, 0 < p i ∧ g r (a i) (b i) ≤ c) : 5 / 6 ≤ c := by
  obtain ⟨i, _, hi⟩ := H (fun _ => 1) (fun _ => 1 / 2) (fun _ => 1 / 2) (1 / 2)
    (by intro i; norm_num) (by intro i; norm_num) (by intro i; norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa only [isotropic_scalar_obstruction] using hi

def ScalarUniversalBound (c : ℝ) : Prop :=
  ∀ (n : ℕ) (p a b : Fin n → ℝ) (r : ℝ),
    (∀ i, 0 ≤ p i) → (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
    (∑ i, p i = 1) → 0 ≤ r → r ≤ 1 →
    (∑ i, p i * a i = r) → (∑ i, p i * b i = 1 - r) →
    ∃ i, 0 < p i ∧ g r (a i) (b i) ≤ c

theorem scalar_relaxation_optimal (c : ℝ) : ScalarUniversalBound c ↔ 5 / 6 ≤ c := by
  constructor
  · intro H
    exact scalar_bound_necessary c (H 1)
  · intro hc n p a b r hp ha hb hsum hrlo hrhi hamean hbmean
    obtain ⟨i, hpi, hi⟩ := scalar_moment_selection p a b r hp ha hb hsum hrlo hrhi hamean hbmean
    exact ⟨i, hpi, le_trans hi hc⟩

theorem isotropic_equality_expression (c d : ℝ) :
    7 * c ^ 2 - 2 * c * d - 3 * d ^ 2 =
      (22 / 3 : ℝ) * c ^ 2 - 3 * (d + c / 3) ^ 2 := by ring

theorem isotropic_equality_impossible (c d : ℝ) (hc : c ^ 2 ≤ 1 / 4) :
    7 * c ^ 2 - 2 * c * d - 3 * d ^ 2 < 2 := by
  nlinarith [sq_nonneg (d + c / 3)]

theorem isotropic_ratio_bound (c d : ℝ) (hc : c ^ 2 ≤ 1 / 4) :
    ((d - c) ^ 2 + 4 * (1 - d ^ 2)) / (2 * (1 - c ^ 2)) ≤ 26 / 9 := by
  have hden : 0 < 2 * (1 - c ^ 2) := by nlinarith
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg (d + c / 3)]

/- Conditional exact arithmetic for the quantitative geometric proof.
   These lemmas verify numeric extraction only; their hypotheses are supplied
   by the separately audited, human-readable frame stability argument. -/
def epsilon : ℝ := 1 / (10 : ℝ) ^ 20

theorem delta_numeric_bound (d : ℝ) (hd : d ^ 2 ≤ (60 / 11 : ℝ) * epsilon) :
    |d| < 5 / (2 * (10 : ℝ) ^ 10) := by
  have hgap : (60 / 11 : ℝ) * epsilon < (5 / (2 * (10 : ℝ) ^ 10)) ^ 2 := by
    norm_num [epsilon]
  have hsq : |d| ^ 2 < (5 / (2 * (10 : ℝ) ^ 10)) ^ 2 := by
    simpa only [sq_abs] using lt_of_le_of_lt hd hgap
  have hb : 0 < (5 / (2 * (10 : ℝ) ^ 10)) := by norm_num
  nlinarith [abs_nonneg d]

theorem eta_numeric_bound (d : ℝ) (hd : d ^ 2 ≤ (60 / 11 : ℝ) * epsilon) :
    2 * epsilon + |d| < 3 / (10 : ℝ) ^ 10 := by
  have hsmall := delta_numeric_bound d hd
  have hgap : 2 * epsilon + 5 / (2 * (10 : ℝ) ^ 10) < 3 / (10 : ℝ) ^ 10 := by
    norm_num [epsilon]
  linarith

theorem zeta_numeric_lower_bound (z t : ℝ) (_ht : 0 ≤ t)
    (htsq : t ^ 2 = z) (hdeficit : (1 / 200 : ℝ) ≤ 60 * t) :
    (1 / 144000000 : ℝ) ≤ z := by
  have htlo : (1 / 12000 : ℝ) ≤ t := by linarith
  have hprod : 0 ≤ (t - 1 / 12000) * (t + 1 / 12000) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem quantitative_numeric_contradiction (d z t : ℝ)
    (hd : d ^ 2 ≤ (60 / 11 : ℝ) * epsilon)
    (_hzlo : 0 ≤ z) (hzhi : z ≤ 19 * (2 * epsilon + |d|))
    (ht : 0 ≤ t) (htsq : t ^ 2 = z)
    (hdeficit : (1 / 200 : ℝ) ≤ 60 * t) : False := by
  have heta := eta_numeric_bound d hd
  have hzsmall : z < 57 / (10 : ℝ) ^ 10 := by nlinarith
  have hzlarge := zeta_numeric_lower_bound z t ht htsq hdeficit
  have hgap : (57 / (10 : ℝ) ^ 10) < (1 / 144000000 : ℝ) := by norm_num
  linarith

theorem quantitative_perturbation_constants (eta : ℝ)
    (_heta0 : 0 ≤ eta) (heta : eta < 3 / (10 : ℝ) ^ 10) :
    eta ≤ 1 / (10 : ℝ) ^ 5 ∧
    eta ≤ 1 / (10 : ℝ) ^ 3 ∧
    (1 / 3 : ℝ) - epsilon - 27 / 2 * eta ≥ 1 / 4 ∧
    (1 / 81 : ℝ) - 332 * eta ≥ 1 / 162 ∧
    (1 / 162 : ℝ) - 19 * eta ≥ 1 / 200 := by
  norm_num [epsilon] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/- The anisotropy improvement follows from scalar moment assumptions alone.
   Neither a selection bound nor its conclusion is assumed. -/
theorem certificate_support_bound (d a b : ℝ)
    (hdlo : -1 ≤ d) (hdhi : d ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h d a b) : a + b ≤ 13 / 10 := by
  have hx : 0 < x d := by unfold x; linarith
  have hy : 0 < y d := by unfold y; linarith
  have hxy : a * y d + b * x d ≤ x d * y d := by
    unfold h P at hh
    linarith
  by_cases hd : 0 ≤ d
  · have hyx : y d ≤ x d := by unfold x y; linarith
    have hbxy := mul_nonneg hb (sub_nonneg.mpr hyx)
    have hs : a + b ≤ x d := by nlinarith
    have hxhi : x d ≤ 13 / 10 := by unfold x; linarith
    linarith
  · have hxy' : x d ≤ y d := by unfold x y; linarith
    have haxy := mul_nonneg ha (sub_nonneg.mpr hxy')
    have hs : a + b ≤ y d := by nlinarith
    have hyhi : y d ≤ 13 / 10 := by unfold y; linarith
    linarith

theorem certificate_anisotropy_bound (r a b : ℝ)
    (hrlo : 0 ≤ r) (hrhi : r ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ h (2 * r - 1) a b) :
    g r a b ≤ 5 / 6 - (11 / 60 : ℝ) * (2 * r - 1) ^ 2 := by
  let d := 2 * r - 1
  have hdlo : -1 ≤ d := by dsimp [d]; linarith
  have hdhi : d ≤ 1 := by dsimp [d]; linarith
  have hx : 0 < x d := by unfold x; linarith
  have hy : 0 < y d := by unfold y; linarith
  have hp : 0 < P d := mul_pos hx hy
  have hd2 : d ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ d + 1) (by linarith : 0 ≤ 1 - d)]
  have hq : 0 < Q d := by unfold Q; nlinarith
  have hh' : 0 ≤ h d a b := hh
  have ht2 : 0 ≤ h d a b * (Q d + a * x d + b * y d) := by positivity
  have ht3 : 0 ≤ a * b * (x d - y d) ^ 2 := by positivity
  have hi := certificate_identity d a b
  have hf : F d a b ≤ -(121 / 100 : ℝ) * d ^ 2 := by nlinarith
  have hs := certificate_support_bound d a b hdlo hdhi ha hb hh'
  have hg := certificate_cost_bound r a b hrlo hrhi ha hb hh
  have hcost := cost_identity r a b ha hb
  have hprod : 0 ≤ (13 / 10 - (a + b)) * (5 / 6 - g r a b) :=
    mul_nonneg (by linarith) (by linarith)
  dsimp [d] at hf
  nlinarith

theorem scalar_anisotropy_selection {ι : Type*} [Fintype ι]
    (p a b : ι → ℝ) (r : ℝ)
    (hp : ∀ i, 0 ≤ p i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsum : ∑ i, p i = 1) (hrlo : 0 ≤ r) (hrhi : r ≤ 1)
    (hamean : ∑ i, p i * a i = r) (hbmean : ∑ i, p i * b i = 1 - r) :
    ∃ i, 0 < p i ∧ g r (a i) (b i) ≤
      5 / 6 - (11 / 60 : ℝ) * (2 * r - 1) ^ 2 := by
  have hm := certificate_mean p a b r hsum hamean hbmean
  have hnonneg : 0 ≤ ∑ i, p i * h (2 * r - 1) (a i) (b i) := by
    rw [hm]
    positivity
  obtain ⟨i, hpi, hhi⟩ := weighted_nonnegative_witness p
    (fun i => h (2 * r - 1) (a i) (b i)) hp hsum hnonneg
  exact ⟨i, hpi,
    certificate_anisotropy_bound r (a i) (b i) hrlo hrhi (ha i) (hb i) hhi⟩

end WeightedSelectionScalar

#eval Lean.versionString
#print axioms WeightedSelectionScalar.certificate_identity
#print axioms WeightedSelectionScalar.certificate_implies
#print axioms WeightedSelectionScalar.cost_identity
#print axioms WeightedSelectionScalar.scalar_moment_selection
#print axioms WeightedSelectionScalar.scalar_bound_necessary
#print axioms WeightedSelectionScalar.scalar_relaxation_optimal
#print axioms WeightedSelectionScalar.isotropic_equality_impossible
#print axioms WeightedSelectionScalar.isotropic_ratio_bound
#print axioms WeightedSelectionScalar.delta_numeric_bound
#print axioms WeightedSelectionScalar.eta_numeric_bound
#print axioms WeightedSelectionScalar.zeta_numeric_lower_bound
#print axioms WeightedSelectionScalar.quantitative_numeric_contradiction
#print axioms WeightedSelectionScalar.quantitative_perturbation_constants
#print axioms WeightedSelectionScalar.certificate_support_bound
#print axioms WeightedSelectionScalar.certificate_anisotropy_bound
#print axioms WeightedSelectionScalar.scalar_anisotropy_selection
#eval "SCALAR_CHECK_COMPLETE"
