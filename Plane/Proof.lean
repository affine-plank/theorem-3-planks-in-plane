/- Complete proof of the affine plank theorem for three planks in the plane. -/
module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Radon
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Pseudo.Real
@[expose] public section
set_option autoImplicit false
noncomputable section

/-!
# Proof guide

The statement and definitions for readers are in `Plane.lean`. This file is
ordered by dependency; its final theorem is `three_planks_cover_convex`.

The argument has three main steps, corresponding to the paper:

* `FiniteCover.fixed_rows_count`: a deficient cover needs at least six frozen
  affine constraints, since otherwise its endpoints can slide to the boundary.
* `FiniteCover.constant_stars_of_deficit_of_rows`: the cube count and deletion
  of redundant constraints leave the six empty same-sign pair caps.
* `SupportingSlopes.width_of_chosen`: slopes chosen toward one obey the plane's
  inequalities, which give the width bound in `WidthInequality.width_bound`.

`FiniteCover.finite_width_bound` assembles these steps. `Coordinates` normalizes
the finite hull and handles zero coefficients in the plane relation. The final
section reduces an arbitrary convex set to six directional witnesses.

The earlier sections supply the segment, incidence, and boundary lemmas used in
these steps. Compactness is used for the bounded space of window endpoints;
the covered set itself need not be closed or bounded.

The public `Plank` is a nonconstant affine function with its interval fixed to
`[0, 1]`. Here the coordinates are the three affine functions, so planks become
coordinate windows `lo i ≤ x i ≤ hi i`. The endpoint argument varies `lo` and
`hi`; `Windows.Walls` keeps these six parameters in an ordinary vector space.
-/

/- A segment between two disjoint strict cuts bounds their cross product. -/

namespace PlaneProof.DisjointCuts
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A segment joining the two strict cuts cannot pass through their intersection. -/
theorem cross_bound (K : Set E) (hK : Convex ℝ K) (g h : E →ᵃ[ℝ] ℝ)
    (p q : E) (hp : p ∈ K) (hq : q ∈ K) (hgp : 0 < g p) (hhq : 0 < h q)
    (he : ¬ ∃ x ∈ K, 0 < g x ∧ 0 < h x) :
    g p * h q ≤ g q * h p := by
  have hhp : h p ≤ 0 := le_of_not_gt (fun hh => he ⟨p, hp, hgp, hh⟩)
  have hgq : g q ≤ 0 := le_of_not_gt (fun hg => he ⟨q, hq, hg, hhq⟩)
  let D := g p - h p + h q - g q
  have hD : 0 < D := by dsimp [D]; linarith only [hgp, hhq, hhp, hgq]
  let t := (g p - h p) / D
  have ht : 0 ≤ t := div_nonneg (by linarith only [hgp, hhp]) hD.le
  have ht1 : t ≤ 1 := (div_le_one hD).mpr (by dsimp [D]; linarith only [hhq, hgq])
  have hx := hK.lineMap_mem hp hq ⟨ht, ht1⟩
  have hvals :
      g (AffineMap.lineMap p q t) = (g p * h q - g q * h p) / D ∧
      h (AffineMap.lineMap p q t) = (g p * h q - g q * h p) / D := by
    constructor <;> rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring] <;>
      dsimp [t] <;> field_simp <;> dsimp [D] <;> ring
  by_contra! hn
  exact he ⟨_, hx, hvals.1 ▸ div_pos (sub_pos.mpr hn) hD,
    hvals.2 ▸ div_pos (sub_pos.mpr hn) hD⟩

end PlaneProof.DisjointCuts

/- On a finite convex hull, one slope choice gives separation and tangency. -/

namespace PlaneProof.SupportingSlopes

/-- A positive supporting slope, chosen as close to one as feasibility allows.
Away from one, the corresponding cap contains a point of tangency. -/
structure Chosen {ι : Type*} (g h : ι → ℝ) (s : ℝ) : Prop where
  positive : 0 < s
  supports : ∀ v, g v + s * h v ≤ 0
  touch_of_one_lt : 1 < s → ∃ v, 0 < g v ∧ g v + s * h v = 0
  touch_of_lt_one : s < 1 → ∃ v, 0 < h v ∧ g v + s * h v = 0

/-- The largest lower slope bound and smallest upper bound select the
feasible slope toward one, with both required tangency witnesses. -/
theorem choose {ι : Type*} [Fintype ι] (g h : ι → ℝ)
    (hp : ∃ p, 0 < g p)
    (hsign : ∀ p, 0 < g p → h p < 0)
    (hcross : ∀ p q, 0 < g p → 0 < h q → g p * h q ≤ g q * h p) :
    ∃ s, Chosen g h s := by
  classical
  obtain ⟨p₀, hp₀⟩ := hp
  let l : ι → ℝ := fun v => if 0 < g v then g v / (-h v) else 0
  let u : ι → ℝ := fun v => if 0 < h v then (-g v) / h v else 1
  obtain ⟨p, _, hmax⟩ := Finset.exists_max_image Finset.univ l ⟨p₀, Finset.mem_univ _⟩
  obtain ⟨q, _, hmin⟩ := Finset.exists_min_image Finset.univ u ⟨p₀, Finset.mem_univ _⟩
  have hpos : 0 < l p := (show 0 < l p₀ by
    simpa [l, hp₀] using div_pos hp₀ (neg_pos.mpr (hsign p₀ hp₀))).trans_le
      (hmax p₀ (Finset.mem_univ _))
  have hp : 0 < g p := by
    by_contra hn
    simp [l, hn] at hpos
  have bound (v : ι) (hv : 0 < h v) : l p ≤ (-g v) / h v := by
    simp only [l, if_pos hp]
    apply (div_le_div_iff₀ (neg_pos.mpr (hsign p hp)) hv).mpr
    nlinarith only [hcross p v hp hv]
  have hmin_one : u q ≤ 1 := by
    have H := hmin p (Finset.mem_univ _)
    simpa [u, not_lt_of_ge (hsign p hp).le] using H
  let s := max (l p) (u q)
  refine ⟨s, hpos.trans_le (le_max_left _ _), ?_, ?_, ?_⟩
  · intro v
    by_cases hg : 0 < g v
    · have H : g v / (-h v) ≤ s := by
        calc g v / (-h v) = l v := by simp [l, hg]
             _ ≤ l p := hmax v (Finset.mem_univ _)
             _ ≤ s := le_max_left _ _
      have H := (div_le_iff₀ (neg_pos.mpr (hsign v hg))).mp H
      nlinarith only [H]
    · by_cases hh : 0 < h v
      · have H : s ≤ (-g v) / h v := max_le (bound v hh) (by
          simpa [u, hh] using hmin v (Finset.mem_univ _))
        have H := (le_div_iff₀ hh).mp H
        linarith only [H]
      · exact add_nonpos (le_of_not_gt hg) (mul_nonpos_of_nonneg_of_nonpos
          (hpos.trans_le (le_max_left _ _)).le (le_of_not_gt hh))
  · intro hgt
    have H : 1 < l p := (lt_max_iff.mp hgt).resolve_right (not_lt_of_ge hmin_one)
    have hs : s = l p := max_eq_left (hmin_one.trans H.le)
    have he : l p * (-h p) = g p := by
      simp only [l, if_pos hp]
      exact div_mul_cancel₀ _ (neg_ne_zero.mpr (hsign p hp).ne)
    exact ⟨p, hp, by rw [hs]; nlinarith only [he]⟩
  · intro hlt
    have H : u q < 1 := (le_max_right _ _).trans_lt hlt
    have hq : 0 < h q := by
      by_contra hn
      simp [u, hn] at H
    have H : l p ≤ u q := by simpa [u, hq] using bound q hq
    have hs : s = u q := max_eq_right H
    have he : u q * h q = -g q := by
      simp only [u, if_pos hq]
      exact div_mul_cancel₀ _ hq.ne'
    exact ⟨q, hq, by rw [hs]; linarith only [he]⟩

/-- The chosen finite separator holds on the full convex hull. Thus one finite
construction supplies both frozen supporting rows and ordered tangencies. -/
theorem chosen_on_hull {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (X : ι → E) (g h : E →ᵃ[ℝ] ℝ)
    (hp : ∃ v, 0 < g (X v)) (hq : ∃ v, 0 < h (X v))
    (he : ¬ ∃ x ∈ convexHull ℝ (Set.range X), 0 < g x ∧ 0 < h x) :
    ∃ s, Chosen (fun v => g (X v)) (fun v => h (X v)) s ∧
      ∀ x ∈ convexHull ℝ (Set.range X), g x + s * h x ≤ 0 := by
  let K := convexHull ℝ (Set.range X)
  have hX (v) : X v ∈ K := subset_convexHull ℝ _ ⟨v, rfl⟩
  obtain ⟨q, hq⟩ := hq
  have hc (p q : ι) (hp : 0 < g (X p)) (hq : 0 < h (X q)) :=
    DisjointCuts.cross_bound K (convex_convexHull ℝ _) g h
      (X p) (X q) (hX p) (hX q) hp hq he
  have hsign (p) (hp : 0 < g (X p)) : h (X p) < 0 := by
    have hgq : g (X q) ≤ 0 := le_of_not_gt (fun hg => he ⟨X q, hX q, hg, hq⟩)
    by_contra! hn
    exact (mul_pos hp hq).not_ge ((hc p q hp hq).trans
      (mul_nonpos_of_nonpos_of_nonneg hgq hn))
  obtain ⟨s, hs⟩ := choose _ _ hp hsign hc
  refine ⟨s, hs, ?_⟩
  exact convexHull_min (by rintro x ⟨v, rfl⟩; exact hs.supports v)
    ((convex_Iic (0 : ℝ)).affine_preimage (g + s • h))

end PlaneProof.SupportingSlopes

/- The paper's six-support width criterion, with all numerical steps together. -/
namespace PlaneProof.WidthInequality
open scoped BigOperators
abbrev Triple := Fin 3 → ℝ

/-- Eliminate the other two coordinates with three alternating inequalities. -/
theorem three_rows (x y z a b c A B C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : x + a*y ≤ A) (h₂ : B ≤ y + b*z) (h₃ : z + c*x ≤ C) :
    (1 + a*b*c)*x ≤ A - a*B + a*b*C := by
  have h₂ := mul_le_mul_of_nonneg_left h₂ ha
  have h₃ := mul_le_mul_of_nonneg_left h₃ (mul_nonneg ha hb)
  nlinarith only [h₁, h₂, h₃]

/-- Nonnegative pair and cycle coefficients make three linear budgets sufficient. -/
private theorem budget_bound (E F H w S R : Triple)
    (hw : ∀ i, 0 ≤ w i) (hR : ∀ i, 0 < R i) (hE : ∀ i, 0 < E i)
    (hs : ∀ i, S i = E i * w i + F i * w (i+1) + H i * w (i+2))
    (hoff : ∀ i, 0 ≤ S i - E i * w i) (hbudget : ∀ i, E i * R i ≤ S i)
    (hp : ∀ i, 0 ≤ E i * E (i+1) - F i * H (i+1))
    (hc : 0 ≤ 2 * (∏ i, E i) - (∏ i, F i) - (∏ i, H i)) :
    1 ≤ ∑ i, w i / R i := by
  have hS (i) : 0 < S i := (mul_pos (hE i) (hR i)).trans_le (hbudget i)
  have hrem : 0 ≤ (∑ i, E i * w i * S (i+1) * S (i+2)) - (∏ i, S i) := by
    calc
      0 ≤ (2 * (∏ i, E i) - (∏ i, F i) - (∏ i, H i)) * (∏ i, w i) +
          ∑ i, (E i * E (i+1) - F i * H (i+1)) * w i * w (i+1) *
            (S (i+2) - E (i+2) * w (i+2)) :=
        add_nonneg (mul_nonneg hc (Finset.prod_nonneg fun i _ => hw i))
          (Finset.sum_nonneg fun i _ => by
            positivity [hp i, hw i, hw (i+1), hoff (i+2)])
      _ = _ := by simp [hs, Fin.sum_univ_three, Fin.prod_univ_three]; ring
  have hcompare (i : Fin 3) : E i * w i ≤ (w i / R i) * S i := by
    have h := mul_le_mul_of_nonneg_left (hbudget i) (div_nonneg (hw i) (hR i).le)
    rwa [mul_left_comm, div_mul_cancel₀ _ (hR i).ne'] at h
  have hbound := (sub_nonneg.mp hrem).trans (Finset.sum_le_sum
    (fun i _ => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hcompare i) (hS (i+1)).le) (hS (i+2)).le))
  have heq : (∑ i, (w i / R i) * S i * S (i+1) * S (i+2)) =
      (∑ i, w i / R i) * ∏ i, S i := by
    simp [Fin.sum_univ_three, Fin.prod_univ_three]
    ring
  rw [heq] at hbound
  exact (le_mul_iff_one_le_left (Finset.prod_pos (fun i _ => hS i))).mp hbound

/-- Six inequalities and attained coordinate extrema suffice. No convexity,
plane equation, or positive window width is assumed in this numerical lemma. -/
theorem width_bound {ι : Type*} (X : ι → Triple) (lo hi R a b : Triple)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (horder : ∀ i, lo i ≤ hi i) (hR : ∀ i, 0 < R i)
    (hzero : ∀ i, ∃ v, X v i = 0) (hmax : ∀ i, ∃ v, X v i = R i)
    (hupper : ∀ i v, X v i + a i * X v (i+1) ≤ hi i + a i * hi (i+1))
    (hlower : ∀ i v, lo i + b i * lo (i+1) ≤ X v i + b i * X v (i+1))
    (hab : ∀ i, a (i+1) * (1-b i) ≤ 1)
    (hba : ∀ i, b (i+1) * (1-a i) ≤ 1) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  let w : Triple := fun i => hi i - lo i
  change 1 ≤ ∑ i, w i / R i
  let L : Triple := fun i => 1 + b i * a (i+1) * b (i+2)
  let U : Triple := fun i => 1 + a i * b (i+1) * a (i+2)
  let E : Triple := fun i => L i * U i
  let F : Triple := fun i => b i * U i + a i * L i
  let H : Triple := fun i => b i * a (i+1) * U i + a i * b (i+1) * L i
  let S : Triple := fun i => E i * w i + F i * w (i+1) + H i * w (i+2)
  let q : Triple := fun i => 1 - a (i+1) + a (i+1) * b i
  let r : Triple := fun i => 1 - b (i+1) + b (i+1) * a i
  let G := (∏ i, q i) + (∏ i, r i) + ∑ i, (a (i+2) + b (i+2)) * q i * r i
  have hw (i) : 0 ≤ w i := sub_nonneg.mpr (horder i)
  have hL (i) : 0 < L i := by dsimp [L]; positivity [hb i, ha (i+1), hb (i+2)]
  have hU (i) : 0 < U i := by dsimp [U]; positivity [ha i, hb (i+1), ha (i+2)]
  have hE (i) : 0 < E i := mul_pos (hL i) (hU i)
  have hq (i) : 0 ≤ q i := by dsimp [q]; nlinarith only [hab i]
  have hr (i) : 0 ≤ r i := by dsimp [r]; nlinarith only [hba i]
  have hG : 0 ≤ G := add_nonneg
    (add_nonneg (Finset.prod_nonneg (fun i _ => hq i)) (Finset.prod_nonneg (fun i _ => hr i)))
    (Finset.sum_nonneg fun i _ => by positivity [ha (i+2), hb (i+2), hq i, hr i])
  have hbudget (i : Fin 3) : E i * R i ≤ S i := by
    have hn : (i+1)+1 = i+2 := by fin_cases i <;> rfl
    have hp : (i+2)+1 = i := by fin_cases i <;> rfl
    obtain ⟨p, hpi⟩ := hmax i
    obtain ⟨z, hzi⟩ := hzero i
    have hupper' (v) := hupper (i+2) v
    have hlower' (v) := hlower (i+2) v
    simp only [hp] at hupper' hlower'
    have hupper'' (v) := hupper (i+1) v
    have hlower'' (v) := hlower (i+1) v
    simp only [hn] at hupper'' hlower''
    have upper := three_rows _ _ _ _ _ _ _ _ _ (ha i) (hb (i+1))
      (hupper i p) (hlower'' p) (hupper' p)
    have lower := three_rows (-X z i) (-X z (i+1)) (-X z (i+2))
      (b i) (a (i+1)) (b (i+2))
      (-lo i - b i * lo (i+1)) (-hi (i+1) - a (i+1) * hi (i+2))
      (-lo (i+2) - b (i+2) * lo i) (hb i) (ha (i+1))
      (by nlinarith only [hlower i z])
      (by nlinarith only [hupper'' z])
      (by nlinarith only [hlower' z])
    rw [hpi] at upper
    rw [hzi] at lower
    have upper := mul_le_mul_of_nonneg_left upper (hL i).le
    have lower := mul_le_mul_of_nonneg_left lower (hU i).le
    dsimp only [S, E, F, H, w, L, U] at *
    linarith only [upper, lower]
  have hoff (i) : 0 ≤ S i - E i * w i := by
    simp only [S, add_assoc, add_sub_cancel_left]
    dsimp only [F, H]
    positivity [ha i, hb i, hL i, hU i, ha (i+1), hb (i+1), hw (i+1), hw (i+2)]
  let d := ((∏ i, a i) * (∏ i, b i) - 1)^2
  have hp (i : Fin 3) : 0 ≤ E i * E (i+1) - F i * H (i+1) := by
    have he : E i * E (i+1) - F i * H (i+1) = d := by
      fin_cases i <;> simp [F, H, E, L, U, d, Fin.prod_univ_three] <;> ring
    rw [he]
    exact sq_nonneg _
  have hc : 0 ≤ 2 * (∏ i, E i) - (∏ i, F i) - (∏ i, H i) := by
    have he : 2 * (∏ i, E i) - (∏ i, F i) - (∏ i, H i) = d * G := by
      simp [F, H, E, L, U, d, G, q, r, Fin.prod_univ_three, Fin.sum_univ_three]
      ring
    rw [he]
    exact mul_nonneg (sq_nonneg _) hG
  exact budget_bound E F H w S R hw hR hE (fun _ => rfl) hoff hbudget hp hc

end PlaneProof.WidthInequality

/- Ordered finite tangencies imply the six-support width criterion. -/
namespace PlaneProof.SupportingSlopes
open scoped BigOperators

abbrev Point := Fin 3 → ℝ

/-- Adjacent chosen supports have ordered tangencies whenever their slope
inequality is not immediate from comparison with one. -/
theorem chosen_weight {ι : Type*} (x y z : ι → ℝ)
    (lx ly hy hz D a b : ℝ) (horder : ly ≤ hy)
    (hplane : ∀ v, x v + y v + z v = D)
    (ha : Chosen (fun v => y v - hy) (fun v => z v - hz) a)
    (hb : Chosen (fun v => lx - x v) (fun v => ly - y v) b) :
    a * (1 - b) ≤ 1 := by
  by_cases ha₁ : a ≤ 1
  · nlinarith only [ha₁, mul_pos ha.positive hb.positive]
  by_cases hb₁ : 1 ≤ b
  · have hm := mul_nonneg ha.positive.le (sub_nonneg.mpr hb₁)
    nlinarith only [hm]
  obtain ⟨p, hp, hep⟩ := ha.touch_of_one_lt (lt_of_not_ge ha₁)
  obtain ⟨q, hq, heq⟩ := hb.touch_of_lt_one (lt_of_not_ge hb₁)
  have hu := ha.supports q
  have hl := hb.supports p
  have hw : 0 < y p - y q := by linarith only [hp, hq, horder]
  have hplane' : x p - x q + (y p - y q) = z q - z p := by
    linarith only [hplane p, hplane q]
  have hupper : a * (z q - z p) ≤ y p - y q := by nlinarith only [hu, hep]
  have hlower : -b * (y p - y q) ≤ x p - x q := by nlinarith only [hl, heq]
  have hscaled := mul_le_mul_of_nonneg_left hlower ha.positive.le
  rw [← hplane'] at hupper
  apply (mul_le_mul_iff_left₀ hw).mp
  nlinarith only [hupper, hscaled]

theorem weights_of_chosen {ι : Type*} (X : ι → Point)
    (lo hi a b : Point) (D : ℝ) (horder : ∀ i, lo i ≤ hi i)
    (hplane : ∀ v, ∑ i, X v i = D)
    (ha : ∀ i, Chosen (fun v => X v i - hi i)
      (fun v => X v (i + 1) - hi (i + 1)) (a i))
    (hb : ∀ i, Chosen (fun v => lo i - X v i)
      (fun v => lo (i + 1) - X v (i + 1)) (b i)) :
    (∀ i, a (i + 1) * (1 - b i) ≤ 1) ∧
    (∀ i, b (i + 1) * (1 - a i) ≤ 1) := by
  have hsum (v : ι) (i : Fin 3) : X v i + X v (i + 1) + X v (i + 2) = D := by
    calc
      _ = ∑ j, X v j := by fin_cases i <;> simp only [Fin.sum_univ_three] <;> ring!
      _ = D := hplane v
  have hn (i : Fin 3) : (i + 1) + 1 = i + 2 := by fin_cases i <;> rfl
  constructor
  · intro i
    apply chosen_weight (fun v => X v i) (fun v => X v (i + 1))
      (fun v => X v (i + 2)) (lo i) (lo (i + 1)) (hi (i + 1)) (hi (i + 2)) D
      (a (i + 1)) (b i) (horder _) (fun v => hsum v i)
    · simpa only [hn] using ha (i + 1)
    · exact hb i
  · intro i
    apply chosen_weight (fun v => -X v i) (fun v => -X v (i + 1))
      (fun v => -X v (i + 2)) (-hi i) (-hi (i + 1)) (-lo (i + 1)) (-lo (i + 2)) (-D)
      (b (i + 1)) (a i) (neg_le_neg (horder _))
      (fun v => by linarith only [hsum v i])
    · simpa only [hn, sub_neg_eq_add, neg_add_eq_sub] using hb (i + 1)
    · simpa only [neg_sub_neg] using ha i

/-- Chosen tangencies give the slope slacks used by the support budgets. -/
theorem width_of_chosen {ι : Type*} (X : ι → Point)
    (lo hi R a b : Point) (D : ℝ)
    (horder : ∀ i, lo i ≤ hi i) (hR : ∀ i, 0 < R i)
    (hplane : ∀ v, ∑ i, X v i = D)
    (hzero : ∀ i, ∃ v, X v i = 0) (hmax : ∀ i, ∃ v, X v i = R i)
    (ha : ∀ i, Chosen (fun v => X v i - hi i)
      (fun v => X v (i + 1) - hi (i + 1)) (a i))
    (hb : ∀ i, Chosen (fun v => lo i - X v i)
      (fun v => lo (i + 1) - X v (i + 1)) (b i)) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  obtain ⟨hab, hba⟩ := weights_of_chosen X lo hi a b D horder hplane ha hb
  apply WidthInequality.width_bound X lo hi R a b
    (fun i => (ha i).positive.le) (fun i => (hb i).positive.le) horder hR hzero hmax
  · intro i v; nlinarith only [(ha i).supports v]
  · intro i v; nlinarith only [(hb i).supports v]
  · exact hab
  · exact hba

end PlaneProof.SupportingSlopes

/- A finite family with a private vertex for every member has few incidences.
The estimate applies to minimal covers by arbitrary finite sets. -/
namespace PlaneProof.Incidence
open scoped BigOperators

variable {E V : Type*} [Fintype V]
  (s : Finset E) (hits : E → V → Prop) [DecidableRel hits]

def degree (v : V) : ℕ := (s.filter fun e => hits e v).card

/-- Count the incidences by vertices or by selected members. -/
theorem double_count : (∑ v, degree s hits v) =
    ∑ e ∈ s, (Finset.univ.filter (hits e)).card := by
  simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- A private vertex has degree one. Choosing one for each selected member
leaves at most `card V - card s` vertices with larger degree. -/
theorem bound (r : ℕ)
    (hp : ∀ e ∈ s, ∃ v, hits e v ∧ ∀ f ∈ s, hits f v → f = e)
    (hd : ∀ v, degree s hits v ≤ r) :
    (∑ v, degree s hits v) + r * s.card ≤ r * Fintype.card V + s.card := by
  classical
  choose p hp hu using fun e : s => hp e e.property
  have hinj : Function.Injective p := by
    intro e f hef
    apply Subtype.ext
    exact (hu f e e.property (by rw [← hef]; exact hp e))
  let L : Finset V := Finset.univ.image p
  have hcard : L.card = s.card := by
    simp [L, Finset.card_image_of_injective _ hinj]
  have hone (v : V) (hv : v ∈ L) : degree s hits v = 1 := by
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.card_eq_one.mpr
    refine ⟨e, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun hf => hu e f hf.1 hf.2
    · rintro rfl
      exact ⟨e.property, hp e⟩
  have hsplit : L.card + Lᶜ.card = Fintype.card V := by
    simp
  have hsum : (∑ v, degree s hits v) ≤ L.card + r * Lᶜ.card := by
    rw [← Finset.sum_add_sum_compl L]
    calc
      _ ≤ (∑ _v ∈ L, 1) + ∑ _v ∈ Lᶜ, r := add_le_add
        (Finset.sum_le_sum fun v hv => (hone v hv).le)
        (Finset.sum_le_sum fun v _ => hd v)
      _ = _ := by simp [Nat.mul_comm]
  rw [← hcard, ← hsplit]
  nlinarith only [hsum]

end PlaneProof.Incidence

/- A cube edge is a coordinate to leave free and two prescribed signs.
The other two selections are the constant-sign vertices. -/
namespace PlaneProof.CubeCover
open scoped BigOperators
open PlaneProof

abbrev Vertex := Fin 3 → Bool
abbrev Edge := Fin 3 × Bool × Bool
abbrev Selection := Edge ⊕ Bool

def edge (i : Fin 3) (v : Vertex) : Selection := .inl (i, v (i + 1), v (i + 2))
def constant (b : Bool) : Vertex := fun _ => b

def hits : Selection → Vertex → Prop
  | .inl (i, b, c), v => v (i + 1) = b ∧ v (i + 2) = c
  | .inr b, v => v = constant b

instance : DecidableRel hits := fun e v => by cases e <;> dsimp [hits] <;> infer_instance

def minimalCover (s : Finset Selection) : Prop :=
  (∀ v, ∃ e ∈ s, hits e v) ∧
  ∀ e ∈ s, ∃ v, hits e v ∧ ∀ f ∈ s, hits f v → f = e

def star (s : Finset Selection) (v : Vertex) : Prop := ∀ i, edge i v ∈ s
def degree (s : Finset Selection) (v : Vertex) : ℕ := Incidence.degree s hits v
def singletons (s : Finset Selection) : ℕ := (s.filter fun e => e.isRight).card
def incidentEdges (v : Vertex) : Finset Selection :=
  Finset.univ.filter fun e => e.isLeft ∧ hits e v

theorem edge_hits (i : Fin 3) (v : Vertex) : hits (edge i v) v := ⟨rfl, rfl⟩
theorem incidentEdges_card : ∀ v, (incidentEdges v).card = 3 := by decide +kernel

theorem singleton_degree (s : Finset Selection) (h : minimalCover s)
    (b : Bool) (he : Sum.inr b ∈ s) : degree s (constant b) = 1 := by
  obtain ⟨v, rfl, hu⟩ := h.2 (.inr b) he
  apply Finset.card_eq_one.mpr
  refine ⟨.inr b, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_singleton]
  exact ⟨fun hf => hu f hf.1 hf.2, fun hf => hf ▸ ⟨he, rfl⟩⟩

theorem degree_bound (s : Finset Selection) (h : minimalCover s) (v : Vertex) :
    degree s v ≤ 3 ∧ (2 < degree s v → star s v) := by
  by_cases hs : ∃ b, Sum.inr b ∈ s ∧ v = constant b
  · obtain ⟨b, he, rfl⟩ := hs
    rw [singleton_degree s h b he]
    exact ⟨by decide, fun hn => (by omega : False).elim⟩
  · have hsub : s.filter (fun e => hits e v) ⊆ incidentEdges v := by
      intro e he
      obtain ⟨he, hev⟩ := Finset.mem_filter.mp he
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_, hev⟩
      cases e with
      | inl a => rfl
      | inr b => exact (hs ⟨b, he, hev⟩).elim
    have hle : degree s v ≤ 3 := (Finset.card_le_card hsub).trans_eq (incidentEdges_card v)
    refine ⟨hle, fun hgt i => ?_⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [incidentEdges_card]
      change 3 ≤ degree s v
      omega)
    have hin : edge i v ∈ s.filter (fun e => hits e v) := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, edge_hits i v⟩
    exact (Finset.mem_filter.mp hin).1

theorem incidence_count (s : Finset Selection) :
    (∑ v, degree s v) + singletons s = 2 * s.card := by
  have hsize : ∀ e : Selection, (Finset.univ.filter (hits e)).card +
      (if e.isRight then 1 else 0) = 2 := by decide +kernel
  calc
    (∑ v, degree s v) + singletons s =
        ∑ e ∈ s, ((Finset.univ.filter (hits e)).card +
          (if e.isRight then 1 else 0)) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact Incidence.double_count s hits
      · simp only [singletons, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ _e ∈ s, 2 := Finset.sum_congr rfl fun e _ => hsize e
    _ = 2 * s.card := by simp [Nat.mul_comm]

theorem singletons_le_two (s : Finset Selection) : singletons s ≤ 2 := by
  exact (Finset.card_le_card
    (Finset.filter_subset_filter _ (Finset.subset_univ s))).trans_eq (by decide +kernel)

theorem singletons_le_one (s : Finset Selection)
    (h : ¬ (Sum.inr false ∈ s ∧ Sum.inr true ∈ s)) : singletons s ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨he, hse⟩ := Finset.mem_filter.mp he
  obtain ⟨hf, hsf⟩ := Finset.mem_filter.mp hf
  cases e with
  | inl a => cases hse
  | inr b =>
    cases f with
    | inl a => cases hsf
    | inr c => cases b <;> cases c <;> simp_all

theorem edge_distinct : ∀ i v, edge (i + 1) v ≠ edge i v := by decide +kernel

theorem other_endpoint : ∀ (i : Fin 3) (u v w : Vertex),
    hits (edge i v) u → hits (edge i v) w → u ≠ v → w ≠ v → u = w := by decide +kernel

/-- Every leaf of a selected full star is private to its incident edge. -/
theorem star_leaf (s : Finset Selection) (h : minimalCover s) (v : Vertex)
    (hs : star s v) (i : Fin 3) (w : Vertex)
    (hw : hits (edge i v) w) (hne : w ≠ v) :
    ∀ f ∈ s, hits f w → f = edge i v := by
  obtain ⟨u, hu, hunique⟩ := h.2 (edge i v) (hs i)
  have huv : u ≠ v := by
    intro huv
    exact edge_distinct i v (hunique _ (hs (i + 1)) (by
      simpa only [huv] using edge_hits (i + 1) v))
  simpa only [other_endpoint i u v w hu hw huv hne] using hunique

def leaf (b : Bool) (i : Fin 3) : Vertex := fun j => if j = i then !b else b

theorem leaf_incidence : ∀ b i,
    hits (edge i (constant b)) (leaf b i) ∧ leaf b i ≠ constant b := by decide +kernel

/-- At distance two from a constant vertex, the other incident edges
meet its private leaves. The constant singleton selections do not occur. -/
theorem opposite_incidence : ∀ b i f, hits f (leaf (!b) i) →
    f = edge i (constant (!b)) ∨
    (hits f (leaf b (i + 1)) ∧ f ≠ edge (i + 1) (constant b)) ∨
    (hits f (leaf b (i + 2)) ∧ f ≠ edge (i + 2) (constant b)) := by
  intro b i f
  fin_cases b <;> fin_cases i <;> fin_cases f <;> decide

theorem constant_stars (s : Finset Selection) (h : minimalCover s)
    (b : Bool) (hs : star s (constant b)) : star s (constant (!b)) := by
  intro i
  obtain ⟨f, hf, hv⟩ := h.1 (leaf (!b) i)
  rcases opposite_incidence b i f hv with rfl | ⟨hv, hne⟩ | ⟨hv, hne⟩
  · exact hf
  · exact (hne (star_leaf s h (constant b) hs (i + 1) (leaf b (i + 1))
      (leaf_incidence _ _).1 (leaf_incidence _ _).2 f hf hv)).elim
  · exact (hne (star_leaf s h (constant b) hs (i + 2) (leaf b (i + 2))
      (leaf_incidence _ _).1 (leaf_incidence _ _).2 f hf hv)).elim

/-- Private vertices give the count; at six, a full star is unavoidable
unless both constant singleton selections occur. -/
theorem cube_count (s : Finset Selection) (h : minimalCover s) :
    s.card ≤ 6 ∧ (s.card = 6 →
      (Sum.inr false ∈ s ∧ Sum.inr true ∈ s) ∨
      (star s (constant false) ∧ star s (constant true)) ∨
      ∃ v, v ≠ constant false ∧ v ≠ constant true ∧ star s v) := by
  have hsum := incidence_count s
  have hthree := Incidence.bound s hits 3 h.2 (fun v => (degree_bound s h v).1)
  have hsingle := singletons_le_two s
  have hvertices : Fintype.card Vertex = 8 := by decide +kernel
  rw [hvertices] at hthree
  change (∑ v, degree s v) + 3 * s.card ≤ 3 * 8 + s.card at hthree
  refine ⟨by omega, fun hcard => ?_⟩
  by_cases hboth : Sum.inr false ∈ s ∧ Sum.inr true ∈ s
  · exact Or.inl hboth
  have hstar : ∃ v, star s v := by
    by_contra! hn
    have htwo := Incidence.bound s hits 2 h.2 (fun v =>
      le_of_not_gt (fun hv => hn v ((degree_bound s h v).2 hv)))
    have hs := singletons_le_one s hboth
    rw [hvertices] at htwo
    change (∑ v, degree s v) + 2 * s.card ≤ 2 * 8 + s.card at htwo
    omega
  obtain ⟨v, hv⟩ := hstar
  by_cases h0 : v = constant false
  · subst v
    exact Or.inr (Or.inl ⟨hv, constant_stars s h false hv⟩)
  by_cases h1 : v = constant true
  · subst v
    exact Or.inr (Or.inl ⟨constant_stars s h true hv, hv⟩)
  exact Or.inr (Or.inr ⟨v, h0, h1, hv⟩)

/-- An inclusion-minimal cover has a private vertex for each selection. -/
theorem exists_minimal_cover (allowed : Selection → Prop)
    (h : ∀ v : Vertex, ∃ e, allowed e ∧ hits e v) :
    ∃ s : Finset Selection, (∀ e ∈ s, allowed e) ∧ minimalCover s := by
  classical
  let t := Finset.univ.filter allowed
  obtain ⟨s, hst, hc, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun s : Finset Selection => ∀ v : Vertex, ∃ e ∈ s, hits e v) t (by
      intro v
      obtain ⟨e, he, hev⟩ := h v
      exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩, hev⟩)
  refine ⟨s, fun e he => (Finset.mem_filter.mp (hst he)).2, hc, ?_⟩
  intro e he
  have herase : ¬ ∀ v : Vertex, ∃ f ∈ s.erase e, hits f v :=
    fun hcover => Finset.notMem_erase e s ((hmin hcover (Finset.erase_subset e s)) he)
  push Not at herase
  obtain ⟨v, hv⟩ := herase
  have unique : ∀ f ∈ s, hits f v → f = e := by
    intro f hf hfv
    by_contra hne
    exact hv f (Finset.mem_erase.mpr ⟨hne, hf⟩) hfv
  obtain ⟨f, hf, hfv⟩ := hc v
  exact ⟨v, unique f hf hfv ▸ hfv, unique⟩

theorem mixed_odd (v : Vertex) (h0 : v ≠ constant false) (h7 : v ≠ constant true) :
    ∃ i, ∀ j, j ≠ i → v j ≠ v i := by
  revert v
  decide +kernel

theorem edge_ne : ∀ (i j : Fin 3) (v : Vertex), i ≠ j → edge i v ≠ edge j v := by
  decide +kernel

theorem omitted_pair_ne : ∀ (i j : Fin 3), i ≠ j →
    ∃ k, k ≠ i ∧ ∀ l, l ≠ k → l = i ∨ l = j := by
  decide +kernel

theorem opposite_edge_endpoints : ∀ (v : Vertex) (i : Fin 3) (w : Vertex),
    (∀ j, j ≠ i → v j ≠ v i) → hits (edge i v) w →
      w = v ∨ w = constant (!v i) := by
  decide +kernel

/-- Replacing the opposite edge of a mixed star by the constant singleton
still covers the cube. -/
theorem replace_star_cover (s : Finset Selection)
    (hcover : ∀ w, ∃ e ∈ s, hits e w)
    (v : Vertex) (i : Fin 3) (hodd : ∀ j, j ≠ i → v j ≠ v i)
    (hv : star s v) :
    ∀ w, ∃ e ∈ insert (.inr (!v i)) (s.erase (edge i v)), hits e w := by
  classical
  intro w
  obtain ⟨e, he, hew⟩ := hcover w
  by_cases heq : e = edge i v
  · subst e
    rcases opposite_edge_endpoints v i w hodd hew with hw | hw
    · exact ⟨edge (i + 1) v, Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨edge_distinct i v, hv (i + 1)⟩), hw ▸ edge_hits _ _⟩
    · exact ⟨.inr (!v i), Finset.mem_insert_self _ _, hw⟩
  · exact ⟨e, Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨heq, he⟩), hew⟩

end PlaneProof.CubeCover

/- Coordinate windows, escape signs, and strict endpoints. -/
namespace PlaneProof.Windows
open Set
open scoped BigOperators Topology

abbrev Point (n : ℕ) := Fin n → ℝ
abbrev Walls (n : ℕ) := Point n × Point n

def cut {n : ℕ} (side : Bool) (i : Fin n) : Point n →L[ℝ] ℝ :=
  if side then ContinuousLinearMap.proj i else -ContinuousLinearMap.proj i

def wall {n : ℕ} (side : Bool) (i : Fin n) : Walls n →L[ℝ] ℝ :=
  if side then (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _)
  else -(ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _)

def Covers {n : ℕ} (K : Set (Point n)) (B : Walls n) : Prop :=
  ∀ x ∈ K, ∃ i, B.1 i ≤ x i ∧ x i ≤ B.2 i

def Escapes {n : ℕ} (B : Walls n) (s : Fin n → Bool) (x : Point n) : Prop :=
  ∀ i, wall (s i) i B < cut (s i) i x

theorem covers_iff_no_escape {n : ℕ} (K : Set (Point n)) (B : Walls n) :
    Covers K B ↔ ∀ s, ¬ ∃ x ∈ K, Escapes B s x := by
  classical
  constructor
  · intro hc s ⟨x, hx, he⟩
    obtain ⟨i, hl, hu⟩ := hc x hx
    have hi := he i
    cases hs : s i <;> simp [wall, cut, hs] at hi <;> linarith
  · intro he x hx
    by_contra hn
    let s : Fin n → Bool := fun i => decide (B.2 i < x i)
    apply he s
    refine ⟨x, hx, ?_⟩
    intro i
    by_cases hh : B.2 i < x i
    · simp [s, wall, cut, hh]
    · have hl : x i < B.1 i := lt_of_not_ge (fun h => hn ⟨i, h, le_of_not_gt hh⟩)
      simp [s, wall, cut, hh, hl]

def coverSet {n : ℕ} (K : Set (Point n)) : Set (Walls n) := {B | Covers K B}

/-- Ordered covering windows with all endpoints in the unit interval. -/
def unitCovers {n : ℕ} (K : Set (Point n)) : Set (Walls n) :=
  (Icc (0, 0) (1, 1) ∩ {B | ∀ i, B.1 i ≤ B.2 i}) ∩ coverSet K

def strictWindows {n : ℕ} : Set (Walls n) :=
  {B | ∀ i, 0 < B.1 i ∧ B.1 i < B.2 i ∧ B.2 i < 1}

theorem open_strictWindows {n : ℕ} : IsOpen (strictWindows (n := n)) := by
  simp only [strictWindows, ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (by fun_prop : Continuous (fun B : Walls n => B.1 i))).inter
    ((isOpen_lt (by fun_prop : Continuous (fun B : Walls n => B.1 i))
      (by fun_prop : Continuous (fun B : Walls n => B.2 i))).inter
      (isOpen_lt (by fun_prop : Continuous (fun B : Walls n => B.2 i)) continuous_const))

theorem unitCovers_of_strict_cover {n : ℕ} (K : Set (Point n))
    (Y : Walls n) (hY : Y ∈ strictWindows) (hc : Covers K Y) : Y ∈ unitCovers K := by
  refine ⟨⟨?_, fun i => (hY i).2.1.le⟩, hc⟩
  constructor
  · exact ⟨fun i => (hY i).1.le, fun i => (hY i).1.le.trans (hY i).2.1.le⟩
  · exact ⟨fun i => (hY i).2.1.le.trans (hY i).2.2.le, fun i => (hY i).2.2.le⟩

theorem closed_coverSet {n : ℕ} (K : Set (Point n)) : IsClosed (coverSet K) := by
  simp only [coverSet, Covers, ofPred_forall, ofPred_exists, ofPred_and]
  exact isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_iUnion_of_finite fun i =>
    (isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le continuous_const (by fun_prop))

theorem compact_unitCovers {n : ℕ} (K : Set (Point n)) : IsCompact (unitCovers K) := by
  apply IsCompact.inter_right
  · apply isCompact_Icc.inter_right
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le (by fun_prop) (by fun_prop)
  · exact closed_coverSet K

end PlaneProof.Windows

/- Helly's argument on a hyperplane of cut values, using Radon's partition. -/
namespace PlaneProof.PlaneCuts
open scoped BigOperators

variable {n : ℕ}

/-- Omission witnesses that are affinely dependent give a common point. -/
theorem common_point_of_dependent_witnesses {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] (F : ι → Set E) (hF : ∀ i, Convex ℝ (F i))
    (p : ι → E) (hp : ∀ i j, j ≠ i → p i ∈ F j)
    (hdep : ¬ AffineIndependent ℝ p) : ∃ x, ∀ i, x ∈ F i := by
  classical
  obtain ⟨I, x, hx, hxc⟩ := _root_.Convex.radon_partition hdep
  refine ⟨x, fun i => ?_⟩
  have hsub (J : Set ι) (hi : i ∉ J) : convexHull ℝ (p '' J) ⊆ F i := by
    apply convexHull_min _ (hF i)
    rintro _ ⟨j, hj, rfl⟩
    exact hp j i (by rintro rfl; exact hi hj)
  by_cases hi : i ∈ I
  · exact hsub Iᶜ (by simpa) hxc
  · exact hsub I hi hx

/-- A nonconstant affine level set cannot contain an affine basis. -/
theorem dependent_of_level {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] (p : ι → E)
    (hcard : Fintype.card ι = Module.finrank ℝ E + 1)
    (L : E →ᵃ[ℝ] ℝ) (hL : ∃ x y, L x ≠ L y) (d : ℝ)
    (hp : ∀ i, L (p i) = d) : ¬ AffineIndependent ℝ p := by
  intro hi
  have hspan := hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr hcard
  have heq : L = AffineMap.const ℝ E d := AffineMap.ext_on hspan (by
    rintro _ ⟨i, rfl⟩
    exact hp i)
  obtain ⟨x, y, hxy⟩ := hL
  exact hxy (by rw [heq]; rfl)

/-- If the strict cuts meet on the body's hyperplane in cut space, an empty
cell on the body already becomes empty after one cut is omitted. -/
theorem exists_redundant_cut (K : Set (Fin n → ℝ)) (hK : Convex ℝ K)
    (L : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (hL : ∃ x y, L x ≠ L y) (d : ℝ)
    (hplane : ∀ x ∈ K, L x = d)
    (f : Fin n → (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (q : Fin n → ℝ) (hqL : L q = d) (hq : ∀ i, 0 < f i q)
    (he : ¬ ∃ x ∈ K, ∀ i, 0 < f i x) :
    ∃ i, ¬ ∃ x ∈ K, ∀ j, j ≠ i → 0 < f j x := by
  classical
  by_contra! hn
  choose p hpK hp using hn
  let F : Fin (n + 1) → Set (Fin n → ℝ) := Fin.cons K (fun i => {x | 0 < f i x})
  let P : Fin (n + 1) → (Fin n → ℝ) := Fin.cons q p
  have hF (i : Fin (n + 1)) : Convex ℝ (F i) := by
    refine Fin.cases hK (fun j => ?_) i
    exact (convex_Ioi (𝕜 := ℝ) (0 : ℝ)).affine_preimage (f j)
  have hP : ∀ i j : Fin (n + 1), j ≠ i → P i ∈ F j := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      exact Fin.cases (fun h => (h rfl).elim) (fun j _ => hq j) j
    · intro j
      exact Fin.cases (fun _ => hpK i)
        (fun j h => hp i j (fun e => h (congrArg Fin.succ e))) j
  have hdep := dependent_of_level P (by simp) L hL d
    (Fin.cases hqL (fun i => hplane _ (hpK i)))
  obtain ⟨x, hx⟩ := common_point_of_dependent_witnesses F hF P hP hdep
  exact he ⟨x, hx 0, fun i => hx i.succ⟩

/-- Pass to the cut values and apply Helly on their relation hyperplane. -/
theorem exists_redundant_cut_of_relation {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (hK : Convex ℝ K) (f : Fin n → E →ᵃ[ℝ] ℝ)
    (r : Fin n → ℝ) (d : ℝ) (hr : ∃ i, r i ≠ 0)
    (hrel : ∀ x ∈ K, ∑ i, r i * f i x = d)
    (hq : ∃ q : Fin n → ℝ, (∀ i, 0 < q i) ∧ ∑ i, r i * q i = d)
    (he : ¬ ∃ x ∈ K, ∀ i, 0 < f i x) :
    ∃ i, ¬ ∃ x ∈ K, ∀ j, j ≠ i → 0 < f j x := by
  let G := AffineMap.pi f
  let L : (Fin n → ℝ) →ᵃ[ℝ] ℝ :=
    (∑ i, r i • (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)).toAffineMap
  have hL (x : Fin n → ℝ) : L x = ∑ i, r i * x i := by
    simp [L, LinearMap.sum_apply, smul_eq_mul]
  have hnc : ∃ x y, L x ≠ L y := by
    obtain ⟨i, hi⟩ := hr
    refine ⟨Pi.single i 1, 0, ?_⟩
    simpa [hL, Pi.single_apply, mul_ite] using hi
  obtain ⟨q, hq, hqL⟩ := hq
  obtain ⟨i, hi⟩ := exists_redundant_cut (G '' K) (hK.affine_image G) L hnc d
    (by rintro _ ⟨x, hx, rfl⟩; simpa [hL, G] using hrel x hx)
    (fun i => AffineMap.proj i) q (by simpa [hL] using hqL) hq
    (by rintro ⟨_, ⟨x, hx, rfl⟩, hf⟩; exact he ⟨x, hx, hf⟩)
  refine ⟨i, ?_⟩
  rintro ⟨x, hx, hf⟩
  exact hi ⟨G x, ⟨x, hx, rfl⟩, hf⟩

private theorem positive_point_by_adjustment (r : Fin n → ℝ) (d : ℝ) (i : Fin n)
    (hri : r i ≠ 0) (ht : 0 ≤ (d - ∑ j, r j) / r i) :
    ∃ q : Fin n → ℝ, (∀ j, 0 < q j) ∧ ∑ j, r j * q j = d := by
  let t := (d - ∑ j, r j) / r i
  refine ⟨fun j => 1 + if j = i then t else 0, ?_, ?_⟩
  · intro j
    dsimp only
    split_ifs <;> linarith only [ht]
  · simp only [mul_add, mul_one, mul_ite, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    dsimp [t]
    rw [mul_div_cancel₀ _ hri]
    ring

/-- A plane with a mixed normal meets the positive orthant at every height. -/
theorem positive_point_of_mixed (r : Fin n → ℝ) (d : ℝ)
    (hp : ∃ i, 0 < r i) (hn : ∃ i, r i < 0) :
    ∃ q : Fin n → ℝ, (∀ i, 0 < q i) ∧ ∑ i, r i * q i = d := by
  by_cases h : (∑ i, r i) ≤ d
  · obtain ⟨i, hi⟩ := hp
    exact positive_point_by_adjustment r d i hi.ne'
      (div_nonneg (sub_nonneg.mpr h) hi.le)
  · obtain ⟨i, hi⟩ := hn
    exact positive_point_by_adjustment r d i hi.ne
      (div_nonneg_of_nonpos (sub_nonpos.mpr (le_of_not_ge h)) hi.le)

/-- A positive normal and positive height give a positive point by scaling. -/
theorem positive_point_of_positive [NeZero n] (r : Fin n → ℝ) (d : ℝ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) :
    ∃ q : Fin n → ℝ, (∀ i, 0 < q i) ∧ ∑ i, r i * q i = d := by
  have hs : 0 < ∑ i, r i := Finset.sum_pos (fun i _ => hr i) Finset.univ_nonempty
  refine ⟨fun _ => d / ∑ i, r i, fun _ => div_pos hd hs, ?_⟩
  rw [← Finset.sum_mul, mul_div_cancel₀ _ hs.ne']

end PlaneProof.PlaneCuts

/- Signed pairs directly connect the cube to the geometric cuts. -/
namespace PlaneProof.EmptyCaps
open scoped BigOperators
open PlaneProof Windows CubeCover

def firstCut (e : Edge) : Point 3 →L[ℝ] ℝ := cut e.2.1 (e.1 + 1)
def secondCut (e : Edge) : Point 3 →L[ℝ] ℝ := cut e.2.2 (e.1 + 2)
def firstWall (e : Edge) : Walls 3 →L[ℝ] ℝ := wall e.2.1 (e.1 + 1)
def secondWall (e : Edge) : Walls 3 →L[ℝ] ℝ := wall e.2.2 (e.1 + 2)

def PairEmpty (K : Set (Point 3)) (B : Walls 3) (e : Edge) : Prop :=
  ¬ ∃ x ∈ K, firstWall e B < firstCut e x ∧ secondWall e B < secondCut e x
def planeRow (c : Point 3) (b : Bool) : Walls 3 →L[ℝ] ℝ := ∑ i, c i • wall b i
def planeLevel (D : ℝ) (b : Bool) : ℝ := if b then D else -D
def Allowed (K : Set (Point 3)) (c : Point 3) (D : ℝ) (B : Walls 3) : Selection → Prop
  | .inl e => PairEmpty K B e
  | .inr b => planeLevel D b ≤ planeRow c b B

def shiftedCut (B : Walls 3) (v : Vertex) (i : Fin 3) : Point 3 →ᵃ[ℝ] ℝ :=
  (cut (v i) i).toLinearMap.toAffineMap - AffineMap.const ℝ _ (wall (v i) i B)
def corner (B : Walls 3) (v : Vertex) (i : Fin 3) : ℝ := if v i then B.2 i else B.1 i
def coefficient (c : Point 3) (v : Vertex) (i : Fin 3) : ℝ := if v i then c i else -c i

@[simp] theorem planeRow_apply (c : Point 3) (b : Bool) (B : Walls 3) :
    planeRow c b B = ∑ i, c i * wall b i B := by simp [planeRow]

theorem shiftedCut_apply (B : Walls 3) (v : Vertex) (i : Fin 3) (x : Point 3) :
    shiftedCut B v i x = cut (v i) i x - wall (v i) i B := rfl

/-- The omitted coordinate leaves exactly the two cuts of its cube edge. -/
theorem pair_cuts (B : Walls 3) (i : Fin 3) (v : Vertex) (x : Point 3) :
    (firstWall (i, v (i + 1), v (i + 2)) B < firstCut (i, v (i + 1), v (i + 2)) x ∧
      secondWall (i, v (i + 1), v (i + 2)) B < secondCut (i, v (i + 1), v (i + 2)) x) ↔
    ∀ j, j ≠ i → 0 < shiftedCut B v j x := by
  fin_cases i <;>
    simp [firstWall, secondWall, firstCut, secondCut, shiftedCut_apply,
      Fin.forall_fin_succ, sub_pos, and_comm]
  exact and_comm

theorem shifted_relation (B : Walls 3) (c : Point 3) (v : Vertex) (x : Point 3) :
    (∑ i, coefficient c v i * shiftedCut B v i x) =
      (∑ i, c i * x i) - ∑ i, c i * corner B v i := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hi : v i <;> simp [coefficient, corner, shiftedCut_apply, cut, wall, hi] <;> ring

theorem constant_relation (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D) (b : Bool) (x : Point 3) (hx : x ∈ K) :
    (∑ i, c i * cut b i x) = planeLevel D b := by
  cases b <;> simp [cut, planeLevel, mul_neg, Finset.sum_neg_distrib, hplane x hx]

theorem constant_shifted_relation (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D) (B : Walls 3) (b : Bool)
    (x : Point 3) (hx : x ∈ K) :
    (∑ i, c i * shiftedCut B (constant b) i x) = planeLevel D b - planeRow c b B := by
  simp only [shiftedCut_apply, constant, mul_sub, Finset.sum_sub_distrib, planeRow_apply]
  rw [constant_relation K c D hplane b x hx]

theorem covers_of_allowed (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hc : ∀ i, 0 < c i) (hplane : ∀ x ∈ K, ∑ i, c i * x i = D)
    (B : Walls 3) (s : Finset Selection)
    (ha : ∀ e ∈ s, Allowed K c D B e)
    (hs : ∀ v, ∃ e ∈ s, hits e v) : Covers K B := by
  apply (covers_iff_no_escape K B).mpr
  rintro v ⟨x, hx, ht⟩
  obtain ⟨e, he, hev⟩ := hs v
  cases e with
  | inl e =>
    apply ha _ he
    refine ⟨x, hx, ?_, ?_⟩
    · change wall e.2.1 (e.1 + 1) B < cut e.2.1 (e.1 + 1) x
      rw [← hev.1]
      exact ht _
    · change wall e.2.2 (e.1 + 2) B < cut e.2.2 (e.1 + 2) x
      rw [← hev.2]
      exact ht _
  | inr b =>
    change v = constant b at hev
    subst v
    have hlt := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun i _ => mul_lt_mul_of_pos_left (ht i) (hc i))
    change (∑ i, c i * wall b i B) < ∑ i, c i * cut b i x at hlt
    rw [constant_relation K c D hplane b x hx, ← planeRow_apply] at hlt
    exact hlt.not_ge (ha _ he)

theorem allowed_of_redundant (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (B : Walls 3) (v : Vertex) (i : Fin 3)
    (he : ¬ ∃ x ∈ K, ∀ j, j ≠ i → 0 < shiftedCut B v j x) :
    ∃ e, Allowed K c D B e ∧ hits e v := by
  refine ⟨edge i v, ?_, edge_hits i v⟩
  rintro ⟨x, hx, hx1, hx2⟩
  exact he ⟨x, hx, (pair_cuts B i v x).mp ⟨hx1, hx2⟩⟩

theorem mixed_signs (v : Vertex) (h : ¬ ∃ b, v = constant b) :
    (∃ i, v i = true) ∧ ∃ i, v i = false := by
  revert v
  decide +kernel

/-- Every sign vertex is excluded by an empty pair cap or its constant
plane bound. The sign vector is already the cube vertex. -/
theorem exists_allowed (K : Set (Point 3)) (hK : Convex ℝ K)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D)
    (B : Walls 3) (hcover : Covers K B) (v : Vertex) :
    ∃ e, Allowed K c D B e ∧ hits e v := by
  have he : ¬ ∃ x ∈ K, ∀ i, 0 < shiftedCut B v i x := by
    rintro ⟨x, hx, hf⟩
    exact (covers_iff_no_escape K B).mp hcover v ⟨x, hx, fun i => sub_pos.mp (hf i)⟩
  by_cases hconst : ∃ b, v = constant b
  · obtain ⟨b, rfl⟩ := hconst
    by_cases hbound : planeLevel D b ≤ planeRow c b B
    · exact ⟨.inr b, hbound, rfl⟩
    obtain ⟨i, hi⟩ := PlaneCuts.exists_redundant_cut_of_relation
      K hK (shiftedCut B (constant b)) c (planeLevel D b - planeRow c b B)
      ⟨0, (hc 0).ne'⟩ (constant_shifted_relation K c D hplane B b)
      (PlaneCuts.positive_point_of_positive _ _ hc
        (sub_pos.mpr (lt_of_not_ge hbound))) he
    exact allowed_of_redundant K c D B (constant b) i hi
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := mixed_signs v hconst
  have hrp : ∃ i, 0 < coefficient c v i := ⟨i, by simpa [coefficient, hi] using hc i⟩
  have hrn : ∃ j, coefficient c v j < 0 := ⟨j, by simpa [coefficient, hj] using neg_neg_of_pos (hc j)⟩
  obtain ⟨k, hk⟩ := PlaneCuts.exists_redundant_cut_of_relation K hK
    (shiftedCut B v) (coefficient c v) (D - ∑ i, c i * corner B v i)
    (hrp.imp fun _ hi => hi.ne') (fun x hx => by rw [shifted_relation, hplane x hx])
    (PlaneCuts.positive_point_of_mixed _ _ hrp hrn) he
  exact allowed_of_redundant K c D B v k hk

/-- Only the two edges through the odd coordinate are needed for the plane bound. -/
theorem mixed_plane_strict (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hc : ∀ j, 0 < c j) (hplane : ∀ x ∈ K, ∑ j, c j * x j = D)
    (B : Walls 3) (horder : ∀ j, B.1 j ≤ B.2 j)
    (hw : ∀ b j, ∃ x ∈ K, wall b j B < cut b j x)
    (s : Finset Selection) (hs : ∀ e ∈ s, Allowed K c D B e)
    (v : Vertex) (i : Fin 3) (hodd : ∀ j, j ≠ i → v j ≠ v i)
    (hv : ∀ k, k ≠ i → edge k v ∈ s) :
    planeLevel D (!v i) < planeRow c (!v i) B := by
  obtain ⟨p, hp, hpi⟩ := hw (v i) i
  have hi : cut (!v i) i p < wall (!v i) i B := by
    cases hvi : v i <;> simp [cut, wall, hvi] at hpi ⊢ <;> linarith only [hpi, horder i]
  have hj (j : Fin 3) (hji : j ≠ i) : cut (!v i) j p ≤ wall (!v i) j B := by
    have hsign : v j = !v i := Bool.eq_not_iff.mpr (hodd j hji)
    rw [← hsign]
    by_contra! hpos
    obtain ⟨k, hki, hk⟩ := omitted_pair_ne i j hji.symm
    apply hs (edge k v) (hv k hki)
    refine ⟨p, hp, (pair_cuts B k v p).mpr ?_⟩
    intro l hl
    rcases hk l hl with rfl | rfl
    · exact sub_pos.mpr hpi
    · exact sub_pos.mpr hpos
  have hall (j : Fin 3) : cut (!v i) j p ≤ wall (!v i) j B := by
    by_cases hji : j = i
    · simpa only [hji] using hi.le
    · exact hj j hji
  have hsum := Finset.sum_lt_sum
    (fun j (_ : j ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hall j) (hc j).le)
    ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hc i)⟩
  rw [constant_relation K c D hplane (!v i) p hp, ← planeRow_apply] at hsum
  exact hsum

end PlaneProof.EmptyCaps

/- Clipping an interval to [0, 1] preserves its covered points
and cannot increase its length. -/

namespace PlaneProof.Intervals

open scoped BigOperators

def clamp (t : ℝ) : ℝ := max 0 (min 1 t)

theorem clamp_nonneg (t : ℝ) : 0 ≤ clamp t := le_max_left _ _

theorem clamp_le_one (t : ℝ) : clamp t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem clamp_mono : Monotone clamp :=
  fun _ _ hab => max_le_max le_rfl (min_le_min le_rfl hab)

theorem clamp_self (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) : clamp t = t := by
  rw [clamp, min_eq_right ht.2, max_eq_right ht.1]

/-- Ordered endpoint clipping cannot increase interval length. -/
theorem clamp_sub_le (l h : ℝ) (hlh : l ≤ h) : clamp h - clamp l ≤ h - l := by
  have hmax : |clamp h - clamp l| ≤ |min 1 h - min 1 l| := by
    simpa only [clamp, max_comm] using
      abs_max_sub_max_le_abs (min 1 h) (min 1 l) (0 : ℝ)
  have hmin : |min 1 h - min 1 l| ≤ |h - l| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (h - l))] using
      abs_min_sub_min_le_max (1 : ℝ) h (1 : ℝ) l
  exact (le_abs_self _).trans ((hmax.trans hmin).trans_eq
    (abs_of_nonneg (sub_nonneg.mpr hlh)))

theorem clamp_interval (l h z : ℝ) (hz : 0 ≤ z ∧ z ≤ 1)
    (hlh : l ≤ z ∧ z ≤ h) : clamp l ≤ z ∧ z ≤ clamp h := by
  simpa only [clamp_self z hz] using
    And.intro (clamp_mono hlh.1) (clamp_mono hlh.2)

end PlaneProof.Intervals

/- A hyperplane containing no relative neighborhood of a convex set can
be removed from a closed cover. No continuity of the affine functional is needed. -/
namespace PlaneProof.ClosedCover
open Filter Topology

theorem closed_cover_remove_affine {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    (K C : Set E) (hK : Convex ℝ K) (hC : IsClosed C) (f : E →ᵃ[ℝ] ℝ)
    (a : ℝ) (p : E) (hp : p ∈ K) (hpa : f p ≠ a)
    (hcov : ∀ x ∈ K, x ∈ C ∨ f x = a) : K ⊆ C := by
  intro x hx
  rcases hcov x hx with hxC | hxa
  · exact hxC
  have hpath : Continuous (fun t : ℝ => AffineMap.lineMap x p t) := by
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  have hlim : Tendsto (AffineMap.lineMap x p) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa only [AffineMap.lineMap_apply_zero] using
      (hpath.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply hC.mem_of_tendsto hlim
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 from zero_lt_one)] with t ht
  rcases hcov _ (hK.lineMap_mem hx hp ⟨ht.1.le, ht.2⟩) with hm | he
  · exact hm
  · have hzero : t * (f p - a) = 0 := by
      simp only [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring', hxa] at he
      linarith only [he]
    exact False.elim ((mul_ne_zero ht.1.ne' (sub_ne_zero.mpr hpa)) hzero)

end PlaneProof.ClosedCover

/- Four contact segments and Cauchy--Schwarz prove the two-window bound.
Clipped transverse coordinates include zero outside margins and boundary windows. -/
namespace PlaneProof.TwoWindows
open Intervals
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Cauchy--Schwarz for two product bounds, without square roots. -/
private theorem row_bound {a b c x y u v : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (h₁ : a * c ≤ u * x) (h₂ : b * c ≤ v * y) :
    c * (a + b) ^ 2 ≤ (u + v) * (a * x + b * y) := by
  have H := mul_le_mul h₁ h₂ (mul_nonneg hb hc)
    ((mul_nonneg ha hc).trans h₁)
  have hp : (a * b * c) ^ 2 ≤ (u * b * y) * (v * a * x) := by
    have h := mul_le_mul_of_nonneg_left H (mul_nonneg ha hb)
    nlinarith only [h]
  have hh := two_mul_le_add_of_sq_le_mul
    (mul_nonneg (mul_nonneg hu hb) hy) (mul_nonneg (mul_nonneg hv ha) hx) hp
  nlinarith only [hh, mul_le_mul_of_nonneg_left h₁ ha,
    mul_le_mul_of_nonneg_left h₂ hb]

/-- Add the two escape-side Cauchy bounds; the contact offsets cancel. -/
private theorem four_corners (a b c d w h s t u v : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hsh : s ≤ h) (ht : 0 ≤ t) (hth : t ≤ h)
    (hu : 0 ≤ u) (huw : u ≤ w) (hv : 0 ≤ v) (hvw : v ≤ w)
    (h₁ : a * c ≤ u * s) (h₂ : b * c ≤ (w - u) * t)
    (h₃ : a * d ≤ v * (h - s)) (h₄ : b * d ≤ (w - v) * (h - t))
    (hX : a + b = 1 - w) (hY : c + d = 1 - h) : 1 ≤ w + h := by
  by_contra! hdef
  have hab : 0 < a + b := by linarith only [hX, hdef, hs, hsh]
  have hL := row_bound ha hb hc hs ht hu (sub_nonneg.mpr huw) h₁ h₂
  have hU := row_bound ha hb hd (sub_nonneg.mpr hsh) (sub_nonneg.mpr hth)
    hv (sub_nonneg.mpr hvw) h₃ h₄
  have H : ((c + d) * (a + b)) * (a + b) ≤ (w * h) * (a + b) := by
    nlinarith only [hL, hU]
  have hAB := (mul_le_mul_iff_left₀ hab).mp H
  rw [hX, hY] at hAB
  nlinarith only [hAB, hdef]

private def clip (l h x : ℝ) : ℝ := max l (min h x)

private theorem clip_bounds (l h x : ℝ) (hlh : l ≤ h) : l ≤ clip l h x ∧ clip l h x ≤ h :=
  ⟨le_max_left _ _, max_le hlh (min_le_left _ _)⟩

private theorem clip_self (l h x : ℝ) (hx : l ≤ x ∧ x ≤ h) : clip l h x = x := by
  rw [clip, min_eq_right hx.2, max_eq_right hx.1]

/-- Signed excess beyond the selected endpoint of a window. -/
private def gap (upper : Bool) (l h : ℝ) : ℝ →ᵃ[ℝ] ℝ :=
  if upper then AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ h
  else AffineMap.const ℝ ℝ l - AffineMap.id ℝ ℝ

private theorem gap_nonpos (upper : Bool) (l h x : ℝ) (hx : l ≤ x ∧ x ≤ h) :
    gap upper l h x ≤ 0 := by
  cases upper <;> dsimp [gap] <;> linarith only [hx.1, hx.2]

/-- One corner inequality, for any independently chosen pair of sides.
Clipping the transverse coordinates only changes a zero-margin case. -/
private theorem corner_bound (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (l₁ h₁ l₂ h₂ : ℝ) (hle₁ : l₁ ≤ h₁) (hle₂ : l₂ ≤ h₂)
    (sx sy : Bool) (p q : E) (hp : p ∈ K) (hq : q ∈ K)
    (hXp : 0 ≤ gap sx l₁ h₁ (X p)) (hYq : 0 ≤ gap sy l₂ h₂ (Y q))
    (hcover : ∀ x ∈ K, (l₁ ≤ X x ∧ X x ≤ h₁) ∨ (l₂ ≤ Y x ∧ Y x ≤ h₂)) :
    gap sx l₁ h₁ (X p) * gap sy l₂ h₂ (Y q) ≤
      gap sx l₁ h₁ (clip l₁ h₁ (X q)) * gap sy l₂ h₂ (clip l₂ h₂ (Y p)) := by
  by_cases hpos : 0 < gap sx l₁ h₁ (X p) * gap sy l₂ h₂ (Y q)
  · have hgp := pos_of_mul_pos_left hpos hYq
    have hhq := pos_of_mul_pos_right hpos hXp
    have hpY := (hcover p hp).resolve_left (fun H => hgp.not_ge (gap_nonpos _ _ _ _ H))
    have hqX := (hcover q hq).resolve_right (fun H => hhq.not_ge (gap_nonpos _ _ _ _ H))
    rw [clip_self _ _ _ hqX, clip_self _ _ _ hpY]
    exact DisjointCuts.cross_bound K hK ((gap sx l₁ h₁).comp X)
      ((gap sy l₂ h₂).comp Y) p q hp hq hgp hhq (by
        rintro ⟨x, hx, hg, hh⟩
        exact (hcover x hx).elim (fun hc => hg.not_ge (gap_nonpos _ _ _ _ hc))
          (fun hc => hh.not_ge (gap_nonpos _ _ _ _ hc)))
  · exact (le_of_not_gt hpos).trans (mul_nonneg_of_nonpos_of_nonpos
      (gap_nonpos _ _ _ _ (clip_bounds _ _ _ hle₁))
      (gap_nonpos _ _ _ _ (clip_bounds _ _ _ hle₂)))

/-- Four clipped contact coordinates handle both boundary and interior windows. -/
private theorem clipped_bound (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (l₁ h₁ l₂ h₂ : ℝ) (hle₁ : l₁ ≤ h₁) (hle₂ : l₂ ≤ h₂)
    (hl₁ : 0 ≤ l₁) (hh₁ : h₁ ≤ 1) (hl₂ : 0 ≤ l₂) (hh₂ : h₂ ≤ 1)
    (hX₀ : ∃ x ∈ K, X x = 0) (hX₁ : ∃ x ∈ K, X x = 1)
    (hY₀ : ∃ x ∈ K, Y x = 0) (hY₁ : ∃ x ∈ K, Y x = 1)
    (hcover : ∀ x ∈ K, (l₁ ≤ X x ∧ X x ≤ h₁) ∨ (l₂ ≤ Y x ∧ Y x ≤ h₂)) :
    1 ≤ (h₁ - l₁) + (h₂ - l₂) := by
  obtain ⟨L, hL, hXL⟩ := hX₀
  obtain ⟨R, hR, hXR⟩ := hX₁
  obtain ⟨B, hB, hYB⟩ := hY₀
  obtain ⟨T, hT, hYT⟩ := hY₁
  have corner (sx sy : Bool) := corner_bound K hK X Y l₁ h₁ l₂ h₂ hle₁ hle₂
    sx sy (if sx then R else L) (if sy then T else B)
    (by cases sx <;> assumption) (by cases sy <;> assumption)
    (by cases sx <;> dsimp [gap] <;> linarith only [hXL, hXR, hl₁, hh₁])
    (by cases sy <;> dsimp [gap] <;> linarith only [hYB, hYT, hl₂, hh₂]) hcover
  have hLL := corner false false
  have hRL := corner true false
  have hLU := corner false true
  have hRU := corner true true
  dsimp [gap] at hLL hRL hLU hRU
  simp only [hXL, hXR, hYB, hYT] at hLL hRL hLU hRU
  have hs := clip_bounds l₂ h₂ (Y L) hle₂
  have ht := clip_bounds l₂ h₂ (Y R) hle₂
  have hu := clip_bounds l₁ h₁ (X B) hle₁
  have hv := clip_bounds l₁ h₁ (X T) hle₁
  apply four_corners l₁ (1 - h₁) l₂ (1 - h₂) (h₁ - l₁) (h₂ - l₂)
    (clip l₂ h₂ (Y L) - l₂) (clip l₂ h₂ (Y R) - l₂)
    (clip l₁ h₁ (X B) - l₁) (clip l₁ h₁ (X T) - l₁)
    hl₁ (sub_nonneg.mpr hh₁) hl₂ (sub_nonneg.mpr hh₂)
    (sub_nonneg.mpr hs.1) (by linarith only [hs.2])
    (sub_nonneg.mpr ht.1) (by linarith only [ht.2])
    (sub_nonneg.mpr hu.1) (by linarith only [hu.2])
    (sub_nonneg.mpr hv.1) (by linarith only [hv.2])
    (by nlinarith only [hLL]) (by nlinarith only [hRL])
    (by nlinarith only [hLU]) (by nlinarith only [hRU]) (by ring) (by ring)

/-- Two closed affine windows covering a convex set have total width at least
one when both coordinates have attained range `[0,1]`. The windows need only
be ordered; the affine maps and contact points need not be distinct. -/
theorem width_bound (K : Set E) (hK : Convex ℝ K) (X Y : E →ᵃ[ℝ] ℝ)
    (hbox : ∀ x ∈ K, (0 ≤ X x ∧ X x ≤ 1) ∧ (0 ≤ Y x ∧ Y x ≤ 1))
    (l₁ h₁ l₂ h₂ : ℝ) (hle₁ : l₁ ≤ h₁) (hle₂ : l₂ ≤ h₂)
    (hX₀ : ∃ x ∈ K, X x = 0) (hX₁ : ∃ x ∈ K, X x = 1)
    (hY₀ : ∃ x ∈ K, Y x = 0) (hY₁ : ∃ x ∈ K, Y x = 1)
    (hcover : ∀ x ∈ K, (l₁ ≤ X x ∧ X x ≤ h₁) ∨ (l₂ ≤ Y x ∧ Y x ≤ h₂)) :
    1 ≤ (h₁ - l₁) + (h₂ - l₂) := by
  have htrim : ∀ x ∈ K,
      (clamp l₁ ≤ X x ∧ X x ≤ clamp h₁) ∨
        (clamp l₂ ≤ Y x ∧ Y x ≤ clamp h₂) := by
    intro x hx
    rcases hcover x hx with h | h
    · exact Or.inl (clamp_interval _ _ _ (hbox x hx).1 h)
    · exact Or.inr (clamp_interval _ _ _ (hbox x hx).2 h)
  have hbound := clipped_bound K hK X Y
    (clamp l₁) (clamp h₁) (clamp l₂) (clamp h₂) (clamp_mono hle₁) (clamp_mono hle₂)
    (clamp_nonneg l₁) (clamp_le_one h₁) (clamp_nonneg l₂) (clamp_le_one h₂)
    hX₀ hX₁ hY₀ hY₁ htrim
  exact hbound.trans (add_le_add (clamp_sub_le _ _ hle₁) (clamp_sub_le _ _ hle₂))

end PlaneProof.TwoWindows

/- A boundary window transfers a covering bound from any finite affine
family to that family with one additional window. A contact homothety
handles the lower boundary; reflection handles the upper boundary. -/
namespace PlaneProof.BoundaryWindows
open scoped BigOperators

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- A lower boundary window can be added to any finite family whose covers
already have total width at least one. Only a lower height bound and one
upper contact are needed. -/
theorem width_bound_of_lower_boundary (K : Set E) (hK : Convex ℝ K)
    (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (hY : ∀ x ∈ K, 0 ≤ Y x) (A : E) (hA : A ∈ K) (hYA : Y A = 1)
    (hcore : ∀ l h : ι → ℝ, (∀ j, l j ≤ h j) →
      (∀ x ∈ K, ∃ j, l j ≤ X j x ∧ X j x ≤ h j) →
      1 ≤ ∑ j, (h j - l j))
    (b : ℝ) (hb : 0 ≤ b) (lo hi : ι → ℝ) (horder : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, Y x ≤ b ∨ ∃ j, lo j ≤ X j x ∧ X j x ≤ hi j) :
    1 ≤ b + ∑ j, (hi j - lo j) := by
  by_contra! hdef
  let C := ∑ j, (hi j - lo j)
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => sub_nonneg.mpr (horder j)
  obtain ⟨t, hbt, htC⟩ := exists_between (show b < 1 - C by dsimp [C]; linarith only [hdef])
  have ht0 : 0 ≤ t := (hb.trans_lt hbt).le
  have ht1 : t < 1 := by linarith only [htC, hC]
  have hscale : 0 < 1 - t := sub_pos.mpr ht1
  let l := fun j => (lo j - t * X j A) / (1 - t)
  let h := fun j => (hi j - t * X j A) / (1 - t)
  have hresidual : ∀ x ∈ K, ∃ j, l j ≤ X j x ∧ X j x ≤ h j := by
    intro x hx
    let y := AffineMap.lineMap x A t
    have hy : y ∈ K := hK.lineMap_mem hx hA ⟨ht0, ht1.le⟩
    have hmap (f : E →ᵃ[ℝ] ℝ) : f y = (1 - t) * f x + t * f A := by
      simp only [y, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
    have havoid : b < Y y := by
      rw [hmap, hYA]
      have hh := mul_nonneg hscale.le (hY x hx)
      nlinarith only [hbt, hh]
    obtain ⟨j, hj0, hj1⟩ := (hcover y hy).resolve_left (not_le.mpr havoid)
    rw [hmap] at hj0 hj1
    refine ⟨j, ?_, ?_⟩
    · exact (div_le_iff₀ hscale).mpr (by nlinarith only [hj0])
    · exact (le_div_iff₀ hscale).mpr (by nlinarith only [hj1])
  have hbound := hcore l h (fun j =>
    div_le_div_of_nonneg_right (sub_le_sub_right (horder j) _) hscale.le) hresidual
  simp only [h, l, ← sub_div, sub_sub_sub_cancel_right, ← Finset.sum_div] at hbound
  have hCbig : 1 - t ≤ C := by
    simpa only [one_mul, C] using (le_div_iff₀ hscale).mp hbound
  linarith only [hCbig, htC]

/-- An ordered window reaching either endpoint of the normalized height
range preserves a known covering bound for the remaining affine coordinates.
Reflecting the height reduces the upper boundary to the lower boundary. -/
theorem width_bound (K : Set E) (hK : Convex ℝ K)
    (Y : E →ᵃ[ℝ] ℝ) (X : ι → E →ᵃ[ℝ] ℝ)
    (hY : ∀ x ∈ K, 0 ≤ Y x ∧ Y x ≤ 1)
    (hY0 : ∃ x ∈ K, Y x = 0) (hY1 : ∃ x ∈ K, Y x = 1)
    (hcore : ∀ l h : ι → ℝ, (∀ j, l j ≤ h j) →
      (∀ x ∈ K, ∃ j, l j ≤ X j x ∧ X j x ≤ h j) →
      1 ≤ ∑ j, (h j - l j))
    (a b : ℝ) (hab : a ≤ b) (lo hi : ι → ℝ) (horder : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, (a ≤ Y x ∧ Y x ≤ b) ∨
      ∃ j, lo j ≤ X j x ∧ X j x ≤ hi j)
    (hboundary : a = 0 ∨ b = 1) :
    1 ≤ b - a + ∑ j, (hi j - lo j) := by
  rcases hboundary with rfl | rfl
  · obtain ⟨A, hA, hYA⟩ := hY1
    simpa only [sub_zero] using width_bound_of_lower_boundary K hK Y X
      (fun x hx => (hY x hx).1) A hA hYA hcore b hab lo hi horder
      (fun x hx => (hcover x hx).imp (fun h => h.2) id)
  · obtain ⟨A, hA, hYA⟩ := hY0
    apply width_bound_of_lower_boundary K hK (AffineMap.const ℝ E (1 : ℝ) - Y) X
      (fun x hx => by change 0 ≤ 1 - Y x; exact sub_nonneg.mpr (hY x hx).2)
      A hA (by change 1 - Y A = 1; rw [hYA, sub_zero]) hcore
      (1 - a) (sub_nonneg.mpr hab) lo hi horder
    exact fun x hx => (hcover x hx).imp (fun h => sub_le_sub_left h.1 1) id

end PlaneProof.BoundaryWindows

/- Clamping preserves covers and decreases width. The two-window theorem
and boundary homothety make every deficient cover strictly interior. -/
namespace PlaneProof.WindowBounds
open scoped BigOperators
open Windows Intervals

def width {n : ℕ} : Walls n →L[ℝ] ℝ :=
  ∑ i, ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _) -
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _))

theorem width_apply {n : ℕ} (B : Walls n) : width B = ∑ i, (B.2 i - B.1 i) := by
  simp [width]

def clipped {n : ℕ} (B : Walls n) : Walls n := (clamp ∘ B.1, clamp ∘ B.2)

theorem clipped_width_le {n : ℕ} (B : Walls n) (horder : ∀ i, B.1 i ≤ B.2 i) :
    width (clipped B) ≤ width B := by
  simp only [width_apply]
  exact Finset.sum_le_sum fun i _ => clamp_sub_le _ _ (horder i)

theorem clipped_unitCovers {n : ℕ} (K : Set (Point n))
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1) (B : Walls n)
    (horder : ∀ i, B.1 i ≤ B.2 i) (hcover : Covers K B) :
    clipped B ∈ unitCovers K := by
  refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, fun i => clamp_mono (horder i)⟩, ?_⟩
  · exact fun i => clamp_nonneg (B.1 i)
  · exact fun i => clamp_nonneg (B.2 i)
  · exact fun i => clamp_le_one (B.1 i)
  · exact fun i => clamp_le_one (B.2 i)
  · intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact ⟨i, clamp_interval _ _ _ (hbox x hx i) hi⟩

private theorem two_coordinates_bound (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (c : Fin 2 → Fin 3) (lo hi : Fin 2 → ℝ) (horder : ∀ j, lo j ≤ hi j)
    (hcover : ∀ x ∈ K, ∃ j, lo j ≤ x (c j) ∧ x (c j) ≤ hi j) :
    1 ≤ ∑ j, (hi j - lo j) := by
  simpa only [Fin.sum_univ_two] using TwoWindows.width_bound K hK
    (AffineMap.proj (c 0)) (AffineMap.proj (c 1))
    (fun x hx => ⟨hbox x hx _, hbox x hx _⟩)
    (lo 0) (hi 0) (lo 1) (hi 1) (horder 0) (horder 1) (hL _) (hU _) (hL _) (hU _)
    (fun x hx => by simpa only [Fin.exists_fin_two, AffineMap.proj_apply] using hcover x hx)

/-- A zero-width window can be removed, leaving the two-window theorem. -/
theorem widths_positive (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (B : Walls 3) (horder : ∀ i, B.1 i ≤ B.2 i)
    (hcover : Covers K B) (hdef : width B < 1) : ∀ i, B.1 i < B.2 i := by
  intro k
  by_contra hn
  have he : B.2 k = B.1 k := le_antisymm (le_of_not_gt hn) (horder k)
  let c := k.succAbove
  let C : Set (Point 3) := ⋃ j : Fin 2, {x | B.1 (c j) ≤ x (c j) ∧ x (c j) ≤ B.2 (c j)}
  have hclosed (i : Fin 3) : IsClosed {x : Point 3 | B.1 i ≤ x i ∧ x i ≤ B.2 i} :=
    (isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_apply i) continuous_const)
  obtain ⟨p, hp, hpk⟩ : ∃ p ∈ K, p k ≠ B.1 k := by
    by_cases hl : B.1 k = 0
    · obtain ⟨p, hp, hpk⟩ := hU k
      exact ⟨p, hp, by rw [hpk, hl]; norm_num⟩
    · obtain ⟨p, hp, hpk⟩ := hL k
      exact ⟨p, hp, by rw [hpk]; exact Ne.symm hl⟩
  have hcov : K ⊆ C := by
    apply ClosedCover.closed_cover_remove_affine K C hK
      (isClosed_iUnion_of_finite fun j => hclosed (c j))
      (AffineMap.proj k) (B.1 k) p hp hpk
    intro x hx
    rcases (Fin.exists_iff_succAbove k).mp (hcover x hx) with ⟨hli, hhi⟩ | h
    · exact Or.inr (by change x k = B.1 k; rw [he] at hhi; exact le_antisymm hhi hli)
    · exact Or.inl (Set.mem_iUnion.mpr h)
  have htwo := two_coordinates_bound K hK hbox hL hU c (B.1 ∘ c) (B.2 ∘ c)
    (fun j => horder (c j)) (fun x hx => Set.mem_iUnion.mp (hcov hx))
  rw [width_apply, Fin.sum_univ_succAbove _ k, he, sub_self, zero_add] at hdef
  exact hdef.not_ge htwo

/-- Every deficient unit cover has strictly ordered, interior endpoints.
A collapsed window leaves two windows; a boundary window leaves a deficient
two-window cover on a homothetic copy of the body. -/
theorem strict_of_deficit (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (B : Walls 3) (hB : B ∈ unitCovers K) (hdef : width B < 1) :
    B ∈ strictWindows := by
  have horder := hB.1.2
  have hcover := hB.2
  have hpos := widths_positive K hK hbox hL hU B horder hcover hdef
  intro k
  have hno : ¬ (B.1 k = 0 ∨ B.2 k = 1) := by
    intro hb
    let c := k.succAbove
    have h := BoundaryWindows.width_bound K hK (AffineMap.proj k)
      (fun j => AffineMap.proj (c j)) (fun x hx => hbox x hx k) (hL k) (hU k)
      (two_coordinates_bound K hK hbox hL hU c) (B.1 k) (B.2 k) (horder k)
      (B.1 ∘ c) (B.2 ∘ c) (fun j => horder (c j))
      (fun x hx => (Fin.exists_iff_succAbove k).mp (hcover x hx)) hb
    rw [width_apply, Fin.sum_univ_succAbove _ k] at hdef
    exact hdef.not_ge h
  exact ⟨lt_of_le_of_ne (hB.1.1.1.1 k) (Ne.symm (not_or.mp hno).1), hpos k,
    lt_of_le_of_ne (hB.1.1.2.2 k) (not_or.mp hno).2⟩

end PlaneProof.WindowBounds

/- A row count and deletion of redundant rows leave the six same-sign caps. -/
namespace PlaneProof.FiniteCover
open scoped BigOperators
open PlaneProof Windows WindowBounds CubeCover EmptyCaps

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ray_zero (S : Set E) (hS : Bornology.IsBounded S) (B d : E)
    (h : ∀ t : ℝ, 0 ≤ t → B + t • d ∈ S) : d = 0 := by
  by_contra hd
  obtain ⟨M, hM⟩ := hS.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt ((M + ‖B‖) / ‖d‖)
  have hn := (div_lt_iff₀ (norm_pos_iff.mpr hd)).mp hn
  have H := norm_sub_le (B + (n : ℝ) • d) B
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)] at H
  exact hn.not_ge (H.trans (add_le_add (hM _ (h n (Nat.cast_nonneg n))) le_rfl))

/-- Move the six endpoints along a common kernel direction of the frozen rows.
The deficient ray cannot reach a non-strict covering, and cannot stay bounded. -/
theorem fixed_rows_count {J : Type*} [Fintype J]
    (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (f : J → Walls 3 →L[ℝ] ℝ) (t : J → ℝ) (B : Walls 3)
    (hB : B ∈ strictWindows) (hdef : width B < 1)
    (hrows : ∀ j, t j ≤ f j B)
    (hcover : ∀ Y ∈ strictWindows, (∀ j, t j ≤ f j Y) → Covers K Y) :
    6 ≤ Fintype.card J := by
  have no_ray (d : Walls 3) (hf : ∀ j, f j d = 0) (hc : width d ≤ 0) : d = 0 := by
    let γ : ℝ → Walls 3 := fun s => B + s • d
    have hcont : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
    have hrows' (s : ℝ) (j : J) : t j ≤ f j (γ s) := by
      simpa only [γ, map_add, map_smul, smul_eq_mul, hf, mul_zero, add_zero] using hrows j
    have hlocal (s : ℝ) (hs : 0 ≤ s) (hC : γ s ∈ unitCovers K) : γ s ∈ strictWindows := by
      have hcost : width (γ s) < 1 := calc
        width (γ s) = width B + s * width d := by simp only [γ, map_add, map_smul, smul_eq_mul]
        _ ≤ width B := add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos hs hc)
        _ < 1 := hdef
      exact strict_of_deficit K hK hbox hL hU (γ s) hC hcost
    apply ray_zero _ (compact_unitCovers K).isBounded B d
    intro s hs
    by_contra hC
    obtain ⟨q, hq, hstrict, hn⟩ := isPreconnected_Ici
      (γ ⁻¹' strictWindows) (γ ⁻¹' (unitCovers K)ᶜ)
      (open_strictWindows.preimage hcont) ((compact_unitCovers K).isClosed.isOpen_compl.preimage hcont)
      (fun u hu => by
        by_cases hU : γ u ∈ unitCovers K
        · exact Or.inl (hlocal u hu hU)
        · exact Or.inr hU)
      ⟨0, le_rfl, by simpa only [Set.mem_preimage, γ, zero_smul, add_zero] using hB⟩ ⟨s, hs, hC⟩
    exact hn (unitCovers_of_strict_cover K (γ q) hstrict (hcover (γ q) hstrict (hrows' q)))
  have ker_zero (d : Walls 3) (hd : ∀ j, f j d = 0) : d = 0 := by
    by_cases hc : width d ≤ 0
    · exact no_ray d hd hc
    · exact neg_eq_zero.mp (no_ray (-d) (fun j => by simp [hd]) (by simp; linarith))
  let F : Walls 3 →ₗ[ℝ] (J → ℝ) := LinearMap.pi (fun j => (f j).toLinearMap)
  have hinj : Function.Injective F := (injective_iff_map_eq_zero F).mpr
    fun d hd => ker_zero d (fun j => congrFun hd j)
  simpa [Module.finrank_prod, Module.finrank_pi] using F.finrank_le_finrank_of_injective hinj

theorem strict_cut_witnesses (K : Set (Point 3))
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (B : Walls 3) (hB : B ∈ strictWindows) :
    ∀ b i, ∃ x ∈ K, wall b i B < cut b i x := by
  intro b i
  cases b
  · obtain ⟨x, hx, hxi⟩ := hL i
    exact ⟨x, hx, by simpa [cut, wall, hxi] using (hB i).1⟩
  · obtain ⟨x, hx, hxi⟩ := hU i
    exact ⟨x, hx, by simpa [cut, wall, hxi] using (hB i).2.2⟩

theorem mixed_pair_incidence : ∀ (v : Vertex) (e f : Selection),
    e ≠ f → hits e v → hits f v →
    (∀ b, ¬ hits e (constant b)) → (∀ b, ¬ hits f (constant b)) →
    ∃ i, (∀ j, j ≠ i → v j ≠ v i) ∧
      ∀ k, k ≠ i → edge k v = e ∨ edge k v = f := by
  intro v e f hne he hf hae haf
  rcases e with ⟨i, b, c⟩ | b
  · rcases f with ⟨j, d, e⟩ | b
    · rcases he with ⟨rfl, rfl⟩
      rcases hf with ⟨rfl, rfl⟩
      revert v
      fin_cases i <;> fin_cases j <;> decide +kernel
    · exact (haf b rfl).elim
  · exact (hae b rfl).elim

/-- With six selections and both constant singletons, two mixed edges
meet at a mixed vertex. -/
theorem mixed_fork_of_both_singletons (s : Finset Selection) (h : minimalCover s)
    (hcard : s.card = 6) (hboth : Sum.inr false ∈ s ∧ Sum.inr true ∈ s) :
    ∃ v i, (∀ j, j ≠ i → v j ≠ v i) ∧ ∀ k, k ≠ i → edge k v ∈ s := by
  have hsum := incidence_count s
  have hsingle := singletons_le_two s
  obtain ⟨v, hv⟩ : ∃ v, 1 < degree s v := by
    by_contra! hn
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hn v)
    have hvertices : Fintype.card Vertex = 8 := by decide +kernel
    simp only [Finset.sum_const, Finset.card_univ, hvertices, smul_eq_mul, mul_one] at hle
    omega
  have singleton_private (b : Bool) : ∀ e ∈ s, hits e (constant b) → e = .inr b := by
    have hb : Sum.inr b ∈ s := Bool.rec hboth.1 hboth.2 b
    obtain ⟨_, rfl, hu⟩ := h.2 (.inr b) hb
    exact hu
  have hnonconstant (b : Bool) : v ≠ constant b := by
    intro heq
    have hb : Sum.inr b ∈ s := Bool.rec hboth.1 hboth.2 b
    rw [heq, singleton_degree s h b hb] at hv
    omega
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp hv
  obtain ⟨he, hev⟩ := Finset.mem_filter.mp he
  obtain ⟨hf, hfv⟩ := Finset.mem_filter.mp hf
  have away (g : Selection) (hg : g ∈ s) (hgv : hits g v) (b : Bool) :
      ¬ hits g (constant b) := by
    intro hgb
    have heq := singleton_private b g hg hgb
    subst g
    exact hnonconstant b hgv
  obtain ⟨i, hi, hedges⟩ := mixed_pair_incidence v e f hef hev hfv
    (away e he hev) (away f hf hfv)
  exact ⟨v, i, hi, fun k hk => (hedges k hk).elim (fun h => h ▸ he) (fun h => h ▸ hf)⟩

/-- Two mixed edges supply the extra constant vertex geometrically. -/
theorem covers_of_mixed_fork (K : Set (Point 3)) (c : Point 3) (D : ℝ)
    (hc : ∀ j, 0 < c j) (hplane : ∀ x ∈ K, ∑ j, c j * x j = D)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (B : Walls 3) (hB : B ∈ strictWindows) (s : Finset Selection)
    (v : Vertex) (i : Fin 3) (hodd : ∀ j, j ≠ i → v j ≠ v i)
    (hv : ∀ k, k ≠ i → edge k v ∈ s)
    (hcover : ∀ w, ∃ e ∈ insert (.inr (!v i)) s, hits e w)
    (hs : ∀ e ∈ s, Allowed K c D B e) : Covers K B := by
  have hb := mixed_plane_strict K c D hc hplane B (fun j => (hB j).2.1.le)
    (strict_cut_witnesses K hL hU B hB) s hs v i hodd hv
  apply covers_of_allowed K c D hc hplane B (insert (.inr (!v i)) s) ?_ hcover
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · exact hb.le
  · exact hs e he

/-- Count rows, then delete a geometrically redundant selection. -/
theorem constant_stars_of_deficit_of_rows (K : Set (Point 3)) (hK : Convex ℝ K)
    (hbox : ∀ x ∈ K, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ x ∈ K, x i = 0) (hU : ∀ i, ∃ x ∈ K, x i = 1)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ K, ∑ i, c i * x i = D)
    (B : Walls 3) (hB : B ∈ unitCovers K) (hdefB : width B < 1)
    (hstrict : B ∈ strictWindows)
    (rows : ∀ e, Allowed K c D B e → ∃ f : Walls 3 →L[ℝ] ℝ, ∃ t : ℝ,
      t ≤ f B ∧ ∀ Y, t ≤ f Y → Allowed K c D Y e) :
    ∃ s : Finset Selection, (∀ e ∈ s, Allowed K c D B e) ∧
      star s (constant false) ∧ star s (constant true) := by
  classical
  have six (s : Finset Selection) (hs : ∀ e ∈ s, Allowed K c D B e)
      (hcover : ∀ Y ∈ strictWindows, (∀ e ∈ s, Allowed K c D Y e) → Covers K Y) :
      6 ≤ s.card := by
    have hrows (e : s) := rows e.val (hs _ e.property)
    choose f t ht hpreserve using hrows
    have H := fixed_rows_count K hK hbox hL hU f t B hstrict hdefB ht
      (fun Y hY hrows => hcover Y hY
        (fun e he => hpreserve ⟨e, he⟩ Y (hrows ⟨e, he⟩)))
    simpa using H
  obtain ⟨s, hs, hminimal⟩ := exists_minimal_cover (Allowed K c D B)
    (exists_allowed K hK c D hc hplane B hB.2)
  have hcard := (cube_count s hminimal).1
  have hsix : s.card = 6 := le_antisymm hcard (six s hs
    (fun Y _ hY => covers_of_allowed K c D hc hplane Y s hY hminimal.1))
  have essential (e : Selection) (he : e ∈ s)
      (hcover : ∀ Y ∈ strictWindows,
        (∀ a ∈ s.erase e, Allowed K c D Y a) → Covers K Y) : False := by
    have H := six (s.erase e) (fun a ha => hs a (Finset.mem_of_mem_erase ha)) hcover
    have E := Finset.card_erase_add_one he
    omega
  refine ⟨s, hs, ?_⟩
  rcases (cube_count s hminimal).2 hsix with hboth | hboth | ⟨v, h0, h1, hv⟩
  · obtain ⟨v, i, hi, hv⟩ := mixed_fork_of_both_singletons s hminimal hsix hboth
    have he : Sum.inr (!v i) ∈ s := Bool.rec hboth.1 hboth.2 (!v i)
    exact False.elim (essential _ he (fun Y hY hrows =>
      covers_of_mixed_fork K c D hc hplane hL hU Y hY (s.erase (.inr (!v i))) v i hi
        (fun k hk => Finset.mem_erase.mpr ⟨by simp [edge], hv k hk⟩)
        (by simpa [Finset.insert_erase he] using hminimal.1) hrows))
  · exact hboth
  · obtain ⟨i, hi⟩ := mixed_odd v h0 h1
    exact False.elim (essential _ (hv i) (fun Y hY hrows =>
      covers_of_mixed_fork K c D hc hplane hL hU Y hY (s.erase (edge i v)) v i hi
        (fun k hk => Finset.mem_erase.mpr ⟨edge_ne k i v hk, hv k⟩)
        (replace_star_cover s hminimal.1 v i hi hv) hrows))

abbrev Hull {ι : Type*} (X : ι → Point 3) := convexHull ℝ (Set.range X)

def excess (c : Point 3) (B : Walls 3) (b : Bool) (i : Fin 3) : Point 3 →ᵃ[ℝ] ℝ :=
  c i • ((cut b i).toLinearMap.toAffineMap - AffineMap.const ℝ _ (wall b i B))

@[simp] theorem excess_apply (c : Point 3) (B : Walls 3) (b : Bool) (i : Fin 3) (x : Point 3) :
    excess c B b i x = c i * (cut b i x - wall b i B) := rfl

theorem choose_edge {ι : Type*} [Fintype ι] (X : ι → Point 3)
    (c : Point 3) (hc : ∀ i, 0 < c i) (B : Walls 3)
    (hw : ∀ b i, ∃ v, wall b i B < cut b i (X v))
    (e : Edge) (he : PairEmpty (Hull X) B e) :
    ∃ a, SupportingSlopes.Chosen
      (fun v => excess c B e.2.1 (e.1 + 1) (X v))
      (fun v => excess c B e.2.2 (e.1 + 2) (X v)) a ∧
      ∀ x ∈ Hull X, excess c B e.2.1 (e.1 + 1) x +
        a * excess c B e.2.2 (e.1 + 2) x ≤ 0 := by
  apply SupportingSlopes.chosen_on_hull X
  · obtain ⟨v, hv⟩ := hw e.2.1 (e.1 + 1)
    exact ⟨v, mul_pos (hc _) (sub_pos.mpr hv)⟩
  · obtain ⟨v, hv⟩ := hw e.2.2 (e.1 + 2)
    exact ⟨v, mul_pos (hc _) (sub_pos.mpr hv)⟩
  · rintro ⟨x, hx, h1, h2⟩
    exact he ⟨x, hx, sub_pos.mp (pos_of_mul_pos_right h1 (hc _).le),
      sub_pos.mp (pos_of_mul_pos_right h2 (hc _).le)⟩

/-- Pair rows use the unscaled cuts and need no condition on the plane normal. -/
theorem finite_supporting_row {ι : Type*} [Fintype ι] (X : ι → Point 3)
    (c : Point 3) (D : ℝ) (B : Walls 3)
    (hw : ∀ b i, ∃ v, wall b i B < cut b i (X v))
    (e : Selection) (he : Allowed (Hull X) c D B e) :
    ∃ f : Walls 3 →L[ℝ] ℝ, ∃ t : ℝ, t ≤ f B ∧
      (∀ Y, t ≤ f Y → Allowed (Hull X) c D Y e) := by
  cases e with
  | inr b => exact ⟨planeRow c b, planeLevel D b, he, fun _ h => h⟩
  | inl e =>
    obtain ⟨a, ha, hsupport⟩ := choose_edge X (fun _ => 1) (fun _ => zero_lt_one) B hw e he
    let f := firstWall e + a • secondWall e
    refine ⟨f, f B, le_rfl, ?_⟩
    intro Y hY ⟨x, hx, h1, h2⟩
    have H := hsupport x hx
    change 1 * (firstCut e x - firstWall e B) +
      a * (1 * (secondCut e x - secondWall e B)) ≤ 0 at H
    have h2 := mul_lt_mul_of_pos_left h2 ha.positive
    change firstWall e B + a * secondWall e B ≤ firstWall e Y + a * secondWall e Y at hY
    nlinarith only [H, h1, h2, hY]

theorem finite_constant_stars_bound {ι : Type*} [Fintype ι] (X : ι → Point 3)
    (hL : ∀ i, ∃ v, X v i = 0) (hU : ∀ i, ∃ v, X v i = 1)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ v, ∑ i, c i * X v i = D)
    (B : Walls 3) (hB : B ∈ strictWindows)
    (hw : ∀ b i, ∃ v, wall b i B < cut b i (X v))
    (s : Finset Selection) (hs : ∀ e ∈ s, Allowed (Hull X) c D B e)
    (hstars : star s (constant false) ∧ star s (constant true)) : 1 ≤ width B := by
  have cuts (b : Bool) (i : Fin 3) :
      ∃ a, SupportingSlopes.Chosen (fun v => excess c B b i (X v))
        (fun v => excess c B b (i + 1) (X v)) a := by
    have H : star s (constant b) := Bool.rec hstars.1 hstars.2 b
    have he := hs _ (H (i + 2))
    have he : PairEmpty (Hull X) B (i + 2, b, b) := by
      simpa only [Allowed, edge, constant] using he
    obtain ⟨a, ha, _⟩ := choose_edge X c hc B hw (i + 2, b, b) he
    refine ⟨a, ?_⟩
    fin_cases i <;> simpa using ha
  choose a ha using cuts true
  choose b hb using cuts false
  have h := SupportingSlopes.width_of_chosen (fun v i => c i * X v i)
    (fun i => c i * B.1 i) (fun i => c i * B.2 i) c a b D
    (fun i => mul_le_mul_of_nonneg_left (hB i).2.1.le (hc i).le) hc hplane
    (fun i => (hL i).imp fun v hv => by rw [hv, mul_zero])
    (fun i => (hU i).imp fun v hv => by rw [hv, mul_one])
    (fun i => by
      simpa only [mul_sub] using
        (show SupportingSlopes.Chosen (fun v => c i * (X v i - B.2 i))
          (fun v => c (i + 1) * (X v (i + 1) - B.2 (i + 1))) (a i) from ha i))
    (fun i => by
      simpa only [neg_sub_neg, mul_sub] using
        (show SupportingSlopes.Chosen (fun v => c i * (-X v i - -B.1 i))
          (fun v => c (i + 1) * (-X v (i + 1) - -B.1 (i + 1))) (b i) from hb i))
  have hratio (i : Fin 3) : (c i * B.2 i - c i * B.1 i) / c i = B.2 i - B.1 i := by
    rw [← mul_sub, mul_div_cancel_left₀ _ (hc i).ne']
  simpa only [hratio, width_apply] using h

/-- Use the same finite slope selector for frozen rows and for the final width bound. -/
theorem finite_width_bound {ι : Type*} [Fintype ι] (X : ι → Point 3)
    (hbox : ∀ x ∈ Hull X, ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hL : ∀ i, ∃ v, X v i = 0) (hU : ∀ i, ∃ v, X v i = 1)
    (c : Point 3) (D : ℝ) (hc : ∀ i, 0 < c i)
    (hplane : ∀ x ∈ Hull X, ∑ i, c i * x i = D)
    (lo hi : Point 3) (horder : ∀ i, lo i ≤ hi i)
    (hcover : Covers (Hull X) (lo, hi)) : 1 ≤ ∑ i, (hi i - lo i) := by
  classical
  let K := Hull X
  have hK : Convex ℝ K := convex_convexHull ℝ _
  have hX (v : ι) : X v ∈ K := subset_convexHull ℝ _ ⟨v, rfl⟩
  have hL' (i : Fin 3) : ∃ x ∈ K, x i = 0 := by
    obtain ⟨v, hv⟩ := hL i
    exact ⟨X v, hX v, hv⟩
  have hU' (i : Fin 3) : ∃ x ∈ K, x i = 1 := by
    obtain ⟨v, hv⟩ := hU i
    exact ⟨X v, hX v, hv⟩
  by_contra! hdef
  let B := clipped (lo, hi)
  have hB : B ∈ unitCovers K := clipped_unitCovers K hbox (lo, hi) horder hcover
  have hcost : width B ≤ width (lo, hi) := clipped_width_le (lo, hi) horder
  have hdefB : width B < 1 := hcost.trans_lt (by simpa only [width_apply] using hdef)
  have hstrict := strict_of_deficit K hK hbox hL' hU' B hB hdefB
  have hw (b : Bool) (i : Fin 3) : ∃ v, wall b i B < cut b i (X v) := by
    cases b
    · obtain ⟨v, hv⟩ := hL i
      exact ⟨v, by simpa [wall, cut, hv] using (hstrict i).1⟩
    · obtain ⟨v, hv⟩ := hU i
      exact ⟨v, by simpa [wall, cut, hv] using (hstrict i).2.2⟩
  obtain ⟨s, hs, hstars⟩ := constant_stars_of_deficit_of_rows
    K hK hbox hL' hU' c D hc hplane B hB hdefB hstrict
    (fun e he => finite_supporting_row X c D B hw e he)
  exact hdefB.not_ge (finite_constant_stars_bound X hL hU c D hc
    (fun v => hplane _ (hX v)) B hstrict hw s hs hstars)

end PlaneProof.FiniteCover

/- Keep the original finite generators through range normalization and the plane tilt. -/
namespace PlaneProof.Coordinates
open scoped BigOperators
abbrev Point := Fin 3 → ℝ
abbrev Hull {ι : Type*} (X : ι → Point) := convexHull ℝ (Set.range X)
variable {ι : Type*}

/-- An affine condition holding at every generator holds on their hull. -/
theorem on_hull (X : ι → Point) (f : Point →ᵃ[ℝ] ℝ) (S : Set ℝ)
    (hS : Convex ℝ S) (hX : ∀ v, f (X v) ∈ S) : ∀ x ∈ Hull X, f x ∈ S :=
  convexHull_min (by rintro _ ⟨v, rfl⟩; exact hX v) (hS.affine_preimage f)

/-- The same generators follow every affine change of coordinates. -/
theorem image_hull (X : ι → Point) (f : Point →ᵃ[ℝ] Point) :
    f '' Hull X = Hull (f ∘ X) := by
  rw [AffineMap.image_convexHull, ← Set.range_comp]

variable [Fintype ι]

/-- Finite minima and maxima give attained coordinate ranges. -/
theorem ranges [Nonempty ι] (X : ι → Point) :
    ∃ m R : Point, (∀ v i, m i ≤ X v i ∧ X v i ≤ m i + R i) ∧
      (∀ i, ∃ v, X v i = m i) ∧ (∀ i, ∃ v, X v i = m i + R i) := by
  classical
  have hn : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  have low (i : Fin 3) := Finset.exists_min_image Finset.univ (fun v => X v i) hn
  have high (i : Fin 3) := Finset.exists_max_image Finset.univ (fun v => X v i) hn
  choose p _ hp using low
  choose q _ hq using high
  refine ⟨fun i => X (p i) i, fun i => X (q i) i - X (p i) i, ?_, ?_, ?_⟩
  · intro v i
    simpa only [add_sub_cancel] using And.intro (hp i v (Finset.mem_univ v))
      (hq i v (Finset.mem_univ v))
  · exact fun i => ⟨p i, rfl⟩
  · exact fun i => ⟨q i, by ring⟩

/-- Shift and scale each coordinate to its attained unit range. -/
def normalize (m R : Point) : Point →ᵃ[ℝ] Point :=
  AffineMap.pi fun i => (R i)⁻¹ • (AffineMap.proj i - AffineMap.const ℝ Point (m i))

theorem normalize_apply (m R x : Point) (i : Fin 3) :
    normalize m R x i = (x i - m i) / R i := by
  simp [normalize, div_eq_mul_inv, mul_comm]

/-- Normalize the generators and apply the theorem for positive plane coefficients. -/
theorem positive_width (X : ι → Point) (m R c : Point) (D : ℝ)
    (hb : ∀ v i, m i ≤ X v i ∧ X v i ≤ m i + R i)
    (hL : ∀ i, ∃ v, X v i = m i) (hU : ∀ i, ∃ v, X v i = m i + R i)
    (hR : ∀ i, 0 < R i) (hc : ∀ i, 0 < c i)
    (hp : ∀ v, ∑ i, c i * X v i = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ Hull X, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  let Y := normalize m R ∘ X
  have hy (v : ι) (i : Fin 3) : Y v i = (X v i - m i) / R i := normalize_apply m R (X v) i
  have hbox : ∀ x ∈ Hull Y, ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
    intro x hx i
    exact on_hull Y (AffineMap.proj i) (Set.Icc 0 1) (convex_Icc _ _) (fun v => by
      change 0 ≤ Y v i ∧ Y v i ≤ 1
      rw [hy]
      exact ⟨div_nonneg (sub_nonneg.mpr (hb v i).1) (hR i).le,
        (div_le_one (hR i)).mpr (by linarith only [(hb v i).2])⟩) x hx
  have hplane : ∀ x ∈ Hull Y, ∑ i, (c i * R i) * x i = D-∑ i, c i * m i := by
    let f : Point →ᵃ[ℝ] ℝ := ∑ i, (c i * R i) • AffineMap.proj i
    have hf (x : Point) : f x = ∑ i, (c i * R i) * x i := by simp [f, Fin.sum_univ_three]
    apply on_hull Y f {D-∑ i, c i * m i} (convex_singleton _) (fun v => ?_)
    change f (Y v) = _
    rw [hf]
    have he (i : Fin 3) : (c i * R i) * Y v i = c i * X v i - c i * m i := by
      rw [hy]; field_simp [(hR i).ne']
    simp only [he, Finset.sum_sub_distrib, hp v]
  have H := FiniteCover.finite_width_bound Y hbox
    (fun i => (hL i).imp fun v hv => by rw [hy, hv, sub_self, zero_div])
    (fun i => (hU i).imp fun v hv => by rw [hy, hv, add_sub_cancel_left, div_self (hR i).ne'])
    (fun i => c i * R i) (D-∑ i, c i * m i) (fun i => mul_pos (hc i) (hR i)) hplane
    (fun i => (lo i - m i) / R i) (fun i => (hi i - m i) / R i)
    (fun i => div_le_div_of_nonneg_right (sub_le_sub_right (horder i) _) (hR i).le) (by
      intro y hy'
      change y ∈ Hull (normalize m R ∘ X) at hy'
      rw [← image_hull] at hy'
      obtain ⟨x, hx, rfl⟩ := hy'
      obtain ⟨i, hi⟩ := hcover x hx
      refine ⟨i, ?_, ?_⟩ <;> rw [normalize_apply]
      · exact (div_le_div_iff_of_pos_right (hR i)).mpr (sub_le_sub_right hi.1 _)
      · exact (div_le_div_iff_of_pos_right (hR i)).mpr (sub_le_sub_right hi.2 _))
  simpa only [← sub_div, sub_sub_sub_cancel_right] using H

/-- Tilt the coordinates slightly so every plane coefficient becomes positive.
Take the new extrema on the same finite list of generators. -/
theorem nonnegative_width [Nonempty ι] (X : ι → Point)
    (hb : ∀ v i, 0 ≤ X v i ∧ X v i ≤ 1)
    (hL : ∀ i, ∃ v, X v i = 0) (hU : ∀ i, ∃ v, X v i = 1)
    (A : Point) (D : ℝ) (hA : ∀ i, 0 ≤ A i) (hpos : ∃ i, 0 < A i)
    (hp : ∀ v, ∑ i, A i * X v i = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ Hull X, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) := by
  by_contra! hdef
  let S := ∑ i, (hi i - lo i)
  let e := (1 - S) / 24
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (horder i))
  have he : 0 < e := div_pos (sub_pos.mpr hdef) (by norm_num)
  have hd : 0 < 1 - 3 * e := by dsimp [e]; linarith
  have hbox (x : Point) (hx : x ∈ Hull X) (i : Fin 3) : 0 ≤ x i ∧ x i ≤ 1 :=
    on_hull X (AffineMap.proj i) (Set.Icc 0 1) (convex_Icc _ _) (fun v => hb v i) x hx
  let g : Point →ᵃ[ℝ] Point := AffineMap.pi fun i =>
    AffineMap.proj i - e • ∑ j : Fin 3, AffineMap.proj j
  have hg (i : Fin 3) (x : Point) : g x i = x i - e*∑ j, x j := by
    simp [g, Fin.sum_univ_three, mul_add]
  have near (x : Point) (hx : x ∈ Hull X) (i : Fin 3) : x i - 3 * e ≤ g x i ∧ g x i ≤ x i := by
    have hsum : 0 ≤ ∑ j, x j ∧ (∑ j, x j) ≤ 3 := by
      constructor
      · exact Finset.sum_nonneg (fun j _ => (hbox x hx j).1)
      · simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hbox x hx j).2)
    rw [hg]
    have H := mul_le_mul_of_nonneg_left hsum.2 he.le
    have L := mul_nonneg he.le hsum.1
    constructor <;> linarith only [H, L]
  have mem (v : ι) : X v ∈ Hull X := subset_convexHull ℝ _ ⟨v, rfl⟩
  obtain ⟨m, R, hrange, hmin, hmax⟩ := ranges (g ∘ X)
  have hRbound (i : Fin 3) : 1 - 3 * e ≤ R i := by
    obtain ⟨p, hp⟩ := hL i
    obtain ⟨q, hq⟩ := hU i
    have P := (near (X p) (mem p) i).2
    have Q := (near (X q) (mem q) i).1
    rw [hp] at P
    rw [hq] at Q
    have L := (hrange p i).1
    have H := (hrange q i).2
    change m i ≤ g (X p) i at L
    change g (X q) i ≤ m i + R i at H
    linarith only [P, Q, L, H]
  have hR (i : Fin 3) : 0 < R i := hd.trans_le (hRbound i)
  have hsumA : 0 < ∑ i, A i := Finset.sum_pos' (fun i _ => hA i)
    (hpos.imp fun i hi => ⟨Finset.mem_univ i, hi⟩)
  let B : Point := fun i => (1 - 3 * e) * A i + e*∑ j, A j
  have hB (i : Fin 3) : 0 < B i :=
    add_pos_of_nonneg_of_pos (mul_nonneg hd.le (hA i)) (mul_pos he hsumA)
  have hplane (v : ι) : ∑ i, B i * g (X v) i = (1 - 3 * e) * D := by
    rw [← hp v]
    simp only [B, hg, Fin.sum_univ_three]
    ring
  let l : Point := fun i => lo i - 3 * e
  have hl (i : Fin 3) : l i ≤ hi i := by dsimp [l]; linarith only [horder i, he]
  have H := positive_width (g ∘ X) m R B ((1 - 3 * e) * D) hrange hmin hmax hR hB hplane l hi hl (by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (image_hull X g).symm ▸ hy
    obtain ⟨i, hi⟩ := hcover x hx
    exact ⟨i, (sub_le_sub_right hi.1 _).trans (near x hx i).1, (near x hx i).2.trans hi.2⟩)
  have hcost : (∑ i, (hi i - l i) / R i) ≤ (S + 9 * e) / (1 - 3 * e) := by
    calc
      _ ≤ ∑ i, (hi i - l i) / (1 - 3 * e) := Finset.sum_le_sum (fun i _ =>
        div_le_div_of_nonneg_left (sub_nonneg.mpr (hl i)) hd (hRbound i))
      _ = _ := by rw [← Finset.sum_div]; congr 1; simp [S, l, Fin.sum_univ_three]; ring
  have hsmall : (S + 9 * e) / (1 - 3 * e) < 1 := by
    apply (div_lt_one hd).mpr
    dsimp [e]
    change S < 1 at hdef
    linarith only [hdef]
  exact (H.trans hcost).not_gt hsmall

/-- Normalize the finite coordinate ranges and reflect the negative relation coefficients. -/
theorem relation_width [Nonempty ι] (X : ι → Point) (m R a : Point) (D : ℝ)
    (hb : ∀ v i, m i ≤ X v i ∧ X v i ≤ m i + R i)
    (hL : ∀ i, ∃ v, X v i = m i) (hU : ∀ i, ∃ v, X v i = m i + R i)
    (hR : ∀ i, 0 < R i) (ha : ∃ i, a i ≠ 0)
    (hp : ∀ v, ∑ i, a i * X v i = D)
    (lo hi : Point) (horder : ∀ i, lo i ≤ hi i)
    (hcover : ∀ x ∈ Hull X, ∃ i, lo i ≤ x i ∧ x i ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) / R i := by
  let F : Point →ᵃ[ℝ] Point := AffineMap.pi fun i =>
    if a i < 0 then AffineMap.const ℝ Point (1 : ℝ) -
      (AffineMap.proj i).comp (normalize m R)
    else (AffineMap.proj i).comp (normalize m R)
  let Y := F ∘ X
  have heval (x : Point) (i : Fin 3) :
      F x i = if a i < 0 then 1 - (x i - m i) / R i else (x i - m i) / R i := by
    by_cases hn : a i < 0 <;> simp [F, hn, normalize_apply]
  have hy (v : ι) (i : Fin 3) :
      Y v i = if a i < 0 then 1 - (X v i - m i) / R i else (X v i - m i) / R i := heval (X v) i
  have hbox (v : ι) (i : Fin 3) : 0 ≤ Y v i ∧ Y v i ≤ 1 := by
    have H : 0 ≤ (X v i - m i) / R i ∧ (X v i - m i) / R i ≤ 1 :=
      ⟨div_nonneg (sub_nonneg.mpr (hb v i).1) (hR i).le,
        (div_le_one (hR i)).mpr (by linarith only [(hb v i).2])⟩
    rw [hy]
    split_ifs
    · constructor <;> linarith only [H.1, H.2]
    · exact H
  have hzero (i : Fin 3) : ∃ v, Y v i = 0 := by
    by_cases hn : a i < 0
    · obtain ⟨v, hv⟩ := hU i
      exact ⟨v, by rw [hy, if_pos hn, hv, add_sub_cancel_left, div_self (hR i).ne', sub_self]⟩
    · obtain ⟨v, hv⟩ := hL i
      exact ⟨v, by rw [hy, if_neg hn, hv, sub_self, zero_div]⟩
  have hone (i : Fin 3) : ∃ v, Y v i = 1 := by
    by_cases hn : a i < 0
    · obtain ⟨v, hv⟩ := hL i
      exact ⟨v, by rw [hy, if_pos hn, hv, sub_self, zero_div, sub_zero]⟩
    · obtain ⟨v, hv⟩ := hU i
      exact ⟨v, by rw [hy, if_neg hn, hv, add_sub_cancel_left, div_self (hR i).ne']⟩
  let A : Point := fun i => |a i| * R i
  let d := D - (∑ i, a i * m i) - (∑ i, if a i < 0 then a i * R i else 0)
  have hplane (v : ι) : ∑ i, A i * Y v i = d := by
    have he (i : Fin 3) : A i * Y v i = a i * X v i - a i * m i-
        (if a i < 0 then a i * R i else 0) := by
      dsimp [A]
      rw [hy]
      by_cases hn : a i < 0
      · rw [if_pos hn, if_pos hn, abs_of_neg hn]; field_simp [(hR i).ne']; ring
      · rw [if_neg hn, if_neg hn, abs_of_nonneg (le_of_not_gt hn)]
        field_simp [(hR i).ne']
        ring
    simp only [he, Finset.sum_sub_distrib, hp v, d]
  let l : Point := fun i => if a i < 0 then 1 - (hi i - m i) / R i else (lo i - m i) / R i
  let h : Point := fun i => if a i < 0 then 1 - (lo i - m i) / R i else (hi i - m i) / R i
  have ordered (i : Fin 3) : l i ≤ h i := by
    have H := div_le_div_of_nonneg_right (sub_le_sub_right (horder i) (m i)) (hR i).le
    dsimp [l, h]
    split_ifs <;> linarith only [H]
  have cover : ∀ y ∈ Hull Y, ∃ i, l i ≤ y i ∧ y i ≤ h i := by
    intro y hy'
    change y ∈ Hull (F ∘ X) at hy'
    rw [← image_hull] at hy'
    obtain ⟨x, hx, rfl⟩ := hy'
    obtain ⟨i, hi'⟩ := hcover x hx
    have L := div_le_div_of_nonneg_right (sub_le_sub_right hi'.1 (m i)) (hR i).le
    have H := div_le_div_of_nonneg_right (sub_le_sub_right hi'.2 (m i)) (hR i).le
    refine ⟨i, ?_⟩
    rw [heval]
    dsimp [l, h]
    split_ifs <;> constructor <;> linarith only [L, H]
  have H := nonnegative_width Y hbox hzero hone A d
    (fun i => mul_nonneg (abs_nonneg _) (hR i).le)
    (by obtain ⟨i, hi⟩ := ha; exact ⟨i, mul_pos (abs_pos.mpr hi) (hR i)⟩)
    hplane l h ordered cover
  have widths (i : Fin 3) : h i - l i = (hi i - lo i) / R i := by
    dsimp [h, l]
    split_ifs <;> ring
  simpa only [widths] using H

end PlaneProof.Coordinates

/- Any three planar affine functions satisfy a nontrivial affine relation. -/
namespace PlaneProof.AffineRelation
open scoped BigOperators

/-- Three affine functions on a space of dimension at most two have a nontrivial
linear combination that is constant. Some coefficients may vanish. -/
theorem exists_relation_of_finrank_le_two {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E ≤ 2)
    (f : Fin 3 → E →ᵃ[ℝ] ℝ) :
    ∃ a : Fin 3 → ℝ, (∃ i, a i ≠ 0) ∧ ∃ d : ℝ, ∀ x, ∑ i, a i * f i x = d := by
  classical
  have hd : Module.finrank ℝ (E →ₗ[ℝ] ℝ) ≤ 2 := by
    rw [← (Module.Basis.ofVectorSpace ℝ E).toDualEquiv.finrank_eq]
    exact hdim
  have hdep : ¬ LinearIndependent ℝ (fun i => (f i).linear) := by
    intro h
    have hc : 3 ≤ Module.finrank ℝ (E →ₗ[ℝ] ℝ) := h.fintype_card_le_finrank
    exact (by norm_num : ¬ (3 ≤ 2)) (hc.trans hd)
  rw [Fintype.linearIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨a, ha, i, hi⟩ := hdep
  refine ⟨a, ⟨i, hi⟩, ∑ i, a i * f i 0, fun x => ?_⟩
  have H := congrArg (fun L : E →ₗ[ℝ] ℝ => L x) ha
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at H
  have he (i : Fin 3) : f i x = (f i).linear x + f i 0 := congrFun (f i).decomp x
  simp only [he, mul_add, Finset.sum_add_distrib, H, zero_add]

end PlaneProof.AffineRelation

/- The planar width theorem in ordinary Cartesian coordinates, with the
directional width expressed as the diameter of an affine image. -/

namespace PlaneProof
open scoped BigOperators

abbrev Point := ℝ × ℝ

/-- A nonconstant affine function is nonconstant on any set with interior. -/
theorem nontrivial_image {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK : (interior K).Nonempty) (f : E →ᵃ[ℝ] ℝ)
    (hf : ∃ x y, f x ≠ f y) : (f '' K).Nontrivial := by
  by_contra hn
  have hsub := Set.not_nontrivial_iff.mp hn
  obtain ⟨p, hp⟩ := hK.mono interior_subset
  have hspan : affineSpan ℝ K = ⊤ := by
    apply top_unique
    rw [← isOpen_interior.affineSpan_eq_top hK]
    exact affineSpan_mono ℝ interior_subset
  have heq : f = AffineMap.const ℝ E (f p) :=
    AffineMap.ext_on hspan (fun x hx => hsub ⟨x, hx, rfl⟩ ⟨p, hp, rfl⟩)
  obtain ⟨x, y, hxy⟩ := hf
  exact hxy (by rw [heq]; rfl)

/-- A pair of points approximates the reciprocal directional width from above.
For an unbounded image the reciprocal diameter is zero, by Mathlib's convention. -/
theorem exists_directional_witness (K : Set Point)
    (hK : (interior K).Nonempty) (f : Point →ᵃ[ℝ] ℝ)
    (nonconstant : ∃ x y, f x ≠ f y) (ε : ℝ) (hε : 0 < ε) :
    ∃ x ∈ K, ∃ y ∈ K,
      1 / ((1 / Metric.diam (f '' K)) + ε) < dist (f x) (f y) := by
  have ht : 0 < (1 / Metric.diam (f '' K)) + ε := by positivity
  by_contra! h
  have hpairs : ∀ u ∈ f '' K, ∀ v ∈ f '' K,
      dist u v ≤ 1 / ((1 / Metric.diam (f '' K)) + ε) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact h x hx y hy
  have hb := Metric.isBounded_iff.mpr ⟨_, hpairs⟩
  have hd := Metric.diam_pos (nontrivial_image K hK f nonconstant) hb
  have hu := Metric.diam_le_of_forall_dist_le (one_div_pos.mpr ht).le hpairs
  have hlt := one_div_lt_one_div_of_lt (one_div_pos.mpr hd)
    (lt_add_of_pos_right (1 / Metric.diam (f '' K)) hε)
  rw [one_div_one_div] at hlt
  exact hlt.not_ge hu

/-- Keep the same six directional witnesses through the finite coordinate proof.
The convex set may be unbounded and the ordered windows may have zero width. -/
theorem three_windows_cover_convex
    (K : Set Point) (convex : Convex ℝ K)
    (interior_nonempty : (interior K).Nonempty)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (nonconstant : ∀ i, ∃ x y, f i x ≠ f i y)
    (lo hi : Fin 3 → ℝ) (ordered : ∀ i, lo i ≤ hi i)
    (covers : ∀ x ∈ K, ∃ i, lo i ≤ f i x ∧ f i x ≤ hi i) :
    1 ≤ ∑ i, (hi i - lo i) / Metric.diam (f i '' K) := by
  classical
  let w : Fin 3 → ℝ := fun i => hi i - lo i
  have hw (i : Fin 3) : 0 ≤ w i := sub_nonneg.mpr (ordered i)
  change 1 ≤ ∑ i, w i / Metric.diam (f i '' K)
  by_contra! hdef
  let S := ∑ i, w i / Metric.diam (f i '' K)
  have hS : S < 1 := hdef
  obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hS) (∑ i, w i)
  choose x hx y hy hxy using fun i =>
    exists_directional_witness K interior_nonempty (f i) (nonconstant i) ε hε
  let p : Fin 3 × Bool → Point := fun v => if v.2 then y v.1 else x v.1
  have hp (v : Fin 3 × Bool) : p v ∈ K := by
    cases hb : v.2 <;> simp [p, hb, hx, hy]
  let F := AffineMap.pi f
  let X : Fin 3 × Bool → Coordinates.Point := F ∘ p
  have hsub : Coordinates.Hull X ⊆ F '' K := by
    apply convexHull_min ?_ (convex.affine_image F)
    rintro _ ⟨v, rfl⟩
    exact ⟨p v, hp v, rfl⟩
  obtain ⟨m, R, hb, hL, hU⟩ := Coordinates.ranges X
  have hd (i : Fin 3) : 1 / ((1 / Metric.diam (f i '' K)) + ε) < R i := by
    apply (hxy i).trans_le
    change dist (X (i, false) i) (X (i, true) i) ≤ R i
    simpa only [add_sub_cancel_left] using
      Real.dist_le_of_mem_Icc (hb (i, false) i) (hb (i, true) i)
  have hR (i : Fin 3) : 0 < R i := lt_trans (by positivity) (hd i)
  obtain ⟨a, ha, d, hplane⟩ := AffineRelation.exists_relation_of_finrank_le_two
    (by simp [Module.finrank_prod]) f
  have hbound := Coordinates.relation_width X m R a d hb hL hU hR ha
    (fun v => hplane (p v)) lo hi ordered (by
      intro z hz
      obtain ⟨q, hq, rfl⟩ := hsub hz
      exact covers q hq)
  change 1 ≤ ∑ i, w i / R i at hbound
  have each (i : Fin 3) : w i / R i ≤ w i / Metric.diam (f i '' K) + w i * ε := by
    have ht : 0 < (1 / Metric.diam (f i '' K)) + ε := by positivity
    have H := (one_div_le_one_div_of_le (one_div_pos.mpr ht)
      (hd i).le).trans_eq (one_div_one_div _)
    simpa only [mul_add, mul_one_div] using mul_le_mul_of_nonneg_left H (hw i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => each i)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  change (∑ i, w i / R i) ≤ S + (∑ i, w i) * ε at hsum
  linarith only [hbound.trans hsum, hsmall]

/-- Three planks covering any planar convex set with nonempty interior have
total relative width at least one. An infinite directional width contributes zero. -/
theorem three_planks_cover_convex
    (K : Set Point) (convex : Convex ℝ K)
    (interior_nonempty : (interior K).Nonempty)
    (f : Fin 3 → Point →ᵃ[ℝ] ℝ) (nonconstant : ∀ i, ∃ x y, f i x ≠ f i y)
    (covers : K ⊆ ⋃ i, {x | 0 ≤ f i x ∧ f i x ≤ 1}) :
    1 ≤ ∑ i, (1 / Metric.diam (f i '' K)) := by
  simpa only [sub_zero] using three_windows_cover_convex K convex interior_nonempty f nonconstant
    (fun _ => 0) (fun _ => 1) (fun _ => zero_le_one)
    (fun x hx => Set.mem_iUnion.mp (covers hx))

end PlaneProof
