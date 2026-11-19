import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Weighted gauges

Zooms cover a box by images of parameter boxes. Around a centre `c` of a box, with weights
`w i ≥ 1` on a set `S` of coordinates, every point of the box is `x i = c i + ρ ^ w i * g i` on
`S`, with a radius `0 ≤ ρ ≤ 1` and `g` on a face of the box `∏ [lo i - c i, hi i - c i]` that does
not contain `0` (`exists_gauge`). The radius is the largest weighted gauge
`|x i - c i| ^ (1 / w i)` over `S`, each measured against the extent of the box beyond `c` on the
side of `x i`.

This is the cover statement of every zoom: polar zooms (all weights `1`), weighted zooms (the
weights of the frame around the zoom centre, and the nested zooms inside their faces), and chart
trees with gauges. Coordinates outside `S` are untouched; a zoom keeps them as parameters.
-/

namespace Nieuwland.Check

/-- The ratio `t / e`, or `0` if `e = 0`. -/
noncomputable def gaugeRatio (t e : ℝ) : ℝ :=
  if e = 0 then 0 else t / e

theorem gaugeRatio_le_one_of_nonneg {t e : ℝ} (he : 0 ≤ e) (ht : t ≤ e) : gaugeRatio t e ≤ 1 := by
  unfold gaugeRatio
  split_ifs with h
  · exact zero_le_one
  · exact (div_le_one₀ (lt_of_le_of_ne he (Ne.symm h))).mpr ht

theorem gaugeRatio_le_one_of_nonpos {t e : ℝ} (he : e ≤ 0) (ht : e ≤ t) : gaugeRatio t e ≤ 1 := by
  unfold gaugeRatio
  split_ifs with h
  · exact zero_le_one
  · exact (div_le_one_of_neg (lt_of_le_of_ne he h)).mpr ht

theorem le_mul_of_gaugeRatio_le {t e δ : ℝ} (he : 0 ≤ e) (ht : t ≤ e) (h : gaugeRatio t e ≤ δ) :
    t ≤ δ * e := by
  unfold gaugeRatio at h
  split_ifs at h with h0
  · rw [h0] at ht ⊢
    simpa using ht
  · exact (div_le_iff₀ (lt_of_le_of_ne he (Ne.symm h0))).mp h

theorem mul_le_of_gaugeRatio_le {t e δ : ℝ} (he : e ≤ 0) (ht : e ≤ t) (h : gaugeRatio t e ≤ δ) :
    δ * e ≤ t := by
  unfold gaugeRatio at h
  split_ifs at h with h0
  · rw [h0] at ht ⊢
    simpa using ht
  · exact (div_le_iff_of_neg (lt_of_le_of_ne he h0)).mp h

theorem gaugeRatio_pos_of_pos {t e : ℝ} (ht : 0 < t) (hte : t ≤ e) : 0 < gaugeRatio t e := by
  have he : 0 < e := ht.trans_le hte
  simp only [gaugeRatio, he.ne', ↓reduceIte]
  exact div_pos ht he

theorem gaugeRatio_pos_of_neg {t e : ℝ} (ht : t < 0) (hte : e ≤ t) : 0 < gaugeRatio t e := by
  have he : e < 0 := hte.trans_lt ht
  simp only [gaugeRatio, he.ne, ↓reduceIte]
  exact div_pos_of_neg_of_neg ht he

theorem gaugeRatio_mul {t e : ℝ} (h : 0 < gaugeRatio t e) : e ≠ 0 ∧ gaugeRatio t e * e = t := by
  unfold gaugeRatio at h ⊢
  split_ifs at h ⊢ with he
  · exact absurd h (lt_irrefl 0)
  · exact ⟨he, div_mul_cancel₀ t he⟩

/-- **The ratio on the side of `t`.** For `a ≤ t ≤ b` with `0 ≤ b`, let `e` be `b` if
`t ≥ 0` and `a` otherwise; then `t = r e` with `r = gaugeRatio t e ∈ [0, 1]`. -/
theorem gaugeRatio_side {t a b : ℝ} (hb : 0 ≤ b) (hta : a ≤ t) (htb : t ≤ b) :
    0 ≤ gaugeRatio t (if 0 ≤ t then b else a) ∧ gaugeRatio t (if 0 ≤ t then b else a) ≤ 1 ∧
      gaugeRatio t (if 0 ≤ t then b else a) * (if 0 ≤ t then b else a) = t := by
  by_cases ht : 0 ≤ t
  · simp only [ht, ↓reduceIte]
    rcases eq_or_lt_of_le hb with hb0 | hb0
    · have : t = 0 := le_antisymm (hb0 ▸ htb) ht
      simp [gaugeRatio, ← hb0, this]
    · simp only [gaugeRatio, hb0.ne', ↓reduceIte]
      exact ⟨div_nonneg ht hb0.le, (div_le_one₀ hb0).mpr htb, div_mul_cancel₀ t hb0.ne'⟩
  · simp only [ht, ↓reduceIte]
    have ha0 : a < 0 := lt_of_le_of_lt hta (not_le.mp ht)
    simp only [gaugeRatio, ha0.ne, ↓reduceIte]
    exact ⟨div_nonneg_of_nonpos (not_le.mp ht).le ha0.le, (div_le_one_of_neg ha0).mpr hta,
      div_mul_cancel₀ t ha0.ne⟩

/-- **Weighted gauges around a point of a box.** Let `c` and `x` lie in the box
`∏ [lo i, hi i]` on a finite set `S` of coordinates with weights `w i ≥ 1`, not all of whose
ranges are points. Then `x i = c i + ρ ^ w i * g i` on `S` with `0 ≤ ρ ≤ 1` and `g` in the box
`∏ [lo i - c i, hi i - c i]` on a face that does not contain `0`: `g j = hi j - c j` with
`c j < hi j` (`upper`), or `g j = lo j - c j` with `lo j < c j`, for some `j ∈ S`. (If `x = c`
on `S`, then `ρ = 0` and any such face will do.) -/
theorem exists_gauge {ι : Type*} (S : Finset ι) (w : ι → ℕ) (hw : ∀ i ∈ S, w i ≠ 0)
    {lo hi c x : ι → ℝ} (hc : ∀ i ∈ S, lo i ≤ c i ∧ c i ≤ hi i)
    (hx : ∀ i ∈ S, lo i ≤ x i ∧ x i ≤ hi i) (hS : ∃ j ∈ S, lo j < hi j) :
    ∃ (j : ι) (upper : Bool) (ρ : ℝ) (g : ι → ℝ), j ∈ S ∧ 0 ≤ ρ ∧ ρ ≤ 1 ∧
      (bif upper then c j < hi j else lo j < c j) ∧
      g j = (bif upper then hi j else lo j) - c j ∧
      ∀ i ∈ S, lo i - c i ≤ g i ∧ g i ≤ hi i - c i ∧ x i = c i + ρ ^ w i * g i := by
  classical
  -- The ratio on the side of `x i - c i`, and its `w i`-th root.
  set E : ι → ℝ := fun i ↦ if 0 ≤ x i - c i then hi i - c i else lo i - c i with hE
  set r : ι → ℝ := fun i ↦ gaugeRatio (x i - c i) (E i) with hr
  have hrat (i) (hiS : i ∈ S) : 0 ≤ r i ∧ r i ≤ 1 ∧ r i * E i = x i - c i :=
    gaugeRatio_side (by linarith [(hc i hiS).2]) (by linarith [(hx i hiS).1])
      (by linarith [(hx i hiS).2])
  set σ : ι → ℝ := fun i ↦ r i ^ ((w i : ℝ)⁻¹) with hσ
  have hσpow (i) (hiS : i ∈ S) : σ i ^ w i = r i :=
    Real.rpow_inv_natCast_pow (hrat i hiS).1 (hw i hiS)
  have hσ0 (i) (hiS : i ∈ S) : 0 ≤ σ i := Real.rpow_nonneg (hrat i hiS).1 _
  have hσ1 (i) (hiS : i ∈ S) : σ i ≤ 1 :=
    Real.rpow_le_one (hrat i hiS).1 (hrat i hiS).2.1 (by positivity)
  obtain ⟨j₀, hj₀, hlt⟩ := hS
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image S σ ⟨j₀, hj₀⟩
  -- Every ratio is at most `σ m ^ w i`.
  have hle (i) (hiS : i ∈ S) : r i ≤ σ m ^ w i := by
    rw [← hσpow i hiS]
    exact pow_le_pow_left₀ (hσ0 i hiS) (hmax i hiS) _
  rcases eq_or_lt_of_le (hσ0 m hm) with h0 | hpos
  · -- `x = c` on `S`: radius `0`, on a face of `j₀`.
    have hxc (i) (hiS : i ∈ S) : x i = c i := by
      have h1 := hle i hiS
      rw [← h0, zero_pow (hw i hiS)] at h1
      have h2 := (hrat i hiS).2.2
      rw [le_antisymm h1 (hrat i hiS).1, zero_mul] at h2
      linarith
    have hface : lo j₀ - c j₀ ≤ (bif decide (c j₀ < hi j₀) then hi j₀ else lo j₀) - c j₀ ∧
        (bif decide (c j₀ < hi j₀) then hi j₀ else lo j₀) - c j₀ ≤ hi j₀ - c j₀ := by
      by_cases h : c j₀ < hi j₀ <;> simp only [h, decide_true, decide_false, Bool.cond_true,
        Bool.cond_false] <;> constructor <;> linarith [(hc j₀ hj₀).1, (hc j₀ hj₀).2]
    refine ⟨j₀, decide (c j₀ < hi j₀), 0, fun i ↦ if i = j₀ then
        (bif decide (c j₀ < hi j₀) then hi j₀ else lo j₀) - c j₀ else 0, hj₀, le_rfl, zero_le_one,
      ?_, by simp, fun i hiS ↦ ?_⟩
    · by_cases h : c j₀ < hi j₀
      · simp [h]
      · simp only [h, decide_false, Bool.cond_false]
        exact lt_of_lt_of_le hlt (not_lt.mp h)
    · refine ⟨?_, ?_, by rw [hxc i hiS, zero_pow (hw i hiS), zero_mul, add_zero]⟩ <;> dsimp only <;>
        split_ifs with hij
      · subst hij; exact hface.1
      · linarith [(hc i hiS).1]
      · subst hij; exact hface.2
      · linarith [(hc i hiS).2]
  · -- The face of the largest gauge.
    have hrm : 0 < r m := by
      rcases eq_or_lt_of_le (hrat m hm).1 with h | h
      · rw [hσ] at hpos
        simp only [← h] at hpos
        rw [Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.mpr (hw m hm)))] at hpos
        exact absurd hpos (lt_irrefl 0)
      · exact h
    have hρw (i) : 0 < σ m ^ w i := pow_pos hpos _
    have htm : x m - c m ≠ 0 := by
      intro h0
      have := hrm
      simp only [hr, h0, gaugeRatio, div_eq_mul_inv, zero_mul, ite_self] at this
      exact lt_irrefl 0 this
    refine ⟨m, decide (0 ≤ x m - c m), σ m, fun i ↦ (x i - c i) / σ m ^ w i, hm, hσ0 m hm,
      hσ1 m hm, ?_, ?_, fun i hiS ↦ ?_⟩
    · by_cases h : 0 ≤ x m - c m
      · simp only [h, decide_true, Bool.cond_true]
        linarith [(hx m hm).2, lt_of_le_of_ne h (Ne.symm htm)]
      · simp only [h, decide_false, Bool.cond_false]
        linarith [(hx m hm).1]
    · -- `x m - c m = r m E m = σ m ^ w m E m`.
      have h2 := (hrat m hm).2.2
      rw [← hσpow m hm] at h2
      have hEm : (x m - c m) / σ m ^ w m = E m := by
        rw [← h2, mul_div_cancel_left₀ _ (hρw m).ne']
      change (x m - c m) / σ m ^ w m = _
      rw [hEm]
      by_cases h : 0 ≤ x m - c m
      · simp only [hE, h, decide_true, Bool.cond_true, ↓reduceIte]
      · simp only [hE, h, decide_false, Bool.cond_false, ↓reduceIte]
    · obtain ⟨hr0, -, hrE⟩ := hrat i hiS
      have hli := hle i hiS
      have hg : (x i - c i) / σ m ^ w i = r i / σ m ^ w i * E i := by
        rw [← hrE]
        ring
      have hq0 : 0 ≤ r i / σ m ^ w i := div_nonneg hr0 (hρw i).le
      have hq1 : r i / σ m ^ w i ≤ 1 := (div_le_one (hρw i)).mpr hli
      refine ⟨?_, ?_, by dsimp only; field_simp [(hρw i).ne']; ring⟩ <;> dsimp only <;> rw [hg] <;>
        by_cases h : 0 ≤ x i - c i <;> simp only [hE, h, ↓reduceIte] <;>
        nlinarith [(hc i hiS).1, (hc i hiS).2]

end Nieuwland.Check
