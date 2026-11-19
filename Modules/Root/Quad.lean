import Modules.Check.Number.Ball

/-!
# Positive quadratic forms by diagonal dominance

The touch leaf of a D2 certificate ends in a quadratic form `∑ ν_jk d_j d_k` that has to be
positive off zero (`code/src/proof/d2/`, the Gershgorin test of `P^T Hess G P`). Two facts about
real numbers, with indices in `range n`:

* `quad_pos_of_dominant`: if every row of the symmetrised matrix has its off-diagonal absolute
  sum below the diagonal entry (`∑_{b ≠ a} |β_ab + β_ba| < 2 β_aa`), the form is positive at
  every `e ≠ 0` (each product `e_a e_b` is at most `(e_a² + e_b²) / 2`).
* `quad_subst`: the form of `ν` at `d = P e` is the form of `P^T ν P` at `e`.
-/

open Finset

namespace Nieuwland.Root

/-- A quadratic form whose symmetrised matrix is strictly diagonally dominant with a positive
diagonal is positive off zero. -/
theorem quad_pos_of_dominant {n : ℕ} (β : ℕ → ℕ → ℝ)
    (h : ∀ a < n, ∑ b ∈ range n, (if a = b then 0 else |β a b + β b a|) < 2 * β a a)
    {e : ℕ → ℝ} (he : ∃ a < n, e a ≠ 0) :
    0 < ∑ a ∈ range n, ∑ b ∈ range n, β a b * e a * e b := by
  set w : ℕ → ℕ → ℝ := fun a b ↦ if a = b then 0 else |β a b + β b a| with hw
  have hsymm : ∀ a b, w a b = w b a := fun a b ↦ by
    by_cases hab : a = b
    · simp [hw, hab]
    · simp [hw, hab, Ne.symm hab, add_comm]
  have hpt : ∀ a b, (if a = b then 2 * β a a * e a ^ 2 else 0) - 1 / 2 * (w a b * e a ^ 2) -
      1 / 2 * (w a b * e b ^ 2) ≤ (β a b + β b a) * e a * e b := by
    intro a b
    by_cases hab : a = b
    · subst hab
      simp only [hw, ↓reduceIte]
      apply le_of_eq
      ring
    · simp only [hw, hab, ↓reduceIte]
      rcases abs_cases (β a b + β b a) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1]
        nlinarith [mul_nonneg h2 (sq_nonneg (e a + e b))]
      · rw [h1]
        nlinarith [mul_nonneg (neg_nonneg.mpr h2.le) (sq_nonneg (e a - e b))]
  have h2 : 2 * ∑ a ∈ range n, ∑ b ∈ range n, β a b * e a * e b =
      ∑ a ∈ range n, ∑ b ∈ range n, (β a b + β b a) * e a * e b := by
    have hc : ∑ a ∈ range n, ∑ b ∈ range n, β b a * e a * e b =
        ∑ a ∈ range n, ∑ b ∈ range n, β a b * e a * e b := by
      rw [sum_comm]
      exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by ring
    simp only [add_mul, sum_add_distrib, hc]
    ring
  have hc' : ∑ a ∈ range n, ∑ b ∈ range n, 1 / 2 * (w a b * e b ^ 2) =
      ∑ a ∈ range n, ∑ b ∈ range n, 1 / 2 * (w a b * e a ^ 2) := by
    rw [sum_comm]
    exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by rw [hsymm a b]
  have key : ∑ a ∈ range n, e a ^ 2 * (2 * β a a - ∑ b ∈ range n, w a b) ≤
      ∑ a ∈ range n, ∑ b ∈ range n, (β a b + β b a) * e a * e b := by
    calc ∑ a ∈ range n, e a ^ 2 * (2 * β a a - ∑ b ∈ range n, w a b)
        = ∑ a ∈ range n, ∑ b ∈ range n, ((if a = b then 2 * β a a * e a ^ 2 else 0) -
            1 / 2 * (w a b * e a ^ 2) - 1 / 2 * (w a b * e a ^ 2)) := by
          refine sum_congr rfl fun a ha ↦ ?_
          rw [sum_sub_distrib, sum_sub_distrib]
          simp only [sum_ite_eq, ha, ↓reduceIte, ← mul_sum, ← sum_mul]
          ring
      _ = ∑ a ∈ range n, ∑ b ∈ range n, ((if a = b then 2 * β a a * e a ^ 2 else 0) -
            1 / 2 * (w a b * e a ^ 2) - 1 / 2 * (w a b * e b ^ 2)) := by
          simp only [sum_sub_distrib, hc']
      _ ≤ _ := sum_le_sum fun a _ ↦ sum_le_sum fun b _ ↦ hpt a b
  obtain ⟨a₀, ha₀, hea⟩ := he
  have hpos : 0 < ∑ a ∈ range n, e a ^ 2 * (2 * β a a - ∑ b ∈ range n, w a b) :=
    sum_pos' (fun a ha ↦ mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (h a (mem_range.mp ha)).le))
      ⟨a₀, mem_range.mpr ha₀, mul_pos (by positivity) (sub_pos.mpr (h a₀ ha₀))⟩
  linarith

/-- The quadratic form of `ν` at `d = P e` is the form of `P^T ν P` at `e`. -/
theorem quad_subst (n : ℕ) (ν P : ℕ → ℕ → ℝ) (e d : ℕ → ℝ)
    (hd : ∀ j < n, d j = ∑ a ∈ range n, P j a * e a) :
    ∑ j ∈ range n, ∑ k ∈ range n, ν j k * d j * d k =
      ∑ a ∈ range n, ∑ b ∈ range n,
        (∑ j ∈ range n, ∑ k ∈ range n, P j a * ν j k * P k b) * e a * e b := by
  have h1 : ∑ j ∈ range n, ∑ k ∈ range n, ν j k * d j * d k =
      ∑ j ∈ range n, ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n,
        P j a * ν j k * P k b * e a * e b := by
    refine sum_congr rfl fun j hj ↦ sum_congr rfl fun k hk ↦ ?_
    rw [hd j (mem_range.mp hj), hd k (mem_range.mp hk), mul_assoc, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun a _ ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun b _ ↦ by ring
  have h2 : ∑ a ∈ range n, ∑ b ∈ range n,
        (∑ j ∈ range n, ∑ k ∈ range n, P j a * ν j k * P k b) * e a * e b =
      ∑ a ∈ range n, ∑ b ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n,
        P j a * ν j k * P k b * e a * e b := by
    refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
    rw [sum_mul, sum_mul]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_mul, sum_mul]
  rw [h1, h2]
  calc ∑ j ∈ range n, ∑ k ∈ range n, ∑ a ∈ range n, ∑ b ∈ range n,
        P j a * ν j k * P k b * e a * e b
      = ∑ j ∈ range n, ∑ a ∈ range n, ∑ k ∈ range n, ∑ b ∈ range n,
          P j a * ν j k * P k b * e a * e b := sum_congr rfl fun j _ ↦ sum_comm
    _ = ∑ a ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n, ∑ b ∈ range n,
          P j a * ν j k * P k b * e a * e b := sum_comm
    _ = ∑ a ∈ range n, ∑ j ∈ range n, ∑ b ∈ range n, ∑ k ∈ range n,
          P j a * ν j k * P k b * e a * e b :=
        sum_congr rfl fun a _ ↦ sum_congr rfl fun j _ ↦ sum_comm
    _ = ∑ a ∈ range n, ∑ b ∈ range n, ∑ j ∈ range n, ∑ k ∈ range n,
          P j a * ν j k * P k b * e a * e b := sum_congr rfl fun a _ ↦ sum_comm

/-- **Positive after a change of coordinates.** With `P Pa = pd ≠ 0`, the form of `ν` is positive
off zero when `P^T ν P` is diagonally dominant. -/
theorem quad_pos_of_dominant_subst {n : ℕ} (ν P Pa : ℕ → ℕ → ℝ) {pd : ℝ} (hpd : pd ≠ 0)
    (hPP : ∀ j < n, ∀ k < n, ∑ c ∈ range n, P j c * Pa c k = if j = k then pd else 0)
    (h : ∀ a < n, ∑ b ∈ range n, (if a = b then 0 else
        |(∑ j ∈ range n, ∑ k ∈ range n, P j a * ν j k * P k b) +
          ∑ j ∈ range n, ∑ k ∈ range n, P j b * ν j k * P k a|) <
      2 * ∑ j ∈ range n, ∑ k ∈ range n, P j a * ν j k * P k a)
    {d : ℕ → ℝ} (hd : ∃ k < n, d k ≠ 0) :
    0 < ∑ j ∈ range n, ∑ k ∈ range n, ν j k * d j * d k := by
  have hde : ∀ j < n, d j = ∑ c ∈ range n, P j c * (pd⁻¹ * ∑ k ∈ range n, Pa c k * d k) := by
    intro j hj
    have e1 : ∑ c ∈ range n, P j c * (pd⁻¹ * ∑ k ∈ range n, Pa c k * d k) =
        pd⁻¹ * ∑ k ∈ range n, (∑ c ∈ range n, P j c * Pa c k) * d k :=
      calc ∑ c ∈ range n, P j c * (pd⁻¹ * ∑ k ∈ range n, Pa c k * d k)
          = ∑ c ∈ range n, ∑ k ∈ range n, pd⁻¹ * (P j c * Pa c k * d k) :=
            sum_congr rfl fun c _ ↦ by
              rw [mul_sum, mul_sum]
              exact sum_congr rfl fun k _ ↦ by ring
        _ = ∑ k ∈ range n, ∑ c ∈ range n, pd⁻¹ * (P j c * Pa c k * d k) := sum_comm
        _ = pd⁻¹ * ∑ k ∈ range n, (∑ c ∈ range n, P j c * Pa c k) * d k := by
            rw [mul_sum]
            exact sum_congr rfl fun k _ ↦ by rw [sum_mul, mul_sum]
    have e2 : ∑ k ∈ range n, (∑ c ∈ range n, P j c * Pa c k) * d k = pd * d j := by
      rw [sum_eq_single j]
      · rw [hPP j hj j hj]
        simp only [↓reduceIte]
      · intro k hk hkj
        have hjk : ¬ j = k := fun e ↦ hkj e.symm
        rw [hPP j hj k (mem_range.mp hk)]
        simp only [hjk, ↓reduceIte, zero_mul]
      · intro hn
        exact absurd (mem_range.mpr hj) hn
    rw [e1, e2, ← mul_assoc, inv_mul_cancel₀ hpd, one_mul]
  have he : ∃ c < n, pd⁻¹ * ∑ k ∈ range n, Pa c k * d k ≠ 0 := by
    by_contra hall
    obtain ⟨k, hk, hdk⟩ := hd
    refine hdk ?_
    rw [hde k hk]
    refine sum_eq_zero fun c hc ↦ ?_
    have hz : pd⁻¹ * ∑ k ∈ range n, Pa c k * d k = 0 :=
      by_contra fun hne ↦ hall ⟨c, mem_range.mp hc, hne⟩
    rw [hz, mul_zero]
  have hpos := quad_pos_of_dominant
    (fun a b ↦ ∑ j ∈ range n, ∑ k ∈ range n, P j a * ν j k * P k b) h he
  rw [quad_subst n ν P _ d hde]
  exact hpos

/-- **The weighted sum of the slacks is a quadratic form of the displacement.** With
`g_i = ∑ σ_ik d_k = ∑ γ_ik d_k + ∑ μ_ijk d_j d_k` and `∑ m_i γ_ik = 0`:
`∑ (cd m_i + cn g_i) g_i = ∑ ν_jk d_j d_k` with
`ν_jk = ∑_i ((cd m_i + cn g_i) μ_ijk + cn σ_ij γ_ik)`. -/
theorem form_eq {n kk : ℕ} (cd cn : ℝ) (m g : ℕ → ℝ) (γ σ : ℕ → ℕ → ℝ) (μ : ℕ → ℕ → ℕ → ℝ)
    (d : ℕ → ℝ) (hs : ∀ i < kk, g i = ∑ k ∈ range n, σ i k * d k)
    (hm : ∀ i < kk, g i = ∑ k ∈ range n, γ i k * d k +
      ∑ j ∈ range n, ∑ k ∈ range n, μ i j k * d j * d k)
    (hst : ∀ k < n, ∑ i ∈ range kk, m i * γ i k = 0) :
    ∑ i ∈ range kk, (cd * m i + cn * g i) * g i =
      ∑ j ∈ range n, ∑ k ∈ range n,
        (∑ i ∈ range kk, ((cd * m i + cn * g i) * μ i j k + cn * σ i j * γ i k)) * d j * d k := by
  have hterm : ∀ i ∈ range kk, (cd * m i + cn * g i) * g i =
      cd * (∑ k ∈ range n, m i * γ i k * d k) +
        ∑ j ∈ range n, ∑ k ∈ range n,
          ((cd * m i + cn * g i) * μ i j k + cn * σ i j * γ i k) * d j * d k := by
    intro i hi
    have e1 := hm i (mem_range.mp hi)
    have e2 := hs i (mem_range.mp hi)
    have e3 : ∑ j ∈ range n, ∑ k ∈ range n,
          ((cd * m i + cn * g i) * μ i j k + cn * σ i j * γ i k) * d j * d k =
        (cd * m i + cn * g i) * (∑ j ∈ range n, ∑ k ∈ range n, μ i j k * d j * d k) +
          cn * ((∑ j ∈ range n, σ i j * d j) * ∑ k ∈ range n, γ i k * d k) := by
      rw [sum_mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun k _ ↦ by ring
    have e4 : ∑ k ∈ range n, m i * γ i k * d k = m i * ∑ k ∈ range n, γ i k * d k := by
      rw [mul_sum]
      exact sum_congr rfl fun k _ ↦ by ring
    rw [e3, e4]
    linear_combination (cd * m i + cn * g i) * e1 + cn * (∑ k ∈ range n, γ i k * d k) * e2
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum]
  have z1 : ∑ i ∈ range kk, ∑ k ∈ range n, m i * γ i k * d k = 0 := by
    rw [sum_comm]
    refine sum_eq_zero fun k hk ↦ ?_
    rw [← sum_mul, hst k (mem_range.mp hk), zero_mul]
  rw [z1, mul_zero, zero_add, sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_mul, sum_mul]

/-- **The leaf with linear multipliers** (`code/src/proof/d2/`, "Leaf with linear multipliers"):
`form_eq` with the multipliers `cd m_i + ∑_k λ_ik d_k + cn g_i` of the first `kl` slacks. The
terms `(∑_k λ_ik d_k) g_i` are, by the slopes of the slacks, the form of `∑_i λ_ij σ_ik`. -/
theorem form_eq_lin {n kk kl : ℕ} (cd cn : ℝ) (m g : ℕ → ℝ) (lam γ σ : ℕ → ℕ → ℝ)
    (μ : ℕ → ℕ → ℕ → ℝ) (d : ℕ → ℝ) (hkl : kl ≤ kk)
    (hs : ∀ i < kk, g i = ∑ k ∈ range n, σ i k * d k)
    (hm : ∀ i < kk, g i = ∑ k ∈ range n, γ i k * d k +
      ∑ j ∈ range n, ∑ k ∈ range n, μ i j k * d j * d k)
    (hst : ∀ k < n, ∑ i ∈ range kk, m i * γ i k = 0) :
    ∑ i ∈ range kk, (cd * m i + cn * g i) * g i +
        ∑ i ∈ range kl, (∑ k ∈ range n, lam i k * d k) * g i =
      ∑ j ∈ range n, ∑ k ∈ range n,
        (∑ i ∈ range kk, ((cd * m i + cn * g i) * μ i j k + cn * σ i j * γ i k) +
          ∑ i ∈ range kl, lam i j * σ i k) * d j * d k := by
  have h1 : ∑ i ∈ range kl, (∑ k ∈ range n, lam i k * d k) * g i =
      ∑ j ∈ range n, ∑ k ∈ range n, (∑ i ∈ range kl, lam i j * σ i k) * d j * d k := by
    have e : ∀ i ∈ range kl, (∑ k ∈ range n, lam i k * d k) * g i =
        ∑ j ∈ range n, ∑ k ∈ range n, lam i j * σ i k * d j * d k := fun i hi ↦ by
      rw [hs i (lt_of_lt_of_le (mem_range.mp hi) hkl), sum_mul_sum]
      exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring
    rw [sum_congr rfl e, sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [sum_comm]
    refine sum_congr rfl fun k _ ↦ ?_
    rw [sum_mul, sum_mul]
  rw [form_eq cd cn m g γ σ μ d hs hm hst, h1, ← sum_add_distrib]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← sum_add_distrib]
  exact sum_congr rfl fun k _ ↦ by ring

/-- **The leaf with a spread** (`code/src/proof/d2/`, "Leaf with a spread"). Slacks `g_i` of the
system with factors `F_i`, and slacks `g'_j` of further contacts tied to them by identities
`D_j g'_j = ∑ p_ji g_i` with `D_j > 0`. If the factors less the spread's share,
`F_i - ∑_j w_j p_ji / D_j`, and the spread's own factors `w_j + cn g'_j` are nonnegative, then
`∑ F_i g_i + ∑ cn g'_j²` is at most `0` wherever no slack is positive: it is
`∑ (F_i - ∑_j w_j p_ji / D_j) g_i + ∑ (w_j + cn g'_j) g'_j`. -/
theorem spread_nonpos {k ns : ℕ} (cn : ℝ) (F g g' D w : ℕ → ℝ) (p : ℕ → ℕ → ℝ)
    (hD : ∀ j < ns, 0 < D j) (hid : ∀ j < ns, D j * g' j = ∑ i ∈ range k, p j i * g i)
    (hσ : ∀ i < k, 0 ≤ F i - ∑ j ∈ range ns, w j * p j i / D j)
    (hτ : ∀ j < ns, 0 ≤ w j + cn * g' j) (hg : ∀ i < k, g i ≤ 0) (hg' : ∀ j < ns, g' j ≤ 0) :
    ∑ i ∈ range k, F i * g i + ∑ j ∈ range ns, cn * g' j * g' j ≤ 0 := by
  have hsw : ∑ i ∈ range k, (∑ j ∈ range ns, w j * p j i / D j) * g i =
      ∑ j ∈ range ns, w j * g' j := by
    simp_rw [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun j hj ↦ ?_
    have hne := (hD j (mem_range.mp hj)).ne'
    have e : ∑ i ∈ range k, w j * p j i / D j * g i =
        w j / D j * ∑ i ∈ range k, p j i * g i := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    rw [e, ← hid j (mem_range.mp hj)]
    field_simp
  have e : ∑ i ∈ range k, F i * g i + ∑ j ∈ range ns, cn * g' j * g' j =
      ∑ i ∈ range k, (F i - ∑ j ∈ range ns, w j * p j i / D j) * g i +
        ∑ j ∈ range ns, (w j + cn * g' j) * g' j := by
    have e1 : ∑ i ∈ range k, (F i - ∑ j ∈ range ns, w j * p j i / D j) * g i =
        ∑ i ∈ range k, F i * g i - ∑ j ∈ range ns, w j * g' j := by
      rw [← hsw, ← sum_sub_distrib]
      exact sum_congr rfl fun i _ ↦ by ring
    have e2 : ∑ j ∈ range ns, (w j + cn * g' j) * g' j =
        ∑ j ∈ range ns, w j * g' j + ∑ j ∈ range ns, cn * g' j * g' j := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun j _ ↦ by ring
    rw [e1, e2]
    ring
  rw [e]
  exact add_nonpos
    (sum_nonpos fun i hi ↦ mul_nonpos_of_nonneg_of_nonpos (hσ i (mem_range.mp hi))
      (hg i (mem_range.mp hi)))
    (sum_nonpos fun j hj ↦ mul_nonpos_of_nonneg_of_nonpos (hτ j (mem_range.mp hj))
      (hg' j (mem_range.mp hj)))

/-- The recursion that takes the spread's share from a factor without a division: from
`(N, M)` the contact `j` gives `(N D_j - w_j p_j M, M D_j)`. -/
def facR (w : ℕ → ℤ) (D p : ℕ → ℝ) (N M : ℝ) : ℕ → ℝ × ℝ
  | 0 => (N, M)
  | j + 1 =>
    ((facR w D p N M j).1 * D j - w j * p j * (facR w D p N M j).2, (facR w D p N M j).2 * D j)

/-- After `ns` steps from `(N, 1)` with positive `D_j`: the second entry is `∏ D_j > 0` and the
first is that product times `N - ∑ w_j p_j / D_j`. -/
theorem facR_eq (w : ℕ → ℤ) (D p : ℕ → ℝ) (N : ℝ) :
    ∀ ns : ℕ, (∀ j < ns, 0 < D j) →
      0 < (facR w D p N 1 ns).2 ∧
        (facR w D p N 1 ns).1 =
          (facR w D p N 1 ns).2 * (N - ∑ j ∈ range ns, w j * p j / D j)
  | 0, _ => by simp [facR]
  | ns + 1, hD => by
    obtain ⟨hpos, he⟩ := facR_eq w D p N ns fun j hj ↦ hD j (Nat.lt_succ_of_lt hj)
    have hd := hD ns (Nat.lt_succ_self ns)
    refine ⟨mul_pos hpos hd, ?_⟩
    simp only [facR]
    rw [he, sum_range_succ]
    field_simp
    ring

/-- A nonnegative first entry: the factor less the spread's share is nonnegative. -/
theorem sub_share_nonneg {w : ℕ → ℤ} {D p : ℕ → ℝ} {N : ℝ} {ns : ℕ} (hD : ∀ j < ns, 0 < D j)
    (h : 0 ≤ (facR w D p N 1 ns).1) : 0 ≤ N - ∑ j ∈ range ns, w j * p j / D j := by
  obtain ⟨hpos, he⟩ := facR_eq w D p N ns hD
  rw [he] at h
  exact nonneg_of_mul_nonneg_right h hpos

end Nieuwland.Root
