import Modules.Check.Leaf.FamilyLeaf
import Modules.Check.Leaf.Null

/-!
# Leaves of chart trees

The leaves of chart trees (`code/src/proof/tree.rs`, L1–L3) certify *weak* conditions on their
closed boxes and conclude at every pose of their family off an *exceptional set*, a finite union
of zero sets of nonzero linear forms of the view direction (part (a) of the density theorem,
`Modules/NoFit/Dense.lean`, turns that into `NoFit` on a box).

* **Bound contract.** A weak condition `p ≥ 0` is certified after division by a monomial `m`
  in slots whose ranges do not cross `0` (`regional::nonneg_on_fbox_exact`): `p = c m s` with
  `c > 0`, and `σ s ≥ 0` for the sign `σ` of `m` on the box (`monoSign`). Then `p ≥ 0`; and where
  `p < 0`, `σ s < 0` (`neg_of_signed`).
* **Weak premises.** Every premise of a support witness is a linear form `g ⬝ᵥ u ≥ 0` of the view
  direction (`Wit.forms`): an envelope `u ⬝ᵥ (c ⨯ (v_a - v_k)) ≥ 0` for every point `v_k` and its
  chosen anchor `v_a`, and the balance weights. The strict premises, nonzero normals and a
  positive sum of the weights, hold off the zero sets of the exceptional vectors (`Wit.excs`):
  a nonzero cross axis of each support direction, and the sum of the balance weights.
* `TObst` (L1, L2): weak premises and the witness polynomials of a nonnegative combination, each
  divided by its monomial with its sign (`Obst.polyOkS`). Off the exceptional set, no fit
  (`TObst.check_sound`).
* `TOut` (L3): `(N - h D) D ≥ 0` for a chart coordinate `N / D` and a bound `h` of the claim box,
  so the coordinate is not strictly inside the bound (`TOut.check_sound`).
* `TExcl` (L4): the improvement numerator of two symmetries of the symmetry data, at the
  quaternion followed by the pre-rotation of the box if any (`PosePoly.pre`), is nonnegative, so
  their pose map increases the score or ties it; an integer point where the numerator is not
  zero makes the ties nowhere dense, so they lie in the null set (`TExcl.check_sound`; part (b)
  of the density theorem, `Modules/Check/Leaf/Null.lean`).
-/

open Matrix

namespace Nieuwland.Check

open Pull

/-! ### Signs of monomials on boxes -/

/-- The sign of `x^e` for `x` in `[lo, hi]` (numerators over a positive denominator): `1` for an
even exponent or `lo ≥ 0`, `-1` for an odd exponent and `hi ≤ 0`, `0` if the range crosses `0`. -/
def slotSgn (lo hi : ℤ) (e : ℕ) : ℤ :=
  if e % 2 = 0 then 1 else if 0 ≤ lo then 1 else if hi ≤ 0 then -1 else 0

/-- The sign of the monomial `x^e` on the box with the ends `lo`, `hi`, over the first `n`
slots. -/
def monoSignL : ℕ → List ℤ → List ℤ → List ℕ → ℤ
  | 0, _, _, _ => 1
  | n + 1, lo, hi, e =>
    slotSgn (lo.headD 0) (hi.headD 0) (e.headD 0) * monoSignL n lo.tail hi.tail e.tail

/-- The sign of the monomial `x^e` on the box `b` of `n` slots (`0` if it is not constant). -/
def monoSign (n : ℕ) (b : Box) (e : List ℕ) : ℤ :=
  monoSignL n b.lo b.hi e

theorem slotSgn_cases (lo hi : ℤ) (e : ℕ) :
    slotSgn lo hi e = 1 ∨ slotSgn lo hi e = -1 ∨ slotSgn lo hi e = 0 := by
  unfold slotSgn
  split_ifs <;> simp

theorem monoSignL_cases : ∀ (n : ℕ) (lo hi : List ℤ) (e : List ℕ),
    monoSignL n lo hi e = 1 ∨ monoSignL n lo hi e = -1 ∨ monoSignL n lo hi e = 0
  | 0, _, _, _ => Or.inl rfl
  | n + 1, lo, hi, e => by
    simp only [monoSignL]
    rcases slotSgn_cases (lo.headD 0) (hi.headD 0) (e.headD 0) with h | h | h <;>
      rcases monoSignL_cases n lo.tail hi.tail e.tail with h' | h' | h' <;> rw [h, h'] <;>
      norm_num

theorem monoSign_cases (n : ℕ) (b : Box) (e : List ℕ) :
    monoSign n b e = 1 ∨ monoSign n b e = -1 ∨ monoSign n b e = 0 :=
  monoSignL_cases n b.lo b.hi e

theorem headD_eq_getD' {α : Type*} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

theorem getD_tail' {α : Type*} (l : List α) (i : ℕ) (d : α) :
    l.tail.getD i d = l.getD (i + 1) d := by
  cases l <;> simp

/-- One factor: `σ x^e ≥ 0` for the sign `σ ≠ 0` of `x ∈ [lo / d, hi / d]`. -/
theorem slotSgn_mul_pow_nonneg {lo hi : ℤ} {e : ℕ} {d x : ℝ} (hd : 0 < d)
    (hx : (lo : ℝ) / d ≤ x ∧ x ≤ (hi : ℝ) / d) (h : slotSgn lo hi e ≠ 0) :
    0 ≤ (slotSgn lo hi e : ℝ) * x ^ e := by
  unfold slotSgn at h ⊢
  split_ifs at h ⊢ with h₁ h₂ h₃
  · simpa using Even.pow_nonneg (Nat.even_iff.mpr h₁) x
  · have : 0 ≤ x := (div_nonneg (by exact_mod_cast h₂) hd.le).trans hx.1
    simpa using pow_nonneg this e
  · have hx0 : x ≤ 0 := hx.2.trans (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h₃) hd.le)
    have hodd : Odd e := Nat.odd_iff.mpr (by omega)
    have := hodd.pow_nonpos hx0
    push_cast
    linarith
  · exact absurd rfl h

theorem monoSignL_mul_nonneg {d : ℝ} (hd : 0 < d) : ∀ (n : ℕ) (lo hi : List ℤ) (e : List ℕ)
    (x : Fin n → ℝ), (∀ i : Fin n, (lo.getD i 0 : ℝ) / d ≤ x i ∧ x i ≤ (hi.getD i 0 : ℝ) / d) →
    monoSignL n lo hi e ≠ 0 → 0 ≤ (monoSignL n lo hi e : ℝ) * DPoly.monoVal n e x
  | 0, _, _, _, _, _, _ => by simp [monoSignL, DPoly.monoVal]
  | n + 1, lo, hi, e, x, hx, h => by
    simp only [monoSignL, ne_eq, mul_eq_zero, not_or] at h
    change 0 ≤ ((slotSgn (lo.headD 0) (hi.headD 0) (e.headD 0) *
      monoSignL n lo.tail hi.tail e.tail : ℤ) : ℝ) *
      (x 0 ^ e.headD 0 * DPoly.monoVal n e.tail (Fin.tail x))
    have h0 : 0 ≤ (slotSgn (lo.headD 0) (hi.headD 0) (e.headD 0) : ℝ) * x 0 ^ e.headD 0 := by
      refine slotSgn_mul_pow_nonneg hd ?_ h.1
      have := hx 0
      simp only [Fin.val_zero] at this
      rwa [headD_eq_getD', headD_eq_getD']
    have h1 := monoSignL_mul_nonneg hd n lo.tail hi.tail e.tail (Fin.tail x) (fun i ↦ by
      have := hx i.succ
      simp only [Fin.val_succ] at this
      rw [getD_tail', getD_tail']
      exact this) h.2
    push_cast
    calc (0 : ℝ) ≤ ((slotSgn (lo.headD 0) (hi.headD 0) (e.headD 0) : ℝ) * x 0 ^ e.headD 0) *
          ((monoSignL n lo.tail hi.tail e.tail : ℝ) * DPoly.monoVal n e.tail (Fin.tail x)) :=
          mul_nonneg h0 h1
      _ = _ := by ring

/-- **Signs of monomials.** If the sign `σ` of `x^e` on the box is not `0`, then `σ x^e ≥ 0`
there. -/
theorem monoSign_mul_nonneg {n : ℕ} {b : Box} {e : List ℕ} (h : monoSign n b e ≠ 0)
    (hden : 0 < b.den) {x : Fin n → ℝ} (hx : b.Mem n x) :
    0 ≤ (monoSign n b e : ℝ) * DPoly.monoVal n e x :=
  monoSignL_mul_nonneg (by exact_mod_cast hden) n b.lo b.hi e x hx h

/-- **The bound contract.** With `p = c m s`, `c > 0`, `σ m ≥ 0` and `σ = ±1`: `σ s ≥ 0` gives
`p ≥ 0`. -/
theorem nonneg_of_signed {p c m s σ : ℝ} (hc : 0 < c) (hσ : σ = 1 ∨ σ = -1) (hm : 0 ≤ σ * m)
    (hp : p = c * m * s) (hs : 0 ≤ σ * s) : 0 ≤ p := by
  have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have : p = c * ((σ * m) * (σ * s)) := by
    rw [hp]
    linear_combination (-(c * m * s)) * hσσ
  rw [this]
  exact mul_nonneg hc.le (mul_nonneg hm hs)

/-- **The bound contract at a negative value.** With `p = c m s`, `c > 0`, `σ m ≥ 0` and
`σ = ±1`: `p < 0` gives `σ s < 0`. -/
theorem neg_of_signed {p c m s σ : ℝ} (hc : 0 < c) (hσ : σ = 1 ∨ σ = -1) (hm : 0 ≤ σ * m)
    (hp : p = c * m * s) (hneg : p < 0) : σ * s < 0 := by
  by_contra hs
  exact absurd (nonneg_of_signed hc hσ hm hp (le_of_not_gt hs)) (not_le.mpr hneg)

theorem monoSign_eq {n : ℕ} {b : Box} {e : List ℕ} (h : monoSign n b e ≠ 0) :
    (monoSign n b e : ℝ) = 1 ∨ (monoSign n b e : ℝ) = -1 := by
  rcases monoSign_cases n b e with h' | h' | h'
  · left
    rw [h']
    norm_num
  · right
    rw [h']
    norm_num
  · exact absurd h' h

/-- **One weak term.** The conclusion of the sign checks (`Pull.check_sound`, the sparse
`Pull.checkX_sound`) for the one term `⟨G, e⟩` and the one tuple `[(0, σ)]` with a weak sign: at a
point `z` of the box, `G = c z^e s` with `c > 0` and `σ s ≥ 0`. -/
theorem single_of_pull {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ] {n : ℕ} {G : GenPoly κ}
    {e : List ℕ} {σ : ℤ} {b : Box}
    (h : ∀ τ ∈ ([[(0, σ)]] : List Tuple), ∀ x : Fin n → ℝ, b.Mem n x → ∃ c : ℝ, 0 < c ∧
      ∃ s : ℕ → ℝ,
      (∀ jw ∈ τ, (([⟨G, e⟩] : List (Term κ)).getD jw.1 default).G.run Exact.re (ext n x) =
        c * DPoly.monoVal n (([⟨G, e⟩] : List (Term κ)).getD jw.1 default).e x * s jw.1) ∧
      Sign false (τ.map fun jw ↦ (jw.2 : ℝ) * s jw.1).sum) {z : Fin n → ℝ} (hz : b.Mem n z) :
    ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ, G.run Exact.re (ext n z) = c * DPoly.monoVal n e z * s ∧
      0 ≤ (σ : ℝ) * s := by
  obtain ⟨c, hc0, s, heq, hsign⟩ := h _ List.mem_cons_self z hz
  have he := heq (0, σ) List.mem_cons_self
  simp only [List.getD_cons_zero] at he
  simp only [Sign, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at hsign
  exact ⟨c, hc0, s 0, he, hsign⟩


/-! ### Linear forms of the view direction -/

section Forms

variable {κ : Type} [Add κ] [Sub κ] [Mul κ]

/-- The linear form `g ⬝ᵥ U` of the view vector, as a pose polynomial. -/
def dotU (g : V3 κ) : PosePoly κ where
  run k U _ := U.dot (g.map k)
  natural f hf k U Q := by
    rw [V3.map_dot hf]
    rfl

variable [ExactBasis κ]

theorem dotU_eval (g : V3 κ) (o : ℕ → ℝ) : (dotU g).eval o = Exact.reV g ⬝ᵥ outU o := by
  simp only [PosePoly.eval, dotU, V3.dot_eq_dotProduct, toFun_viewOf]
  rw [dotProduct_comm]
  rfl

/-- A default form. -/
def dfltForm : V3 κ × List ℕ := (⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩, [])

/-- Linear forms `g` with the exponents `e` of their dividing monomials: each is nonnegative at
the view outputs of `Ψ` on the box `b` of `n` slots (bound contract), with the bisection order `o`
(`Pull.bisW`). -/
def formsPull (n : ℕ) (Ψ : GenMap κ) (b : Box) (depth : ℕ) (fs : List (V3 κ × List ℕ))
    (o : List (ℕ × ℕ) := []) : Bool :=
  fs.all (fun f ↦ monoSign n b f.2 != 0) &&
    Pull.check n (fs.map fun f ↦ (⟨(dotU f.1).comp Ψ, f.2⟩ : Term κ)) false depth b
      ((List.range fs.length).map fun i ↦ [(i, monoSign n b (fs.getD i dfltForm).2)]) o

/-- The forms that are not nonnegative at the vertex hull of the views (`hullPts`): all of them
unless every slot enters the views with a single exponent. -/
def formsLeft (n : ℕ) (Ψ : GenMap κ) (b : Box) (fs : List (V3 κ × List ℕ)) :
    List (V3 κ × List ℕ) :=
  match hullPts Ψ n b with
  | some us => fs.filter fun f ↦ !nonnegAt us f.1
  | none => fs

/-- Linear forms `g` with the exponents `e` of their dividing monomials, each nonnegative at the
view outputs of `Ψ` on the box `b` of `n` slots: at the vertex hull of the views where that shows
it, by the bound contract otherwise. On the leaves of chart trees the views are multilinear in the
slots, so the hull decides every form. -/
def formsOk (n : ℕ) (Ψ : GenMap κ) (b : Box) (depth : ℕ) (fs : List (V3 κ × List ℕ))
    (o : List (ℕ × ℕ) := []) : Bool :=
  formsPull n Ψ b depth (formsLeft n Ψ b fs) o

/-- **Soundness of linear forms by the bound contract.** -/
theorem formsPull_sound {n : ℕ} {Ψ : GenMap κ} {b : Box} {depth : ℕ} {fs : List (V3 κ × List ℕ)}
    {o : List (ℕ × ℕ)} (h : formsPull n Ψ b depth fs o = true) {z : Fin n → ℝ} (hz : b.Mem n z) :
    ∀ f ∈ fs, 0 ≤ Exact.reV f.1 ⬝ᵥ outU (Ψ.run Exact.re (ext n z)) := by
  simp only [formsPull, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨hsg, hc⟩ := h
  have hden : 0 < b.den := Pull.den_pos_of_check hc
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hfi : fs.getD i dfltForm = fs[i] := List.getD_eq_getElem _ _ hi
  have hmem : [(i, monoSign n b (fs.getD i dfltForm).2)] ∈
      (List.range fs.length).map fun i ↦ [(i, monoSign n b (fs.getD i dfltForm).2)] :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  obtain ⟨c, hc0, s, heq, hsign⟩ := Pull.check_sound hc _ hmem z hz
  have he := heq _ List.mem_cons_self
  rw [getD_map_of_lt _ dfltForm _ hi, hfi] at he
  simp only [PosePoly.comp_run, dotU_eval] at he
  simp only [Sign, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, hfi] at hsign
  have hs0 : monoSign n b fs[i].2 ≠ 0 := hsg _ (List.getElem_mem hi)
  exact nonneg_of_signed hc0 (monoSign_eq hs0) (monoSign_mul_nonneg hs0 hden hz) he hsign

/-- **Soundness of linear forms.** -/
theorem formsOk_sound {n : ℕ} {Ψ : GenMap κ} {b : Box} {depth : ℕ} {fs : List (V3 κ × List ℕ)}
    {o : List (ℕ × ℕ)} (h : formsOk n Ψ b depth fs o = true) {z : Fin n → ℝ} (hz : b.Mem n z) :
    ∀ f ∈ fs, 0 ≤ Exact.reV f.1 ⬝ᵥ outU (Ψ.run Exact.re (ext n z)) := by
  have hden : 0 < b.den := by
    simp only [formsOk, formsPull, Bool.and_eq_true] at h
    exact Pull.den_pos_of_check h.2
  have hp := formsPull_sound h hz
  intro f hf
  unfold formsLeft at hp
  split at hp
  · rename_i us hus
    by_cases hu : nonnegAt us f.1 = true
    · exact (coneBound_hullPts hus hden hz).nonneg hu
    · exact hp f (List.mem_filter.mpr ⟨hf, by simpa using hu⟩)
  · exact hp f hf

end Forms

/-! ### Weak premises of support witnesses -/

section Weak

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- The envelope forms `c ⨯ (v_{dom k} - v_k)` of the direction `c`, for every point `v_k` and
its chosen anchor `dom k`. -/
def envForms (pts : List (V3 κ)) (c : V3 κ) (dom : List ℕ) : List (V3 κ) :=
  (List.range pts.length).map fun k ↦ c.cross ((pt pts (dom.getD k 0)).sub (pt pts k))

/-- The chosen anchors of the first `m` points are anchors. -/
def domOk (A dom : List ℕ) (m : ℕ) : Bool :=
  (List.range m).all fun k ↦ decide (dom.getD k 0 ∈ A)

theorem cross_dot_eq (c d u : Fin 3 → ℝ) : (c ⨯₃ d) ⬝ᵥ u = (u ⨯₃ c) ⬝ᵥ d := by
  simp only [cross_apply, dotProduct, Fin.sum_univ_three]
  simp
  ring

/-- **Envelopes from forms.** If every point's form is nonnegative at `u`, every point is
dominated by its chosen anchor along the normal `u ⨯₃ c`. -/
theorem envelope_of_forms {pts : List (V3 κ)} {c : V3 κ} {A dom : List ℕ}
    (hd : domOk A dom pts.length = true) {u : Fin 3 → ℝ}
    (hf : ∀ g ∈ envForms pts c dom, 0 ≤ Exact.reV g ⬝ᵥ u) :
    Envelope pts (u ⨯₃ Exact.reV c) A := by
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Polyhedron.mem_ofPoints.mp hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
  refine ⟨dom.getD k 0, of_decide_eq_true (List.all_eq_true.mp hd k (List.mem_range.mpr hk)), ?_⟩
  have hg := hf _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  have hpk : pt pts k = pts[k] := by
    rw [pt, List.getD_eq_getElem _ _ hk]
  rw [Exact.reV_cross, Exact.reV_sub, cross_dot_eq, dotProduct_sub, hpk] at hg
  linarith

namespace Wit

/-- The weak premise forms of the witness with the chosen anchors `dom` (one list per support):
the envelopes, then for balanced supports the balance weights. -/
def forms (pts : List (V3 κ)) : Wit κ → List (List ℕ) → List (V3 κ)
  | balanced w, dom => envForms pts (w.dir pts 0) (dom.getD 0 []) ++
      envForms pts (w.dir pts 1) (dom.getD 1 []) ++ envForms pts (w.dir pts 2) (dom.getD 2 []) ++
      [weightVec w.sigma (w.dir pts) 0, weightVec w.sigma (w.dir pts) 1,
        weightVec w.sigma (w.dir pts) 2]
  | width w, dom => envForms pts w.c (dom.getD 0 []) ++
      envForms pts (V3.smul (Exact.ofInt (-1)) w.c) (dom.getD 1 [])
  | centred w, dom => envForms pts w.c (dom.getD 0 []) ++
      envForms pts (V3.smul (Exact.ofInt (-1)) w.c) (dom.getD 1 [])

/-- The plugs are points and the chosen anchors are anchors. -/
def domOk (pts : List (V3 κ)) : Wit κ → List (List ℕ) → Bool
  | balanced w, dom => allFin3 fun i ↦ decide ((w.sup i).plug < pts.length) &&
      Check.domOk (w.sup i).anchors (dom.getD i []) pts.length
  | width w, dom => decide (w.pos.plug < pts.length) && decide (w.neg.plug < pts.length) &&
      Check.domOk w.pos.anchors (dom.getD 0 []) pts.length &&
      Check.domOk w.neg.anchors (dom.getD 1 []) pts.length
  | centred w, dom => decide (w.plugs.1 < pts.length) && decide (w.plugs.2 < pts.length) &&
      Check.domOk (w.pairs.map Prod.fst) (dom.getD 0 []) pts.length &&
      Check.domOk (w.pairs.map Prod.snd) (dom.getD 1 []) pts.length && w.sumsOk pts

/-- The first vector of a list known to be nonzero. -/
def firstNZ (gs : List (V3 κ)) : Option (V3 κ) :=
  gs.find? fun g ↦ Exact.nonzeroV g

theorem firstNZ_spec {gs : List (V3 κ)} {g : V3 κ} (h : firstNZ gs = some g) :
    g ∈ gs ∧ Exact.nonzeroV g = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

/-- The sum of the balance weights of balanced supports. -/
def weightSum (pts : List (V3 κ)) (w : Balanced) : V3 κ :=
  ((weightVec w.sigma (w.dir pts) 0).add (weightVec w.sigma (w.dir pts) 1)).add
    (weightVec w.sigma (w.dir pts) 2)

/-- The exceptional vectors: a nonzero cross axis of each support direction (the normal does not
vanish off its zero set) and, for balanced supports, the sum of the balance weights (positive off
its zero set); `none` if one of them is missing or zero. -/
def excs (pts : List (V3 κ)) : Wit κ → Option (List (V3 κ))
  | balanced w =>
    match firstNZ (crossAxes (w.dir pts 0)), firstNZ (crossAxes (w.dir pts 1)),
      firstNZ (crossAxes (w.dir pts 2)) with
    | some g₀, some g₁, some g₂ =>
      if Exact.nonzeroV (weightSum pts w) then some [g₀, g₁, g₂, weightSum pts w] else none
    | _, _, _ => none
  | width w => (firstNZ (crossAxes w.c)).map fun g ↦ [g]
  | centred w => (firstNZ (crossAxes w.c)).map fun g ↦ [g]

/-- The exceptional vectors are not zero. -/
theorem excs_ne {pts : List (V3 κ)} {W : Wit κ} {gs : List (V3 κ)} (h : W.excs pts = some gs) :
    ∀ g ∈ gs, Exact.nonzeroV g = true := by
  cases W with
  | balanced w =>
    simp only [excs] at h
    split at h
    next g₀ g₁ g₂ h₀ h₁ h₂ =>
      split_ifs at h with hG
      simp only [Option.some.injEq] at h
      subst h
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact (firstNZ_spec h₀).2
      · exact (firstNZ_spec h₁).2
      · exact (firstNZ_spec h₂).2
      · exact hG
    next => exact absurd h (by simp)
  | width w =>
    simp only [excs] at h
    obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.mp h
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact (firstNZ_spec hg').2
  | centred w =>
    simp only [excs] at h
    obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.mp h
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact (firstNZ_spec hg').2

/-- A nonzero cross axis of `c` that is not orthogonal to `u`: the normal `u ⨯₃ c` does not
vanish. -/
theorem normal_ne {c g : V3 κ} (hg : firstNZ (crossAxes c) = some g) {u : Fin 3 → ℝ}
    (hu : Exact.reV g ⬝ᵥ u ≠ 0) : u ⨯₃ Exact.reV c ≠ 0 :=
  fun h0 ↦ hu (dot_crossAxes_eq_zero h0 g (firstNZ_spec hg).1)

/-- **Weak premises.** If the premise forms are nonnegative at `u` and `u` is not orthogonal to
the exceptional vectors, the premises hold at `u`. -/
theorem premises_of_weak {pts : List (V3 κ)} {W : Wit κ} {dom : List (List ℕ)}
    {gs : List (V3 κ)} (hd : W.domOk pts dom = true) (he : W.excs pts = some gs)
    {u : Fin 3 → ℝ} (hf : ∀ g ∈ W.forms pts dom, 0 ≤ Exact.reV g ⬝ᵥ u)
    (hu : ∀ g ∈ gs, Exact.reV g ⬝ᵥ u ≠ 0) : W.Premises pts u := by
  cases W with
  | balanced w =>
    simp only [domOk, allFin3_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd
    simp only [excs] at he
    split at he
    next g₀ g₁ g₂ h₀ h₁ h₂ =>
      split_ifs at he with hG
      simp only [Option.some.injEq] at he
      subst he
      simp only [forms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
      have henv (i : Fin 3) :
          Envelope pts (u ⨯₃ Exact.reV (w.dir pts i)) (w.sup i).anchors := by
        refine envelope_of_forms (hd i).2 fun g hg ↦ hf g ?_
        fin_cases i
        · exact Or.inl (Or.inl (Or.inl hg))
        · exact Or.inl (Or.inl (Or.inr hg))
        · exact Or.inl (Or.inr hg)
      have hw (i : Fin 3) : 0 ≤ weightPoly (w.sigma : ℝ) u (Exact.reV (w.dir pts (i + 1)))
          (Exact.reV (w.dir pts (i + 2))) := by
        rw [weightPoly_eq]
        refine hf _ (Or.inr ?_)
        fin_cases i <;> simp
      refine ⟨fun i ↦ (hd i).1, fun i ↦ ?_, henv, hw, ?_⟩
      · fin_cases i
        · exact normal_ne h₀ (hu g₀ (by simp))
        · exact normal_ne h₁ (hu g₁ (by simp))
        · exact normal_ne h₂ (hu g₂ (by simp))
      · have hsum : ∑ i, weightPoly (w.sigma : ℝ) u (Exact.reV (w.dir pts (i + 1)))
            (Exact.reV (w.dir pts (i + 2))) = Exact.reV (weightSum pts w) ⬝ᵥ u := by
          simp only [weightPoly_eq, Fin.sum_univ_three, weightSum, Exact.reV_add, add_dotProduct]
        rw [hsum]
        have hnn : 0 ≤ Exact.reV (weightSum pts w) ⬝ᵥ u := by
          rw [← hsum]
          exact Finset.sum_nonneg fun i _ ↦ hw i
        exact lt_of_le_of_ne hnn (hu _ (by simp)).symm
    next => exact absurd he (by simp)
  | width w =>
    simp only [domOk, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨⟨hpP, hpN⟩, hdP⟩, hdN⟩ := hd
    simp only [excs] at he
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp he
    simp only [forms, List.mem_append] at hf
    exact ⟨hpP, hpN, normal_ne hg (hu g (by simp)),
      envelope_of_forms hdP fun g' hg' ↦ hf g' (Or.inl hg'),
      envelope_of_forms hdN fun g' hg' ↦ hf g' (Or.inr hg')⟩
  | centred w =>
    simp only [domOk, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨⟨⟨hpP, hpN⟩, hdP⟩, hdN⟩, hs⟩ := hd
    simp only [excs] at he
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp he
    simp only [forms, List.mem_append] at hf
    exact ⟨⟨hpP, hpN, normal_ne hg (hu g (by simp)),
      envelope_of_forms hdP fun g' hg' ↦ hf g' (Or.inl hg'),
      envelope_of_forms hdN fun g' hg' ↦ hf g' (Or.inr hg')⟩, Centred.sums_of_ok hs⟩

end Wit

end Weak

/-! ### Signed combinations -/

/-- The weighted tuples of a combination with signed monomials: for the parts `(i, m, c)`, one
choice `j < m` of every part, as the term `i K + j` with weight `c σ i j`, where `σ i j` is the
sign of the monomial dividing choice `j` of part `i`. -/
def combTuplesS (K : ℕ) (σ : ℕ → ℕ → ℤ) : List (ℕ × ℕ × ℤ) → List Tuple
  | [] => [[]]
  | (i, m, c) :: ps => (List.range m).flatMap fun j ↦
      (combTuplesS K σ ps).map fun τ ↦ (i * K + j, c * σ i j) :: τ

theorem mem_combTuplesS (K : ℕ) (σ : ℕ → ℕ → ℤ) (g : ℕ → ℕ) : ∀ ps : List (ℕ × ℕ × ℤ),
    (∀ p ∈ ps, g p.1 < p.2.1) →
      ps.map (fun p ↦ (p.1 * K + g p.1, p.2.2 * σ p.1 (g p.1))) ∈ combTuplesS K σ ps
  | [], _ => by simp [combTuplesS]
  | (i, m, c) :: ps, h => by
    simp only [List.map_cons, combTuplesS, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨g i, h _ List.mem_cons_self, _,
      mem_combTuplesS K σ g ps fun p hp ↦ h p (List.mem_cons_of_mem _ hp), rfl⟩

theorem combTuplesS_eq_combL (K : ℕ) (σ : ℕ → ℕ → ℤ) : ∀ ps : List (ℕ × ℕ × ℤ),
    combTuplesS K σ ps = Pull.combL K σ (ps.map fun p ↦ (p.1, List.range p.2.1, p.2.2))
  | [] => rfl
  | (i, m, c) :: ps => by
    simp only [combTuplesS, List.map_cons, Pull.combL, combTuplesS_eq_combL K σ ps]

theorem sum_neg_of_mul_neg {s : ℕ → ℝ} : ∀ τ : Tuple, τ ≠ [] →
    (∀ jw ∈ τ, (jw.2 : ℝ) * s jw.1 < 0) → (τ.map fun jw ↦ (jw.2 : ℝ) * s jw.1).sum < 0
  | [], h, _ => absurd rfl h
  | jw :: τ, _, h => by
    rw [List.map_cons, List.sum_cons]
    have h1 := h jw List.mem_cons_self
    rcases τ with _ | ⟨jw', τ⟩
    · simpa using h1
    · have h2 := sum_neg_of_mul_neg (jw' :: τ) (List.cons_ne_nil _ _) fun x hx ↦
        h x (List.mem_cons_of_mem _ hx)
      linarith

namespace Obst

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]
variable (pts : List (V3 κ)) (n : ℕ) (Ψ : GenMap κ) (b : Box) (ob : Obst κ) (pre : Option (Q4 κ))

/-- The sign of the monomial dividing choice `j` of part `i` on the box. -/
def sgn (i j : ℕ) : ℤ :=
  monoSign n b ((ob.exps.getD i []).getD j [])

/-- The factor of the weight of choice `j` of part `i` in the factors `f` (per part and choice;
a missing one is `1`). -/
def fac (f : List (List ℤ)) (i j : ℕ) : ℤ := (f.getD i []).getD j 1

/-- The signed weight factor of choice `j` of part `i`: its monomial's sign times its factor in
`f`. -/
def sgnF (f : List (List ℤ)) (i j : ℕ) : ℤ := ob.sgn n b i j * fac f i j

/-- **The polynomial check with signed monomials**: every monomial has a sign on the box, every
factor of `f` is positive, and every weighted sum of one anchor choice per part (with the
pre-rotation `pre`), each divided by its monomial and multiplied by the monomial's sign and its
factor, is nonnegative on the box, in the bisection order `o` (`Pull.bisW`). The factors make the
sums positive multiples of rupert's where Lean's slots are rupert's over scales (`TLeaf.obstF`);
any positive factors are sound. -/
def polyOkS (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  (List.range ob.parts.length).all (fun i ↦
    (List.range (ob.part i).1.choices.length).all fun j ↦
      ob.sgn n b i j != 0 && decide (0 < fac f i j)) &&
    Pull.check n (ob.terms pts Ψ pre) false ob.depth b
      (combTuplesS ob.K (ob.sgnF n b f) ob.specs) o

/-- `polyOkS` as compiled code runs it (`polyOkS_eq_polyOkSF`): the sign check of the
combinations by `Pull.checkComb`, once per tuple of representatives of the anchor choices with
equal data. -/
def polyOkSF (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  (List.range ob.parts.length).all (fun i ↦
    (List.range (ob.part i).1.choices.length).all fun j ↦
      ob.sgn n b i j != 0 && decide (0 < fac f i j)) &&
    Pull.checkComb n (ob.terms pts Ψ pre) false ob.depth b ob.K (ob.sgnF n b f)
      (ob.specs.map fun p ↦ (p.1, List.range p.2.1, p.2.2)) o

@[csimp] theorem polyOkS_eq_polyOkSF : @polyOkS = @polyOkSF := by
  funext κ _ _ _ _ pts n Ψ b ob pre o f
  rw [polyOkS, polyOkSF, combTuplesS_eq_combL, Pull.check_combL]

variable {pts n Ψ b ob pre}

/-- **Soundness of signed combinations.** If every part has positive weight and an anchor choice
whose polynomial is negative at a point of the box, the check fails. -/
theorem polyOkS_sound {o : List (ℕ × ℕ)} {f : List (List ℤ)}
    (h : ob.polyOkS pts n Ψ b pre o f = true) {z : Fin n → ℝ} (hz : b.Mem n z)
    (hne : ob.parts ≠ []) (hw : ∀ p ∈ ob.parts, 0 < p.2)
    (hneg : ∀ i, i < ob.parts.length → ∃ j, j < (ob.part i).1.choices.length ∧
      (((ob.part i).1.poly pts ((ob.part i).1.choices.getD j [])).pre pre).eval
        (Ψ.run Exact.re (ext n z)) < 0) : False := by
  simp only [polyOkS, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne,
    ne_eq, decide_eq_true_eq] at h
  obtain ⟨hmono, hcheck⟩ := h
  have hden : 0 < b.den := Pull.den_pos_of_check hcheck
  choose! g hg hgneg using hneg
  set τ := ob.specs.map fun p ↦ (p.1 * ob.K + g p.1, p.2.2 * ob.sgnF n b f p.1 (g p.1)) with hτ
  have hmem : τ ∈ combTuplesS ob.K (ob.sgnF n b f) ob.specs :=
    mem_combTuplesS _ _ g _ fun p hp ↦ by
    simp only [specs, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    exact hg i hi
  obtain ⟨c, hc, s, heq, hsign⟩ := Pull.check_sound hcheck τ hmem z hz
  have hall : ∀ jw ∈ τ, (jw.2 : ℝ) * s jw.1 < 0 := by
    intro jw hjw
    simp only [hτ, specs, List.map_map, List.mem_map, List.mem_range, Function.comp] at hjw
    obtain ⟨i, hi, rfl⟩ := hjw
    have hgi := hg i hi
    have hgK := lt_of_lt_of_le hgi (le_K hi)
    have he := heq _ (List.mem_map.mpr ⟨(i, (ob.part i).1.choices.length, ((ob.part i).2 : ℤ)),
      List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, rfl⟩)
    simp only [getD_terms hi hgK, term, PosePoly.comp_run] at he
    have hs0 : ob.sgn n b i (g i) ≠ 0 := (hmono i hi (g i) hgi).1
    have hf0 : (0 : ℝ) < (fac f i (g i) : ℝ) := by exact_mod_cast (hmono i hi (g i) hgi).2
    have hσs := neg_of_signed hc (monoSign_eq hs0) (monoSign_mul_nonneg hs0 hden hz) he
      (hgneg i hi)
    have hwi : (0 : ℝ) < ((ob.part i).2 : ℝ) := by exact_mod_cast hw _ (part_mem hi)
    simp only [sgnF, sgn] at hσs ⊢
    push_cast
    have : ((ob.part i).2 : ℝ) * ((monoSign n b ((ob.exps.getD i []).getD (g i) []) : ℝ) *
        (fac f i (g i) : ℝ)) * s (i * ob.K + g i) = ((ob.part i).2 : ℝ) * (fac f i (g i) : ℝ) *
        ((monoSign n b ((ob.exps.getD i []).getD (g i) []) : ℝ) * s (i * ob.K + g i)) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg (mul_pos hwi hf0) hσs
  have hτne : τ ≠ [] := by
    simp only [hτ, specs, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
    exact fun h0 ↦ hne (List.length_eq_zero_iff.mp h0)
  have hsum := sum_neg_of_mul_neg τ hτne hall
  simp only [Sign, Bool.false_eq_true, ↓reduceIte] at hsign
  linarith

end Obst

/-! ### Obstruction and combination leaves (L1, L2) -/

/-- A part of an obstruction leaf of a chart tree: a support witness with its positive weight,
the chosen anchors of its supports (per support, per point), the exponents of the monomials
dividing its premise forms (in the order of `Wit.forms`) and those of its anchor choices. -/
structure TPart (κ : Type) where
  /-- The witness. -/
  wit : Wit κ
  /-- The weight. -/
  weight : ℕ
  /-- The chosen anchors, per support and point. -/
  dom : List (List ℕ)
  /-- The exponents of the monomials dividing the premise forms. -/
  pexps : List (List ℕ)
  /-- The exponents of the monomials dividing the anchor choices. -/
  exps : List (List ℕ)

/-- An obstruction leaf (one part) or a combination leaf (several parts) of a chart tree, with
the bisection depth of its sign checks. -/
structure TObst (κ : Type) where
  /-- The parts. -/
  parts : List (TPart κ)
  /-- The bisection depth. -/
  depth : ℕ

namespace TObst

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]
variable (pts : List (V3 κ)) (n : ℕ) (Ψ : GenMap κ) (b : Box) (t : TObst κ) (pre : Option (Q4 κ))

/-- The leaf as an `Obst` (its premise flag unused). -/
def obst : Obst κ :=
  ⟨t.parts.map fun p ↦ (p.wit, p.weight), t.parts.map (·.exps), false, t.depth⟩

/-- The premise forms of all parts, with their exponents. -/
def forms : List (V3 κ × List ℕ) :=
  t.parts.flatMap fun p ↦ (p.wit.forms pts p.dom).mapIdx fun i g ↦ (g, p.pexps.getD i [])

/-- The exceptional vectors of all parts. -/
def excs : List (V3 κ) :=
  t.parts.flatMap fun p ↦ (p.wit.excs pts).getD []

/-- **The check of an obstruction or combination leaf** of a chart tree on the family with map
`Ψ` and box `b` of `n` slots, with the pre-rotation `pre`, the bisection order `o` and the factors
`f` of the anchor choices' weights (`Obst.polyOkS`). -/
def check (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  !t.parts.isEmpty &&
    t.parts.all (fun p ↦
      decide (0 < p.weight) && p.wit.domOk pts p.dom && (p.wit.excs pts).isSome) &&
    formsOk n Ψ b t.depth (t.forms pts) o && t.obst.polyOkS pts n Ψ b pre o f

/-- `check` as compiled code runs it (`check_eq_checkP`): with a stage line after the premise
forms (`Modules/Check/Leaf/Progress.lean`). -/
def checkP (o : List (ℕ × ℕ) := []) (f : List (List ℤ) := []) : Bool :=
  !t.parts.isEmpty &&
    t.parts.all (fun p ↦
      decide (0 < p.weight) && p.wit.domOk pts p.dom && (p.wit.excs pts).isSome) &&
    stage "forms" (fun r ↦ s!" forms={(t.forms pts).length} ok={r}")
      (formsOk n Ψ b t.depth (t.forms pts) o) && t.obst.polyOkS pts n Ψ b pre o f

@[csimp] theorem check_eq_checkP : @check = @checkP := by
  funext κ _ _ _ _ pts n Ψ b t pre o f
  simp only [check, checkP, stage_eq]

variable {pts n Ψ b t pre}

theorem mem_forms {p : TPart κ} (hp : p ∈ t.parts) {g : V3 κ}
    (hg : g ∈ p.wit.forms pts p.dom) :
    ∃ e, (g, e) ∈ t.forms pts := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  refine ⟨p.pexps.getD i [], List.mem_flatMap.mpr ⟨p, hp, ?_⟩⟩
  exact List.mem_mapIdx.mpr ⟨i, hi, rfl⟩

theorem obst_part {i : ℕ} (hi : i < t.parts.length) :
    t.obst.part i = ((t.parts[i]).wit, (t.parts[i]).weight) := by
  simp only [Obst.part, obst]
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

/-- **Soundness of tree obstruction leaves.** At a point of the box whose view output is not
orthogonal to the exceptional vectors, the outputs have no fit with the pre-rotation. -/
theorem check_sound {o : List (ℕ × ℕ)} {f : List (List ℤ)} (h : t.check pts n Ψ b pre o f = true)
    (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0)
    {z : Fin n → ℝ} (hz : b.Mem n z)
    (hexc : ∀ g ∈ t.excs pts, Exact.reV g ⬝ᵥ outU (Ψ.run Exact.re (ext n z)) ≠ 0)
    (hq : outQ (Ψ.run Exact.re (ext n z)) ≠ 0) :
    NoFitRep pts (Exact.rePre pre) (Ψ.run Exact.re (ext n z)) := by
  simp only [check, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    List.isEmpty_eq_false_iff, List.all_eq_true, decide_eq_true_eq, Option.isSome_iff_exists]
    at h
  obtain ⟨⟨⟨hne, hparts⟩, hforms⟩, hpoly⟩ := h
  have hf := formsOk_sound hforms hz
  intro hfit
  refine Obst.polyOkS_sound hpoly hz (by simpa [obst] using hne) (fun q hq' ↦ ?_) fun i hi ↦ ?_
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq'
    exact (hparts p hp).1.1
  · have hi' : i < t.parts.length := by simpa [obst] using hi
    rw [obst_part hi']
    set p := t.parts[i] with hpdef
    have hp : p ∈ t.parts := List.getElem_mem hi'
    obtain ⟨⟨-, hd⟩, gs, hgs⟩ := hparts p hp
    have hprem := Wit.premises_of_weak hd hgs (fun g hg ↦ by
      obtain ⟨e, he⟩ := mem_forms hp hg
      exact hf _ he) fun g hg ↦ hexc g (List.mem_flatMap.mpr ⟨p, hp, by rw [hgs]; exact hg⟩)
    obtain ⟨tt, ht, hlt⟩ := Wit.exists_neg hq hpre hprem hfit
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
    exact ⟨j, hj, by rwa [List.getD_eq_getElem _ _ hj]⟩

end TObst

/-! ### Outside leaves (L3) -/

theorem le_div_of_nonneg {N D hn hd : ℝ} (hd0 : 0 < hd) (hD : D ≠ 0)
    (h : 0 ≤ (hd * N - hn * D) * D) : hn / hd ≤ N / D := by
  have key : N / D - hn / hd = (hd * N - hn * D) * D / (hd * (D * D)) := by
    field_simp
  have : 0 ≤ N / D - hn / hd := by
    rw [key]
    exact div_nonneg h (mul_pos hd0 (mul_self_pos.mpr hD)).le
  linarith

theorem div_le_of_nonneg {N D hn hd : ℝ} (hd0 : 0 < hd) (hD : D ≠ 0)
    (h : 0 ≤ (hn * D - hd * N) * D) : N / D ≤ hn / hd := by
  have key : hn / hd - N / D = (hn * D - hd * N) * D / (hd * (D * D)) := by
    field_simp
  have : 0 ≤ hn / hd - N / D := by
    rw [key]
    exact div_nonneg h (mul_pos hd0 (mul_self_pos.mpr hD)).le
  linarith

/-- The denominator of a chart coordinate does not vanish at outputs that represent a chart
pose. -/
theorem den_ne_of_represents {p : ChartPose} {o : ℕ → ℝ} (h : Represents p o) (c : Fin 5) :
    o (coordIdx p.view p.rot c).2 ≠ 0 := by
  obtain ⟨a, b, ha, hb, hu, hq⟩ := h
  have hU (i : Fin 3) : o i = a * viewDir p.view p.s p.t i := congrFun hu i
  have hQ (i : Fin 4) : o (i + 3) = b * chartQuat p.rot p.x i := congrFun hq i
  fin_cases c <;> simp only [coordIdx, hU, hQ, chartQuat_self, viewDir, sub_self] <;>
    simp [ha, hb]

/-- An outside leaf of a chart tree (L3): chart coordinate `coord` is not strictly inside the
claim box beyond its upper end (`upper`) or its lower end, certified weakly with the exponents
`e` of the dividing monomial and the bisection depth. -/
structure TOut where
  /-- The chart coordinate. -/
  coord : Fin 5
  /-- The upper end, or the lower end. -/
  upper : Bool
  /-- The exponents of the dividing monomial. -/
  e : List ℕ
  /-- The bisection depth. -/
  depth : ℕ

namespace TOut

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- The numerator of the bound of the claim box `B`. -/
def bound (B : ChartBox) (x : TOut) : ℤ :=
  bif x.upper then B.box.hi.getD x.coord 0 else B.box.lo.getD x.coord 0

/-- **The check of an outside leaf** on the family with map `Ψ` and box `b` of `n` slots, for
the claim box `B`: `(d N - h D) D ≥ 0` (or `(h D - d N) D ≥ 0`) for the numerator `N` and the
denominator `D` of the coordinate and the bound `h / d`, in the bisection order `o`. -/
def check (B : ChartBox) (n : ℕ) (Ψ : GenMap κ) (b : Box) (x : TOut) (o : List (ℕ × ℕ) := []) :
    Bool :=
  decide (0 < B.box.den) && monoSign n b x.e != 0 &&
    Pull.check n
      [⟨(outsideP B.view B.rot x.coord x.upper (x.bound B) B.box.den).comp Ψ, x.e⟩]
      false x.depth b [[(0, monoSign n b x.e)]] o

/-- **Soundness of outside leaves from their sign check** (`check_sound`, the sparse
`checkX_sound` of `Modules/Check/Sign/SparsePull.lean`). If the outside numerator is `c z^e s` at `z`
with `c > 0` and `σ s ≥ 0` for the sign `σ ≠ 0` of `z^e` on the box, then where the outputs
represent a pose `p` in the charts of `B`, its coordinate is at or beyond the bound. -/
theorem sound_of {B : ChartBox} {n : ℕ} {Ψ : GenMap κ} {b : Box} {x : TOut}
    (hden : 0 < B.box.den) (hs0 : monoSign n b x.e ≠ 0) (hbden : 0 < b.den) {z : Fin n → ℝ}
    (hz : b.Mem n z)
    (hP : ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ,
      ((outsideP B.view B.rot x.coord x.upper (x.bound B) B.box.den).comp Ψ).run Exact.re
        (ext n z) = c * DPoly.monoVal n x.e z * s ∧ 0 ≤ (monoSign n b x.e : ℝ) * s)
    {p : ChartPose} (hv : p.view = B.view) (hr : p.rot = B.rot)
    (hrep : Represents p (Ψ.run Exact.re (ext n z))) :
    bif x.upper then (B.box.hi.getD x.coord 0 : ℝ) / B.box.den ≤ p.coords x.coord
      else p.coords x.coord ≤ (B.box.lo.getD x.coord 0 : ℝ) / B.box.den := by
  obtain ⟨c, hc0, s, he, hsign⟩ := hP
  simp only [PosePoly.comp_run] at he
  have hnn := nonneg_of_signed hc0 (monoSign_eq hs0) (monoSign_mul_nonneg hs0 hbden hz) he hsign
  have hco := coordOf_of_represents hrep x.coord
  have hD := den_ne_of_represents hrep x.coord
  rw [hv, hr] at hco hD
  have hd : (0 : ℝ) < B.box.den := by exact_mod_cast hden
  obtain ⟨h1, h2⟩ := coordIdx_lt B.view B.rot x.coord
  simp only [PosePoly.eval, outsideP, outOf_of h1, outOf_of h2, Exact.re_ofInt] at hnn
  simp only [coordOf] at hco
  cases hup : x.upper <;> simp only [hup, Bool.cond_true, Bool.cond_false, bound] at hnn ⊢ <;>
    push_cast at hnn
  · rw [← hco]
    exact div_le_of_nonneg hd hD hnn
  · rw [← hco]
    exact le_div_of_nonneg hd hD hnn

/-- **Soundness of outside leaves.** Where the outputs represent a pose `p` in the charts of `B`,
its coordinate is at or beyond the bound. -/
theorem check_sound {B : ChartBox} {n : ℕ} {Ψ : GenMap κ} {b : Box} {x : TOut}
    {o : List (ℕ × ℕ)} (h : x.check B n Ψ b o = true) {z : Fin n → ℝ} (hz : b.Mem n z)
    {p : ChartPose} (hv : p.view = B.view) (hr : p.rot = B.rot)
    (hrep : Represents p (Ψ.run Exact.re (ext n z))) :
    bif x.upper then (B.box.hi.getD x.coord 0 : ℝ) / B.box.den ≤ p.coords x.coord
      else p.coords x.coord ≤ (B.box.lo.getD x.coord 0 : ℝ) / B.box.den := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hden, hs0⟩, hc⟩ := h
  exact sound_of hden hs0 (Pull.den_pos_of_check hc) hz (single_of_pull (Pull.check_sound hc) hz)
    hv hr hrep

end TOut

/-! ### Exclusion leaves -/

/-- The improvement numerator of an exclusion leaf: times `|U|²` for a fold, as rupert's
(`improvement_numerator_at` in `code/src/proof/symmetry.rs`), so that the two are positive
multiples of each other and their sign checks agree. -/
def improvementT {κ : Type} (d : Improvement κ) : PosePoly κ where
  run k U Q := bif d.fold then U.dot U * improvementG k d U Q else improvementG k d U Q
  natural f hf k U Q := by
    cases d.fold
    · exact map_improvementG hf k d U Q
    · simp only [Bool.cond_true, hf.map_mul, V3.map_dot hf, map_improvementG hf]

theorem improvementT_eval {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ] (d : Improvement κ)
    (pre : Option (Q4 κ)) (o : ℕ → ℝ) :
    ((improvementT d).pre pre).eval o = (bif d.fold then outU o ⬝ᵥ outU o else 1) *
      improvementPoly d (outU o) (preQuat (outQ o) (Exact.rePre pre)) := by
  cases hf : d.fold <;>
    simp only [PosePoly.eval, PosePoly.pre, improvementT, hf, Bool.cond_false, Bool.cond_true,
      improvementG_re, V3.dot_eq_dotProduct, toFun_viewOf, toFun_preQ, toFun_quatOf, one_mul]

/-- An exclusion leaf (L4): the symmetries `i` and `j` of the symmetry data, the exponents `e` of
the monomial dividing the improvement numerator of their pose map, the bisection depth, and an
integer point `(wu, wq)` where the numerator is not zero. -/
structure TExcl where
  /-- The first symmetry (acting on the view and from the left). -/
  i : ℕ
  /-- The second symmetry (acting on the inner copy). -/
  j : ℕ
  /-- The exponents of the monomial. -/
  e : List ℕ
  /-- The bisection depth of the sign check. -/
  depth : ℕ
  /-- The view vector of the witness point. -/
  wu : V3 ℤ
  /-- The quaternion of the witness point. -/
  wq : Q4 ℤ

namespace TExcl

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **The check of an exclusion leaf** on the family with map `Ψ` and box `b` of `n` slots, with
the quaternion followed by the pre-rotation `pre`, if any: the improvement numerator is nonnegative
on the box (bound contract, in the bisection order `o`) and not zero at the witness point. -/
def check (D : SymmData κ) (n : ℕ) (Ψ : GenMap κ) (b : Box) (pre : Option (Q4 κ)) (x : TExcl)
    (o : List (ℕ × ℕ) := []) : Bool :=
  match D.syms[x.i]?, D.syms[x.j]? with
  | some S₁, some S₂ => monoSign n b x.e != 0 &&
      Exact.nonzero (improvementG id (Improvement.of D.score S₁ S₂) (x.wu.map Exact.ofInt)
        (x.wq.map Exact.ofInt)) &&
      Pull.check n [⟨((improvementT (Improvement.of D.score S₁ S₂)).pre pre).comp Ψ, x.e⟩] false
        x.depth b [[(0, monoSign n b x.e)]] o
  | _, _ => false

/-- **Soundness of exclusion leaves from their sign check** (`check_sound`, the sparse
`checkX_sound` of `Modules/Check/Sign/SparsePull.lean`), for the symmetries `S₁`, `S₂` at `i`, `j`.
If the improvement numerator is `c z^e s` at `z` with `c > 0` and `σ s ≥ 0` for the sign `σ ≠ 0`
of `z^e` on the box, and not zero at the witness point, then at a chart pose represented there,
with its rotation followed by the pre-rotation, the pose map of the symmetries increases the
score, or the pose is null. -/
theorem sound_of {pts : List (V3 κ)} {D : SymmData κ} {n : ℕ} {Ψ : GenMap κ}
    {b : Box} {pre : Option (Q4 κ)} {x : TExcl} {S₁ S₂ : Symm κ} (hD : D.ok pts = true)
    (hS₁ : D.syms[x.i]? = some S₁) (hS₂ : D.syms[x.j]? = some S₂) (hsg : monoSign n b x.e ≠ 0)
    (hw : Exact.nonzero (improvementG id (Improvement.of D.score S₁ S₂) (x.wu.map Exact.ofInt)
        (x.wq.map Exact.ofInt)) = true) (hden : 0 < b.den)
    (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) {z : Fin n → ℝ} (hz : b.Mem n z)
    (hP : ∃ c : ℝ, 0 < c ∧ ∃ s : ℝ,
      (((improvementT (Improvement.of D.score S₁ S₂)).pre pre).comp Ψ).run Exact.re (ext n z) =
        c * DPoly.monoVal n x.e z * s ∧ 0 ≤ (monoSign n b x.e : ℝ) * s)
    {p : ChartPose} (hp : Represents p (Ψ.run Exact.re (ext n z))) :
    (Polyhedron.ofPoints pts).ExcludedAt D.centre D.score.f (viewDir p.view p.s p.t)
        (p.rotation * preRot (Exact.rePre pre)) ∨
      (viewDir p.view p.s p.t, p.rotation * preRot (Exact.rePre pre)) ∈ null κ D.score := by
  have hD' := hD
  simp only [SymmData.ok, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hD'
  obtain ⟨c, hc0, s, he, hsign⟩ := hP
  simp only [PosePoly.comp_run, improvementT_eval] at he
  have hnn := nonneg_of_signed hc0 (monoSign_eq hsg) (monoSign_mul_nonneg hsg hden hz) he hsign
  obtain ⟨a, a', ha, ha', hu, hq⟩ := hp
  have hu0 : outU (Ψ.run Exact.re (ext n z)) ≠ 0 := by
    rw [hu]
    exact smul_ne_zero ha (viewDir_ne_zero _ _ _)
  have hpos : 0 < bif (Improvement.of D.score S₁ S₂).fold then
      outU (Ψ.run Exact.re (ext n z)) ⬝ᵥ outU (Ψ.run Exact.re (ext n z)) else 1 := by
    cases (Improvement.of D.score S₁ S₂).fold
    · exact one_pos
    · rw [Bool.cond_true]
      exact lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
        (Ne.symm (dotProduct_self_eq_zero.not.mpr hu0))
  replace hnn := (mul_nonneg_iff_of_pos_left hpos).mp hnn
  rw [hu, hq, preQuat_smul, improvementPoly_smul₂] at hnn
  have hS₁ := List.mem_of_getElem? hS₁
  have hS₂ := List.mem_of_getElem? hS₂
  rcases excluded_or_tie hD hS₁ hS₂ (viewDir_ne_zero _ _ _)
      (preQuat_ne_zero (chartQuat_ne_zero p.rot p.x) hpre)
      ((mul_nonneg_iff_of_pos_left (by positivity)).mp hnn) with hex | htie
  · rw [quatRotation_preQuat] at hex
    exact Or.inl hex
  · rw [quatRotation_preQuat] at htie
    exact Or.inr (mem_null_of_tie
      (isNowhereDense_tieSet (hD'.1 S₁ hS₁) (hD'.1 S₂ hS₂) hD'.2 hw) htie)

/-- **Soundness of exclusion leaves.** At a chart pose represented in the box, with its rotation
followed by the pre-rotation, the pose map of the symmetries increases the score, or the pose is
null. -/
theorem check_sound {pts : List (V3 κ)} {D : SymmData κ} {n : ℕ} {Ψ : GenMap κ}
    {b : Box} {pre : Option (Q4 κ)} {x : TExcl} {o : List (ℕ × ℕ)} (hD : D.ok pts = true)
    (h : x.check D n Ψ b pre o = true) (hpre : ∀ c ∈ Exact.rePre pre, c ≠ 0) {z : Fin n → ℝ}
    (hz : b.Mem n z) {p : ChartPose} (hp : Represents p (Ψ.run Exact.re (ext n z))) :
    (Polyhedron.ofPoints pts).ExcludedAt D.centre D.score.f (viewDir p.view p.s p.t)
        (p.rotation * preRot (Exact.rePre pre)) ∨
      (viewDir p.view p.s p.t, p.rotation * preRot (Exact.rePre pre)) ∈ null κ D.score := by
  unfold check at h
  split at h
  next S₁ S₂ hS₁ hS₂ =>
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hsg, hw⟩, hc⟩ := h
    exact sound_of hD hS₁ hS₂ hsg hw (Pull.den_pos_of_check hc) hpre hz
      (single_of_pull (Pull.check_sound hc) hz) hp
  next => exact absurd h (by simp)

end TExcl

end Nieuwland.Check
