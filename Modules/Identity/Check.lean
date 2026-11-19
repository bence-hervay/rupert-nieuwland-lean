import Modules.Identity.Faces
import Modules.Check.Number.Exact
import Modules.Rupert.Scale

/-!
# Facet certificates checked by the kernel

The data of a facet certificate (`Modules/Identity/Faces.lean`) over exact values (`Check.Exact`:
`ℤ`, `ZSqrt d`, `ZTheta R`) for points `pts` (a body's points times a common denominator):

* faces `FaceE κ`: a cycle of indices, a normal `n` and an offset `h` over `κ`, a regularity
  flag; one `faceOk` per face checks the plane (zero on the face's points, positive `h - n ⬝ᵥ x`
  on the others), the convex position, regularity and a common edge length;
* combinatorial hints, checked by `combOk` on the cycles alone: three faces per point that meet
  only there (`vtx`), and per face the index of the face across each edge (`ptn`).

`hasFaces_of_check` turns the checks into `Polyhedron.HasFaces` for the polyhedron of the points
scaled by any `c > 0` (generated modules take `c` as one over the common denominator, so that the
polyhedron is the fixture's). Everything is decided by the kernel (`decide +kernel`); faces are
checked one declaration each.
-/

open Matrix

namespace Nieuwland.Identity

open Check Check.Exact

/-! ### Boolean helpers -/

/-- No entry repeats. -/
def nodupB {α : Type} [BEq α] : List α → Bool
  | [] => true
  | a :: l => !l.contains a && nodupB l

theorem nodupB_iff {α : Type} [BEq α] [LawfulBEq α] : ∀ l : List α, nodupB l = true ↔ l.Nodup
  | [] => by simp [nodupB]
  | a :: l => by simp [nodupB, nodupB_iff l, List.nodup_cons]

/-- `p (i + k) lₖ` for every entry `lₖ`. -/
def allIdx {α : Type} (p : ℕ → α → Bool) : ℕ → List α → Bool
  | _, [] => true
  | i, a :: l => p i a && allIdx p (i + 1) l

theorem allIdx_sound {α : Type} {p : ℕ → α → Bool} :
    ∀ {i : ℕ} {l : List α}, allIdx p i l = true → ∀ k (hk : k < l.length), p (i + k) l[k] = true
  | _, [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | i, a :: l, h, k, hk => by
    simp only [allIdx, Bool.and_eq_true] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := allIdx_sound h.2 k (by simpa using hk)
      rwa [show i + 1 + k = i + (k + 1) by omega] at this

/-- `p a b` for every pair of entries `a` before `b`. -/
def allPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => true
  | a :: l => l.all (p a) && allPairs p l

theorem allPairs_sound {α : Type} {p : α → α → Bool} :
    ∀ {l : List α}, allPairs p l = true → l.Pairwise fun a b ↦ p a b = true
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    simp only [allPairs, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (allPairs_sound h.2)

theorem contains_false {α : Type} [BEq α] [LawfulBEq α] {l : List α} {a : α} :
    l.contains a = false ↔ a ∉ l := by
  rw [Bool.eq_false_iff, Ne, List.contains_iff_mem]

/-! ### Faces over exact values -/

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- A face over exact values: a cycle of indices, a normal, an offset and a regularity flag. -/
structure FaceE (κ : Type) where
  /-- The indices of the face's points, in cyclic order. -/
  cyc : List ℕ
  /-- The outward normal. -/
  n : V3 κ
  /-- The offset. -/
  h : κ
  /-- The face is claimed regular. -/
  reg : Bool

/-- The origin. -/
def zero3 : V3 κ :=
  ⟨ofInt 0, ofInt 0, ofInt 0⟩

/-- The point with index `i` (the origin past the end). -/
def ptE (pts : List (V3 κ)) (i : ℕ) : V3 κ :=
  pts.getD i zero3

/-- The squared length. -/
def norm2 (v : V3 κ) : κ :=
  v.dot v

/-- The point `v` with index `j` against the plane of `F`: on it if `j` is a vertex of `F`,
strictly below otherwise. -/
def planeOk (F : FaceE κ) (j : ℕ) (v : V3 κ) : Bool :=
  if F.cyc.contains j then isZero (F.n.dot v - F.h) else pos (F.h - F.n.dot v)

/-- Every point of the face other than the ends of an edge lies strictly to its left. -/
def leftOk (pts : List (V3 κ)) (F : FaceE κ) : Bool :=
  (cycEdges F.cyc).all fun e ↦ F.cyc.all fun j ↦ j == e.1 || j == e.2 ||
    pos ((((ptE pts e.2).sub (ptE pts e.1)).cross ((ptE pts j).sub (ptE pts e.1))).dot F.n)

/-- At each corner `(a, b, c)`: `|b - a|² = |c - b|² = s` and `|c - a|² = d`, for the values `s`
and `d` at the first corner. -/
def regOk (pts : List (V3 κ)) (c : List ℕ) : Bool :=
  match cycCorners c with
  | [] => true
  | τ₀ :: _ =>
    let s := norm2 ((ptE pts τ₀.2.1).sub (ptE pts τ₀.1))
    let d := norm2 ((ptE pts τ₀.2.2).sub (ptE pts τ₀.1))
    (cycCorners c).all fun τ ↦ isZero (norm2 ((ptE pts τ.2.1).sub (ptE pts τ.1)) - s) &&
      isZero (norm2 ((ptE pts τ.2.2).sub (ptE pts τ.2.1)) - s) &&
      isZero (norm2 ((ptE pts τ.2.2).sub (ptE pts τ.1)) - d)

/-- Every edge has squared length `s`, if `s` is given. -/
def lenOk (pts : List (V3 κ)) (c : List ℕ) : Option κ → Bool
  | none => true
  | some s => (cycEdges c).all fun e ↦ isZero (norm2 ((ptE pts e.2).sub (ptE pts e.1)) - s)

/-- **The check of one face.** -/
def faceOk (pts : List (V3 κ)) (s : Option κ) (F : FaceE κ) : Bool :=
  decide (3 ≤ F.cyc.length) && nodupB F.cyc && F.cyc.all (· < pts.length) &&
    allIdx (planeOk F) 0 pts && leftOk pts F && (!F.reg || regOk pts F.cyc) && lenOk pts F.cyc s

/-! ### The combinatorial check -/

/-- Three faces `t` through the point `i` that meet only there. -/
def vtxOk (cycs : List (List ℕ)) (i : ℕ) (t : ℕ × ℕ × ℕ) : Bool :=
  let c := cycs.getD t.1 []
  let d := cycs.getD t.2.1 []
  let e := cycs.getD t.2.2 []
  decide (t.1 < cycs.length) && decide (t.2.1 < cycs.length) && decide (t.2.2 < cycs.length) &&
    c.contains i && d.contains i && e.contains i &&
    c.all fun j ↦ j == i || !(d.contains j && e.contains j)

/-- `vtxOk` for the points `i, i + 1, …` with the hints `ts`. -/
def vtxAll (cycs : List (List ℕ)) : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | i, t :: ts => vtxOk cycs i t && vtxAll cycs (i + 1) ts

/-- The faces `c` and `d` have only the ends of `e` in common. -/
def meetOk (c d : List ℕ) (e : ℕ × ℕ) : Bool :=
  c.all fun j ↦ j == e.1 || j == e.2 || !d.contains j

/-- Each edge `e` of the face `c` is reversed in the face with the hinted index, which meets `c`
only in the ends of `e`. -/
def closedOk (cycs : List (List ℕ)) (c : List ℕ) : List (ℕ × ℕ) → List ℕ → Bool
  | [], _ => true
  | _ :: _, [] => false
  | e :: es, g :: gs =>
    decide (g < cycs.length) && (cycEdges (cycs.getD g [])).contains e.swap &&
      meetOk c (cycs.getD g []) e && closedOk cycs c es gs

/-- `closedOk` for every face, with one list of hints per face. -/
def closedAll (cycs : List (List ℕ)) : List (List ℕ) → List (List ℕ) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | c :: cs, ps :: pss => closedOk cycs c (cycEdges c) ps && closedAll cycs cs pss

/-- **The combinatorial check** of the cycles `cycs` on `np` points, with the hints `vtx` (three
faces per point) and `ptn` (the face across each edge). -/
def combOk (cycs : List (List ℕ)) (np : ℕ) (vtx : List (ℕ × ℕ × ℕ)) (ptn : List (List ℕ)) :
    Bool :=
  (vtx.length == np) && vtxAll cycs 0 vtx && closedAll cycs cycs ptn &&
    allPairs (fun c d ↦ c.any fun i ↦ !d.contains i) cycs && nodupB (cycs.flatMap cycEdges)

/-- The kinds of faces (`KindsOk`). -/
def kindsOk (faces : List (FaceE κ)) (kinds : List (ℕ × Bool × ℕ)) : Bool :=
  nodupB (kinds.map fun k ↦ (k.1, k.2.1)) && faces.length == (kinds.map fun k ↦ k.2.2).sum &&
    kinds.all fun k ↦
      (faces.filter fun F ↦ F.cyc.length == k.1 && F.reg == k.2.1).length == k.2.2

/-! ### Soundness of the combinatorial check -/

theorem mem_of_getD {cycs : List (List ℕ)} {g : ℕ} (h : g < cycs.length) :
    cycs.getD g [] ∈ cycs := by
  simp [List.getElem?_eq_getElem h]

theorem vtxAll_sound {cycs : List (List ℕ)} :
    ∀ {i : ℕ} {ts : List (ℕ × ℕ × ℕ)}, vtxAll cycs i ts = true → ∀ j, i ≤ j → j < i + ts.length →
      ∃ c ∈ cycs, ∃ d ∈ cycs, ∃ e ∈ cycs, j ∈ c ∧ j ∈ d ∧ j ∈ e ∧
        ∀ k ∈ c, k ∈ d → k ∈ e → k = j
  | _, [], _, j, h₁, h₂ => by simp at h₂; omega
  | i, t :: ts, h, j, h₁, h₂ => by
    simp only [vtxAll, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h₁ with rfl | h₁
    · have h := h.1
      simp only [vtxOk, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem,
        List.all_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
        Bool.and_eq_false_iff, contains_false] at h
      obtain ⟨⟨⟨⟨⟨⟨hc, hd⟩, he⟩, hic⟩, hid⟩, hie⟩, hall⟩ := h
      refine ⟨_, mem_of_getD hc, _, mem_of_getD hd, _, mem_of_getD he, hic, hid, hie,
        fun k hk hkd hke ↦ ?_⟩
      rcases hall k hk with h | h | h
      · exact h
      · exact absurd hkd h
      · exact absurd hke h
    · exact vtxAll_sound h.2 j h₁ (by simp at h₂; omega)

theorem closedOk_sound {cycs : List (List ℕ)} {c : List ℕ} :
    ∀ {es : List (ℕ × ℕ)} {gs : List ℕ}, closedOk cycs c es gs = true → ∀ e ∈ es,
      ∃ d ∈ cycs, e.swap ∈ cycEdges d ∧ ∀ j ∈ c, j ∈ d → j = e.1 ∨ j = e.2
  | [], _, _, e, he => absurd he List.not_mem_nil
  | _ :: _, [], h, _, _ => by simp [closedOk] at h
  | e :: es, g :: gs, h, e', he' => by
    simp only [closedOk, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp he' with rfl | he'
    · obtain ⟨⟨⟨hg, hsw⟩, hm⟩, -⟩ := h
      refine ⟨_, mem_of_getD hg, List.contains_iff_mem.mp hsw, fun j hj hjd ↦ ?_⟩
      simp only [meetOk, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
        Bool.not_eq_true', contains_false] at hm
      rcases hm j hj with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hjd h
    · exact closedOk_sound h.2 e' he'

theorem closedAll_sound {cycs : List (List ℕ)} :
    ∀ {cs pss : List (List ℕ)}, closedAll cycs cs pss = true → ∀ c ∈ cs, ∀ e ∈ cycEdges c,
      ∃ d ∈ cycs, e.swap ∈ cycEdges d ∧ ∀ j ∈ c, j ∈ d → j = e.1 ∨ j = e.2
  | [], _, _, c, hc => absurd hc List.not_mem_nil
  | _ :: _, [], h, _, _ => by simp [closedAll] at h
  | c :: cs, ps :: pss, h, c', hc' => by
    simp only [closedAll, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact closedOk_sound h.1
    · exact closedAll_sound h.2 c' hc'

/-- **Soundness of the combinatorial check.** -/
theorem combOk_sound {cycs : List (List ℕ)} {np : ℕ} {vtx : List (ℕ × ℕ × ℕ)}
    {ptn : List (List ℕ)} (h : combOk cycs np vtx ptn = true) : CombOk cycs np := by
  simp only [combOk, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hl, hv⟩, hc⟩, hd⟩, hn⟩ := h
  refine ⟨?_, fun i hi ↦ vtxAll_sound hv i (Nat.zero_le _) (by omega), closedAll_sound hc,
    (nodupB_iff _).mp hn⟩
  refine (allPairs_sound hd).imp fun {c d} h ↦ ?_
  simp only [List.any_eq_true, Bool.not_eq_true', contains_false] at h
  exact h

/-! ### Soundness of the face checks -/

/-- The real points: `c` times the values of `pts`. -/
noncomputable def rpts (c : ℝ) (pts : List (V3 κ)) : List (Fin 3 → ℝ) :=
  pts.map fun v ↦ c • reV v

/-- The real face: the plane scaled with the points. -/
noncomputable def rface (c : ℝ) (F : FaceE κ) : Face :=
  ⟨F.cyc, reV F.n, c * re F.h, F.reg⟩

theorem reV_zero3 : reV (zero3 : V3 κ) = 0 := by
  funext i
  fin_cases i <;> simp [reV, zero3, V3.map, V3.toFun, re_ofInt]

theorem pt_rpts (c : ℝ) (pts : List (V3 κ)) (i : ℕ) : pt (rpts c pts) i = c • reV (ptE pts i) := by
  simp only [pt, rpts, ptE, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases pts[i]? with
  | none => simp [reV_zero3]
  | some v => rfl

theorem length_rpts (c : ℝ) (pts : List (V3 κ)) : (rpts c pts).length = pts.length :=
  List.length_map _

theorem re_norm2_sub (u v : V3 κ) : re (norm2 (u.sub v)) = dist2 (reV u) (reV v) := by
  rw [norm2, re_dot, reV_sub, dist2]

theorem dist2_smul (c : ℝ) (x y : Fin 3 → ℝ) : dist2 (c • x) (c • y) = c ^ 2 * dist2 x y := by
  simp only [dist2, ← smul_sub, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem dist2_comm (x y : Fin 3 → ℝ) : dist2 x y = dist2 y x := by
  simp only [dist2, dotProduct, Pi.sub_apply, Fin.sum_univ_three]
  ring

theorem corner_dot (x y z : Fin 3 → ℝ) :
    (x - y) ⬝ᵥ (z - y) = (dist2 x y + dist2 z y - dist2 z x) / 2 := by
  simp only [dist2, dotProduct, Pi.sub_apply, Fin.sum_univ_three]
  ring

theorem cross_dot_smul (c : ℝ) (a b j n : Fin 3 → ℝ) :
    ((c • b - c • a) ⨯₃ (c • j - c • a)) ⬝ᵥ n = c ^ 2 * (((b - a) ⨯₃ (j - a)) ⬝ᵥ n) := by
  simp only [cross_apply, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three]
  simp
  ring

theorem zero_of_isZero_sub {a b : κ} (h : isZero (a - b) = true) : re a = re b := by
  have := isZero_sound _ h
  rw [re_sub] at this
  linarith

theorem lt_of_pos_sub {a b : κ} (h : pos (a - b) = true) : re b < re a := by
  have := pos_sound _ h
  rw [re_sub] at this
  linarith

variable {pts : List (V3 κ)} {s : Option κ} {F : FaceE κ} {c : ℝ}

/-- **Soundness of the face check**: a facet of the points scaled by `c > 0`. -/
theorem faceOk_facet (hc : 0 < c) (h : faceOk pts s F = true) :
    (rface c F).IsFacet (rpts c pts) := by
  simp only [faceOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h3, hnd⟩, hlt⟩, hpl⟩, hleft⟩, -⟩, -⟩ := h
  have hpl' : ∀ i < pts.length, planeOk F i (ptE pts i) = true := by
    intro i hi
    have := allIdx_sound hpl i hi
    rwa [Nat.zero_add, ← List.getD_eq_getElem (d := zero3)] at this
  have hval : ∀ i, (rface c F).n ⬝ᵥ pt (rpts c pts) i = c * re (F.n.dot (ptE pts i)) := by
    intro i
    rw [pt_rpts, re_dot, dotProduct_smul, smul_eq_mul]
    rfl
  refine ⟨h3, (nodupB_iff _).mp hnd, fun i hi ↦ ?_, fun i hi ↦ ?_, fun i hi ↦ ?_, ?_⟩
  · rw [length_rpts]
    simpa using (List.all_eq_true.mp hlt) i hi
  · rw [length_rpts] at hi
    have := hpl' i hi
    rw [hval]
    simp only [rface]
    unfold planeOk at this
    split at this
    · exact (mul_le_mul_iff_of_pos_left hc).mpr (zero_of_isZero_sub this).le
    · exact (mul_le_mul_iff_of_pos_left hc).mpr (lt_of_pos_sub this).le
  · rw [length_rpts] at hi
    have := hpl' i hi
    rw [hval]
    simp only [rface]
    unfold planeOk at this
    split at this
    next hm =>
      simp only [List.contains_iff_mem] at hm
      simp [zero_of_isZero_sub this, hm]
    next hm =>
      simp only [List.contains_iff_mem] at hm
      simp only [hm, iff_false]
      exact ((mul_lt_mul_iff_of_pos_left hc).mpr (lt_of_pos_sub this)).ne
  · intro e he j hj h₁ h₂
    have := (List.all_eq_true.mp ((List.all_eq_true.mp hleft) e he)) j hj
    simp only [Bool.or_eq_true, beq_iff_eq, h₁, h₂, false_or] at this
    have hp := pos_sound _ this
    simp only [rface, pt_rpts, cross_dot_smul]
    rw [re_dot, reV_cross, reV_sub, reV_sub] at hp
    positivity

/-- **Soundness of the regularity check.** -/
theorem regOk_regular (h : regOk pts F.cyc = true) : (rface c F).IsRegular (rpts c pts) := by
  unfold regOk at h
  split at h
  next => exact ⟨0, 0, fun τ hτ ↦ by simp_all [rface]⟩
  next τ₀ l hτ₀ =>
    refine ⟨c ^ 2 * re (norm2 ((ptE pts τ₀.2.1).sub (ptE pts τ₀.1))),
      (2 * (c ^ 2 * re (norm2 ((ptE pts τ₀.2.1).sub (ptE pts τ₀.1)))) -
        c ^ 2 * re (norm2 ((ptE pts τ₀.2.2).sub (ptE pts τ₀.1)))) / 2, fun τ hτ ↦ ?_⟩
    simp only [rface] at hτ
    have := (List.all_eq_true.mp h) τ hτ
    simp only [Bool.and_eq_true] at this
    obtain ⟨⟨h₁, h₂⟩, h₃⟩ := this
    have e₁ := zero_of_isZero_sub h₁
    have e₂ := zero_of_isZero_sub h₂
    have e₃ := zero_of_isZero_sub h₃
    rw [re_norm2_sub, re_norm2_sub] at e₁ e₂ e₃
    simp only [pt_rpts, re_norm2_sub]
    refine ⟨?_, ?_⟩
    · rw [dist2_smul, dist2_comm, e₁]
    · rw [corner_dot, dist2_smul, dist2_smul, dist2_smul,
        dist2_comm (reV (ptE pts τ.1)) (reV (ptE pts τ.2.1)), e₁, e₂, e₃]
      ring

/-- **Soundness of the edge-length check.** -/
theorem lenOk_edges {x : κ} (h : lenOk pts F.cyc (some x) = true) :
    ∀ e ∈ cycEdges (rface c F).cyc,
      dist2 (pt (rpts c pts) e.1) (pt (rpts c pts) e.2) = c ^ 2 * re x := by
  intro e he
  have := zero_of_isZero_sub ((List.all_eq_true.mp h) e he)
  rw [re_norm2_sub] at this
  simp only [pt_rpts, dist2_smul, dist2_comm (reV (ptE pts e.1)), this]

theorem kindsOk_sound {faces : List (FaceE κ)} {kinds : List (ℕ × Bool × ℕ)}
    (h : kindsOk faces kinds = true) : KindsOk (faces.map (rface c)) kinds := by
  simp only [kindsOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hn, hl⟩, hk⟩ := h
  refine ⟨(nodupB_iff _).mp hn, by simpa using hl, fun k hk' ↦ ?_⟩
  rw [List.filter_map, List.length_map]
  exact hk k hk'

/-- The regularity and edge-length parts of `faceOk`. -/
theorem faceOk_parts {vpts : List (V3 κ)} {G : FaceE κ} (h : faceOk vpts s G = true) :
    (G.reg = true → regOk vpts G.cyc = true) ∧ lenOk vpts G.cyc s = true := by
  simp only [faceOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨-, hr⟩, hl⟩ := h
  refine ⟨fun hg ↦ ?_, hl⟩
  rcases hr with hr | hr
  · rw [hg] at hr
    cases hr
  · exact hr

/-- **The face checks are sound**: faces passing `faceOk`, with hints passing `combOk`, form a
facet certificate of the points `c • vpts` (`c > 0`). -/
theorem isFaceCert_of_check {vpts : List (V3 κ)} {faces : List (FaceE κ)}
    {vtx : List (ℕ × ℕ × ℕ)} {ptn : List (List ℕ)} (hc : 0 < c)
    (hf : ∀ F ∈ faces, faceOk vpts s F = true)
    (hcomb : combOk (faces.map FaceE.cyc) vpts.length vtx ptn = true) :
    IsFaceCert (rpts c vpts) (faces.map (rface c)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
    exact faceOk_facet hc (hf G hG)
  · intro F hF hreg
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
    exact regOk_regular ((faceOk_parts (hf G hG)).1 hreg)
  · have : (faces.map (rface c)).map Face.cyc = faces.map FaceE.cyc := by
      simp [rface, Function.comp_def]
    rw [this, length_rpts]
    exact combOk_sound hcomb

/-- **Facet certificates checked by the kernel**, on points `vpts` of `P` (scaled by `c > 0`)
whose hull is `P`'s, give `Polyhedron.HasFaces`: `V` points, `E` edges (half the faces' sides), the
faces' `kinds`, and edges of squared length `c² s` if `s` is given. -/
theorem hasFaces_of_checkOn {P : Polyhedron} {vpts : List (V3 κ)} {faces : List (FaceE κ)}
    {vtx : List (ℕ × ℕ × ℕ)} {ptn : List (List ℕ)} {kinds : List (ℕ × Bool × ℕ)}
    {V E : ℕ} {sR : Option ℝ} (hc : 0 < c) (hsub : ∀ x ∈ rpts c vpts, x ∈ P.vertices)
    (hhull : P.hull = convexHull ℝ {x | x ∈ rpts c vpts})
    (hV : vpts.length = V) (hf : ∀ F ∈ faces, faceOk vpts s F = true)
    (hcomb : combOk (faces.map FaceE.cyc) vpts.length vtx ptn = true)
    (hk : kindsOk faces kinds = true) (hE : 2 * E = (faces.map fun F ↦ F.cyc.length).sum)
    (hs : s.map (fun x ↦ c ^ 2 * re x) = sR) : P.HasFaces V E kinds sR := by
  refine ⟨rpts c vpts, faces.map (rface c), hsub, hhull, by rw [length_rpts, hV],
    isFaceCert_of_check hc hf hcomb, ?_, kindsOk_sound hk, ?_⟩
  · simpa [rface, Function.comp_def] using hE
  · cases s with
    | none =>
      subst hs
      trivial
    | some x =>
      subst hs
      intro F hF e he
      obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hF
      exact lenOk_edges (faceOk_parts (hf G hG)).2 e he

theorem mem_vertices_iff {pts : List (V3 κ)} (x : Fin 3 → ℝ) :
    x ∈ ((Polyhedron.ofPoints pts).smul c).vertices ↔ x ∈ rpts c pts := by
  simp only [Polyhedron.mem_smul_vertices, Polyhedron.mem_ofPoints, rpts, List.mem_map]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩

/-- The hull of the exact points `pts` scaled by `c`. -/
theorem hull_smul_ofPoints {pts : List (V3 κ)} :
    ((Polyhedron.ofPoints pts).smul c).hull = convexHull ℝ {x | x ∈ rpts c pts} := by
  simp only [Polyhedron.hull]
  congr 1
  ext x
  exact mem_vertices_iff x

/-- **Facet certificates checked by the kernel**, when every point is a vertex: the polyhedron
of the points `pts` scaled by `c > 0` has the faces of the certificate (`hasFaces_of_checkOn`). -/
theorem hasFaces_of_check {P : Polyhedron} {pts : List (V3 κ)} {faces : List (FaceE κ)}
    {vtx : List (ℕ × ℕ × ℕ)} {ptn : List (List ℕ)} {kinds : List (ℕ × Bool × ℕ)}
    {V E : ℕ} {sR : Option ℝ} (hc : 0 < c) (hP : P = (Polyhedron.ofPoints pts).smul c)
    (hV : pts.length = V) (hf : ∀ F ∈ faces, faceOk pts s F = true)
    (hcomb : combOk (faces.map FaceE.cyc) pts.length vtx ptn = true)
    (hk : kindsOk faces kinds = true) (hE : 2 * E = (faces.map fun F ↦ F.cyc.length).sum)
    (hs : s.map (fun x ↦ c ^ 2 * re x) = sR) : P.HasFaces V E kinds sR := by
  subst hP
  exact hasFaces_of_checkOn hc (fun x hx ↦ (mem_vertices_iff x).mpr hx) hull_smul_ofPoints hV hf
    hcomb hk hE hs

/-! ### Points inside the hull -/

/-- The sum of points. -/
def sumV (l : List (V3 κ)) : V3 κ :=
  l.foldr V3.add zero3

theorem reV_sumV : ∀ l : List (V3 κ), reV (sumV l) = (l.map reV).sum
  | [] => reV_zero3
  | v :: l => by rw [sumV, List.foldr_cons, ← sumV, reV_add, reV_sumV l, List.map_cons,
      List.sum_cons]

/-- `p` is a convex combination of points of `vpts`: `D p = ∑ wⱼ v_{iⱼ}` with `D > 0`, every
`wⱼ ≥ 0` and `∑ wⱼ = D`. -/
def innerOk (vpts : List (V3 κ)) (p : V3 κ) (D : κ) (ws : List (ℕ × κ)) : Bool :=
  pos D && ws.all (fun w ↦ decide (w.1 < vpts.length) && nonneg w.2) &&
    isZero (sumL (ws.map Prod.snd) - D) &&
    eqV (V3.smul D p) (sumV (ws.map fun w ↦ V3.smul w.2 (ptE vpts w.1)))

/-- A convex combination of points of `S`, as a list of weights and points, lies in the hull. -/
theorem list_sum_mem_convexHull {S : Set (Fin 3 → ℝ)} (l : List (ℝ × (Fin 3 → ℝ)))
    (h₀ : ∀ x ∈ l, 0 ≤ x.1) (hS : ∀ x ∈ l, x.2 ∈ S) (h₁ : (l.map Prod.fst).sum = 1) :
    (l.map fun x ↦ x.1 • x.2).sum ∈ convexHull ℝ S := by
  refine mem_convexHull_of_exists_fintype (fun i : Fin l.length ↦ l[(i : ℕ)].1)
    (fun i : Fin l.length ↦ l[(i : ℕ)].2) (fun i ↦ h₀ _ (List.getElem_mem _))
    ?_ (fun i ↦ hS _ (List.getElem_mem _)) ?_
  · rw [← List.sum_ofFn, List.ofFn_getElem_eq_map l Prod.fst, h₁]
  · rw [← List.sum_ofFn, List.ofFn_getElem_eq_map l fun x ↦ x.1 • x.2]

theorem sum_map_div {α : Type} (l : List α) (f : α → ℝ) (d : ℝ) :
    (l.map fun x ↦ f x / d).sum = (l.map f).sum / d := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, add_div]

theorem innerOk_sound {vpts : List (V3 κ)} {p : V3 κ} {D : κ} {ws : List (ℕ × κ)} (hc : 0 < c)
    (h : innerOk vpts p D ws = true) : c • reV p ∈ convexHull ℝ {x | x ∈ rpts c vpts} := by
  simp only [innerOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hD, hw⟩, hsum⟩, heq⟩ := h
  have hD' := pos_sound _ hD
  have hsum' := zero_of_isZero_sub hsum
  rw [re_sumL, List.map_map] at hsum'
  have heq' := reV_eq_of_eqV heq
  rw [reV_smul, reV_sumV, List.map_map] at heq'
  have hmap : (reV ∘ fun w : ℕ × κ ↦ V3.smul w.2 (ptE vpts w.1)) =
      fun w ↦ re w.2 • reV (ptE vpts w.1) := by
    funext w
    exact reV_smul _ _
  rw [hmap] at heq'
  -- `c p = ∑ (wⱼ / D) (c vⱼ)`
  have key : c • reV p = ((ws.map fun w ↦ (re w.2 / re D, c • reV (ptE vpts w.1))).map
      fun x ↦ x.1 • x.2).sum := by
    have h1 : reV p = (re D)⁻¹ • (ws.map fun w ↦ re w.2 • reV (ptE vpts w.1)).sum := by
      rw [← heq', smul_smul, inv_mul_cancel₀ hD'.ne', one_smul]
    rw [h1, smul_smul, List.smul_sum, List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun w _ ↦ ?_
    simp only [Function.comp_apply, smul_smul]
    congr 1
    field_simp
  rw [key]
  refine list_sum_mem_convexHull _ (fun x hx ↦ ?_) (fun x hx ↦ ?_) ?_
  · obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hx
    exact div_nonneg (nonneg_sound _ (hw w hw').2) hD'.le
  · obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hx
    have hlt : w.1 < vpts.length := (hw w hw').1
    simp only [Set.mem_ofPred_eq, rpts, List.mem_map]
    exact ⟨ptE vpts w.1, by simp [ptE, List.getElem?_eq_getElem hlt], rfl⟩
  · rw [List.map_map]
    have : (Prod.fst ∘ fun w : ℕ × κ ↦ (re w.2 / re D, c • reV (ptE vpts w.1))) =
        fun w ↦ re w.2 / re D := rfl
    have hs' : (ws.map fun w ↦ re w.2).sum = re D := by simpa [Function.comp_def] using hsum'
    rw [this, sum_map_div, hs', div_self hD'.ne']

/-- **Facet certificates checked by the kernel**, with points inside the hull: the vertices are
the points with the indices `vidx`, and every other point is a convex combination of them
(`innerOk`, with the data `inner`: the point's index, `D` and the weights). -/
theorem hasFaces_of_check_inner {P : Polyhedron} {pts : List (V3 κ)} {vidx : List ℕ}
    {inner : List (ℕ × κ × List (ℕ × κ))} {faces : List (FaceE κ)}
    {vtx : List (ℕ × ℕ × ℕ)} {ptn : List (List ℕ)} {kinds : List (ℕ × Bool × ℕ)}
    {V E : ℕ} {sR : Option ℝ} (hc : 0 < c) (hP : P = (Polyhedron.ofPoints pts).smul c)
    (hvidx : vidx.all (· < pts.length) = true)
    (hin : allIdx (fun i p ↦ vidx.contains i || inner.any fun t ↦
      t.1 == i && innerOk (vidx.map (ptE pts)) p t.2.1 t.2.2) 0 pts = true)
    (hV : vidx.length = V) (hf : ∀ F ∈ faces, faceOk (vidx.map (ptE pts)) s F = true)
    (hcomb : combOk (faces.map FaceE.cyc) vidx.length vtx ptn = true)
    (hk : kindsOk faces kinds = true) (hE : 2 * E = (faces.map fun F ↦ F.cyc.length).sum)
    (hs : s.map (fun x ↦ c ^ 2 * re x) = sR) : P.HasFaces V E kinds sR := by
  subst hP
  have hsub : ∀ x ∈ rpts c (vidx.map (ptE pts)),
      x ∈ ((Polyhedron.ofPoints pts).smul c).vertices := by
    intro x hx
    rw [mem_vertices_iff]
    simp only [rpts, List.map_map, List.mem_map, Function.comp_apply] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    have hlt : i < pts.length := by simpa using (List.all_eq_true.mp hvidx) i hi
    exact ⟨ptE pts i, by simp [ptE, List.getElem?_eq_getElem hlt], rfl⟩
  refine hasFaces_of_checkOn hc hsub ?_ (by simpa using hV) hf (by simpa using hcomb) hk hE hs
  apply Set.Subset.antisymm
  · refine convexHull_min (fun x hx ↦ ?_) (convex_convexHull ℝ _)
    rw [Finset.mem_coe, mem_vertices_iff] at hx
    simp only [rpts, List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
    have := allIdx_sound hin i hi
    simp only [Nat.zero_add, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true,
      beq_iff_eq, List.contains_iff_mem] at this
    rcases this with hi' | ⟨t, -, rfl, ht⟩
    · refine subset_convexHull ℝ _ ?_
      simp only [Set.mem_ofPred_eq, rpts, List.map_map, List.mem_map, Function.comp_apply]
      exact ⟨i, hi', by simp [ptE, List.getElem?_eq_getElem hi]⟩
    · exact innerOk_sound hc ht
  · exact convexHull_mono fun x hx ↦ hsub x hx

end Nieuwland.Identity
