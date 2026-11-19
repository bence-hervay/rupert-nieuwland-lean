import Modules.Check.Sign.Engine

/-!
# The origin vertex

The packed engine (`Lay.run`) tries dominance at the vertex where the centred linear part is
smallest (`lowSign`). `Lay.runO` is the same engine with one more attempt per box, the mirror of
the origin vertex of `nonneg_on_fbox_exact` in `code/src/proof/regional.rs`: dominance at the
origin of the box's own coordinates, where the box has it as a vertex. An exact frame at a pose
with margin zero puts the zero of the polynomial there, and the centred linear part need not
decrease towards it.

The flags `O` say per coordinate where the origin is on the cube `[-1, 1]^n`: `-1` at the lower
end, `1` at the upper end, any other value at neither. The caller sets them from the box, and a
bisection keeps a flag in the half that keeps that end (`halfO`). Dominance at any vertex is sound
(`domOkAt_sound`), so the soundness (`runO_sound`) uses nothing about the flags: they only have to
follow the Rust check for a certificate to replay. Without flags the engine is `run`
(`runO_nil`).

Not used by a checker yet: the cached engine (`EngineCache.lean`) and the callers of `Lay.run`
follow (`notes/rethink.md`, "Corner trees").
-/

open Finset

namespace Nieuwland.Check

namespace Lay

open DPoly Num

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

variable (κ) in
/-- Dominance at the vertex `σ` (`domOkAt_sound`); `domOk` is this at `lowSign`
(`domOk_eq_domOkAt`). -/
def domOkAt (σ : ℕ → ℤ) (n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (Ns : List ℕ) : Bool :=
  match vertAll B sh σ n Ns with
  | none => false
  | some Vs => (domOf (κ := κ) n sh B Vs).2 && signTest strict (domOf (κ := κ) n sh B Vs).1

theorem domOk_eq_domOkAt (n : ℕ) (sh : List ℕ) (B : ℕ) (strict : Bool) (Ns : List ℕ) :
    domOk κ n sh B strict Ns = domOkAt κ (lowSign κ sh B Ns) n sh B strict Ns := rfl

/-- The origin's vertex from the flags: the upper end where the flag is `1`, else the lower end. -/
def origSign (O : List ℤ) (i : ℕ) : ℤ := bif O.getD i 0 == 1 then 1 else -1

theorem origSign_cases (O : List ℤ) (i : ℕ) : origSign O i = 1 ∨ origSign O i = -1 := by
  unfold origSign
  cases O.getD i 0 == 1 <;> simp

/-- Whether the origin is a vertex of the box: every coordinate of positive degree has it at an
end (in a coordinate that the polynomial does not contain any end serves). -/
def origAt (n : ℕ) (sh : List ℕ) (O : List ℤ) : Bool :=
  (List.range n).all fun i ↦ deg sh i == 0 || O.getD i 0 == 1 || O.getD i 0 == -1

variable (κ) in
/-- Whether the origin's vertex is another than `lowSign`'s in a coordinate of positive degree. -/
def origNew (n : ℕ) (sh : List ℕ) (B : ℕ) (O : List ℤ) (Ns : List ℕ) : Bool :=
  (List.range n).any fun i ↦ deg sh i != 0 && origSign O i != lowSign κ sh B Ns i

variable (κ) in
/-- The tests of one box with the origin's flags: `boxOk`, then, if `dom`, dominance at the origin
where it is a vertex of the box other than `lowSign`'s. -/
def boxOkO (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom : Bool) (O : List ℤ) (Ns : List ℕ) : Bool :=
  boxOk κ n sh B strict dom Ns ||
    (dom && origAt n sh O && origNew κ n sh B O Ns && domOkAt κ (origSign O) n sh B strict Ns)

/-- The flags of a half along `i`: the lower half (`s = -1`) keeps an origin at the lower end, the
upper half (`s = 1`) one at the upper end; the half's other end along `i` is the midpoint. -/
def halfO (O : List ℤ) (i : ℕ) (s : ℤ) : List ℤ :=
  O.mapIdx fun j f ↦ if j = i then (if f = s then f else 0) else f

variable (κ) in
/-- **The engine with the origin vertex** (`runO_sound`): `run` with the box tests `boxOkO`. -/
def runO (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) :
    ℕ → List ℤ → List ℤ → List ℕ → Bool
  | 0, _, O, Ns => boxOkO κ n sh B strict dom O Ns
  | d + 1, W, O, Ns =>
    boxOkO κ n sh B strict dom O Ns ||
      let i := pickW last n W
      let W' := halveW W i
      bif deg sh i == 0 then runO n sh B strict dom last d W' O Ns
      else
        match subAll B sh i (halfW sh i) (-1) 1 (2 ^ deg sh i) Ns,
          subAll B sh i (halfW sh i) 1 1 (2 ^ deg sh i) Ns with
        | some Lo, some Hi =>
          runO n sh B strict dom last d W' (halfO O i (-1)) Lo &&
            runO n sh B strict dom last d W' (halfO O i 1) Hi
        | _, _ => false

/-! #### Soundness -/

variable {n : ℕ} {sh : List ℕ} {B : ℕ} {strict : Bool} {Ns : List ℕ}

/-- Dominance at any vertex gives the sign on the cube. -/
theorem domOkAt_sound {σ : ℕ → ℤ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (hB : 0 < B)
    (hsh : sh.length ≤ n) (hNs : ∀ N ∈ Ns, Inv B sh N)
    (hlen : ExactBasis.dim κ ≤ Ns.length) (h : domOkAt κ σ n sh B strict Ns = true) {y : ℕ → ℝ}
    (hy : ∀ i, |y i| ≤ 1) : Sign strict (val (κ := κ) sh B Ns y) := by
  unfold domOkAt at h
  split at h
  · exact absurd h (by simp)
  · rename_i Vs hV
    simp only [Bool.and_eq_true] at h
    obtain ⟨-, hlenV, hpv⟩ := vertAll_spec hB hσ n hNs hV
    refine sign_of_le (sign_of_signTest h.2) ?_
    have hd := domOf_le (κ := κ) n sh B Vs (fun i ↦ vertPt σ n y i)
      (hlenV ▸ hlen) (fun i ↦ vertPt_mem hσ hy i.2) h.1
    refine hd.trans (le_of_eq ?_)
    rw [sum_eval_unpack hsh]
    exact sum_congr rfl fun j hj ↦ by
      rw [hpv j ((mem_range.mp hj).trans_le hlen)]

theorem boxOkO_sound {dom : Bool} {O : List ℤ} (hB : 0 < B) (hsh : sh.length ≤ n)
    (hNs : ∀ N ∈ Ns, Inv B sh N) (hlen : ExactBasis.dim κ ≤ Ns.length)
    (h : boxOkO κ n sh B strict dom O Ns = true) {y : ℕ → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    Sign strict (val (κ := κ) sh B Ns y) := by
  simp only [boxOkO, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨-, h⟩
  · exact boxOk_sound hB hsh hNs hlen h hy
  · exact domOkAt_sound (origSign_cases O) hB hsh hNs hlen h hy

/-- **Soundness of the engine with the origin vertex**, for any flags. -/
theorem runO_sound {dom last : Bool} (hB : 0 < B) (hsh : sh.length ≤ n) :
    ∀ (depth : ℕ) (W O : List ℤ) {Ns : List ℕ}, (∀ N ∈ Ns, Inv B sh N) →
      ExactBasis.dim κ ≤ Ns.length → runO κ n sh B strict dom last depth W O Ns = true →
      ∀ y : ℕ → ℝ, (∀ i, |y i| ≤ 1) → Sign strict (val (κ := κ) sh B Ns y)
  | 0, W, O, Ns, hNs, hlen, h, y, hy => boxOkO_sound hB hsh hNs hlen h hy
  | d + 1, W, O, Ns, hNs, hlen, h, y, hy => by
    simp only [runO, Bool.or_eq_true] at h
    rcases h with h | h
    · exact boxOkO_sound hB hsh hNs hlen h hy
    cases hd : deg sh (pickW last n W) == 0
    · rw [hd, Bool.cond_false] at h
      split at h
      · rename_i Lo Hi hLo hHi
        simp only [Bool.and_eq_true] at h
        have hLo' := hLo
        have hHi' := hHi
        obtain ⟨hiLo, hlLo, -⟩ := subAll_spec hB (halfW_bound sh _ (s := -1) rfl) hNs hLo'
        obtain ⟨hiHi, hlHi, -⟩ := subAll_spec hB (halfW_bound sh _ (s := 1) rfl) hNs hHi'
        exact half_sound hB hNs hlen hLo hHi
          (runO_sound hB hsh d _ _ hiLo (hlLo ▸ hlen) h.1)
          (runO_sound hB hsh d _ _ hiHi (hlHi ▸ hlen) h.2) hy
      · exact absurd h (by simp)
    · rw [hd, Bool.cond_true] at h
      exact runO_sound hB hsh d _ _ hNs hlen h y hy

/-! #### Without flags -/

theorem halfO_nil (i : ℕ) (s : ℤ) : halfO [] i s = [] := rfl

/-- Without flags no box has the origin as a vertex other than `lowSign`'s. -/
theorem boxOkO_nil (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom : Bool) (Ns : List ℕ) :
    boxOkO κ n sh B strict dom [] Ns = boxOk κ n sh B strict dom Ns := by
  have h : (origAt n sh [] && origNew κ n sh B [] Ns) = false := by
    cases hA : origAt n sh [] with
    | false => rfl
    | true =>
      simp only [origAt, List.all_eq_true, List.mem_range, List.getD_nil, Bool.or_eq_true,
        beq_iff_eq] at hA
      simp only [Bool.true_and, origNew, List.any_eq_false, List.mem_range, Bool.and_eq_true,
        bne_iff_ne, not_and]
      intro i hi hd
      rcases hA i hi with (h0 | h1) | h2
      · exact absurd h0 hd
      · exact absurd h1 (by decide)
      · exact absurd h2 (by decide)
  simp only [boxOkO, Bool.and_assoc, h, Bool.false_and, Bool.and_false, Bool.or_false]

/-- **Without flags the engine is `run`.** -/
theorem runO_nil (n : ℕ) (sh : List ℕ) (B : ℕ) (strict dom last : Bool) :
    ∀ (depth : ℕ) (W : List ℤ) (Ns : List ℕ),
      runO κ n sh B strict dom last depth W [] Ns = run κ n sh B strict dom last depth W Ns
  | 0, W, Ns => boxOkO_nil n sh B strict dom Ns
  | d + 1, W, Ns => by
    simp only [runO, run, boxOkO_nil, halfO_nil, runO_nil n sh B strict dom last d]
    cases subAll B sh (pickW last n W) (halfW sh (pickW last n W)) (-1) 1
        (2 ^ deg sh (pickW last n W)) Ns <;>
      cases subAll B sh (pickW last n W) (halfW sh (pickW last n W)) 1 1
        (2 ^ deg sh (pickW last n W)) Ns <;> rfl

end Field

end Lay

end Nieuwland.Check
