import Modules.Check.Chart.ChartBox

/-!
# Cover trees

A cover tree (`CoverNode` in `code/src/proof/cert.rs`, `FaceTree` in `regional/zoom.rs`) splits a
region by halving coordinates and discharges each leaf with its data. The regions only need to
halve: a `Halving` says how, and which points a region contains. `Cover.checkWith H ok r T`
checks every leaf of `T` over the region `r` with `ok`. Its soundness (`Cover.checkWith_sound`) is
generic in the conclusion: if every leaf that `ok` accepts has a property `Q` at all its points,
so does `r`, since the two halves of a region contain it. `ok` only needs to be sound for the data
that occur in `T` (`Cover.data`).

Chart boxes (`ChartBox.halving`, with `Cover.check`) and boxes of `n` coordinates
(`Box.halving`) halve. Two kinds of leaves of chart boxes give `NoFit`:

* claims, checked in place (`Modules/Check/Leaf/Claim.lean`);
* boxes proved by other theorems (`Cover.forall_of_proved`, `Cover.noFit_of_proved`): a leaf `C`
  discharges any box inside `C`. This assembles a large certificate from separately checked
  parts.
-/

namespace Nieuwland.Check

/-- Regions of type `R`, with points of type `X`, that cover trees halve: when `valid r`, the halves
`lower r k` and `upper r k` along coordinate `k` together contain `r`. -/
structure Halving (R X : Type) where
  /-- The points of a region. -/
  mem : R → Set X
  /-- Whether a region may be halved. -/
  valid : R → Bool
  /-- The lower half along a coordinate. -/
  lower : R → ℕ → R
  /-- The upper half along a coordinate. -/
  upper : R → ℕ → R
  subset_union : ∀ r k, valid r = true → mem r ⊆ mem (lower r k) ∪ mem (upper r k)

/-- Chart boxes halve (`ChartBox.lowerHalf`, `ChartBox.upperHalf`). -/
def ChartBox.halving : Halving ChartBox ChartPose where
  mem := ChartBox.poses
  valid B := decide (0 < B.box.den)
  lower := ChartBox.lowerHalf
  upper := ChartBox.upperHalf
  subset_union _ k h := ChartBox.poses_subset_union (of_decide_eq_true h) k

/-- Boxes of `n` coordinates halve (`Box.lowerHalf`, `Box.upperHalf`). -/
def Box.halving (n : ℕ) : Halving Box (Fin n → ℝ) where
  mem b := {x | b.Mem n x}
  valid b := decide (0 < b.den)
  lower b := b.lowerHalf n
  upper b := b.upperHalf n
  subset_union _ k h _ hx := Box.mem_lowerHalf_or_upperHalf k (of_decide_eq_true h) hx

/-- A cover tree with leaves carrying data of type `E`. -/
inductive Cover (E : Type) where
  /-- A leaf. -/
  | leaf (e : E)
  /-- Halve coordinate `dim` (`Halving.lower`, `Halving.upper`). -/
  | split (dim : ℕ) (lo hi : Cover E)

namespace Cover

variable {E R X : Type}

/-- The data of the leaves. -/
def data : Cover E → List E
  | leaf e => [e]
  | split _ lo hi => lo.data ++ hi.data

/-- Check every leaf with `ok`, on the region of the leaf. -/
def checkWith (H : Halving R X) (ok : R → E → Bool) : R → Cover E → Bool
  | r, leaf e => ok r e
  | r, split d lo hi => H.valid r && checkWith H ok (H.lower r d) lo &&
      checkWith H ok (H.upper r d) hi

/-- **Soundness of cover trees.** -/
theorem checkWith_sound {H : Halving R X} {Q : X → Prop} {ok : R → E → Bool} :
    ∀ {T : Cover E} {r : R},
      (∀ r, ∀ e ∈ T.data, ok r e = true → ∀ x ∈ H.mem r, Q x) →
      T.checkWith H ok r = true → ∀ x ∈ H.mem r, Q x
  | leaf e, r, hok, h => hok r e (List.mem_singleton_self e) h
  | split d lo hi, r, hok, h => by
    simp only [checkWith, Bool.and_eq_true] at h
    obtain ⟨⟨hval, hlo⟩, hhi⟩ := h
    intro x hx
    rcases H.subset_union r d hval hx with hx | hx
    · exact checkWith_sound (fun r e he ↦ hok r e (List.mem_append_left _ he)) hlo x hx
    · exact checkWith_sound (fun r e he ↦ hok r e (List.mem_append_right _ he)) hhi x hx

/-- Check every leaf with `ok`, on the chart box of the leaf. -/
def check (ok : ChartBox → E → Bool) : ChartBox → Cover E → Bool :=
  checkWith ChartBox.halving ok

/-- **Soundness of cover trees of chart boxes.** -/
theorem check_sound {Q : ChartPose → Prop} {ok : ChartBox → E → Bool} {T : Cover E}
    {B : ChartBox} (hok : ∀ B, ∀ e ∈ T.data, ok B e = true → ∀ p ∈ B.poses, Q p)
    (h : T.check ok B = true) : ∀ p ∈ B.poses, Q p :=
  checkWith_sound (H := ChartBox.halving) hok h

/-- **Assembly.** A cover tree whose leaves are boxes where a property holds at every pose
proves it on its box. -/
theorem forall_of_proved {Q : ChartPose → Prop} {T : Cover ChartBox}
    (hT : ∀ C ∈ T.data, ∀ p ∈ C.poses, Q p) {B : ChartBox}
    (h : T.check (fun B C ↦ B.subset C) B = true) : ∀ p ∈ B.poses, Q p :=
  check_sound (fun _ C hC hsub p hp ↦ hT C hC p (ChartBox.poses_subset hsub hp)) h

/-- **Assembly of `NoFit`.** -/
theorem noFit_of_proved {P : Polyhedron} {T : Cover ChartBox}
    (hT : ∀ C ∈ T.data, P.NoFit C.poses) {B : ChartBox}
    (h : T.check (fun B C ↦ B.subset C) B = true) : P.NoFit B.poses :=
  forall_of_proved hT h

end Cover

end Nieuwland.Check
