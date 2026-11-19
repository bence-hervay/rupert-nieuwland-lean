import Definitions.Rupertness
import Definitions.Polynomials

/-!
# The optimum of a Rupert polyhedron as the one root of a polynomial system

The statement proved for every Rupert solid: its Nieuwland number and an optimal pose are the one
root of a polynomial system written out as data.

A pose is two rotations and a translation: the plug is turned by `R₁`, the hole by `R₂`, and the
plug's shadow is moved by `t`. A system keeps a pose as twenty of its variables: the nine entries
of each rotation, row by row, and the two coordinates of the translation. With the scale these are
the twenty-one numbers of an optimum, and an enclosure holds each of them within a rational
interval.
-/

open Matrix

namespace Nieuwland

open Notation

/-! ### A pose among the variables of a system -/

/-- The `3 × 3` matrix of the coordinates `x i, …, x (i + 8)`, row by row. -/
def matAt (x : ℕ → ℝ) (i : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := fun a b ↦ x (i + 3 * a + b)

/-- Where a system keeps a pose: the plug's rotation at the variables `plug, …, plug + 8`, the
hole's rotation at `hole, …, hole + 8`, the translation at `shift, shift + 1`. -/
structure PoseLayout where
  /-- The first variable of the plug's rotation `R₁`. -/
  plug : ℕ
  /-- The first variable of the hole's rotation `R₂`. -/
  hole : ℕ
  /-- The first variable of the translation `t`. -/
  shift : ℕ

/-- **The point `x` holds a weak fit of `P` at the scale `x 0`**: the variables named by `L` are
rotations `R₁`, `R₂` and a translation `t` such that the shadow of `R₁ (x 0 • P)`, moved by `t`,
lies in the shadow of `R₂ P` (it may touch its boundary). -/
def Polyhedron.WeakFitAt (P : Polyhedron) (L : PoseLayout) (x : ℕ → ℝ) : Prop :=
  matAt x L.plug ∈ SO(3) ∧ matAt x L.hole ∈ SO(3) ∧
    {projXY (matAt x L.plug *ᵥ y) + ![x L.shift, x (L.shift + 1)] | y ∈ (P.smul (x 0)).hull} ⊆
      {projXY (matAt x L.hole *ᵥ y) | y ∈ P.hull}

/-! ### The optimum -/

/-- **The optimum of `P` is the one root of `S`.** The system `S` has exactly one root in its box,
and at this root

* the first variable is the Nieuwland number `ν P`, which is greater than `1`;
* the variables named by `L` are a pose at which `P` scaled by `ν P` still fits weakly through
  `P` (an optimal pose);

and no larger copy of `P` fits through `P`. -/
structure Polyhedron.IsOptimum (P : Polyhedron) (S : PolynomialSystem) (L : PoseLayout) : Prop where
  /-- `S` has exactly one root in its box. -/
  uniqueRoot : S.HasUniqueRoot
  /-- At the root, the first variable is the Nieuwland number of `P`. -/
  scale : ∀ x, S.Solves x → x 0 = ν P
  /-- The Nieuwland number of `P` is greater than `1`. -/
  one_lt : 1 < ν P
  /-- At the root, the pose variables are a weak fit of `P` scaled by `ν P` through `P`. -/
  fit : ∀ x, S.Solves x → P.WeakFitAt L x
  /-- No copy of `P` larger than `ν P` fits through `P`. -/
  largest : ∀ c, ν P < c → ¬ (P.smul c).FitsThrough P

/-! ### Rational enclosures of an optimum -/

/-- The twenty-one variables of an optimum: the scale `x 0`, the nine entries of the plug's
rotation, the nine entries of the hole's rotation (row by row), and the two coordinates of the
translation. -/
def PoseLayout.variables (L : PoseLayout) : List ℕ :=
  0 :: ((List.range 9).map fun n ↦ L.plug + n) ++ ((List.range 9).map fun n ↦ L.hole + n) ++
    [L.shift, L.shift + 1]

/-- **The intervals `E` enclose the optimum of `S` to within `w`**: `E` has one interval for each
of the twenty-one variables of the optimum, in the order of `L.variables`; at every root of `S`
(there is one) each of these variables lies in its interval; and no interval is wider than `w`. -/
def PolynomialSystem.EnclosedBy (S : PolynomialSystem) (L : PoseLayout) (E : List (ℚ × ℚ))
    (w : ℚ) : Prop :=
  List.Forall₂ (fun i I ↦ ∀ x, S.Solves x → (I.1 : ℝ) ≤ x i ∧ x i ≤ (I.2 : ℝ)) L.variables E ∧
    ∀ I ∈ E, I.2 - I.1 ≤ w

end Nieuwland
