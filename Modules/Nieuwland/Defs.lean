import Definitions.Rupertness
import Modules.Rupert.Scale
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Nieuwland numbers: the definitions

For a full-dimensional convex polyhedron `P`, its **Nieuwland number** is the supremum of the
scales `c > 0` such that `P` scaled by `c`, rotated and translated, passes strictly through `P`:
its shadow lies in the interior of a shadow of `P`. A Nopert has Nieuwland number `1`; a NoFit
certificate at scale `c` proves `nieuwland P ≤ c`, and a weak fit at `c` proves `c ≤ nieuwland P`.

The statement, for review. `SO(3)`, `projXY`, `Polyhedron.hull` and `interior` are those of
`Polyhedron.IsRupert` (`Definitions/Rupertness.lean`, `Modules/Rupert/Defs.lean`); `P.smul c` is `P`
with its points times `c` (`Modules/Rupert/Scale.lean`); `P.FullDim` says the hull of `P` has an
interior point in `ℝ³` (`Modules/Rupert/FullDim.lean`).

```lean
def Polyhedron.FitsThrough (plug hole : Polyhedron) : Prop :=
  ∃ R₁ ∈ SO(3), ∃ R₂ ∈ SO(3), ∃ t : Fin 2 → ℝ,
    {projXY (R₁ *ᵥ x) + t | x ∈ plug.hull} ⊆ interior {projXY (R₂ *ᵥ x) | x ∈ hole.hull}

def Polyhedron.WeakFitsThrough (plug hole : Polyhedron) : Prop :=
  ∃ R₁ ∈ SO(3), ∃ R₂ ∈ SO(3), ∃ t : Fin 2 → ℝ,
    {projXY (R₁ *ᵥ x) + t | x ∈ plug.hull} ⊆ {projXY (R₂ *ᵥ x) | x ∈ hole.hull}

noncomputable def Polyhedron.nieuwland (P : Polyhedron) : ℝ :=
  sSup {c : ℝ | 0 < c ∧ (P.smul c).FitsThrough P}

theorem isRupert_iff_fitsThrough (P : Polyhedron) : P.IsRupert ↔ P.FitsThrough P

-- Modules/Nieuwland/Basic.lean, for P Q : Polyhedron and c c' L a b θ θ' : ℝ
theorem FitsThrough.smul_of_le (h : (P.smul c).FitsThrough Q) (hc' : 0 ≤ c') (hle : c' ≤ c) :
    (P.smul c').FitsThrough Q
theorem FitsAlong.smul_of_le (h : P.FitsAlong u (θ • R)) (hθ' : 0 ≤ θ') (hle : θ' ≤ θ) :
    P.FitsAlong u (θ' • R)
theorem WeakFitsThrough.fitsThrough_smul_of_lt (h : (P.smul c).WeakFitsThrough Q)
    (hQ : Q.FullDim) (hc' : 0 ≤ c') (hlt : c' < c) : (P.smul c').FitsThrough Q
theorem FitsThrough.exists_lt_smul (h : (P.smul c).FitsThrough Q) :
    ∃ c'' > c, (P.smul c'').FitsThrough Q
theorem FullDim.bddAbove_fitsThrough (hP : P.FullDim) :
    BddAbove {c : ℝ | 0 < c ∧ (P.smul c).FitsThrough P}
theorem fitsThrough_smul_iff_lt_nieuwland (hP : P.FullDim) (hc : 0 ≤ c) :
    (P.smul c).FitsThrough P ↔ c < P.nieuwland
theorem nieuwland_le_of_not_fitsThrough (hc : 0 ≤ c) (h : ¬ (P.smul c).FitsThrough P) :
    P.nieuwland ≤ c
theorem le_nieuwland_of_forall_lt (hP : P.FullDim)
    (h : ∀ c, 0 < c → c < L → (P.smul c).FitsThrough P) : L ≤ P.nieuwland
theorem le_nieuwland_of_weakFitsThrough (hP : P.FullDim) (h : (P.smul c).WeakFitsThrough P) :
    c ≤ P.nieuwland
theorem nieuwland_eq_of_iff (hL : 0 < L)
    (h : ∀ c, 0 < c → ((P.smul c).FitsThrough P ↔ c < L)) : P.nieuwland = L
theorem one_le_nieuwland (hP : P.FullDim) : 1 ≤ P.nieuwland
theorem nieuwland_eq_one_of_not_isRupert (hP : P.FullDim) (h : ¬ P.IsRupert) :
    P.nieuwland = 1
theorem nieuwland_eq_one_iff (hP : P.FullDim) : P.nieuwland = 1 ↔ ¬ P.IsRupert
theorem fitsThrough_smul_iff (ha : a ≠ 0) :
    (P.smul a).FitsThrough (Q.smul a) ↔ P.FitsThrough Q
theorem fitsThrough_smul_smul_iff (hb : b ≠ 0) :
    (P.smul a).FitsThrough (Q.smul b) ↔ (P.smul (a / b)).FitsThrough Q
theorem nieuwland_smul (ha : a ≠ 0) : (P.smul a).nieuwland = P.nieuwland
theorem fitsThrough_smul_neg : (P.smul (-c)).FitsThrough Q ↔ (P.smul c).FitsThrough Q
```

Remarks:

* The plug is scaled about the origin; the free translation makes the centre irrelevant, and a
  negative scale is a reflected copy that fits exactly when the positive one does
  (`fitsThrough_smul_neg`), so `nieuwland` takes `c > 0` only.
* `sSup` is `Real.sSup`, which is `0` for a set that is empty or not bounded above. Both happen
  for degenerate polyhedra (no points: every scale fits; one point: none does), so the lemmas
  that need the set nonempty or bounded assume `FullDim`, which every solid of the project has
  (`<name>_fullDim`). `Nieuwland/Examples/Nieuwland.lean` shows that these hypotheses are needed.
* `FitsAlong` (`Modules/NoFit/Along.lean`) takes any matrix: `P.FitsAlong u (θ • R)` is the fit
  of `θ R P` through `P` along `u`, the form in which scaled chunk checks will conclude.

## Main definitions

* `Nieuwland.Polyhedron.FitsThrough plug hole`: `plug` passes strictly through `hole`.
* `Nieuwland.Polyhedron.WeakFitsThrough plug hole`: the same with the closed shadow of the hole.
* `Nieuwland.Polyhedron.nieuwland P`: the supremum of the scales `c > 0` at which `P.smul c` fits
  through `P`.
-/

open Matrix

namespace Nieuwland

namespace Polyhedron

/-- `plug` **fits weakly through** `hole`: as `FitsThrough`, but the moved shadow of `R₁ plug`
need only lie in the shadow of `R₂ hole`, and may touch its boundary. (The proofs about the
Nieuwland number use it; no statement of a solid does.) -/
def WeakFitsThrough (plug hole : Polyhedron) : Prop :=
  ∃ R₁ ∈ SO(3), ∃ R₂ ∈ SO(3), ∃ t : Fin 2 → ℝ,
    {projXY (R₁ *ᵥ x) + t | x ∈ plug.hull} ⊆ {projXY (R₂ *ᵥ x) | x ∈ hole.hull}

/-- With one polyhedron as plug and hole, `FitsThrough` is `IsRupert`, by definition. -/
theorem isRupert_iff_fitsThrough (P : Polyhedron) : P.IsRupert ↔ P.FitsThrough P :=
  Iff.rfl

end Polyhedron

end Nieuwland
