import Definitions.Optimum
import Modules.Nieuwland.Basic
import Modules.Pose.PoseRoot
import Modules.System.PolyRootEq

/-!
# The optimum of a Rupert polyhedron, from its pose root

The statement a reader reads, `Polyhedron.IsOptimum` (`Definitions/Optimum.lean`), from the
statements the certificates prove: the pose root at the Nieuwland number
(`PolynomialSystem.IsPoseRoot`), full-dimensionality, and a box whose scales exceed `1`.

## Main statements

* `PolynomialSystem.IsPoseRoot.isOptimum`: the optimum from the pose root.
* `Polyhedron.IsOptimum.weakFitsThrough`: the optimum's pose is a weak fit at `ν P`.
* `Polyhedron.isRupert_of_one_lt_nieuwland`: `1 < ν P` makes a full-dimensional `P` Rupert.
-/

namespace Nieuwland

open Notation

namespace PolynomialSystem

/-- Among systems that each have their one root at the scale `N`, so has the first alone. -/
theorem IsRootEq.head {S : PolynomialSystem} {Ss : List PolynomialSystem} {N : ℝ}
    (h : IsRootEq (S :: Ss) N) : IsRootEq [S] N :=
  ⟨by simp, fun T hT ↦ by
    rw [List.mem_singleton.mp hT]
    exact h.2 S List.mem_cons_self⟩

/-- **The optimum from the pose root.** For a full-dimensional `P`, a system with exactly one
root, of scale `ν P`, whose pose variables are a weak fit there, in a box whose scales exceed `1`,
is the optimum of `P`. -/
theorem IsPoseRoot.isOptimum {P : Polyhedron} {S : PolynomialSystem} {i j k : ℕ}
    (hP : P.FullDim) (h : IsPoseRoot P S (ν P) i j k) (h1 : (1 : ℚ) < (S.box.getD 0 (0, 0)).1) :
    P.IsOptimum S ⟨i, j, k⟩ := by
  obtain ⟨hone, hsc, hfit⟩ := h
  have hscale : ∀ x, S.Solves x → x 0 = ν P := fun x hx ↦ by
    have hmem : x 0 ∈ scales [S] := ⟨S, List.mem_singleton.mpr rfl, x, hx, rfl⟩
    rw [hsc] at hmem
    exact hmem
  refine ⟨hone, hscale, ?_, fun x hx ↦ hfit x hx, fun c hc hf ↦ ?_⟩
  · obtain ⟨hlen, -, x, hx, -⟩ := hone
    rw [← hscale x hx]
    exact lt_of_lt_of_le (by exact_mod_cast h1) (hx.1 0 hlen).1
  · exact absurd ((Polyhedron.fitsThrough_smul_iff_lt_nieuwland hP
      (P.nieuwland_nonneg.trans hc.le)).mp hf) (not_lt.mpr hc.le)

end PolynomialSystem

namespace Polyhedron

/-- A full-dimensional polyhedron with `1 < ν P` is Rupert. -/
theorem isRupert_of_one_lt_nieuwland {P : Polyhedron} (hP : P.FullDim) (h : 1 < ν P) :
    P.IsRupert :=
  (one_lt_nieuwland_iff hP).mp h

/-- A full-dimensional polyhedron that is not Rupert is a Nopert with `ν P = 1`. -/
theorem nieuwland_eq_one_of_isNopert {P : Polyhedron} (hP : P.FullDim) (h : P.IsNopert) :
    ν P = 1 :=
  (nieuwland_eq_one_iff hP).mpr h

/-- **The optimum's pose is a weak fit at the Nieuwland number**: `P` scaled by `ν P` fits weakly
through `P`. -/
theorem IsOptimum.weakFitsThrough {P : Polyhedron} {S : PolynomialSystem} {L : PoseLayout}
    (h : P.IsOptimum S L) : (P.smul (ν P)).WeakFitsThrough P := by
  obtain ⟨-, -, x, hx, -⟩ := h.uniqueRoot
  obtain ⟨h₁, h₂, hsub⟩ := h.fit x hx
  rw [h.scale x hx] at hsub
  exact ⟨_, h₁, _, h₂, _, hsub⟩

end Polyhedron

end Nieuwland
