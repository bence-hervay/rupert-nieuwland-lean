import Modules.System.PolyRootOf

/-!
# One root: a Nopert's system and a system in the scale alone

The systems with one variable have exactly one root (`PolynomialSystem.HasUniqueRoot`,
`Modules/System/PolyRootOf.lean`) by what their exact theorems already state:

* `Nieuwland.isRootMax_scales_one`: a Nopert, `x 0 = 1` with the interval `[1, 1]` (the system of
  `isMaxSingle_scales_one` has no interval);
* `Nieuwland.PolynomialSystem.IsMaxSingle.isRootMax_of_one_var`: a system whose one variable is the scale
  (a closed form: `P(x 0) = 0` in the interval of the number's decimals) has exactly one root when
  it has one scale, which `<def>_exact_list` states.

The contact systems are in `Modules/Root/HasUniqueRoot.lean`.
-/

namespace Nieuwland

open PolynomialSystem

/-- **A Nopert**: `x 0 = 1` in `[1, 1]`, exactly one root. -/
theorem isRootMax_scales_one {N : ℝ} (hN : N = 1) :
    IsRootMax [⟨[([(1, [(0, 1)])], [(1, [])])], [(1, 1)]⟩] N := by
  subst hN
  have hev : ∀ x : ℕ → ℝ, RationalPolynomial.eval [(1, [(0, 1)])] x = x 0 := fun x ↦ by
    simp [RationalPolynomial.eval, monomial]
  have hev1 : ∀ x : ℕ → ℝ, RationalPolynomial.eval [(1, [])] x = 1 := fun x ↦ by
    simp [RationalPolynomial.eval, monomial]
  have hsol : (⟨[([(1, [(0, 1)])], [(1, [])])], [(1, 1)]⟩ : PolynomialSystem).Solves fun _ ↦ 1 := by
    refine ⟨fun i hi ↦ ?_, fun e he ↦ ?_⟩
    · obtain rfl : i = 0 := by simpa using hi
      simp
    · rw [List.mem_singleton.mp he, hev, hev1]
  have hone : ∀ y : ℕ → ℝ,
      (⟨[([(1, [(0, 1)])], [(1, [])])], [(1, 1)]⟩ : PolynomialSystem).Solves y → y 0 = 1 := fun y hy ↦ by
    have := hy.2 _ (List.mem_singleton_self _)
    rwa [hev, hev1] at this
  refine ⟨⟨⟨_, List.mem_singleton_self _, _, hsol, rfl⟩, ?_⟩, fun S hS ↦ ?_⟩
  · rintro l ⟨S, hS, x, hx, rfl⟩
    rw [List.mem_singleton.mp hS] at hx
    exact (hone x hx).le
  · rw [List.mem_singleton.mp hS]
    refine ⟨by simp, by decide, _, hsol, fun y hy i hi ↦ ?_⟩
    obtain rfl : i = 0 := by simpa using hi
    exact hone y hy

/-- **A system in the scale alone**: with one scale, exactly one root. -/
theorem PolynomialSystem.IsMaxSingle.isRootMax_of_one_var {S : PolynomialSystem} {N : ℝ}
    (h : IsMaxSingle [S] N) (hl : S.box.length = 1) (hb : S.boxed = true) : IsRootMax [S] N := by
  refine ⟨h.1, fun T hT ↦ ?_⟩
  rw [List.mem_singleton.mp hT]
  obtain ⟨v, hv⟩ := h.2 S (List.mem_singleton_self _)
  obtain ⟨S', hS', x, hx, -⟩ := h.1.1
  rw [List.mem_singleton.mp hS'] at hx
  refine ⟨by omega, hb, x, hx, fun y hy i hi ↦ ?_⟩
  obtain rfl : i = 0 := by omega
  have h1 : y 0 ∈ scales [S] := ⟨S, List.mem_singleton_self _, y, hy, rfl⟩
  have h2 : x 0 ∈ scales [S] := ⟨S, List.mem_singleton_self _, x, hx, rfl⟩
  rw [hv, Set.mem_singleton_iff] at h1 h2
  rw [h1, h2]

end Nieuwland
