import Modules.System.PolyRootOf

/-!
# One shared scale: the representatives' form

`IsPolyRootEq a`: `a` is **the first coordinate of the root of each** of finitely many (at least
one) systems of integer polynomial equations, each in a rational box of all its variables and
**each with exactly one root in its box**. It implies `IsPolyRootMax a`
(`IsPolyRootEq.isPolyRootMax`, `Modules/System/PolyRoot.lean`) for the same systems.

The list form, for the systems of `Modules/System/System.lean`:

* `Nieuwland.PolynomialSystem.IsRootEq Ss N`: `Ss` is not empty, and each of its systems has exactly one
  root, of scale `N`;
* `Nieuwland.PolynomialSystem.IsRootMax.isRootEq`: if `N` is the largest scale of the systems `Ss`, each
  with exactly one root (`IsRootMax`), and their scales are all one number, then any nonempty
  part of `Ss` has `IsRootEq` with `N`;
* `Nieuwland.PolynomialSystem.isPolyRootEq`: with integer coefficients, `IsRootEq Ss N` gives
  `IsPolyRootEq N` by the same systems as Mathlib polynomials.

No certificate is involved here: `Modules/Root/Reps.lean` shows the scales of a solid's systems
equal, by links between its roots.
-/

namespace Nieuwland

open MvPolynomial

/-- `a` is the first coordinate of the root of each of finitely many (at least one) systems of
integer polynomial equations, each in a rational box of all its variables and each with exactly
one root in its box. -/
def IsPolyRootEq (a : ℝ) : Prop :=
  ∃ Ss : List (Σ n, BoxSystem n), Ss ≠ [] ∧
    ∀ S ∈ Ss, (∃! x, S.2.IsRoot x) ∧ ∀ x, S.2.IsRoot x → x 0 = a

/-- **The shared form implies the largest-root form**, by the same systems. -/
theorem IsPolyRootEq.isPolyRootMax {a : ℝ} (h : IsPolyRootEq a) : IsPolyRootMax a := by
  obtain ⟨Ss, hne, h⟩ := h
  refine ⟨Ss, fun S hS ↦ (h S hS).1, ⟨?_, ?_⟩⟩
  · obtain ⟨S, hS⟩ := List.exists_mem_of_ne_nil Ss hne
    obtain ⟨x, hx, -⟩ := (h S hS).1
    exact ⟨S, hS, x, hx, (h S hS).2 x hx⟩
  · rintro l ⟨S, hS, x, hx, rfl⟩
    exact ((h S hS).2 x hx).le

namespace PolynomialSystem

/-- `Ss` is not empty, and each of its systems has exactly one root, of scale `N`: the list form
of `IsPolyRootEq`. -/
def IsRootEq (Ss : List PolynomialSystem) (N : ℝ) : Prop :=
  Ss ≠ [] ∧ ∀ S ∈ Ss, S.HasUniqueRoot ∧ scales [S] = {N}

/-- **Equal scales, any representatives**: if `N` is the largest scale of the systems `Ss`, each
with exactly one root, and every system of `Ss` has the one scale `c`, then every nonempty part of
`Ss` has exactly one root per system, of scale `N`. -/
theorem IsRootMax.isRootEq {Ss : List PolynomialSystem} {N c : ℝ} (h : IsRootMax Ss N)
    (hc : ∀ S ∈ Ss, scales [S] = {c}) {Rs : List PolynomialSystem} (hne : Rs ≠ [])
    (hsub : ∀ S ∈ Rs, S ∈ Ss) : IsRootEq Rs N := by
  obtain ⟨S, hS, x, hx, hx0⟩ := h.1.1
  have hNc : N = c := by
    have hm : x 0 ∈ scales [S] := ⟨S, List.mem_singleton_self _, x, hx, rfl⟩
    rw [hc S hS, hx0] at hm
    exact hm
  refine ⟨hne, fun S hS ↦ ⟨h.2 S (hsub S hS), ?_⟩⟩
  rw [hc S (hsub S hS), hNc]

/-- **One system**: a single system with exactly one root has `IsRootEq` with its scale. -/
theorem IsRootMax.isRootEq_singleton {S : PolynomialSystem} {N : ℝ} (h : IsRootMax [S] N) :
    IsRootEq [S] N := by
  obtain ⟨c, hc⟩ := (h.2 S (List.mem_singleton_self _)).scales_eq
  exact h.isRootEq (c := c) (fun S' hS' ↦ by rw [List.mem_singleton.mp hS']; exact hc)
    (List.cons_ne_nil _ _) fun _ h ↦ h

/-- **A part of the systems**: any nonempty part of systems with `IsRootEq` has it too. -/
theorem IsRootEq.sub {Ss Rs : List PolynomialSystem} {N : ℝ} (h : IsRootEq Ss N) (hne : Rs ≠ [])
    (hsub : ∀ S ∈ Rs, S ∈ Ss) : IsRootEq Rs N :=
  ⟨hne, fun S hS ↦ h.2 S (hsub S hS)⟩

/-- **The list form gives `IsPolyRootEq`**: systems with integer coefficients, each with exactly
one root of scale `N`, are, as Mathlib polynomials in their `n` variables, systems each with
exactly one root in its box, of first coordinate `N`. -/
theorem isPolyRootEq {Ss : List PolynomialSystem} (h : Ss.all intSides = true) {N : ℝ}
    (hN : IsRootEq Ss N) : IsPolyRootEq N := by
  have hint : ∀ S ∈ Ss, S.intSides = true := fun S hS ↦ List.all_eq_true.mp h S hS
  have hlen : ∀ S ∈ Ss, S.box.length = (S.box.length - 1) + 1 := fun S hS ↦ by
    have := (hN.2 S hS).1.1; omega
  refine ⟨Ss.map fun S ↦ ⟨S.box.length - 1, S.toBox (S.box.length - 1)⟩, ?_, ?_⟩
  · simpa using hN.1
  intro T hT
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
  refine ⟨(hN.2 S hS).1.existsUnique (hint S hS), fun r hr ↦ ?_⟩
  have hs := (isRoot_toBox S (hint S hS) (hlen S hS) r).mp hr
  have hm : ofFin r 0 ∈ scales [S] := ⟨S, List.mem_singleton_self _, _, hs, rfl⟩
  rw [(hN.2 S hS).2] at hm
  have e : ofFin r 0 = r 0 := by rw [ofFin_lt r (Nat.succ_pos _)]; rfl
  rw [← e]
  exact hm

end PolynomialSystem

end Nieuwland
