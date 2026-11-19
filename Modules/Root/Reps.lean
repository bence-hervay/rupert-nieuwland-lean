import Modules.Root.LinkCheck
import Modules.Root.OneRoot
import Modules.System.PolyRootEq

/-!
# Representatives: the roots of a certificate that links give one scale

A root-form certificate may have several roots of the largest scale, each with its completed
system (`Modules/Root/HasUniqueRoot.lean`; a solid's `<def>_nu_roots_list`). Links between the roots
(`Modules/Root/LinkCheck.lean`) show their scales equal, and then any of the systems, or one per
class of roots, carries the number:

* `linkGroupsOk pts A R known gs`: links in groups by source root (indices into `A`, `R` the
  default), each group's source reached before (at first the roots `known`), all checked by
  `linksOk` (the balls of a source's zero computed once per group);
* `scale_of_linkGroupsOk`: then every root reached has the scale of the roots `known`;
* `isRootEq_of_links`: from `IsRootMax` of the completed systems of the roots `T`
  (`<def>_nu_roots_list`) and links that reach every root of `T` from root `0`, every nonempty
  part of those systems has `IsRootEq` (`Modules/System/PolyRootEq.lean`): exactly one root
  each, all of scale `N`.

The links say nothing of which roots differ in their pictures: that is a fact of the data, not of
this module.
-/

open Finset
open Nieuwland.Check

namespace Nieuwland.Root

section Reps

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- Links in groups by source (module docs): `(i, ts)` links the root `i` of `A` (`R` the
default) to the roots `t.1` with the records `t.2`, `i` being reached before. -/
def linkGroupsOk (pts : List (V3 κ)) (A : List RootRec) (R : RootRec) :
    List ℕ → List (ℕ × List (ℕ × LinkRec)) → Bool
  | _, [] => true
  | known, (i, ts) :: gs => known.contains i &&
      linksOk pts (A.getD i R) (ts.map fun t ↦ (A.getD t.1 R, t.2)) &&
      linkGroupsOk pts A R (ts.map Prod.fst ++ known) gs

/-- The roots that links in groups reach from the roots `known` (links of any kind). -/
def reached {α : Type} (known : List ℕ) (gs : List (ℕ × List (ℕ × α))) : List ℕ :=
  known ++ gs.flatMap fun g ↦ g.2.map Prod.fst

variable [RootBasis κ]

/-- A root that checks has its zero. -/
theorem exists_isZero {pts : List (V3 κ)} {R : RootRec} (h : R.ok pts = true) :
    ∃ y, (R.kraw pts).IsZero (basisPar κ) y := by
  have hp := RootRec.parOk (pts := pts) (RootRec.parCheck_of_ok h)
  have hchk : (R.kraw pts).check = true := by
    simp only [RootRec.ok, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.2
  obtain ⟨y, hy, hu⟩ := (R.kraw pts).existsUnique hchk hp
  exact ⟨y, hy, hu⟩

/-- **Links in groups give one scale** to the roots they reach. -/
theorem scale_of_linkGroupsOk {pts : List (V3 κ)} {A : List RootRec} {R : RootRec}
    (hok : ∀ i, (A.getD i R).ok pts = true) {c : ℝ} :
    ∀ {known : List ℕ} {gs : List (ℕ × List (ℕ × LinkRec))},
      linkGroupsOk pts A R known gs = true → (∀ i ∈ known, (A.getD i R).scale pts = c) →
        ∀ i ∈ reached known gs, (A.getD i R).scale pts = c
  | known, [], _, hk => by simpa [reached] using hk
  | known, (i, ts) :: gs, h, hk => by
    simp only [linkGroupsOk, Bool.and_eq_true, List.contains_iff_mem] at h
    obtain ⟨⟨hi, hl⟩, hgs⟩ := h
    have hts : ∀ t ∈ ts, (A.getD t.1 R).scale pts = c := by
      intro t ht
      have := scale_eq_of_linksOk hl (hok i) (fun t' ht' ↦ by
        obtain ⟨u, -, rfl⟩ := List.mem_map.mp ht'
        exact hok u.1) _ (List.mem_map.mpr ⟨t, ht, rfl⟩)
      rw [this, hk i hi]
    have hk' : ∀ j ∈ ts.map Prod.fst ++ known, (A.getD j R).scale pts = c := by
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hj
        exact hts t ht
      · exact hk j hj
    have ih := scale_of_linkGroupsOk hok hgs hk'
    intro j hj
    simp only [reached, List.flatMap_cons, List.mem_append] at hj
    rcases hj with hj | hj | hj
    · exact hk j hj
    · exact hk' j (List.mem_append_left _ hj)
    · exact ih j (List.mem_append_right _ hj)

theorem getD_mem_cons (R : RootRec) (Rs : List RootRec) (i : ℕ) : (R :: Rs).getD i R ∈ R :: Rs := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (R :: Rs)[i]? with
  | none => exact List.mem_cons_self
  | some a => exact List.mem_of_getElem? h

theorem exists_left_of_forall₂' {α β : Type} {r : α → β → Prop} {l₁ : List α}
    {l₂ : List β} (h : List.Forall₂ r l₁ l₂) : ∀ b ∈ l₂, ∃ a ∈ l₁, r a b := by
  induction h with
  | nil => intro b hb; simp at hb
  | cons hab _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons.mpr (Or.inl rfl), hab⟩
    · obtain ⟨a, ha, hr⟩ := ih b hb
      exact ⟨a, List.mem_cons.mpr (Or.inr ha), hr⟩

/-- **The scales of a root's completed system**: the root's scale alone. -/
theorem IsSystemOf.scales_eq_scale {pts : List (V3 κ)} {F : ParData} {R : RootRec}
    {S : PolynomialSystem} (h : IsSystemOf pts F R S) (hF : F.Spec κ) (hU : F.Unique)
    (hF1 : F.box.length = 1) (hR : R.ok pts = true) : PolynomialSystem.scales [S] = {R.scale pts} := by
  obtain ⟨y, hy⟩ := exists_isZero hR
  rw [h.scales_eq hF hU hF1 (P := fun _ ↦ True) ⟨y, hy, trivial⟩, R.scales_explicit pts hF hy,
    RootRec.scale_eq hy]

/-- **Representatives by links**: the completed systems `Ss` of the roots `T` of `R :: Rs` have
the largest scale `N` (`IsRootMax`), and links from root `0` reach every root of `T`: then every
nonempty part of `Ss` has exactly one root per system, all of scale `N`. -/
theorem isRootEq_of_links {pts : List (V3 κ)} {F : ParData} (hF : F.Spec κ) (hU : F.Unique)
    (hF1 : F.box.length = 1) {R : RootRec} {Rs : List RootRec} {N : ℝ}
    (hok : ∀ R' ∈ R :: Rs, R'.ok pts = true) {Ss : List PolynomialSystem}
    (hN : PolynomialSystem.IsRootMax Ss N) (T : List ℕ)
    (hSs : List.Forall₂ (fun i S ↦ IsSystemOf pts F ((R :: Rs).getD i R) S) T Ss)
    (gs : List (ℕ × List (ℕ × LinkRec))) (hl : linkGroupsOk pts (R :: Rs) R [0] gs = true)
    (hT : T.all (fun i ↦ (reached [0] gs).contains i) = true)
    {Reps : List PolynomialSystem} (hne : Reps ≠ []) (hsub : ∀ S ∈ Reps, S ∈ Ss) :
    PolynomialSystem.IsRootEq Reps N := by
  have hok' : ∀ i, ((R :: Rs).getD i R).ok pts = true := fun i ↦ hok _ (getD_mem_cons R Rs i)
  have hsc := scale_of_linkGroupsOk hok' (c := R.scale pts) hl (fun i hi ↦ by
    rw [List.mem_singleton.mp hi]; rfl)
  refine PolynomialSystem.IsRootMax.isRootEq hN (c := R.scale pts) (fun S hS ↦ ?_) hne hsub
  obtain ⟨i, hi, h⟩ := exists_left_of_forall₂' hSs S hS
  have hiT := List.all_eq_true.mp hT i hi
  rw [List.contains_iff_mem] at hiT
  rw [h.scales_eq_scale hF hU hF1 (hok' i), hsc i hiT]

end Reps

end Nieuwland.Root
