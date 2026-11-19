import Modules.Check.Leaf.Global

/-!
# Whole certificates

A whole certificate covers the twelve unit chart boxes with its roots, each the box of a node
proved settled from its chunks (`Cover.settled_of_chunks`, `Modules/Certificate/Chunk.lean`). The roots
are data: `unitsIn` checks that every unit chart box lies in one of them, and
`Polyhedron.not_isRupert_of_roots` concludes from the spanning check and the settled roots that
the polyhedron is not Rupert (`Polyhedron.not_isRupert_of_settled`). The exporter
(`code/lean-export cert --whole`) writes this as the final theorem of a certificate, scaled back to
the fixture's polyhedron.
-/

namespace Nieuwland.Check

section Roots

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- Every unit chart box lies in one of the boxes `roots`. -/
def unitsIn (roots : List ChartBox) : Bool :=
  ([0, 1, 2] : List (Fin 3)).all fun a ↦ ([0, 1, 2, 3] : List (Fin 4)).all fun k ↦
    roots.any fun B ↦ (ChartBox.unit a k).subset B

/-- **Whole certificates.** If the points span space, every unit chart box lies in one of the
boxes `roots`, and every pose of every root is settled, the polyhedron is not Rupert. -/
theorem Polyhedron.not_isRupert_of_roots [Countable κ] {pts : List (V3 κ)} {D : SymmData κ}
    {i j k l : ℕ} (hspan : spanOk pts i j k l = true) {roots : List ChartBox}
    (hroots : unitsIn roots = true) (h : roots.Forall fun B ↦ ∀ p ∈ B.poses, Settled pts D p) :
    ¬ (Polyhedron.ofPoints pts).IsRupert := by
  refine Polyhedron.not_isRupert_of_settled (D := D) hspan fun a k p hp ↦ ?_
  simp only [unitsIn, List.all_eq_true, List.any_eq_true] at hroots
  obtain ⟨B, hB, hsub⟩ := hroots a (by fin_cases a <;> simp) k (by fin_cases k <;> simp)
  exact List.forall_iff_forall_mem.mp h B hB p (ChartBox.poses_subset hsub hp)

end Roots

end Nieuwland.Check
