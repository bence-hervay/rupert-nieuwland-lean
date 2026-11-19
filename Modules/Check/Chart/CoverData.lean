import Modules.Check.Chart.Cover

/-!
# A property over a cover's leaves, proved along the tree

A cover whose leaves are proved one by one (a root's box cut into natively checked pieces, each a
module with its own theorem) needs the property at every element of `Cover.data`. The proof
follows the tree: `Cover.forall_data_leaf` at a leaf, `Cover.forall_data_split` at a bisection.
Its depth is the tree's, not the number of leaves: a tuple of the leaves' proofs against the list
of their data runs into the elaborator's recursion limit at a few hundred leaves.
-/

namespace Nieuwland.Check.Cover

variable {E : Type}

/-- A property of a leaf's datum holds over the leaf's data. -/
theorem forall_data_leaf {P : E → Prop} {e : E} (h : P e) : ∀ C ∈ (leaf e).data, P C := by
  intro C hC
  rw [data, List.mem_singleton] at hC
  exact hC ▸ h

/-- A property over the data of both halves holds over the data of the bisection. -/
theorem forall_data_split {P : E → Prop} {d : ℕ} {lo hi : Cover E}
    (hl : ∀ C ∈ lo.data, P C) (hh : ∀ C ∈ hi.data, P C) : ∀ C ∈ (split d lo hi).data, P C := by
  intro C hC
  rw [data, List.mem_append] at hC
  exact hC.elim (hl C) (hh C)

end Nieuwland.Check.Cover
