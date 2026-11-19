import Polyhedra.Other.Tom7Septopert.Proof.Points
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk0
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk1
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk2
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk3
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk4
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk5
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk6
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk7
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk8
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk9
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk10
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk11
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk12
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk13
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk14
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk15
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk16
import Polyhedra.Other.Tom7Septopert.Certificates.Chunk17
import Modules.Certificate.Whole

set_option linter.style.longLine false

/-!
# Exported nodes

Nodes of the cover of
`gs://main-69696-data/noperts-results/x1-2026-10-29/septopert-guided/certificate.jsonl`, assembled
from 18 chunks: 318606 items, 318606 of them checked (224720 checks); unsupported: none. Generated
by `code/lean-export`. The nodes: `Node0`: root 0, path ``; `Node1`: root 1, path ``; `Node2`: root
2, path ``; `Node3`: root 3, path ``; `Node4`: root 4, path ``; `Node5`: root 5, path ``; `Node6`:
root 6, path ``; `Node7`: root 7, path ``; `Node8`: root 8, path ``; `Node9`: root 9, path ``;
`Node10`: root 10, path ``; `Node11`: root 11, path ``.
-/

open Nieuwland.Check Nieuwland.Cert

/-!
## Node 0

The node at path `` of root 0: 187559 items in 6 chunks, 187559 of them checked (98372 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node0

/-- The box of the node. -/
def box : ChartBox :=
  ⟨0, 0, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.split 0
    (.split 1
      (.split 2
        (.split 3
          (.split 4
            (.leaf (Chunk0.box, Chunk0.missing))
            (.leaf (Chunk1.box, Chunk1.missing)))
          (.leaf (Chunk2.box, Chunk2.missing)))
        (.leaf (Chunk3.box, Chunk3.missing)))
      (.leaf (Chunk4.box, Chunk4.missing)))
    (.leaf (Chunk5.box, Chunk5.missing)))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    ⟨Chunk0.settled, Chunk1.settled, Chunk2.settled, Chunk3.settled, Chunk4.settled, Chunk5.settled⟩ hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node0

/-!
## Node 1

The node at path `` of root 1: 3818 items in 1 chunk, 3818 of them checked (3818 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node1

/-- The box of the node. -/
def box : ChartBox :=
  ⟨0, 1, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk6.box, Chunk6.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk6.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node1

/-!
## Node 2

The node at path `` of root 2: 3947 items in 1 chunk, 3947 of them checked (3947 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node2

/-- The box of the node. -/
def box : ChartBox :=
  ⟨0, 2, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk7.box, Chunk7.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk7.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node2

/-!
## Node 3

The node at path `` of root 3: 4115 items in 1 chunk, 4115 of them checked (4115 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node3

/-- The box of the node. -/
def box : ChartBox :=
  ⟨0, 3, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk8.box, Chunk8.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk8.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node3

/-!
## Node 4

The node at path `` of root 4: 7119 items in 1 chunk, 7119 of them checked (6913 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node4

/-- The box of the node. -/
def box : ChartBox :=
  ⟨1, 0, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk9.box, Chunk9.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk9.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node4

/-!
## Node 5

The node at path `` of root 5: 862 items in 1 chunk, 862 of them checked (862 checks); unsupported:
none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node5

/-- The box of the node. -/
def box : ChartBox :=
  ⟨1, 1, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk10.box, Chunk10.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk10.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node5

/-!
## Node 6

The node at path `` of root 6: 1266 items in 1 chunk, 1266 of them checked (1266 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node6

/-- The box of the node. -/
def box : ChartBox :=
  ⟨1, 2, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk11.box, Chunk11.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk11.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node6

/-!
## Node 7

The node at path `` of root 7: 1295 items in 1 chunk, 1295 of them checked (1295 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node7

/-- The box of the node. -/
def box : ChartBox :=
  ⟨1, 3, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk12.box, Chunk12.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk12.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node7

/-!
## Node 8

The node at path `` of root 8: 70251 items in 2 chunks, 70251 of them checked (65757 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node8

/-- The box of the node. -/
def box : ChartBox :=
  ⟨2, 0, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.split 0
    (.leaf (Chunk13.box, Chunk13.missing))
    (.leaf (Chunk14.box, Chunk14.missing)))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    ⟨Chunk13.settled, Chunk14.settled⟩ hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node8

/-!
## Node 9

The node at path `` of root 9: 11098 items in 1 chunk, 11098 of them checked (11098 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node9

/-- The box of the node. -/
def box : ChartBox :=
  ⟨2, 1, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk15.box, Chunk15.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk15.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node9

/-!
## Node 10

The node at path `` of root 10: 12951 items in 1 chunk, 12951 of them checked (12952 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node10

/-- The box of the node. -/
def box : ChartBox :=
  ⟨2, 2, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk16.box, Chunk16.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk16.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node10

/-!
## Node 11

The node at path `` of root 11: 14325 items in 1 chunk, 14325 of them checked (14325 checks);
unsupported: none.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert.Node11

/-- The box of the node. -/
def box : ChartBox :=
  ⟨2, 3, ⟨[-1, -1, -1, -1, -1], [1, 1, 1, 1, 1], 1⟩⟩

/-- The chunks: their boxes and unsupported parts. -/
def chunks : Cover (ChartBox × List (Unsupported ℤ)) :=
  (.leaf (Chunk17.box, Chunk17.missing))

theorem chunks_check : chunks.check (fun B c ↦ B.subset c.1) box = true := by
  decide +kernel

/-- The unsupported parts of all chunks. -/
def missing : List (Unsupported ℤ) :=
  chunks.data.flatMap Prod.snd

theorem missing_length : missing.length = 0 := by
  decide +kernel

/-- **The node.** Every pose of its box is settled, if the unsupported parts are. -/
theorem settled (hM : ∀ u ∈ missing, ∀ p ∈ u.region.poses,
    SettledRot points symm (Exact.rePre u.pre) p) :
    ∀ p ∈ box.poses, Settled points symm p :=
  Cover.settled_of_chunks (T := chunks)
    Chunk17.settled hM chunks_check

/-- **The node, unconditionally:** it has no unsupported parts. -/
theorem settled_all : ∀ p ∈ box.poses, Settled points symm p :=
  settled fun u hu ↦ by
    rw [List.length_eq_zero_iff.mp missing_length] at hu
    simp at hu

end Nieuwland.Results.Gen.ExternalTom7Septopert.Node11

/-!
## The certificate

The roots cover the twelve unit chart boxes (`unitsIn`), and every pose of every root is settled:
the polyhedron is not Rupert (`Polyhedron.not_isRupert_of_roots`), and scaled back
(`Nieuwland.Results.Gen.ExternalTom7Septopert.eq_smul`), so is `Other.Tom7Septopert.polyhedron`.
-/

namespace Nieuwland.Results.Gen.ExternalTom7Septopert

/-- The roots of the cover. -/
def roots : List ChartBox :=
  [Node0.box, Node1.box, Node2.box, Node3.box, Node4.box, Node5.box, Node6.box, Node7.box,
   Node8.box, Node9.box, Node10.box, Node11.box]

/-- **The certificate**: the polyhedron of Lean's points is not Rupert. -/
theorem not_isRupert : ¬ (Polyhedron.ofPoints points).IsRupert :=
  Polyhedron.not_isRupert_of_roots span_ok (roots := roots) (by decide +kernel)
    ⟨Node0.settled_all, Node1.settled_all, Node2.settled_all, Node3.settled_all, Node4.settled_all,
    Node5.settled_all, Node6.settled_all, Node7.settled_all, Node8.settled_all, Node9.settled_all,
    Node10.settled_all, Node11.settled_all⟩

end Nieuwland.Results.Gen.ExternalTom7Septopert

namespace Nieuwland.Polyhedra

/-- **Septopert (Tom 7) is not Rupert.** -/
theorem externalTom7Septopert_not_isRupert : ¬ Other.Tom7Septopert.polyhedron.IsRupert := by
  rw [Nieuwland.Results.Gen.ExternalTom7Septopert.eq_smul, Polyhedron.isRupert_smul_iff (by norm_num)]
  exact Nieuwland.Results.Gen.ExternalTom7Septopert.not_isRupert

end Nieuwland.Polyhedra
