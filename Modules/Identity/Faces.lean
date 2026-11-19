import Modules.Identity.Hull
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.GetD

/-!
# Facet certificates

A **facet certificate** for finitely many points `pts` of space lists faces: each a cycle of
indices into `pts` and a plane `n ⬝ᵥ x = h` (`Face`). `IsFaceCert pts faces` says, in plain
geometric terms:

* every face is a facet (`Face.IsFacet`): all points satisfy `n ⬝ᵥ x ≤ h`, with equality exactly
  for the face's points, and these lie in strictly convex position in the listed cyclic order,
  counterclockwise seen from the side `n` points to;
* faces flagged regular are equilateral and equiangular (`Face.IsRegular`);
* the faces' point sets are pairwise different, and each point lies on three faces that have only
  it in common (combinatorial data `CombOk`);
* every edge `(a, b)` of a face appears reversed, `(b, a)`, in a face that shares only `a` and `b`
  with it, and no directed edge appears twice.

From these the module proves what a reader expects of a polytope's face structure:

* the points are distinct and are exactly the extreme points of their hull
  (`IsFaceCert.nodup`, `IsFaceCert.extremePoints_eq`);
* each face's plane supports the hull and meets it exactly in the hull of the face's points
  (`Face.IsFacet.le_of_mem_hull`, `Face.IsFacet.hull_inter_eq`), which is two-dimensional (three
  of its points are not collinear: `Face.IsFacet.n_ne_zero` and `Face.IsFacet.left`);
* the listed faces are pairwise different subsets of the hull (`IsFaceCert.facets_pairwise_ne`);
* each edge of a face is an edge of the hull: a supporting plane meets the hull exactly in the
  segment between its two (different) ends (`IsFaceCert.edge`).

`Polyhedron.HasFaces P V E kinds s` is the summary for a polyhedron `P`: its hull is the hull of
`V` of its given points with such a certificate (these are then its extreme points), whose faces
have `2 E` sides in all, sorted into `kinds` (side counts, regularity, numbers), all edges of
squared length `s` if `s` is given.

**Completeness of the face list** is not formalised. The classical argument: every edge of a
three-dimensional polytope lies in exactly two of its facets, and its facets are connected through
shared edges. If a facet `G` of the hull were missing from a nonempty list, some missing facet
would share an edge `e` with a listed facet `F`; `e` is an edge of the polygon `F`, so the list
also contains the facet across `e` (`IsFaceCert.closed`, and different from `F`), which must then
be `G`. Hence the list holds every facet, and the counts of `HasFaces` are the polytope's.
-/

open Matrix

namespace Nieuwland.Identity

/-- The directed edges of a cycle of indices `[c₀, …, c_{k-1}]`: `(cᵢ, cᵢ₊₁)`, and
`(c_{k-1}, c₀)`. -/
def cycEdges (c : List ℕ) : List (ℕ × ℕ) :=
  c.zip (c.rotate 1)

/-- The corners of a cycle: `(cᵢ, cᵢ₊₁, cᵢ₊₂)`, indices modulo the length. -/
def cycCorners (c : List ℕ) : List (ℕ × ℕ × ℕ) :=
  c.zip ((c.rotate 1).zip (c.rotate 2))

/-- The point with index `i` (`0` past the end; certificates use indices below the length). -/
def pt (pts : List (Fin 3 → ℝ)) (i : ℕ) : Fin 3 → ℝ :=
  pts.getD i 0

/-- The squared Euclidean distance. -/
def dist2 (x y : Fin 3 → ℝ) : ℝ :=
  (x - y) ⬝ᵥ (x - y)

/-- A face of the hull of a list of points: the indices of its vertices in cyclic order and a
plane `n ⬝ᵥ x = h`; `reg` says that the face is claimed regular. -/
structure Face where
  /-- The indices of the face's points, in cyclic order. -/
  cyc : List ℕ
  /-- The outward normal. -/
  n : Fin 3 → ℝ
  /-- The offset: the plane is `n ⬝ᵥ x = h`. -/
  h : ℝ
  /-- The face is claimed regular. -/
  reg : Bool

variable (pts : List (Fin 3 → ℝ))

/-- **A facet of the hull of `pts`, with its vertices in convex position.** At least three
distinct indices of points; every point satisfies `n ⬝ᵥ x ≤ h`, with equality exactly for the
face's points; and for each edge `(a, b)` of the cycle, every other point `x` of the face lies
strictly to its left seen from the side `n` points to: `((b - a) ⨯₃ (x - a)) ⬝ᵥ n > 0`. -/
structure Face.IsFacet (F : Face) : Prop where
  three : 3 ≤ F.cyc.length
  nodup : F.cyc.Nodup
  lt : ∀ i ∈ F.cyc, i < pts.length
  le : ∀ i < pts.length, F.n ⬝ᵥ pt pts i ≤ F.h
  eq_iff : ∀ i < pts.length, F.n ⬝ᵥ pt pts i = F.h ↔ i ∈ F.cyc
  left : ∀ e ∈ cycEdges F.cyc, ∀ j ∈ F.cyc, j ≠ e.1 → j ≠ e.2 →
    0 < ((pt pts e.2 - pt pts e.1) ⨯₃ (pt pts j - pt pts e.1)) ⬝ᵥ F.n

/-- **A regular polygon**: equilateral and equiangular. At each corner `(a, b, c)` the side `ab`
has squared length `s` and `(a - b) ⬝ᵥ (c - b) = t`; with all sides equal, equal dot products are
equal angles. -/
def Face.IsRegular (F : Face) : Prop :=
  ∃ s t : ℝ, ∀ τ ∈ cycCorners F.cyc, dist2 (pt pts τ.1) (pt pts τ.2.1) = s ∧
    (pt pts τ.1 - pt pts τ.2.1) ⬝ᵥ (pt pts τ.2.2 - pt pts τ.2.1) = t

/-- The combinatorial part of a facet certificate, on the faces' cycles of indices into `np`
points. -/
structure CombOk (cycs : List (List ℕ)) (np : ℕ) : Prop where
  /-- Of two listed faces, the first has a point that the second does not. -/
  distinct : cycs.Pairwise fun c d ↦ ∃ i ∈ c, i ∉ d
  /-- Every point lies on three faces that have only it in common. -/
  vertex : ∀ i < np, ∃ c ∈ cycs, ∃ d ∈ cycs, ∃ e ∈ cycs, i ∈ c ∧ i ∈ d ∧ i ∈ e ∧
    ∀ j ∈ c, j ∈ d → j ∈ e → j = i
  /-- Every directed edge `(a, b)` of a face is reversed in a face that has only `a` and `b` in
  common with it. -/
  closed : ∀ c ∈ cycs, ∀ e ∈ cycEdges c, ∃ d ∈ cycs, e.swap ∈ cycEdges d ∧
    ∀ j ∈ c, j ∈ d → j = e.1 ∨ j = e.2
  /-- No directed edge occurs twice. -/
  edges_nodup : (cycs.flatMap cycEdges).Nodup

/-- **A facet certificate** for the points `pts` (module docs). -/
structure IsFaceCert (faces : List Face) : Prop where
  facet : ∀ F ∈ faces, F.IsFacet pts
  regular : ∀ F ∈ faces, F.reg = true → F.IsRegular pts
  comb : CombOk (faces.map Face.cyc) pts.length

/-- The faces sorted into kinds `(k, r, m)`: `m` faces with `k` sides whose flag `reg` is `r`,
every face in one kind. -/
def KindsOk (faces : List Face) (kinds : List (ℕ × Bool × ℕ)) : Prop :=
  (kinds.map fun κ ↦ (κ.1, κ.2.1)).Nodup ∧ faces.length = (kinds.map fun κ ↦ κ.2.2).sum ∧
    ∀ κ ∈ kinds, (faces.filter fun F ↦ F.cyc.length == κ.1 && F.reg == κ.2.1).length = κ.2.2

/-- Every edge of every face has squared length `s`, if `s` is given. -/
def EdgesOk (faces : List Face) : Option ℝ → Prop
  | none => True
  | some s => ∀ F ∈ faces, ∀ e ∈ cycEdges F.cyc, dist2 (pt pts e.1) (pt pts e.2) = s

end Nieuwland.Identity

namespace Nieuwland

open Identity

/-- **The face structure of a polyhedron** (module docs of `Modules/Identity/Faces.lean`): the hull
of `P` is the hull of `V` of its points with a facet certificate, whose faces have `2 E` sides in
all, sorted into `kinds` (`(k, true, m)`: `m` regular faces with `k` sides; `(k, false, m)`: `m`
faces with `k` sides not claimed regular), every edge of squared length `s` if `s` is given. These
`V` points are then exactly the extreme points of the hull (`HasFaces.extremePoints_eq`); any other
given point of `P` lies in the hull of them. -/
def Polyhedron.HasFaces (P : Polyhedron) (V E : ℕ) (kinds : List (ℕ × Bool × ℕ))
    (s : Option ℝ) : Prop :=
  ∃ pts : List (Fin 3 → ℝ), ∃ faces : List Face, (∀ x ∈ pts, x ∈ P.vertices) ∧
    P.hull = convexHull ℝ {x | x ∈ pts} ∧ pts.length = V ∧ IsFaceCert pts faces ∧
    2 * E = (faces.map fun F ↦ F.cyc.length).sum ∧ KindsOk faces kinds ∧ EdgesOk pts faces s

end Nieuwland

namespace Nieuwland.Identity

variable {pts : List (Fin 3 → ℝ)}

/-! ### Cycles -/

theorem fst_mem_of_mem_cycEdges {c : List ℕ} {e : ℕ × ℕ} (h : e ∈ cycEdges c) : e.1 ∈ c :=
  (List.of_mem_zip h).1

theorem snd_mem_of_mem_cycEdges {c : List ℕ} {e : ℕ × ℕ} (h : e ∈ cycEdges c) : e.2 ∈ c :=
  (List.mem_rotate.mp (List.of_mem_zip h).2)

/-- The ends of an edge of a cycle without repetitions and of length at least two differ. -/
theorem fst_ne_snd_of_mem_cycEdges {c : List ℕ} (hc : c.Nodup) (h2 : 2 ≤ c.length) {e : ℕ × ℕ}
    (h : e ∈ cycEdges c) : e.1 ≠ e.2 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp h
  have hk' : k < c.length := by simpa [cycEdges] using hk
  simp only [cycEdges, List.getElem_zip, List.getElem_rotate]
  intro heq
  have := (hc.getElem_inj_iff (hi := hk') (hj := Nat.mod_lt _ (by omega))).mp heq
  rcases Nat.lt_or_ge (k + 1) c.length with h₁ | h₁
  · rw [Nat.mod_eq_of_lt h₁] at this
    omega
  · have h0 : (k + 1) % c.length = 0 := by
      rw [show k + 1 = c.length by omega, Nat.mod_self]
    omega

/-- The points of a list, as indices. -/
theorem exists_pt_of_mem {x : Fin 3 → ℝ} (hx : x ∈ pts) : ∃ i < pts.length, pt pts i = x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  exact ⟨i, hi, by simp [pt, List.getElem?_eq_getElem hi]⟩

theorem pt_mem {i : ℕ} (hi : i < pts.length) : pt pts i ∈ pts := by
  simp [pt, List.getElem?_eq_getElem hi]

/-! ### Facets -/

namespace Face.IsFacet

variable {F : Face} (hF : F.IsFacet pts)
include hF

/-- The normal of a facet is not zero. -/
theorem n_ne_zero : F.n ≠ 0 := by
  obtain ⟨a, b, j, l, hc⟩ : ∃ a b j l, F.cyc = a :: b :: j :: l := by
    match h : F.cyc, hF.three with
    | a :: b :: j :: l, _ => exact ⟨a, b, j, l, rfl⟩
  have hn := hF.nodup
  rw [hc] at hn
  have he : (a, b) ∈ cycEdges F.cyc := by simp [hc, cycEdges, List.rotate_cons_succ]
  have := hF.left _ he j (by simp [hc]) (by simp at hn; tauto) (by simp at hn; tauto)
  intro h0
  rw [h0, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- The hull lies on the side `n ⬝ᵥ x ≤ h` of the facet's plane. -/
theorem le_of_mem_hull {x : Fin 3 → ℝ} (hx : x ∈ convexHull ℝ {y | y ∈ pts}) : F.n ⬝ᵥ x ≤ F.h :=
  le_of_mem_convexHull (fun v hv ↦ by
    obtain ⟨i, hi, rfl⟩ := exists_pt_of_mem hv
    exact hF.le i hi) hx

/-- **The facet is the hull of its points**: the plane meets the hull of `pts` exactly in the
hull of the face's points. -/
theorem hull_inter_eq :
    convexHull ℝ {y | y ∈ pts} ∩ {x | F.n ⬝ᵥ x = F.h} =
      convexHull ℝ {x | ∃ i ∈ F.cyc, pt pts i = x} := by
  classical
  have hs : {y | y ∈ pts} = ((pts.toFinset : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) := by
    ext; simp
  rw [hs, convexHull_inter_eq fun v hv ↦ by
    obtain ⟨i, hi, rfl⟩ := exists_pt_of_mem (List.mem_toFinset.mp hv)
    exact hF.le i hi]
  congr 1
  ext x
  simp only [List.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hxh⟩
    obtain ⟨i, hi, rfl⟩ := exists_pt_of_mem hx
    exact ⟨i, (hF.eq_iff i hi).mp hxh, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨pt_mem (hF.lt i hi), (hF.eq_iff i (hF.lt i hi)).mpr hi⟩

end Face.IsFacet

/-! ### Certificates -/

namespace IsFaceCert

variable {faces : List Face} (hC : IsFaceCert pts faces)
include hC

omit hC in
/-- The faces of a cycle of the certificate. -/
theorem exists_face {c : List ℕ} (hc : c ∈ faces.map Face.cyc) : ∃ F ∈ faces, F.cyc = c :=
  List.mem_map.mp hc

/-- Two different indices are told apart by a face: on it, one point lies on the plane and the
other strictly below. -/
theorem pt_ne {i j : ℕ} (hi : i < pts.length) (hj : j < pts.length) (hij : i ≠ j) :
    pt pts i ≠ pt pts j := by
  obtain ⟨c, hc, d, hd, e, he, hic, hid, hie, hall⟩ := hC.comb.vertex i hi
  have hsep : ∃ G ∈ faces, i ∈ G.cyc ∧ j ∉ G.cyc := by
    obtain ⟨F, hF, rfl⟩ := exists_face hc
    obtain ⟨G, hG, rfl⟩ := exists_face hd
    obtain ⟨H, hH, rfl⟩ := exists_face he
    by_cases h₁ : j ∈ F.cyc
    · by_cases h₂ : j ∈ G.cyc
      · exact ⟨H, hH, hie, fun h₃ ↦ hij (hall j h₁ h₂ h₃).symm⟩
      · exact ⟨G, hG, hid, h₂⟩
    · exact ⟨F, hF, hic, h₁⟩
  obtain ⟨G, hG, hiG, hjG⟩ := hsep
  have hf := hC.facet G hG
  intro heq
  have h₁ := (hf.eq_iff i hi).mpr hiG
  rw [heq] at h₁
  exact hjG ((hf.eq_iff j hj).mp h₁)

/-- **The points are distinct.** -/
theorem nodup : pts.Nodup := by
  refine List.nodup_iff_injective_get.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ h ↦ ?_
  by_contra hne
  have hij : i ≠ j := fun h' ↦ hne (Fin.ext h')
  refine hC.pt_ne hi hj hij ?_
  simpa [pt, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] using h

/-- **Every point is an extreme point of the hull**: the sum of the normals of three faces
through it is maximised on the points only there. -/
theorem mem_extremePoints {i : ℕ} (hi : i < pts.length) :
    pt pts i ∈ (convexHull ℝ {y | y ∈ pts}).extremePoints ℝ := by
  classical
  obtain ⟨c, hc, d, hd, e, he, hic, hid, hie, hall⟩ := hC.comb.vertex i hi
  obtain ⟨F, hF, rfl⟩ := exists_face hc
  obtain ⟨G, hG, rfl⟩ := exists_face hd
  obtain ⟨H, hH, rfl⟩ := exists_face he
  have f₁ := hC.facet F hF
  have f₂ := hC.facet G hG
  have f₃ := hC.facet H hH
  have hs : {y | y ∈ pts} = ((pts.toFinset : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) := by
    ext; simp
  rw [hs]
  have hle : ∀ v ∈ pts.toFinset, (F.n + G.n + H.n) ⬝ᵥ v ≤ F.h + G.h + H.h := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := exists_pt_of_mem (List.mem_toFinset.mp hv)
    simp only [add_dotProduct]
    linarith [f₁.le j hj, f₂.le j hj, f₃.le j hj]
  refine mem_extremePoints_of_contact (List.mem_toFinset.mpr (pt_mem hi)) hle fun v hv ↦ ?_
  obtain ⟨j, hj, rfl⟩ := exists_pt_of_mem (List.mem_toFinset.mp hv)
  simp only [add_dotProduct]
  constructor
  · intro h
    have e₁ := f₁.le j hj
    have e₂ := f₂.le j hj
    have e₃ := f₃.le j hj
    have hj₁ := (f₁.eq_iff j hj).mp (by linarith)
    have hj₂ := (f₂.eq_iff j hj).mp (by linarith)
    have hj₃ := (f₃.eq_iff j hj).mp (by linarith)
    rw [hall j hj₁ hj₂ hj₃]
  · intro h
    rw [h, (f₁.eq_iff i hi).mpr hic, (f₂.eq_iff i hi).mpr hid, (f₃.eq_iff i hi).mpr hie]

/-- **The points are exactly the extreme points of their hull.** -/
theorem extremePoints_eq :
    (convexHull ℝ {y | y ∈ pts}).extremePoints ℝ = {y | y ∈ pts} := by
  refine Set.Subset.antisymm extremePoints_convexHull_subset fun x hx ↦ ?_
  obtain ⟨i, hi, rfl⟩ := exists_pt_of_mem hx
  exact hC.mem_extremePoints hi

/-- **The listed faces are pairwise different subsets of the hull.** -/
theorem facets_pairwise_ne :
    faces.Pairwise fun F G ↦ convexHull ℝ {y | y ∈ pts} ∩ {x | F.n ⬝ᵥ x = F.h} ≠
      convexHull ℝ {y | y ∈ pts} ∩ {x | G.n ⬝ᵥ x = G.h} := by
  have hd := hC.comb.distinct
  rw [List.pairwise_map] at hd
  refine List.Pairwise.imp_of_mem (fun {F G} hF hG h ↦ ?_) hd
  obtain ⟨i, hi, hiG⟩ := h
  have f₁ := hC.facet F hF
  have f₂ := hC.facet G hG
  have hlt := f₁.lt i hi
  intro heq
  have hmem : pt pts i ∈ convexHull ℝ {y | y ∈ pts} ∩ {x | F.n ⬝ᵥ x = F.h} :=
    ⟨subset_convexHull ℝ _ (pt_mem hlt), (f₁.eq_iff i hlt).mpr hi⟩
  rw [heq] at hmem
  exact hiG ((f₂.eq_iff i hlt).mp hmem.2)

/-- **Edges of faces are edges of the hull**: for an edge `(a, b)` of a face, a supporting plane
(the sum of the planes of the two faces at the edge) meets the hull exactly in the segment
`[a, b]`, and `a ≠ b`. -/
theorem edge {F : Face} (hF : F ∈ faces) {e : ℕ × ℕ} (he : e ∈ cycEdges F.cyc) :
    ∃ w : Fin 3 → ℝ, ∃ c : ℝ, (∀ x ∈ convexHull ℝ {y | y ∈ pts}, w ⬝ᵥ x ≤ c) ∧
      convexHull ℝ {y | y ∈ pts} ∩ {x | w ⬝ᵥ x = c} = segment ℝ (pt pts e.1) (pt pts e.2) ∧
      pt pts e.1 ≠ pt pts e.2 := by
  classical
  have f₁ := hC.facet F hF
  obtain ⟨d, hd, hsw, hmeet⟩ := hC.comb.closed F.cyc (List.mem_map_of_mem hF) e he
  obtain ⟨G, hG, rfl⟩ := exists_face hd
  have f₂ := hC.facet G hG
  have ha₁ := fst_mem_of_mem_cycEdges he
  have hb₁ := snd_mem_of_mem_cycEdges he
  have ha₂ : e.1 ∈ G.cyc := snd_mem_of_mem_cycEdges hsw
  have hb₂ : e.2 ∈ G.cyc := fst_mem_of_mem_cycEdges hsw
  have hs : {y | y ∈ pts} = ((pts.toFinset : Finset (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) := by
    ext; simp
  have hle : ∀ v ∈ pts.toFinset, (F.n + G.n) ⬝ᵥ v ≤ F.h + G.h := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := exists_pt_of_mem (List.mem_toFinset.mp hv)
    simp only [add_dotProduct]
    linarith [f₁.le j hj, f₂.le j hj]
  refine ⟨F.n + G.n, F.h + G.h, fun x hx ↦ ?_, ?_, ?_⟩
  · rw [hs] at hx
    exact le_of_mem_convexHull hle hx
  · rw [hs]
    refine convexHull_inter_eq_segment (List.mem_toFinset.mpr (pt_mem (f₁.lt _ ha₁)))
      (List.mem_toFinset.mpr (pt_mem (f₁.lt _ hb₁))) hle fun v hv ↦ ?_
    obtain ⟨j, hj, rfl⟩ := exists_pt_of_mem (List.mem_toFinset.mp hv)
    simp only [add_dotProduct]
    constructor
    · intro h
      have e₁ := f₁.le j hj
      have e₂ := f₂.le j hj
      rcases hmeet j ((f₁.eq_iff j hj).mp (by linarith)) ((f₂.eq_iff j hj).mp (by linarith))
        with h' | h'
      · exact Or.inl (h' ▸ rfl)
      · exact Or.inr (h' ▸ rfl)
    · rintro (h | h)
      · rw [h, (f₁.eq_iff _ (f₁.lt _ ha₁)).mpr ha₁, (f₂.eq_iff _ (f₁.lt _ ha₁)).mpr ha₂]
      · rw [h, (f₁.eq_iff _ (f₁.lt _ hb₁)).mpr hb₁, (f₂.eq_iff _ (f₁.lt _ hb₁)).mpr hb₂]
  · exact hC.pt_ne (f₁.lt _ ha₁) (f₁.lt _ hb₁)
      (fst_ne_snd_of_mem_cycEdges f₁.nodup (by have := f₁.three; omega) he)

end IsFaceCert

end Nieuwland.Identity

namespace Nieuwland.Polyhedron

open Identity

variable {P : Polyhedron} {V E : ℕ} {kinds : List (ℕ × Bool × ℕ)} {s : Option ℝ}

/-- **The extreme points of the hull are the certificate's points**, which are given points of
`P`. -/
theorem HasFaces.extremePoints_eq (h : P.HasFaces V E kinds s) :
    ∃ pts : List (Fin 3 → ℝ), pts.Nodup ∧ pts.length = V ∧ (∀ x ∈ pts, x ∈ P.vertices) ∧
      P.hull.extremePoints ℝ = {x | x ∈ pts} := by
  obtain ⟨pts, faces, hsub, hhull, hV, hC, -⟩ := h
  exact ⟨pts, hC.nodup, hV, hsub, by rw [hhull, hC.extremePoints_eq]⟩

/-- **`P` has `V` vertices**: its hull has `V` extreme points. -/
theorem HasFaces.ncard_extremePoints (h : P.HasFaces V E kinds s) :
    (P.hull.extremePoints ℝ).ncard = V := by
  classical
  obtain ⟨pts, hnd, hV, -, he⟩ := h.extremePoints_eq
  rw [he, ← hV, ← List.toFinset_card_of_nodup hnd, ← Set.ncard_coe_finset]
  congr 1
  ext; simp

end Nieuwland.Polyhedron
