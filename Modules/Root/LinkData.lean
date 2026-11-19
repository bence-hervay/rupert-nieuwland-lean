import Modules.Root.Chain
import Modules.Root.Assembly

/-!
# Links between the roots of a certificate: the data and its checks

A root-form certificate (`Modules/Root/Assembly.lean`) may have several roots of the same scale:
copies of one optimal pose under maps that do not change the contact geometry. A **link** from
root `R` to root `R'` records such a map: for each contact `i` of `R` (plug vertex against hole
edge) the contact `sigma i` of `R'` it goes to, whether the edge's ends swap (`flip`) and, in
centred mode, whether it goes to the antipodal contact (`anti`); and frames of pairs of points
(a point and its image) that fix an isometry of the hole side and one of the plug side.

Everything else is computed and checked here, over the solid's field `κ`:

* `frameIso`: the isometry `x ↦ (M x + b) / d` of a frame (`M = d T` from the adjugate of the
  frame's matrix, no division), the sign `s` of its determinant and a quaternion `q` of its
  rotation (`quatOf`); `Iso.ok`: `d ≠ 0`, `q ≠ 0` and `|q|² s M = d Q(q)`, so that
  `T = (s / |q|²) Q(q)` is orthogonal;
* `Iso.maps`: a point goes to a point, exactly;
* `contactMaps`: a contact's three points go to the image contact's (swapped, or the antipodes,
  as recorded).

`Modules/Root/LinkCheck.lean` adds the target point, the pose map's image of the zero of `R`'s
system coordinate by coordinate as a quotient of expressions in `R`'s variables (`coordE`,
`Modules/Root/Link.lean`), each in the box of `R'`'s Krawczyk test by balls at the zero of `R`
(`quotIn`), and the check of all of these (`linksOk`), and proves that a link that checks gives
the two roots the same scale (`scale_eq_of_linksOk`).
-/

open Nieuwland.Check Finset

namespace Nieuwland.Root

/-- The record of a link from a root to another (module docs). -/
structure LinkRec where
  /-- For each contact of the source, the index of its image among the target's contacts. -/
  sigma : List ℕ
  /-- For each contact, whether the image edge runs the other way. -/
  flip : List Bool
  /-- For each contact (centred mode), whether the image is the antipodal contact. -/
  anti : List Bool
  /-- The hole's frame: pairs (point, its image) of indices of points. -/
  hole : List (ℕ × ℕ)
  /-- `0` for a frame spanning space; `±1` for a planar frame, the sign of the normal's image. -/
  hn : ℤ
  /-- The plug's frame. -/
  plug : List (ℕ × ℕ)
  /-- As `hn`, for the plug's frame. -/
  pn : ℤ
  deriving Repr

section Field

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-- An isometry `x ↦ (M x + b) / d` as exact data, the sign `s` of its determinant and a
quaternion `q` of its rotation `s M / d` (`Iso.ok`). -/
structure Iso (κ : Type) where
  /-- `d` times the linear part. -/
  M : M3 κ
  /-- The denominator. -/
  d : κ
  /-- The sign of the determinant. -/
  s : ℤ
  /-- A quaternion of the rotation `s M / d`. -/
  q : Q4 κ
  /-- `d` times the translation. -/
  b : V3 κ

/-- `a G`. -/
def smulM (a : κ) (G : M3 κ) : M3 κ := ⟨V3.smul a G.x, V3.smul a G.y, V3.smul a G.z⟩

/-- `quatMatrix` over `κ`. -/
def quatM3 (q : Q4 κ) : M3 κ :=
  let two : κ := Exact.ofInt 2
  ⟨⟨q.w * q.w + q.x * q.x - q.y * q.y - q.z * q.z, two * (q.x * q.y - q.w * q.z),
      two * (q.x * q.z + q.w * q.y)⟩,
    ⟨two * (q.x * q.y + q.w * q.z), q.w * q.w - q.x * q.x + q.y * q.y - q.z * q.z,
      two * (q.y * q.z - q.w * q.x)⟩,
    ⟨two * (q.x * q.z - q.w * q.y), two * (q.y * q.z + q.w * q.x),
      q.w * q.w - q.x * q.x - q.y * q.y + q.z * q.z⟩⟩

/-- A quaternion of the rotation `P / d`: the first of the four standard candidates whose
leading entry is not zero (any choice is checked by `Iso.ok`). -/
def quatOf (P : M3 κ) (d : κ) : Q4 κ :=
  let c0 : Q4 κ := ⟨d + (P.x.x + P.y.y + P.z.z), P.z.y - P.y.z, P.x.z - P.z.x, P.y.x - P.x.y⟩
  let c1 : Q4 κ := ⟨P.z.y - P.y.z, d + P.x.x - P.y.y - P.z.z, P.x.y + P.y.x, P.x.z + P.z.x⟩
  let c2 : Q4 κ := ⟨P.x.z - P.z.x, P.x.y + P.y.x, d - P.x.x + P.y.y - P.z.z, P.y.z + P.z.y⟩
  let c3 : Q4 κ := ⟨P.y.x - P.x.y, P.x.z + P.z.x, P.y.z + P.z.y, d - P.x.x - P.y.y + P.z.z⟩
  if !Exact.isZero c0.w then c0 else if !Exact.isZero c1.x then c1
  else if !Exact.isZero c2.y then c2 else c3

/-- The isometry taking the vectors `x₁ x₂ x₃` (columns of a matrix with determinant `d`) to
`y₁ y₂ y₃`, and the point `x₀` to `y₀` (`lin`: no translation). -/
def isoOfVecs (lin : Bool) (x₀ y₀ x₁ x₂ x₃ y₁ y₂ y₃ : V3 κ) : Iso κ :=
  let adj : M3 κ := ⟨x₂.cross x₃, x₃.cross x₁, x₁.cross x₂⟩
  let d := x₁.dot (x₂.cross x₃)
  let M := (M3.transpose ⟨y₁, y₂, y₃⟩).mul adj
  let s : ℤ := if Exact.pos (M.det * d) then 1 else -1
  let q := quatOf (smulM (Exact.ofInt s) M) d
  let b : V3 κ := if lin then ⟨Exact.ofInt 0, Exact.ofInt 0, Exact.ofInt 0⟩
    else (V3.smul d y₀).sub (M.mulVec x₀)
  ⟨M, d, s, q, b⟩

/-- The isometry of a frame of pairs of points of `pts` (module docs): four pairs, or three and
the sign `n` of the normal's image (general mode); three pairs, or two and `n` (`lin`: centred
mode, linear maps). -/
def frameIso (pts : List (V3 κ)) (lin : Bool) (prs : List (ℕ × ℕ)) (n : ℤ) : Option (Iso κ) :=
  let P := Exact.pt pts
  let nv (u v : V3 κ) (sg : ℤ) : V3 κ := V3.smul (Exact.ofInt sg) (u.cross v)
  match lin, prs with
  | false, [(a₀, b₀), (a₁, b₁), (a₂, b₂), (a₃, b₃)] =>
    if n = 0 then
      some (isoOfVecs false (P a₀) (P b₀) ((P a₁).sub (P a₀)) ((P a₂).sub (P a₀))
        ((P a₃).sub (P a₀)) ((P b₁).sub (P b₀)) ((P b₂).sub (P b₀)) ((P b₃).sub (P b₀)))
    else none
  | false, [(a₀, b₀), (a₁, b₁), (a₂, b₂)] =>
    let u₁ := (P a₁).sub (P a₀)
    let u₂ := (P a₂).sub (P a₀)
    let v₁ := (P b₁).sub (P b₀)
    let v₂ := (P b₂).sub (P b₀)
    if n = 0 then none else some (isoOfVecs false (P a₀) (P b₀) u₁ u₂ (nv u₁ u₂ 1) v₁ v₂ (nv v₁ v₂ n))
  | true, [(a₀, b₀), (a₁, b₁), (a₂, b₂)] =>
    if n = 0 then some (isoOfVecs true (P a₀) (P b₀) (P a₀) (P a₁) (P a₂) (P b₀) (P b₁) (P b₂))
    else none
  | true, [(a₀, b₀), (a₁, b₁)] =>
    if n = 0 then none
    else some (isoOfVecs true (P a₀) (P b₀) (P a₀) (P a₁) (nv (P a₀) (P a₁) 1) (P b₀) (P b₁)
      (nv (P b₀) (P b₁) n))
  | _, _ => none

namespace Iso

/-- The checks of an isometry's data: `d ≠ 0`, `q ≠ 0`, a sign, and `|q|² s M = d Q(q)`. -/
def ok (I : Iso κ) : Bool :=
  Exact.pos (I.d * I.d) && Exact.pos I.q.norm2 && (I.s == 1 || I.s == -1) &&
    M3.eqb (smulM (I.q.norm2 * Exact.ofInt I.s) I.M) (smulM I.d (quatM3 I.q))

/-- `p` is the image of `v`: `d p = M v + b`. -/
def maps (I : Iso κ) (v p : V3 κ) : Bool :=
  Exact.eqV (V3.smul I.d p) ((I.M.mulVec v).add I.b)

end Iso

/-- `-v`. -/
def negV3 (v : V3 κ) : V3 κ := V3.smul (Exact.ofInt (-1)) v

/-- The image of a point: itself, or its antipode. -/
def signedPt (pts : List (V3 κ)) (anti : Bool) (j : ℕ) : V3 κ :=
  if anti then negV3 (Exact.pt pts j) else Exact.pt pts j

/-- Contact `i` of `cs` goes to contact `j` of `cs'`: the hole edge's ends by `H`, swapped if
`fl`, the plug vertex by `G`, all to the antipodes if `an`. -/
def contactMaps (pts : List (V3 κ)) (H G : Iso κ) (c c' : ℕ × ℕ × ℕ) (fl an : Bool) : Bool :=
  let (wa, wb) := if fl then (c'.2.1, c'.1) else (c'.1, c'.2.1)
  H.maps (Exact.pt pts c.1) (signedPt pts an wa) && H.maps (Exact.pt pts c.2.1) (signedPt pts an wb) &&
    G.maps (Exact.pt pts c.2.2) (signedPt pts an c'.2.2)

end Field

end Nieuwland.Root
