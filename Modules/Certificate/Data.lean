import Mathlib.Init

/-!
# Certificate data

The records of a format-1 certificate stream (`code/src/proof/stream.rs`) as Lean data, one
constructor per Rust variant: solids over every field, chart boxes (pre-rotated ones included),
every evidence schema with its zoom and chart trees, decisions, and cover leaves. The exporter
`code/lean-export` writes them from the checker crate's own types with exhaustive matches, so a
new Rust variant does not compile until it is exported here or listed as unsupported.

These types only hold data. Checked evidence is translated to the check types of
`Nieuwland/Check/` (integers over a common denominator); data without a proved Lean check is kept in
this form and listed (`Modules/Certificate/Chunk.lean`), so nothing is dropped silently. Numbers are
exact: rationals `num / den` as written in the stream, field elements as power-basis
coefficients (`code/src/io.rs`).
-/

namespace Nieuwland.Cert

/-- A rational `num / den`, as written in the stream. -/
structure Q where
  /-- The numerator. -/
  num : Int
  /-- The denominator. -/
  den : Nat

/-- A field element: its power-basis coefficients, constant term first. -/
abbrev Elem := List Q

/-- The coefficient field of a solid (`FieldSpec` in `code/src/math/scalar.rs`). -/
inductive FieldSpec where
  /-- The rationals. -/
  | rational
  /-- `ℚ(√d)`, with the positive square root. -/
  | quadratic (d : Nat)
  /-- `ℚ[g]/(m)` with `g` the real root of `m` in the open interval `(lo, hi)`; `poly` lists the
  coefficients of `m`, constant term first. -/
  | numberField (poly : List Q) (lo hi : Q)

/-- A solid file: points with coordinates in the field. -/
structure SolidFile where
  /-- The name. -/
  name : String
  /-- The field. -/
  field : FieldSpec
  /-- The input points, three coordinates each. -/
  points : List (List Elem)

/-- A declared pose map (`SymSpec` in `code/src/proof/symmetry.rs`): two matrices, row-major. -/
structure SymSpec where
  /-- The first matrix. -/
  g1 : List Elem
  /-- The second matrix. -/
  g2 : List Elem

/-- The orbit score `alpha cos²(u, w) + q₀² / |q|²` (`ScoreSpec`). -/
structure ScoreSpec where
  /-- The direction `w`. -/
  w : List Q
  /-- The weight `alpha`. -/
  alpha : Q

/-- A chart box (`ChartBox` in `code/src/proof/mod.rs`): charts, the box of chart coordinates
`(s, t, x₁, x₂, x₃)`, and an optional pre-rotation quaternion. -/
structure CBox where
  /-- The view chart. -/
  view : Nat
  /-- The rotation chart. -/
  rot : Nat
  /-- The lower ends. -/
  lo : List Q
  /-- The upper ends. -/
  hi : List Q
  /-- The pre-rotation quaternion, if any. -/
  pre : Option (List Elem)

/-- A polynomial over the field (`PolyData` in `code/src/proof/tree.rs`). -/
structure PolyData where
  /-- The number of variables. -/
  nvars : Nat
  /-- The terms: exponents and coefficients. -/
  terms : List (List Nat × Elem)

mutual

/-- Evidence on a chart box (`BoxEvidence` in `code/src/proof/regional.rs`). -/
inductive BoxEvidence where
  /-- `CentredSupport`. -/
  | centred (dir : Nat × Nat) (anchors : List Nat) (plug : Nat)
  /-- `BalancedSupport`. -/
  | balanced (dirs : List (Nat × Nat)) (anchors : List (List Nat)) (plugs : List Nat)
      (sigma : Int)
  /-- `WidthSupport`. -/
  | width (c : List Elem) (anchors : List (List Nat)) (plugs : List Nat)
  /-- `PolarZoom`: faces `(axis, upper, tree)`. -/
  | polar (centre : List Elem) (faces : List (Nat × Bool × FaceTree))
  /-- `WeightedZoom`: faces `(coord, upper, tree)`. -/
  | weighted (centre : List Elem) (viewFrame rotFrame : List (List Elem)) (weights : List Nat)
      (faces : List (Nat × Bool × WTree))
  /-- `ChartTree`. -/
  | chartTree (tree : Tree)

/-- A face tree of a polar zoom (`FaceTree` in `regional/zoom.rs`). -/
inductive FaceTree where
  /-- A leaf. -/
  | leaf (w : BoxEvidence)
  /-- A split. -/
  | split (dim : Nat) (lo hi : FaceTree)

/-- A face tree of a weighted zoom (`WTree` in `regional/wzoom.rs`). -/
inductive WTree where
  /-- An obstruction leaf. -/
  | leaf (w : BoxEvidence)
  /-- A nonnegative combination of witnesses. -/
  | combo (ws : List BoxEvidence) (weights : List Q)
  /-- Global exclusion. -/
  | excluded (sym : Nat)
  /-- Local exclusion. -/
  | localExcluded (sym : Nat)
  /-- Outside the claim box. -/
  | outside (coord : Nat) (upper : Bool)
  /-- A split. -/
  | split (dim : Nat) (lo hi : WTree)
  /-- A nested zoom: faces `(coord, upper, tree)`. -/
  | nested (coords : List Nat) (centre : List Q) (weights : List Nat)
      (faces : List (Nat × Bool × WTree))

/-- A chart tree (`Tree` in `code/src/proof/tree.rs`). -/
inductive Tree where
  /-- S1. -/
  | split (slot : Nat) (at_ : Q) (lo hi : Tree)
  /-- S2a. -/
  | affine (slots : List Nat) (m : List (List Elem)) (kappa : List Elem) (lo hi : List Q)
      (child : Tree)
  /-- S2b. -/
  | rechart (a : List (List Elem)) (b : List Elem) (psi : List PolyData)
      (d lamU lamQ : PolyData) (lo hi : List Q) (child : Tree)
  /-- S3: faces `(slot, upper, tree)`. -/
  | blowUp (slots : List Nat) (centre : List Q) (weights : List Nat) (rho : Nat)
      (faces : List (Nat × Bool × Tree))
  /-- L1. -/
  | obstruction (w : BoxEvidence)
  /-- L2. -/
  | combination (ws : List BoxEvidence) (weights : List Q)
  /-- L3. -/
  | outside (coord : Nat) (upper : Bool)
  /-- L4. -/
  | excluded (sym : Nat)
  /-- Search state. -/
  | open_ (note : String)

end

/-- A learned label of a decision (`Label` in `code/src/complete/labels.rs`). -/
inductive Label where
  /-- Support pair `(a, b)` and plug `j`. -/
  | centred (a b j : Nat)
  /-- Three terms `[aᵢ, bᵢ, jᵢ]` and the sign of the weights. -/
  | balanced (terms : List (List Nat)) (sigma : Int)

/-- The budget of a decision (`DecisionBudget`). -/
structure Budget where
  /-- `max_cells`. -/
  maxCells : Nat
  /-- `max_degree`. -/
  maxDegree : Nat
  /-- `max_terms`. -/
  maxTerms : Nat

/-- A complete-route decision (`Decision` in `code/src/proof/cert.rs`). -/
structure Decision where
  /-- The region; the decision concerns its open interior. -/
  region : CBox
  /-- `formulation`. -/
  formulation : String
  /-- `supports`. -/
  supports : String
  /-- `projection`. -/
  projection : String
  /-- `backend`. -/
  backend : String
  /-- `compiler`. -/
  compiler : String
  /-- The learned labels, if any. -/
  labels : Option (List Label)
  /-- The budget, if recorded. -/
  budget : Option Budget
  /-- The variable order, if recorded. -/
  order : Option (List String)
  /-- The solid's identity, if recorded. -/
  solidIdentity : Option String

/-- How a cover leaf is discharged (`LeafRec` in `stream.rs`: exactly one of its fields). -/
inductive Discharge where
  /-- Evidence for the leaf's own box. -/
  | ev (e : BoxEvidence)
  /-- A claim, by id. -/
  | claim (id : String)
  /-- A mapped leaf: the pose map `sym` sends the box into the region of the claim `id`. -/
  | mapped (sym : Nat) (id : String)
  /-- An excluded leaf. -/
  | excluded (sym : Nat)
  /-- A decision, by id. -/
  | decided (id : String)
  /-- An open leaf. -/
  | open_ (note : String)

end Nieuwland.Cert
