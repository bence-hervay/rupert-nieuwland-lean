import Modules.Identity.Solids
import Modules.Identity.Check
import Modules.Check.Number.Theta

/-!
# Constructions checked by the kernel

Exact counterparts of the textbook constructions of `Modules/Identity/Solids.lean` and the checks
that compare them with a fixture's points (`Nieuwland/Results/Gen/*Construction.lean`). Each real
construction is the image of exact points (`ZSqrt d`, `ZTheta R`) under `c • reV` for a rational
scale `c` (`scaled c`); the kernel compares exact points.

* Permutations and signs (`evenPermsE`, `oddPermsE`, `withSignsE`) commute with `c • reV`.
* `sameSet A B`: the points of `A` are those of `B` (`scaled_eq_of_sameSet`).
* `gyrateE`, `diminishE`: gyration and diminishing with the cap decided exactly on each point
  (`splitOk`); the rotation by `36°` about the normal of a pentagonal face of the
  rhombicosidodecahedron is `rot36E` in `ℤ[√5]` (`reV_rot36E`, from `cos (π / 5) = φ / 2`).
* `polarOk`: the points of `Q` are the poles of the faces of a facet certificate of `P`
  (`isPolarOf_of_check`).
* `transport`: the coordinates of one number field written in another, given the image of the
  generator, certified by `Root.eq_of_root` (`isAlphaOf`).
* `existsUnique_tribonacci`, `existsUnique_snubRoot`: the cubics of the snub cube and the snub
  dodecahedron have exactly one real root each, so the theorems about `snubCube t` and
  `snubDodecahedron ξ` for any root are about the textbook solids.
-/

open Matrix Real
open scoped goldenRatio

namespace Nieuwland.Identity

open Check Check.Exact

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [Exact κ]

/-! ### Scaled exact points -/

open Classical in
/-- The real points `c • v` of exact points `v`. -/
noncomputable def scaled (c : ℝ) (L : List (V3 κ)) : Finset (Fin 3 → ℝ) :=
  (L.map fun v ↦ c • reV v).toFinset

theorem mem_scaled {c : ℝ} {L : List (V3 κ)} {x : Fin 3 → ℝ} :
    x ∈ scaled c L ↔ ∃ v ∈ L, c • reV v = x := by
  simp [scaled]

theorem vertices_smul_ofPoints (c : ℝ) (pts : List (V3 κ)) :
    ((Polyhedron.ofPoints pts).smul c).vertices = scaled c pts := by
  ext x
  rw [mem_vertices_iff, mem_scaled]
  simp [rpts]

theorem image_smul_scaled (a c : ℝ) (L : List (V3 κ)) :
    (scaled c L).image (a • ·) = scaled (a * c) L := by
  ext x
  simp only [Finset.mem_image, mem_scaled]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, by rw [smul_smul]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨c • reV v, ⟨v, hv, rfl⟩, by rw [smul_smul]⟩

theorem scaled_map_smul (c : ℝ) (k : ℤ) (L : List (V3 κ)) :
    scaled c (L.map (V3.smul (ofInt k))) = scaled (c * k) L := by
  ext x
  simp only [mem_scaled, List.mem_map]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, by rw [reV_smul, re_ofInt, smul_smul]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, by rw [reV_smul, re_ofInt, smul_smul]⟩

/-- The points of `A` are those of `B`, as exact values. -/
def sameSet (A B : List (V3 κ)) : Bool :=
  A.all (fun a ↦ B.any (eqV a)) && B.all fun b ↦ A.any (eqV b)

theorem scaled_eq_of_sameSet {A B : List (V3 κ)} (h : sameSet A B = true) (c : ℝ) :
    scaled c A = scaled c B := by
  simp only [sameSet, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at h
  ext x
  simp only [mem_scaled]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, he⟩ := h.1 a ha
    exact ⟨b, hb, by rw [reV_eq_of_eqV he]⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha, he⟩ := h.2 b hb
    exact ⟨a, ha, by rw [reV_eq_of_eqV he]⟩

/-! ### Permutations and signs -/

/-- `-a`. -/
def negE (a : κ) : κ :=
  ofInt 0 - a

theorem re_negE (a : κ) : re (negE a) = -re a := by
  simp [negE, re_sub, re_ofInt]

/-- The even permutations of the coordinates (`evenPerms`). -/
def evenPermsE (v : V3 κ) : List (V3 κ) :=
  [v, ⟨v.y, v.z, v.x⟩, ⟨v.z, v.x, v.y⟩]

/-- The odd permutations of the coordinates (`oddPerms`). -/
def oddPermsE (v : V3 κ) : List (V3 κ) :=
  [⟨v.x, v.z, v.y⟩, ⟨v.z, v.y, v.x⟩, ⟨v.y, v.x, v.z⟩]

/-- `v` with the signs `s` (`withSigns`). -/
def withSignsE (s : Bool × Bool × Bool) (v : V3 κ) : V3 κ :=
  ⟨if s.1 then v.x else negE v.x, if s.2.1 then v.y else negE v.y,
    if s.2.2 then v.z else negE v.z⟩

theorem reV_mk (a b d : κ) : reV (⟨a, b, d⟩ : V3 κ) = ![re a, re b, re d] := by
  ext i
  fin_cases i <;> rfl

theorem smul_reV_mk (c : ℝ) (a b d : κ) :
    c • reV (⟨a, b, d⟩ : V3 κ) = ![c * re a, c * re b, c * re d] := by
  ext i
  fin_cases i <;> rfl

theorem map_evenPermsE (c : ℝ) (v : V3 κ) :
    (evenPermsE v).map (fun u ↦ c • reV u) = evenPerms (c • reV v) := by
  obtain ⟨x, y, z⟩ := v
  simp only [evenPermsE, evenPerms, List.map_cons, List.map_nil, smul_reV_mk]
  simp

theorem map_oddPermsE (c : ℝ) (v : V3 κ) :
    (oddPermsE v).map (fun u ↦ c • reV u) = oddPerms (c • reV v) := by
  obtain ⟨x, y, z⟩ := v
  simp only [oddPermsE, oddPerms, List.map_cons, List.map_nil, smul_reV_mk]
  simp

theorem smul_reV_withSignsE (c : ℝ) (s : Bool × Bool × Bool) (v : V3 κ) :
    c • reV (withSignsE s v) = withSigns s (c • reV v) := by
  obtain ⟨x, y, z⟩ := v
  obtain ⟨s₀, s₁, s₂⟩ := s
  simp only [withSignsE, withSigns, smul_reV_mk]
  cases s₀ <;> cases s₁ <;> cases s₂ <;> simp [re_negE]

/-- The orbit of exact points under sign changes `S` and even permutations. -/
def orbitE (S : List (Bool × Bool × Bool)) (gens : List (V3 κ)) : List (V3 κ) :=
  gens.flatMap fun v ↦ S.flatMap fun s ↦ evenPermsE (withSignsE s v)

theorem map_orbitE (c : ℝ) (S : List (Bool × Bool × Bool)) (gens : List (V3 κ)) :
    (orbitE S gens).map (fun u ↦ c • reV u) =
      (gens.map fun v ↦ c • reV v).flatMap fun w ↦ S.flatMap fun s ↦ evenPerms (withSigns s w) := by
  simp [orbitE, List.map_flatMap, List.flatMap_map, map_evenPermsE, smul_reV_withSignsE]

/-- The orbit of exact points under sign changes `S` and odd permutations. -/
def orbitOddE (S : List (Bool × Bool × Bool)) (gens : List (V3 κ)) : List (V3 κ) :=
  gens.flatMap fun v ↦ S.flatMap fun s ↦ oddPermsE (withSignsE s v)

theorem map_orbitOddE (c : ℝ) (S : List (Bool × Bool × Bool)) (gens : List (V3 κ)) :
    (orbitOddE S gens).map (fun u ↦ c • reV u) =
      (gens.map fun v ↦ c • reV v).flatMap fun w ↦ S.flatMap fun s ↦ oddPerms (withSigns s w) := by
  simp [orbitOddE, List.map_flatMap, List.flatMap_map, map_oddPermsE, smul_reV_withSignsE]

/-- **Exact points as a textbook set.** If the fixture is `pts` scaled by `1 / k` and the
construction is `L` scaled by `1 / m`, the kernel compares `m pts` with `k L`. -/
theorem vertices_eq_of_sameSet {P : Polyhedron} {pts L : List (V3 κ)} {k m : ℕ} (hk : 0 < k)
    (hP : P = (Polyhedron.ofPoints pts).smul (1 / k))
    (h : sameSet (pts.map (V3.smul (ofInt m))) (L.map (V3.smul (ofInt k))) = true) (hm : 0 < m) :
    P.vertices = scaled (1 / m) L := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have e₁ := scaled_map_smul (1 / (k * m) : ℝ) (m : ℤ) pts
  have e₂ := scaled_map_smul (1 / (k * m) : ℝ) (k : ℤ) L
  push_cast at e₁ e₂
  rw [hP, vertices_smul_ofPoints, show (1 / k : ℝ) = 1 / (k * m) * m by field_simp, ← e₁,
    scaled_eq_of_sameSet h, e₂, show (1 / (k * m) * k : ℝ) = 1 / m by field_simp]

/-! ### Gyration and diminishing -/

theorem rotAbout_smul (n : Fin 3 → ℝ) (θ a : ℝ) (x : Fin 3 → ℝ) :
    rotAbout n θ (a • x) = a • rotAbout n θ x := by
  simp only [rotAbout, map_smul, dotProduct_smul, smul_eq_mul]
  module

/-- `D` times the gyrated points (`gyrate`): `R v` (`D` times the rotated point) for the points
with `t ≤ n ⬝ v` and `D v` for the others, the side decided by `pos (t - n ⬝ v)`. -/
def gyrateE (D : ℤ) (R : V3 κ → V3 κ) (n : V3 κ) (t : κ) (V : List (V3 κ)) : List (V3 κ) :=
  V.map fun v ↦ if pos (t - n.dot v) then V3.smul (ofInt D) v else R v

/-- Every point of `V` is known to be strictly below the plane `n ⬝ x = t`, or on or above it. -/
def splitOk (n : V3 κ) (t : κ) (V : List (V3 κ)) : Bool :=
  V.all fun v ↦ pos (t - n.dot v) || nonneg (n.dot v - t)

theorem dot_scaled {c a : ℝ} {n : V3 κ} {n' : Fin 3 → ℝ} (ha : 0 < a) (hn : reV n = a • n')
    (v : V3 κ) : n' ⬝ᵥ (c • reV v) = c / a * re (n.dot v) := by
  rw [re_dot, hn, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  field_simp

/-- **Gyration of exact points** (`gyrate`): the real axis `n'` and level `t'` are `n` and `t`
up to the factor `a > 0`, and `R` is `D` times the rotation by `36°` about `n'`. -/
theorem gyrate_scaled {c a : ℝ} {D : ℤ} {V : List (V3 κ)} {n : V3 κ} {t : κ}
    {R : V3 κ → V3 κ} {n' : Fin 3 → ℝ} {t' : ℝ} (hc : 0 < c) (ha : 0 < a) (hD : 0 < D)
    (hn : reV n = a • n') (ht : c * re t = a * t')
    (hR : ∀ v ∈ V, reV (R v) = (D : ℝ) • rotAbout n' (π / 5) (reV v))
    (hok : splitOk n t V = true) :
    gyrate (scaled c V) n' t' = scaled (c / D) (gyrateE D R n t V) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have ht' : t' = c / a * re t := by field_simp; linarith
  have key : ∀ v ∈ V, (if t' ≤ n' ⬝ᵥ (c • reV v) then rotAbout n' (π / 5) (c • reV v)
      else c • reV v) = (c / D) • reV (if pos (t - n.dot v) then V3.smul (ofInt D) v else R v) := by
    intro v hv
    have hcond : t' ≤ n' ⬝ᵥ (c • reV v) ↔ re t ≤ re (n.dot v) := by
      rw [dot_scaled ha hn, ht', mul_le_mul_iff_right₀ (div_pos hc ha)]
    have hsplit := (List.all_eq_true.mp hok) v hv
    simp only [Bool.or_eq_true] at hsplit
    by_cases hp : pos (t - n.dot v) = true
    · have hlt := lt_of_pos_sub hp
      rw [ite_eq_right fun h ↦ absurd (hcond.mp h) (not_le.mpr hlt), ite_eq_left hp, reV_smul,
        re_ofInt, smul_smul, div_mul_cancel₀ _ hD']
    · have hge := nonneg_sound _ (hsplit.resolve_left hp)
      rw [re_sub] at hge
      rw [ite_eq_left (hcond.mpr (by linarith)), ite_eq_right hp, hR v hv, smul_smul,
        div_mul_cancel₀ _ hD', rotAbout_smul]
  ext x
  simp only [gyrate, Finset.mem_image, mem_scaled, gyrateE, List.mem_map]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, (key v hv).symm⟩
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨c • reV v, ⟨v, hv, rfl⟩, key v hv⟩

/-- The points on or below the plane `n ⬝ x = t` (`diminish`), decided by `nonneg (t - n ⬝ v)`. -/
def diminishE (n : V3 κ) (t : κ) (V : List (V3 κ)) : List (V3 κ) :=
  V.filter fun v ↦ nonneg (t - n.dot v)

/-- Every point of `V` is known to be on or below the plane `n ⬝ x = t`, or strictly above. -/
def splitOk' (n : V3 κ) (t : κ) (V : List (V3 κ)) : Bool :=
  V.all fun v ↦ nonneg (t - n.dot v) || pos (n.dot v - t)

/-- **Diminishing exact points** (`diminish`). -/
theorem diminish_scaled {c a : ℝ} {V : List (V3 κ)} {n : V3 κ} {t : κ} {n' : Fin 3 → ℝ}
    {t' : ℝ} (hc : 0 < c) (ha : 0 < a) (hn : reV n = a • n') (ht : c * re t = a * t')
    (hok : splitOk' n t V = true) :
    diminish (scaled c V) n' t' = scaled c (diminishE n t V) := by
  have ht' : t' = c / a * re t := by field_simp; linarith
  have hca : 0 < c / a := div_pos hc ha
  have key : ∀ v ∈ V, (n' ⬝ᵥ (c • reV v) ≤ t' ↔ nonneg (t - n.dot v) = true) := by
    intro v hv
    rw [dot_scaled ha hn, ht', mul_le_mul_iff_right₀ hca]
    have hsplit := (List.all_eq_true.mp hok) v hv
    simp only [Bool.or_eq_true] at hsplit
    constructor
    · intro hle
      refine hsplit.resolve_right fun hp ↦ ?_
      have := lt_of_pos_sub hp
      linarith
    · intro hn'
      have := nonneg_sound _ hn'
      rw [re_sub] at this
      linarith
  ext x
  simp only [diminish, Finset.mem_filter, mem_scaled, diminishE, List.mem_filter]
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hle⟩
    exact ⟨v, ⟨hv, (key v hv).mp hle⟩, rfl⟩
  · rintro ⟨v, ⟨hv, hn'⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, (key v hv).mpr hn'⟩

/-! ### The rotation by `36°` about a five-fold axis -/

theorem sqrt5_sq : √(5 : ℝ) ^ 2 = 5 :=
  Real.sq_sqrt (by norm_num)

/-- `sin 36° / ‖(0, φ, 1)‖ = (√5 - 1) / 4`. -/
theorem sin_pi_div_five_div : sin (π / 5) / √(φ + 2) = (√5 - 1) / 4 := by
  have h5 := sqrt5_sq
  have hφ : 0 < φ + 2 := by positivity
  have hs : 0 < sin (π / 5) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hr : 0 < √5 - 1 := by
    have : (1 : ℝ) < √5 := by
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  rw [div_eq_iff (Real.sqrt_pos.mpr hφ).ne']
  refine (pow_left_inj₀ hs.le (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt hφ.le, sin_sq, cos_pi_div_five, goldenRatio]
  linear_combination (-(√5 + 5) / 32) * h5

/-- `40` times the rotation by `36°` about `ℝ n₂`, exactly in `ℤ[√5]`, for `n₂` twice a vector of
squared length `φ + 2` (`reV_rot36E`): the normals `(0, φ, 1)` of the pentagonal faces of
`rhombicosidodecahedron`, permuted cyclically and with signs. -/
def rot36E (n₂ x : V3 (ZSqrt 5)) : V3 (ZSqrt 5) :=
  ((V3.smul ⟨10, 10⟩ x).add (V3.smul ⟨-5, 5⟩ (n₂.cross x))).add (V3.smul (⟨5, -2⟩ * n₂.dot x) n₂)

theorem reV_rot36E {n₂ : V3 (ZSqrt 5)} {n' : Fin 3 → ℝ} (hn : reV n₂ = (2 : ℝ) • n')
    (hn' : n' ⬝ᵥ n' = φ + 2) (x : V3 (ZSqrt 5)) :
    reV (rot36E n₂ x) = ((40 : ℤ) : ℝ) • rotAbout n' (π / 5) (reV x) := by
  have h5 := sqrt5_sq
  have hφ : 0 < φ + 2 := by positivity
  have hsq : √(φ + 2) ≠ 0 := (Real.sqrt_pos.mpr hφ).ne'
  have hsin : sin (π / 5) = (√5 - 1) / 4 * √(φ + 2) := by
    rw [← sin_pi_div_five_div, div_mul_cancel₀ _ hsq]
  have hinv : (√(φ + 2))⁻¹ * (√(φ + 2))⁻¹ = (φ + 2)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hφ.le]
  simp only [rot36E, reV_add, reV_smul, reV_cross, re_mul, re_dot, hn, ZSqrt.re_mk, rotAbout, hn',
    map_smul, LinearMap.smul_apply, smul_dotProduct, smul_eq_mul, cos_pi_div_five, hsin]
  have hφ' : (φ + 2)⁻¹ = (5 - √5) / 10 := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [goldenRatio]
    linear_combination (-1 / 20 : ℝ) * h5
  match_scalars
  · ring
  · field_simp
    ring
  · rw [show (1 - (1 + √5) / 4) * ((√(φ + 2))⁻¹ * (n' ⬝ᵥ reV x)) * (√(φ + 2))⁻¹ =
      (1 - (1 + √5) / 4) * (n' ⬝ᵥ reV x) * ((√(φ + 2))⁻¹ * (√(φ + 2))⁻¹) by ring, hinv, hφ']
    linear_combination -(n' ⬝ᵥ reV x) * h5

/-- A normal `n'` of a pentagonal face of `rhombicosidodecahedron`, given as `n₂ = 2 n'` in
`ℤ[√5]`: `‖n'‖² = φ + 2`, as for `(0, φ, 1)` and its cyclic permutations with signs. -/
theorem pentagonAxis {n₂ : V3 (ZSqrt 5)} {n' : Fin 3 → ℝ} (h : (1 / 2 : ℝ) • reV n₂ = n')
    (h2 : isZero (n₂.dot n₂ - ⟨10, 2⟩) = true) : reV n₂ = (2 : ℝ) • n' ∧ n' ⬝ᵥ n' = φ + 2 := by
  have e := isZero_sound _ h2
  rw [re_sub, re_dot, ZSqrt.re_mk] at e
  subst h
  refine ⟨by rw [smul_smul]; norm_num, ?_⟩
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, goldenRatio]
  push_cast at e
  linear_combination e / 4

/-! ### Polar reciprocals -/

/-- **The points `Q` are the poles of the faces**, up to the map `g`: every face has `h > 0`, and
each point `q` of `Q` and some face, and each face and some point, satisfy `h q = k g(n)`. -/
def polarOk (k : ℤ) (g : V3 κ → V3 κ) (Q : List (V3 κ)) (faces : List (FaceE κ)) : Bool :=
  faces.all (fun F ↦ pos F.h) &&
    Q.all (fun q ↦ faces.any fun F ↦ eqV (V3.smul F.h q) (V3.smul (ofInt k) (g F.n))) &&
    faces.all fun F ↦ Q.any fun q ↦ eqV (V3.smul F.h q) (V3.smul (ofInt k) (g F.n))

/-- **Polar reciprocals checked by the kernel**: `P` is the points `pts` scaled by `cP > 0` with
a facet certificate (`faceOk`, `combOk`), `Q` the points `qs` scaled by `cQ`, `g` an exact linear
map with real counterpart `G`, `cP cQ k = 1` and `polarOk`. -/
theorem isPolarOf_of_check {P Q : Polyhedron} {pts qs : List (V3 κ)} {faces : List (FaceE κ)}
    {vtx : List (ℕ × ℕ × ℕ)} {ptn : List (List ℕ)} {s : Option κ} {cP cQ : ℝ} {k : ℤ}
    {g : V3 κ → V3 κ} {G : (Fin 3 → ℝ) → Fin 3 → ℝ} (hcP : 0 < cP)
    (hP : P = (Polyhedron.ofPoints pts).smul cP) (hQ : Q.vertices = scaled cQ qs)
    (hf : ∀ F ∈ faces, faceOk pts s F = true)
    (hcomb : combOk (faces.map FaceE.cyc) pts.length vtx ptn = true) (hk : cP * cQ * k = 1)
    (hG : ∀ v, reV (g v) = G (reV v)) (hGs : ∀ (a : ℝ) x, G (a • x) = a • G x)
    (hok : polarOk k g qs faces = true) : Q.IsPolarOf P G := by
  simp only [polarOk, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hok
  obtain ⟨⟨hpos, hQF⟩, hFQ⟩ := hok
  subst hP
  have key : ∀ F ∈ faces, ∀ q, eqV (V3.smul F.h q) (V3.smul (ofInt k) (g F.n)) = true →
      cQ • reV q = G ((cP * re F.h)⁻¹ • reV F.n) := by
    intro F hF q he
    have h1 := reV_eq_of_eqV he
    rw [reV_smul, reV_smul, re_ofInt, hG] at h1
    have hh : re F.h ≠ 0 := (pos_sound _ (hpos F hF)).ne'
    have hq : reV q = ((re F.h)⁻¹ * k) • G (reV F.n) := by
      rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ hh, one_smul]
    have hcP' : cP ≠ 0 := hcP.ne'
    rw [hGs, hq, smul_smul]
    congr 1
    field_simp
    linear_combination hk
  refine ⟨rpts cP pts, faces.map (rface cP), fun x hx ↦ (mem_vertices_iff x).mpr hx,
    hull_smul_ofPoints, isFaceCert_of_check hcP hf hcomb, ?_, ?_⟩
  · intro F hF
    obtain ⟨F', hF', rfl⟩ := List.mem_map.mp hF
    exact mul_pos hcP (pos_sound _ (hpos F' hF'))
  · ext y
    simp only [hQ, Finset.mem_coe, mem_scaled, List.mem_map, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨F, hF, he⟩ := hQF q hq
      exact ⟨rface cP F, ⟨F, hF, rfl⟩, key F hF q he⟩
    · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
      obtain ⟨q, hq, he⟩ := hFQ F hF
      exact ⟨q, hq, key F hF q he⟩

/-- **Exact points are a textbook set**, same scale: the fixture is `pts` scaled by `c`. -/
theorem vertices_eq_of_sameSet' {P : Polyhedron} {pts L : List (V3 κ)} {c : ℝ}
    (hP : P = (Polyhedron.ofPoints pts).smul c) (h : sameSet pts L = true) :
    P.vertices = scaled c L := by
  rw [hP, vertices_smul_ofPoints, scaled_eq_of_sameSet h]

/-! ### Real roots -/

theorem goldenRatio_cube : φ ^ 3 = 2 + √5 := by
  have h5 := sqrt5_sq
  rw [goldenRatio]
  linear_combination (√5 + 3) / 8 * h5

/-- `φ` is the positive root of `x² = x + 1`. -/
theorem eq_goldenRatio {x : ℝ} (h : x ^ 2 = x + 1) (hx : 0 < x) : x = φ := by
  have h5 := sqrt5_sq
  have h1 : (x - φ) * (x - ψ) = 0 := by
    rw [goldenRatio, goldenConj]
    linear_combination h - h5 / 4
  rcases mul_eq_zero.mp h1 with h1 | h1
  · linarith
  · linarith [goldenConj_neg]

/-- `x³ = x² + x + 1` has one real root: any root is the root `y > 5/3`. -/
theorem tribonacci_unique {x y : ℝ} (hx : x ^ 3 = x ^ 2 + x + 1) (hy : y ^ 3 = y ^ 2 + y + 1)
    (hy' : 5 / 3 < y) : x = y := by
  have h : (x - y) * (x ^ 2 + x * y + y ^ 2 - x - y - 1) = 0 := by linear_combination hx - hy
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · nlinarith [sq_nonneg (2 * x + y - 1), mul_pos (by linarith : (0 : ℝ) < 3 * y - 5)
      (by linarith : (0 : ℝ) < y + 1)]

/-- `x³ - 2x = φ` has one real root: any root is the root `y > 5/3`. -/
theorem snubRoot_unique {x y : ℝ} (hx : x ^ 3 - 2 * x = φ) (hy : y ^ 3 - 2 * y = φ)
    (hy' : 5 / 3 < y) : x = y := by
  have h : (x - y) * (x ^ 2 + x * y + y ^ 2 - 2) = 0 := by linear_combination hx - hy
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · nlinarith [sq_nonneg (2 * x + y), mul_pos (by linarith : (0 : ℝ) < 3 * y - 5)
      (by linarith : (0 : ℝ) < 3 * y + 5)]

/-- **The tribonacci constant**: `t³ = t² + t + 1` has exactly one real root (in `(5/3, 2)`). -/
theorem existsUnique_tribonacci : ∃! t : ℝ, t ^ 3 = t ^ 2 + t + 1 := by
  have h1 : (1 : ℝ) ^ 3 - 1 ^ 2 - 1 - 1 ≤ 0 := by norm_num
  have h2 : 0 ≤ (2 : ℝ) ^ 3 - 2 ^ 2 - 2 - 1 := by norm_num
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2)
    (f := fun t : ℝ ↦ t ^ 3 - t ^ 2 - t - 1) (by fun_prop) (Set.mem_Icc.mpr ⟨h1, h2⟩)
  have ht' : t ^ 3 = t ^ 2 + t + 1 := by linear_combination ht
  -- `t³ - t² - t - 1 = (t - 5/3) (t + 1/3)² - 22/27`
  have hgt : 5 / 3 < t := by
    by_contra hle
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : t - 5 / 3 ≤ 0) (sq_nonneg (t + 1 / 3))]
  exact ⟨t, ht', fun x hx ↦ tribonacci_unique hx ht' hgt⟩

/-- `ξ³ - 2ξ = φ` has exactly one real root (in `(5/3, 2)`). -/
theorem existsUnique_snubRoot : ∃! ξ : ℝ, ξ ^ 3 - 2 * ξ = φ := by
  have h5 : (2 : ℝ) < √5 ∧ √5 < 3 := by
    have := sqrt5_sq
    constructor <;> nlinarith [Real.sqrt_nonneg 5]
  have hφ : 3 / 2 < φ ∧ φ < 2 := by
    rw [goldenRatio]
    constructor <;> linarith [h5.1, h5.2]
  have h1 : (1 : ℝ) ^ 3 - 2 * 1 - φ ≤ 0 := by linarith [hφ.1]
  have h2 : 0 ≤ (2 : ℝ) ^ 3 - 2 * 2 - φ := by linarith [hφ.2]
  obtain ⟨ξ, -, hξ⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2)
    (f := fun ξ : ℝ ↦ ξ ^ 3 - 2 * ξ - φ) (by fun_prop) (Set.mem_Icc.mpr ⟨h1, h2⟩)
  have hξ' : ξ ^ 3 - 2 * ξ = φ := by linear_combination hξ
  -- `ξ³ - 2ξ - φ = (ξ - 5/3) ((ξ + 5/6)² + 1/12) + 35/27 - φ`
  have hgt : 5 / 3 < ξ := by
    by_contra hle
    nlinarith [mul_nonpos_of_nonpos_of_nonneg (by linarith : ξ - 5 / 3 ≤ 0)
      (by positivity : (0 : ℝ) ≤ (ξ + 5 / 6) ^ 2 + 1 / 12)]
  exact ⟨ξ, hξ', fun x hx ↦ snubRoot_unique hx hξ' hgt⟩

/-! ### The rhombicosidodecahedron -/

/-- The generators of `rhombicosidodecahedron`, times `2`, in `ℤ[√5]`. -/
def ridGens : List (V3 (ZSqrt 5)) :=
  [⟨⟨2, 0⟩, ⟨2, 0⟩, ⟨4, 2⟩⟩, ⟨⟨3, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩⟩, ⟨⟨5, 1⟩, ⟨0, 0⟩, ⟨3, 1⟩⟩]

/-- `rhombicosidodecahedron`, times `2`. -/
def ridE : List (V3 (ZSqrt 5)) :=
  orbitE allSigns ridGens

theorem rhombicosidodecahedron_eq : rhombicosidodecahedron = scaled (1 / 2) ridE := by
  have h5 := sqrt5_sq
  have hg : ridGens.map (fun v ↦ (1 / 2 : ℝ) • reV v) =
      [![1, 1, φ ^ 3], ![φ ^ 2, φ, 2 * φ], ![2 + φ, 0, φ ^ 2]] := by
    simp only [ridGens, List.map_cons, List.map_nil, smul_reV_mk, ZSqrt.re_mk, goldenRatio_cube,
      goldenRatio_sq]
    norm_num [goldenRatio]
    ring_nf
    simp
  rw [rhombicosidodecahedron, scaled, ridE, map_orbitE, hg]

/-- The fixture `pts` scaled by `1 / k` is `rhombicosidodecahedron`. -/
theorem rhombicosidodecahedron_of_check {P : Polyhedron} {pts : List (V3 (ZSqrt 5))} {k : ℕ}
    (hk : 0 < k) (hP : P = (Polyhedron.ofPoints pts).smul (1 / k))
    (h : sameSet (pts.map (V3.smul (ofInt 2))) (ridE.map (V3.smul (ofInt k))) = true) :
    P.vertices = rhombicosidodecahedron := by
  rw [rhombicosidodecahedron_eq]
  exact_mod_cast vertices_eq_of_sameSet hk hP h two_pos

/-! ### The snub cube -/

/-- `snubCube` from exact `t` and `1 / t`. -/
def snubCubeE (tE tinvE : κ) : List (V3 κ) :=
  orbitE plusOdd [⟨ofInt 1, tinvE, tE⟩] ++ orbitOddE plusEven [⟨ofInt 1, tinvE, tE⟩]

theorem snubCube_eq {tE tinvE : κ} {t : ℝ} (ht : re tE = t) (hinv : re tinvE = 1 / t) :
    snubCube t = scaled (1 / 1) (snubCubeE tE tinvE) := by
  have hg : [(⟨ofInt 1, tinvE, tE⟩ : V3 κ)].map (fun v ↦ (1 / 1 : ℝ) • reV v) =
      [![1, 1 / t, t]] := by
    simp [reV_mk, re_ofInt, ht, hinv]
  rw [snubCube, scaled, snubCubeE, List.map_append, map_orbitE, map_orbitOddE, hg]
  simp

/-- The exact facts behind `snubCube_of_check`: `t³ = t² + t + 1`, `t (1 / t) = 1`, `t > 5/3`,
and the points. -/
def snubCubeOk (tE tinvE : κ) (pts : List (V3 κ)) : Bool :=
  isZero (tE * tE * tE - tE * tE - tE - ofInt 1) && isZero (tE * tinvE - ofInt 1) &&
    pos (ofInt 3 * tE - ofInt 5) && sameSet pts (snubCubeE tE tinvE)

/-- **The snub cube**: the fixture `pts` is `snubCube t` for the real root `t` of
`t³ = t² + t + 1`. -/
theorem snubCube_of_check {P : Polyhedron} {pts : List (V3 κ)} {tE tinvE : κ}
    (hP : P = (Polyhedron.ofPoints pts).smul (1 / 1)) (h : snubCubeOk tE tinvE pts = true) {t : ℝ}
    (ht : t ^ 3 = t ^ 2 + t + 1) : P.vertices = snubCube t := by
  simp only [snubCubeOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
  have e₁ := isZero_sound _ h₁
  have e₂ := isZero_sound _ h₂
  have e₃ := pos_sound _ h₃
  simp only [re_sub, re_mul, re_ofInt] at e₁ e₂ e₃
  push_cast at e₁ e₂ e₃
  have hte : t = re tE := tribonacci_unique ht (by linear_combination e₁) (by linarith)
  have hinv : re tinvE = 1 / t := by
    rw [hte, eq_div_iff (by linarith)]
    linear_combination e₂
  rw [snubCube_eq hte.symm hinv]
  exact vertices_eq_of_sameSet' hP h₄

/-! ### The snub dodecahedron -/

/-- The generators of `snubDodecahedron` from exact `ξ`, `1 / ξ`, `φ` and `1 / φ`. -/
def snubDodecahedronGensE (ξE ξinvE φE φinvE : κ) : List (V3 κ) :=
  let α := ξE - ξinvE
  let β := ξE * φE + φE * φE + φE * ξinvE
  [⟨ofInt 2 * α, ofInt 2, ofInt 2 * β⟩,
    ⟨α + β * φinvE + φE, negE α * φE + β + φinvE, α * φinvE + β * φE - ofInt 1⟩,
    ⟨negE α * φinvE + β * φE + ofInt 1, negE α + β * φinvE - φE, α * φE + β - φinvE⟩,
    ⟨negE α * φinvE + β * φE - ofInt 1, α - β * φinvE - φE, α * φE + β + φinvE⟩,
    ⟨α + β * φinvE - φE, α * φE - β + φinvE, α * φinvE + β * φE + ofInt 1⟩]

theorem snubDodecahedron_eq {ξE ξinvE φE φinvE : κ} {ξ : ℝ} (hξ : re ξE = ξ)
    (hξinv : re ξinvE = 1 / ξ) (hφ : re φE = φ) (hφinv : re φinvE = 1 / φ) :
    snubDodecahedron ξ =
      scaled (1 / 1) (orbitE plusEven (snubDodecahedronGensE ξE ξinvE φE φinvE)) := by
  rw [snubDodecahedron, scaled, map_orbitE]
  congr 2
  generalize goldenRatio = p at hφ hφinv ⊢
  simp only [snubDodecahedronGensE, List.map_cons, List.map_nil, smul_reV_mk, re_add, re_sub,
    re_mul, re_negE, re_ofInt, hξ, hξinv, hφ, hφinv, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (ext i; fin_cases i <;> simp <;> ring)

/-- The exact facts behind `snubDodecahedron_of_check`: `ξ (1 / ξ) = 1`, `φ = ξ³ - 2ξ`,
`φ² = φ + 1`, `φ > 0`, `φ (1 / φ) = 1`, `ξ > 5/3`, and the points. -/
def snubDodecahedronOk (ξE ξinvE φE φinvE : κ) (pts : List (V3 κ)) : Bool :=
  isZero (ξE * ξinvE - ofInt 1) && isZero (ξE * ξE * ξE - ofInt 2 * ξE - φE) &&
    isZero (φE * φE - φE - ofInt 1) && pos φE && isZero (φE * φinvE - ofInt 1) &&
    pos (ofInt 3 * ξE - ofInt 5) &&
    sameSet pts (orbitE plusEven (snubDodecahedronGensE ξE ξinvE φE φinvE))

/-- **The snub dodecahedron**: the fixture `pts` is `snubDodecahedron ξ` for the real root `ξ` of
`ξ³ - 2ξ = φ`. -/
theorem snubDodecahedron_of_check {P : Polyhedron} {pts : List (V3 κ)} {ξE ξinvE φE φinvE : κ}
    (hP : P = (Polyhedron.ofPoints pts).smul (1 / 1))
    (h : snubDodecahedronOk ξE ξinvE φE φinvE pts = true) {ξ : ℝ} (hξ : ξ ^ 3 - 2 * ξ = φ) :
    P.vertices = snubDodecahedron ξ := by
  simp only [snubDodecahedronOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩ := h
  have e₁ := isZero_sound _ h₁
  have e₂ := isZero_sound _ h₂
  have e₃ := isZero_sound _ h₃
  have e₄ := pos_sound _ h₄
  have e₅ := isZero_sound _ h₅
  have e₆ := pos_sound _ h₆
  simp only [re_sub, re_mul, re_ofInt] at e₁ e₂ e₃ e₅ e₆
  push_cast at e₁ e₂ e₃ e₅ e₆
  have hφ : re φE = φ := eq_goldenRatio (by linear_combination e₃) e₄
  have hξe : ξ = re ξE := snubRoot_unique hξ (by linear_combination e₂ + hφ) (by linarith)
  have hξinv : re ξinvE = 1 / ξ := by
    rw [hξe, eq_div_iff (by linarith)]
    linear_combination e₁
  have hφinv : re φinvE = 1 / φ := by
    rw [← hφ, eq_div_iff e₄.ne']
    linear_combination e₅
  rw [snubDodecahedron_eq hξe.symm hξinv hφ hφinv]
  exact vertices_eq_of_sameSet' hP h₇

/-! ### Mirror images and changes of field -/

/-- The mirror image in the plane `x₀ = 0`. -/
def mirrorE (v : V3 κ) : V3 κ :=
  ⟨negE v.x, v.y, v.z⟩

theorem reV_mirrorE (v : V3 κ) : reV (mirrorE v) = ![-reV v 0, reV v 1, reV v 2] := by
  obtain ⟨x, y, z⟩ := v
  simp [mirrorE, reV_mk, re_negE]

theorem scaled_map_eq {κ' : Type} [Add κ'] [Sub κ'] [Mul κ'] [Exact κ'] {f : V3 κ' → V3 κ}
    {L : List (V3 κ')} (h : ∀ v ∈ L, reV (f v) = reV v) (c : ℝ) :
    scaled c (L.map f) = scaled c L := by
  ext x
  simp only [mem_scaled, List.mem_map]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, by rw [h v hv]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨f v, ⟨v, hv, rfl⟩, by rw [h v hv]⟩

section Transport

variable {R R' : Root}

/-- `∑ᵢ lᵢ qⁱ` in `ZTheta R`, by Horner's rule. -/
def hornerT (q : ZTheta R) : List ℤ → ZTheta R
  | [] => ofInt 0
  | a :: l => ofInt a + q * hornerT q l

theorem re_hornerT (q : ZTheta R) : ∀ l : List ℤ, re (hornerT q l) = evalZ l (re q)
  | [] => by simp [hornerT, re_ofInt, evalZ_nil]
  | a :: l => by rw [hornerT, re_add, re_mul, re_ofInt, re_hornerT q l, evalZ_cons]

/-- An element of `ZTheta R'` written in `ZTheta R`, given the image `q` of the generator
`R'.α`. -/
def transport (q : ZTheta R) (a : ZTheta R') : ZTheta R :=
  hornerT q (a.c.take R'.n)

theorem re_transport {q : ZTheta R} (hq : R'.α = re q) (a : ZTheta R') :
    re (transport q a) = re a := by
  rw [transport, re_hornerT, ← hq, ZTheta.re_eq, ZTheta.re_eq_evalZ]

theorem reV_map_transport {q : ZTheta R} (hq : R'.α = re q) (v : V3 (ZTheta R')) :
    reV (v.map (transport q)) = reV v := by
  obtain ⟨x, y, z⟩ := v
  simp [V3.map, reV_mk, re_transport hq]

/-- `q` is the generator `α` of `R'`: a root of `R'.N` in `[A/E, B/E]` (`Root.eq_of_root`). -/
def isAlphaOf (R' : Root) (q : ZTheta R) : Bool :=
  decide (0 < R'.E) && isZero (hornerT q R'.N) &&
    nonneg (q * ofInt (R'.E : ℤ) - ofInt R'.A) && nonneg (ofInt R'.B - q * ofInt (R'.E : ℤ))

theorem isAlphaOf_sound {q : ZTheta R} (h : isAlphaOf R' q = true) : R'.α = re q := by
  simp only [isAlphaOf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hE, h₀⟩, hA⟩, hB⟩ := h
  have hEr : (0 : ℝ) < R'.E := by exact_mod_cast hE
  have h₁ := nonneg_sound _ hA
  have h₂ := nonneg_sound _ hB
  simp only [re_sub, re_mul, re_ofInt, Int.cast_natCast] at h₁ h₂
  refine R'.eq_of_root ?_ ?_ ?_
  · rw [div_le_iff₀ hEr]
    linarith
  · rw [le_div_iff₀ hEr]
    linarith
  · rw [← re_hornerT]
    exact isZero_sound _ h₀

end Transport

end Nieuwland.Identity
