import Modules.System.PolyMaxOf
import Modules.Root.Explicit

/-!
# One scale per system

The list form `PolynomialSystem.IsMaxSingle Ss N` of the exact theorems
(`Modules/System/PolyMaxOf.lean`): `N` is the largest scale of the systems `Ss`, and each
system has one scale. For each kind of
certificate:

* a Nopert: `x 0 = 1`, no box, its one scale `1` (`isMaxSingle_scales_one`);
* a closed form: one equation `P(x 0) = 0` with the box inside the coarse enclosure of the checked
  root of `P`, where that root is the only one (`Check.Root.eq_of_root`), and holding the root's
  decimals (`isMaxSingle_scales_of_exact_dec`);
* a root form: each written-out contact system has the scale of the only zero of its root's system
  in the box of Krawczyk's test (`RootRec.scales_explicit`) (`Root.isMaxSingle_one`,
  `Root.isMaxSingle_topScale`).

These theorems are unfolded by the elaborator and the kernel only, so the module is left out of
the compiled library (`scripts/native.py`).
-/

namespace Nieuwland

open PolynomialSystem

/-- **A Nopert**: `x 0 = 1`, no box, its one scale `1`. -/
theorem isMaxSingle_scales_one {N : ℝ} (hN : N = 1) :
    IsMaxSingle [⟨[([(1, [(0, 1)])], [(1, [])])], []⟩] N ∧ N ∈ Set.Icc (1 : ℝ) 1 := by
  obtain ⟨h, h1⟩ := isGreatest_scales_one hN
  refine ⟨⟨h, fun S hS ↦ ⟨1, ?_⟩⟩, h1⟩
  rw [List.mem_singleton.mp hS]
  ext l
  constructor
  · rintro ⟨_, hT, x, ⟨-, heq⟩, rfl⟩
    rw [List.mem_singleton.mp hT] at heq
    have := heq _ (List.mem_singleton_self _)
    simpa [RationalPolynomial.eval, monomial] using this
  · rintro rfl
    exact ⟨_, List.mem_singleton_self _, fun _ ↦ 1,
      ⟨fun i hi ↦ absurd hi (by simp), fun e he ↦ by
        rw [List.mem_singleton.mp he]; simp [RationalPolynomial.eval, monomial]⟩, rfl⟩

/-- A scale of the system `L = Rt` in the box `[a, b]`, `L = Rt` the polynomial `m` with both
sides positive, is a root of `m` in `[a, b]`. -/
theorem mem_scales_split {m : List ℚ} {L Rt : RationalPolynomial}
    (hP : RationalPolynomial.split (RationalPolynomial.ofUni 0 m) = (L, Rt)) {a b : ℚ} {l : ℝ}
    (hl : l ∈ scales [⟨[(L, Rt)], [(a, b)]⟩]) :
    (a : ℝ) ≤ l ∧ l ≤ b ∧ polyEval m l = 0 := by
  have hS : (⟨[(L, Rt)], [(a, b)]⟩ : PolynomialSystem) =
      (⟨[RationalPolynomial.ofUni 0 m], [(a, b)]⟩ : ZSystem).toSystem := by
    simp [ZSystem.toSystem, hP]
  rw [hS, ZSystem.scales_toSystem] at hl
  obtain ⟨x, ⟨hbox, heq⟩, rfl⟩ := hl
  obtain ⟨hxa, hxb⟩ := hbox 0 (by simp)
  simp only [List.getD_cons_zero] at hxa hxb
  have h0 := heq _ (List.mem_singleton_self _)
  have hev := eval_ofUni_map_mul 1 m x
  simp only [one_mul, Rat.cast_one, List.map_id_fun', id_eq] at hev
  exact ⟨hxa, hxb, hev ▸ h0⟩

/-- **A closed form, one scale**: `isGreatest_scales_of_exact_dec`, with a box `[a, b]` that holds
the decimals and lies in the coarse enclosure of the checked root (divided by `c`), where that
root is the only one: the system's one scale is `N`. -/
theorem isMaxSingle_scales_of_exact_dec {κ : Type} [Add κ] [Sub κ] [Mul κ] [Check.Exact κ]
    (R : Check.Root) (Θ : Check.Scale κ) {N : ℝ} (hN : N = Θ.re) (p : List ℤ)
    (hm : R.m = p.map (Int.cast)) (hden : 0 < Θ.den)
    (hz : Check.Exact.isZero (homEval Θ.num (Θ.den : ℤ) p) = true)
    (hA : Check.Exact.nonneg (Check.Exact.ofInt ((R.E : ℤ) * R.c) * Θ.num -
      Check.Exact.ofInt (R.A * Θ.den)) = true)
    (hB : Check.Exact.nonneg (Check.Exact.ofInt (R.B * Θ.den) -
      Check.Exact.ofInt ((R.E : ℤ) * R.c) * Θ.num) = true)
    {L Rt : RationalPolynomial} (hP : RationalPolynomial.split (RationalPolynomial.ofUni 0 (p.map Int.cast)) = (L, Rt))
    {a b : ℚ} {U V : ℕ} (k : ℕ) (hlo : R.lo < a) (hhi : b < R.hi) (hau : a ≤ (U : ℚ) / 10 ^ k)
    (hvb : (V : ℚ) / 10 ^ k ≤ b) (hu : (U : ℚ) / 10 ^ k * (R.c * R.D) ≤ R.Xl)
    (hv : (R.Xh : ℚ) ≤ (V : ℚ) / 10 ^ k * (R.c * R.D))
    (hcA : (R.A : ℚ) ≤ a * (R.E * R.c)) (hcB : b * (R.E * R.c) ≤ R.B) :
    IsMaxSingle [⟨[(L, Rt)], [(a, b)]⟩] N ∧
      N ∈ Set.Icc ((U : ℝ) / 10 ^ k) ((V : ℝ) / 10 ^ k) := by
  obtain ⟨h, h1⟩ := isGreatest_scales_of_exact_dec R Θ hN p hm hden hz hA hB hP k hlo hhi hau hvb
    hu hv
  have hP' : RationalPolynomial.split (RationalPolynomial.ofUni 0 R.m) = (L, Rt) := by rw [hm]; exact hP
  have hE : (0 : ℝ) < R.E := by
    have h₂ := R.coarse
    simp only [Check.coarseCheck, Bool.and_eq_true, decide_eq_true_eq] at h₂
    exact_mod_cast h₂.1.1.1.1.1.1
  have hc : (0 : ℝ) < R.c := by exact_mod_cast R.c_pos
  have hcA' : (R.A : ℝ) ≤ a * (R.E * R.c) := by exact_mod_cast hcA
  have hcB' : (b : ℝ) * (R.E * R.c) ≤ R.B := by exact_mod_cast hcB
  -- every scale `l` of the system is a root of `m` in `[a, b]`, so `c l = α`
  have hα : ∀ l ∈ scales [⟨[(L, Rt)], [(a, b)]⟩], R.α = R.c * l := by
    intro l hl
    obtain ⟨hla, hlb, hl0⟩ := mem_scales_split hP' hl
    have hEc : (0 : ℝ) ≤ R.E * R.c := (mul_pos hE hc).le
    have ha := mul_le_mul_of_nonneg_right hla hEc
    have hb := mul_le_mul_of_nonneg_right hlb hEc
    have h1 : (R.A : ℝ) / R.E ≤ R.c * l := by
      rw [div_le_iff₀ hE]; linarith
    have h2 : R.c * l ≤ (R.B : ℝ) / R.E := by
      rw [le_div_iff₀ hE]; linarith
    exact R.eq_of_root h1 h2 ((R.polyEval_eq_zero_iff l).mp hl0)
  refine ⟨⟨h, fun S hS ↦ ⟨N, ?_⟩⟩, h1⟩
  rw [List.mem_singleton.mp hS]
  ext l
  refine ⟨fun hl ↦ ?_, fun hl ↦ (Set.mem_singleton_iff.mp hl) ▸ h.1⟩
  have := (hα l hl).symm.trans (hα N h.1)
  exact Set.mem_singleton_iff.mpr (mul_left_cancel₀ hc.ne' this)

namespace Root

open Check (V3 ExactBasis)

variable {κ : Type} [Add κ] [Sub κ] [Mul κ] [ExactBasis κ]

/-- **A root form of several roots, one scale per system**: `isGreatest_topScale`, and each
written-out system has the scale of its root's only zero (`RootRec.scales_explicit`). -/
theorem isMaxSingle_topScale {pts : List (V3 κ)} {F : ParData} (hF : F.Spec κ) {R : RootRec}
    {Rs : List RootRec} {N : ℝ} (hN : N = topScale pts R Rs)
    (hz : ∀ R' ∈ R :: Rs, ∃ y, (R'.kraw pts).IsZero (basisPar κ) y ∧
      R'.scale pts = (R'.kraw pts).env (basisPar κ) y (nx R'.cen))
    (T : List ℕ) (hT : ∀ i ∈ T, i < (R :: Rs).length) (hsep : sepOk R Rs T = true)
    {Ss : List PolynomialSystem} (hSs : Ss = T.map fun i ↦ ((R :: Rs).getD i R).explicit pts F) :
    IsMaxSingle Ss N := by
  refine ⟨isGreatest_topScale hF hN hz T hT hsep hSs, fun S hS ↦ ?_⟩
  rw [hSs, List.mem_map] at hS
  obtain ⟨i, hi, rfl⟩ := hS
  have hmem : (R :: Rs).getD i R ∈ R :: Rs := by
    rw [List.getD_eq_getElem _ _ (hT i hi)]; exact List.getElem_mem _
  obtain ⟨y, hy, -⟩ := hz _ hmem
  exact ⟨_, ((R :: Rs).getD i R).scales_explicit pts hF hy⟩

/-- **A root form of one root, one scale**: `isGreatest_one`, and the written-out system has the
scale of the root's only zero. -/
theorem isMaxSingle_one {pts : List (V3 κ)} {F : ParData} (hF : F.Spec κ) {R : RootRec} {N : ℝ}
    (h : ∃ y, (R.kraw pts).IsZero (basisPar κ) y ∧ N = (R.kraw pts).env (basisPar κ) y (nx R.cen))
    {Ss : List PolynomialSystem} (hSs : Ss = [R.explicit pts F]) :
    IsMaxSingle Ss N := by
  refine ⟨isGreatest_one hF h hSs, fun S hS ↦ ?_⟩
  obtain ⟨y, hy, -⟩ := h
  rw [hSs, List.mem_singleton] at hS
  rw [hS]
  exact ⟨_, R.scales_explicit pts hF hy⟩

end Root

end Nieuwland
