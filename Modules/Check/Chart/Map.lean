import Modules.Check.Number.Frac
import Modules.Check.Number.Ext

/-!
# Generic maps

A pulled-back polynomial `p ∘ Φ` is a generic computation (`GenPoly κ`) composed with a generic
map `Φ`: a vector of generic computations with constants in `κ`, natural in maps that commute with
`+`, `-` and `*` (`GenMap κ`). Computations compose with maps and maps with maps
(`GenPoly.comp`, `GenMap.comp`), so
the parameter maps of nested zooms are compositions of simple pieces
(`Nieuwland/Check/Zoom.lean`). `powG` is the power `x ^ m` by repeated multiplication.

Compiled code runs composites through `GenMap.all`, the first outputs as data (`comp_eq_compM`):
each level of a nested composite is computed once per call, where the kernel shares the repeated
inner values by itself.
-/

namespace Nieuwland.Check

/-! ### Powers -/

section Pow

variable {α β : Type*} [Mul α] [Mul β]

/-- `x ^ m` by repeated multiplication, with `x ^ 0 = one`. -/
def powG (one x : α) : ℕ → α
  | 0 => one
  | 1 => x
  | m + 2 => powG one x (m + 1) * x

theorem map_powG {f : α → β} (hf : ∀ a b, f (a * b) = f a * f b) (one x : α) :
    ∀ m, f (powG one x m) = powG (f one) (f x) m
  | 0 => rfl
  | 1 => rfl
  | m + 2 => by rw [powG, hf, map_powG hf one x (m + 1)]; rfl

theorem powG_one {R : Type*} [CommRing R] (x : R) : ∀ m, powG 1 x m = x ^ m
  | 0 => by simp [powG]
  | 1 => by simp [powG]
  | m + 2 => by rw [powG, powG_one x (m + 1), ← pow_succ]

end Pow

/-! ### Maps -/

/-- The number of outputs that `GenMap.all` computes by default: at least the slots of every
family (eleven in weighted zooms). -/
def GenMap.width : ℕ := 16

/-- A vector of polynomial computations (outputs `0, 1, …`) that runs in any type with `+`, `-`
and `*`, from the inputs `x i` and constants in `κ` embedded by `k`, and is natural in maps
that commute with the operations. -/
structure GenMap (κ : Type) where
  /-- The computation of the outputs. -/
  run : {α : Type} → [Add α] → [Sub α] → [Mul α] → (κ → α) → (ℕ → α) → ℕ → α
  /-- Naturality. -/
  natural : ∀ {α β : Type} [Add α] [Sub α] [Mul α] [Add β] [Sub β] [Mul β] (f : α → β),
    IsArith f → ∀ (k : κ → α) (x : ℕ → α), f ∘ run k x = run (f ∘ k) (f ∘ x)
  /-- The first outputs together, as data: what compiled code computes once and reads with `look`
  (a call of `run` computes one output). -/
  all : {α : Type} → [Add α] → [Sub α] → [Mul α] → (κ → α) → (ℕ → α) → Array α :=
    fun k x ↦ Array.ofFn (n := GenMap.width) fun i ↦ run k x i
  /-- The outputs in `all` are those of `run`. -/
  all_get : ∀ {α : Type} [Add α] [Sub α] [Mul α] (k : κ → α) (x : ℕ → α) (i : ℕ)
    (h : i < (all k x).size), (all k x)[i] = run k x i := by
    intros; simp only [Array.getElem_ofFn]

namespace GenMap

variable {κ : Type}

/-- The identity map. Its `all` is empty, so that `look (id.all k x) f` reduces to `f` and
`Φ.comp id` unifies with `Φ`. -/
def id : GenMap κ where
  run _ x := x
  natural _ _ _ _ := rfl
  all _ _ := #[]
  all_get _ _ _ h := absurd h (Nat.not_lt_zero _)

/-- The outputs, read from `all` where it has them. -/
theorem look_all (Φ : GenMap κ) {α : Type} [Add α] [Sub α] [Mul α] (k : κ → α) (x : ℕ → α) :
    look (Φ.all k x) (Φ.run k x) = Φ.run k x :=
  look_eq (Φ.all_get k x)

/-- The composite `Φ ∘ Ψ`: the inputs of `Φ` are the outputs of `Ψ`. -/
def comp (Φ Ψ : GenMap κ) : GenMap κ where
  run k x := Φ.run k (Ψ.run k x)
  natural f hf k x := by
    rw [Φ.natural f hf, Ψ.natural f hf]
  all k x := Φ.all k (look (Ψ.all k x) (Ψ.run k x))
  all_get k x i h := by
    rw [Φ.all_get, look_all]

/-- `comp` with the outputs of `Ψ` computed once per call, as data: what compiled code runs
(`comp_eq_compM`). Calls of `run` in nested composites would otherwise recompute the inner
outputs at every use, exponentially often in the depth. -/
def compM (Φ Ψ : GenMap κ) : GenMap κ where
  run k x := Φ.run k (look (Ψ.all k x) (Ψ.run k x))
  natural f hf k x := by
    rw [look_all, look_all]
    exact (Φ.comp Ψ).natural f hf k x
  all k x := Φ.all k (look (Ψ.all k x) (Ψ.run k x))
  all_get k x i h := by
    rw [Φ.all_get]

theorem ext_run {Φ Ψ : GenMap κ}
    (hr : ∀ {α : Type} [Add α] [Sub α] [Mul α] (k : κ → α) (x : ℕ → α), Φ.run k x = Ψ.run k x)
    (ha : ∀ {α : Type} [Add α] [Sub α] [Mul α] (k : κ → α) (x : ℕ → α), Φ.all k x = Ψ.all k x) :
    Φ = Ψ := by
  obtain ⟨r, n, a, g⟩ := Φ
  obtain ⟨r', n', a', g'⟩ := Ψ
  obtain rfl : @r = @r' := by
    funext α _ _ _ k x
    exact hr k x
  obtain rfl : @a = @a' := by
    funext α _ _ _ k x
    exact ha k x
  rfl

@[csimp] theorem comp_eq_compM : @comp = @compM := by
  funext κ Φ Ψ
  exact ext_run (fun k x ↦ by simp only [comp, compM, look_all]) fun _ _ ↦ rfl

/-- Output `i` as a computation. -/
def out (Φ : GenMap κ) (i : ℕ) : GenPoly κ where
  run k x := Φ.run k x i
  natural f hf k x := congrFun (Φ.natural f hf k x) i

end GenMap

/-- The composite `G ∘ Φ`: the inputs of `G` are the outputs of `Φ`. -/
def GenPoly.comp {κ : Type} (G : GenPoly κ) (Φ : GenMap κ) : GenPoly κ where
  run k x := G.run k (Φ.run k x)
  natural f hf k x := by
    rw [G.natural f hf, Φ.natural f hf]

/-- `GenPoly.comp` with the outputs of `Φ` computed once, as data: what compiled code runs
(`GenPoly.comp_eq_compM`). -/
def GenPoly.compM {κ : Type} (G : GenPoly κ) (Φ : GenMap κ) : GenPoly κ where
  run k x := G.run k (look (Φ.all k x) (Φ.run k x))
  natural f hf k x := by
    rw [GenMap.look_all, GenMap.look_all]
    exact (G.comp Φ).natural f hf k x

@[csimp] theorem GenPoly.comp_eq_compM : @GenPoly.comp = @GenPoly.compM := by
  funext κ G Φ
  simp only [GenPoly.comp, GenPoly.compM, GenMap.look_all]

end Nieuwland.Check
