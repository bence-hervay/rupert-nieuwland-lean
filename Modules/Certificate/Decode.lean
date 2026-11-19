import Modules.Certificate.Syn
import Modules.Check.Leaf.Global
import Modules.Check.Number.Theta

/-!
# Decoding exported data

`Dec α` decodes the exporter's Lean term for a value of type `α` from its syntax (`Cert/Syn.lean`):
anonymous constructors for structures, constructors in dot notation for inductive types, and
literals, lists, tuples and options as Lean writes them. A name refers to an entry of the text
(`Env`) and is replaced by its syntax first (`Syn.deref`).

Decoding is not trusted (`Cert/Syn.lean`): a native check is sound for whatever data it decodes.
It only fails on syntax that the exporter does not write.
-/

namespace Nieuwland.Cert

open Check

/-- The entries of a text by name. -/
abbrev Env := Std.HashMap String Syn

/-- How many references to references `Syn.deref` follows. -/
def derefFuel : ℕ := 8

/-- The syntax `s`, with a reference to an entry replaced by the entry's syntax (references to
references are followed up to `fuel` times). -/
def Syn.deref (env : Env) : ℕ → Syn → Syn
  | fuel + 1, .name s =>
    match env[s]? with
    | some t => deref env fuel t
    | none => .name s
  | _, s => s

/-- Decoding values of type `α` from their syntax. -/
class Dec (α : Type) where
  /-- The value of the syntax `s`, with the entries `env` for references; `none` if `s` does not
  denote a value of `α`. -/
  dec : Env → Syn → Option α

namespace Dec

/-- The syntax `s` with references replaced (`Syn.deref`). -/
@[inline] def view (env : Env) (s : Syn) : Syn :=
  s.deref env derefFuel

instance : Dec ℤ where
  dec env s := match view env s with
    | .num n => some n
    | _ => none

instance : Dec ℕ where
  dec env s := match view env s with
    | .num n => if 0 ≤ n then some n.toNat else none
    | _ => none

instance {n : ℕ} : Dec (Fin n) where
  dec env s := match view env s with
    | .num k => if h : 0 ≤ k ∧ k.toNat < n then some ⟨k.toNat, h.2⟩ else none
    | _ => none

instance : Dec Bool where
  dec env s := match view env s with
    | .name "true" => some true
    | .name "false" => some false
    | _ => none

instance : Dec Empty where
  dec _ _ := none

instance {α : Type} [Dec α] : Dec (List α) where
  dec env s := match view env s with
    | .list xs => xs.toList.mapM (dec env)
    | _ => none

instance {α β : Type} [Dec α] [Dec β] : Dec (α × β) where
  dec env s := match view env s with
    | .tuple xs =>
      if xs.size = 2 then
        return (← dec env xs[0]!, ← dec env xs[1]!)
      else if xs.size > 2 then
        return (← dec env xs[0]!, ← dec env (.tuple (xs.extract 1 xs.size)))
      else none
    | _ => none

instance {α : Type} [Dec α] : Dec (Option α) where
  dec env s := match view env s with
    | .name "none" => some none
    | .someOf a => (dec env a).map some
    | _ => none

/-! ### Exact values -/

instance {d : ℕ} : Dec (ZSqrt d) where
  dec env s := match view env s with
    | .anon #[a, b] => return ⟨← dec env a, ← dec env b⟩
    | _ => none

instance {R : Root} : Dec (ZTheta R) where
  dec env s := match view env s with
    | .anon #[c] => return ⟨← dec env c⟩
    | _ => none

/-! ### Vectors and boxes -/

instance {α : Type} [Dec α] : Dec (V3 α) where
  dec env s := match view env s with
    | .anon #[x, y, z] => return ⟨← dec env x, ← dec env y, ← dec env z⟩
    | _ => none

instance {α : Type} [Dec α] : Dec (Q4 α) where
  dec env s := match view env s with
    | .anon #[w, x, y, z] => return ⟨← dec env w, ← dec env x, ← dec env y, ← dec env z⟩
    | _ => none

instance : Dec Box where
  dec env s := match view env s with
    | .anon #[lo, hi, den] => return ⟨← dec env lo, ← dec env hi, ← dec env den⟩
    | _ => none

instance : Dec ChartBox where
  dec env s := match view env s with
    | .anon #[v, r, b] => return ⟨← dec env v, ← dec env r, ← dec env b⟩
    | _ => none

/-! ### Witnesses -/

instance : Dec SupportData where
  dec env s := match view env s with
    | .anon #[o₀, o₁, a, p] => return ⟨← dec env o₀, ← dec env o₁, ← dec env a, ← dec env p⟩
    | _ => none

instance : Dec Balanced where
  dec env s := match view env s with
    | .anon #[s₀, s₁, s₂, σ] => return ⟨← dec env s₀, ← dec env s₁, ← dec env s₂, ← dec env σ⟩
    | _ => none

instance : Dec WidthSide where
  dec env s := match view env s with
    | .anon #[a, p] => return ⟨← dec env a, ← dec env p⟩
    | _ => none

variable {κ : Type} [Dec κ]

instance : Dec (Width κ) where
  dec env s := match view env s with
    | .anon #[c, p, n] => return ⟨← dec env c, ← dec env p, ← dec env n⟩
    | _ => none

instance : Dec (Centred κ) where
  dec env s := match view env s with
    | .anon #[c, p, q] => return ⟨← dec env c, ← dec env p, ← dec env q⟩
    | _ => none

instance : Dec (Wit κ) where
  dec env s := match view env s with
    | .dot "balanced" #[w] => return .balanced (← dec env w)
    | .dot "width" #[w] => return .width (← dec env w)
    | .dot "centred" #[w] => return .centred (← dec env w)
    | _ => none

/-! ### Trees -/

/-- A cover tree (`Cover`). -/
partial def cover {E : Type} [Dec E] (env : Env) (s : Syn) : Option (Cover E) :=
  match view env s with
  | .dot "leaf" #[e] => return .leaf (← dec env e)
  | .dot "split" #[d, lo, hi] => return .split (← dec env d) (← cover env lo) (← cover env hi)
  | _ => none

instance {E : Type} [Dec E] : Dec (Cover E) := ⟨cover⟩

instance : Dec Blow where
  dec env s := match view env s with
    | .anon #[zs, rho] => return ⟨← dec env zs, ← dec env rho⟩
    | _ => none

mutual

/-- A family tree (`FTree`). -/
partial def ftree {L St : Type} [Dec L] [Dec St] (env : Env) (s : Syn) : Option (FTree L St) :=
  match view env s with
  | .dot "leaf" #[l] => return .leaf (← dec env l)
  | .dot "split" #[k, e, m, lo, hi] =>
    return .split (← dec env k) (← dec env e) (← dec env m) (← ftree env lo) (← ftree env hi)
  | .dot "blow" #[bl, fs] => return .blow (← dec env bl) (← ffaces env fs)
  | .dot "step" #[st, c] => return .step (← dec env st) (← ftree env c)
  | _ => none

/-- The faces of a blow-up (`FFaces`). -/
partial def ffaces {L St : Type} [Dec L] [Dec St] (env : Env) (s : Syn) :
    Option (FFaces L St) :=
  match view env s with
  | .dot "nil" #[] => some .nil
  | .dot "cons" #[j, u, t, r] =>
    return .cons (← dec env j) (← dec env u) (← ftree env t) (← ffaces env r)
  | _ => none

end

instance {L St : Type} [Dec L] [Dec St] : Dec (FTree L St) := ⟨ftree⟩

/-! ### Polar zooms -/

instance : Dec (PolarFace κ) where
  dec env s := match view env s with
    | .anon #[a, u, t] => return ⟨← dec env a, ← dec env u, ← dec env t⟩
    | _ => none

instance : Dec (Polar κ) where
  dec env s := match view env s with
    | .anon #[c, d, fs] => return ⟨← dec env c, ← dec env d, ← dec env fs⟩
    | _ => none

/-! ### Weighted zooms -/

instance : Dec (Obst κ) where
  dec env s := match view env s with
    | .anon #[p, e, st, d] => return ⟨← dec env p, ← dec env e, ← dec env st, ← dec env d⟩
    | _ => none

instance : Dec ExclLeaf where
  dec env s := match view env s with
    | .anon #[i, j, e, d] => return ⟨← dec env i, ← dec env j, ← dec env e, ← dec env d⟩
    | _ => none

instance : Dec OutLeaf where
  dec env s := match view env s with
    | .anon #[c, u, e, d] => return ⟨← dec env c, ← dec env u, ← dec env e, ← dec env d⟩
    | _ => none

instance : Dec LocLeaf where
  dec env s := match view env s with
    | .anon #[i, j, p₀, p₁, f, e, d] =>
      return ⟨← dec env i, ← dec env j, ← dec env p₀, ← dec env p₁, ← dec env f, ← dec env e,
        ← dec env d⟩
    | _ => none

instance : Dec (WLeaf κ) where
  dec env s := match view env s with
    | .dot "obst" #[o] => return .obst (← dec env o)
    | .dot "excl" #[e] => return .excl (← dec env e)
    | .dot "out" #[o] => return .out (← dec env o)
    | .dot "loc" #[l] => return .loc (← dec env l)
    | _ => none

instance : Dec (WFrame κ) where
  dec env s := match view env s with
    | .anon #[L, p0, mv, mr, w, nv, dv, nr, dr, E] =>
      return ⟨← dec env L, ← dec env p0, ← dec env mv, ← dec env mr, ← dec env w, ← dec env nv,
        ← dec env dv, ← dec env nr, ← dec env dr, ← dec env E⟩
    | _ => none

instance : Dec (WZoom κ) where
  dec env s := match view env s with
    | .anon #[f, fs, c] => return ⟨← dec env f, ← dec env fs, ← dec env c⟩
    | _ => none

/-! ### Chart trees -/

instance : Dec (TPart κ) where
  dec env s := match view env s with
    | .anon #[w, wt, dom, pe, e] =>
      return ⟨← dec env w, ← dec env wt, ← dec env dom, ← dec env pe, ← dec env e⟩
    | _ => none

instance : Dec (TObst κ) where
  dec env s := match view env s with
    | .anon #[p, d] => return ⟨← dec env p, ← dec env d⟩
    | _ => none

instance : Dec TOut where
  dec env s := match view env s with
    | .anon #[c, u, e, d] => return ⟨← dec env c, ← dec env u, ← dec env e, ← dec env d⟩
    | _ => none

instance : Dec TExcl where
  dec env s := match view env s with
    | .anon #[i, j, e, d, wu, wq] =>
      return ⟨← dec env i, ← dec env j, ← dec env e, ← dec env d, ← dec env wu, ← dec env wq⟩
    | _ => none

/-- A leaf of a chart tree (`TLeaf`). -/
partial def tleaf (env : Env) (s : Syn) : Option (TLeaf κ) :=
  match view env s with
  | .dot "obst" #[o] => return .obst (← dec env o)
  | .dot "out" #[o] => return .out (← dec env o)
  | .dot "excl" #[x] => return .excl (← dec env x)
  | .dot "obstB" #[w, o] => return .obstB (← dec env w) (← dec env o)
  | .dot "outB" #[w, o] => return .outB (← dec env w) (← dec env o)
  | .dot "exclB" #[w, x] => return .exclB (← dec env w) (← dec env x)
  | .dot "obstF" #[w, f, o] => return .obstF (← dec env w) (← dec env f) (← dec env o)
  | .dot "exact" #[l] => return .exact (← tleaf env l)
  | _ => none

instance : Dec (TLeaf κ) := ⟨tleaf⟩

instance : Dec (Affine κ) where
  dec env s := match view env s with
    | .anon #[sl, m, c, inv, e, sc, lo, hi] =>
      return ⟨← dec env sl, ← dec env m, ← dec env c, ← dec env inv, ← dec env e, ← dec env sc,
        ← dec env lo, ← dec env hi⟩
    | _ => none

instance : Dec (Rechart κ) where
  dec env s := match view env s with
    | .anon #[k, a, b, psi, d, lu, lq, sg, lo, hi, den, ex, dp] =>
      return ⟨← dec env k, ← dec env a, ← dec env b, ← dec env psi, ← dec env d, ← dec env lu,
        ← dec env lq, ← dec env sg, ← dec env lo, ← dec env hi, ← dec env den, ← dec env ex,
        ← dec env dp⟩
    | _ => none

instance : Dec (TStep κ) where
  dec env s := match view env s with
    | .dot "affine" #[a] => return .affine (← dec env a)
    | .dot "rechart" #[r] => return .rechart (← dec env r)
    | _ => none

instance : Dec (ChartTree κ) where
  dec env s := match view env s with
    | .anon #[n, L, t] => return ⟨← dec env n, ← dec env L, ← dec env t⟩
    | _ => none

/-! ### Symmetry data -/

instance : Dec Score where
  dec env s := match view env s with
    | .anon #[a, b, w] => return ⟨← dec env a, ← dec env b, ← dec env w⟩
    | _ => none

instance : Dec (Symm κ) where
  dec env s := match view env s with
    | .anon #[g, den, img] => return ⟨← dec env g, ← dec env den, ← dec env img⟩
    | _ => none

instance : Dec (SymmData κ) where
  dec env s := match view env s with
    | .anon #[C, m, syms, sc] => return ⟨← dec env C, ← dec env m, ← dec env syms, ← dec env sc⟩
    | _ => none

/-! ### Claims and leaves -/

instance : Dec (Evidence κ) where
  dec env s := match view env s with
    | .dot "balanced" #[w] => return .balanced (← dec env w)
    | .dot "width" #[w] => return .width (← dec env w)
    | .dot "centred" #[w] => return .centred (← dec env w)
    | .dot "polar" #[z] => return .polar (← dec env z)
    | .dot "wzoom" #[z] => return .wzoom (← dec env z)
    | .dot "tree" #[t] => return .tree (← dec env t)
    | .dot "wzoomLoc" #[z, D, i, j, k, l] =>
      return .wzoomLoc (← dec env z) (← dec env D) (← dec env i) (← dec env j) (← dec env k)
        (← dec env l)
    | _ => none

instance : Dec (Claim κ) where
  dec env s := match view env s with
    | .anon #[r, p, e] => return ⟨← dec env r, ← dec env p, ← dec env e⟩
    | _ => none

instance : Dec Excl where
  dec env s := match view env s with
    | .anon #[r, i, j] => return ⟨← dec env r, ← dec env i, ← dec env j⟩
    | _ => none

instance : Dec (Leaf κ) where
  dec env s := match view env s with
    | .dot "claim" #[c] => return .claim (← dec env c)
    | .dot "excl" #[e] => return .excl (← dec env e)
    | .dot "zoom" #[r, z] => return .zoom (← dec env r) (← dec env z)
    | .dot "tree" #[r, p, t] => return .tree (← dec env r) (← dec env p) (← dec env t)
    | .dot "mapped" #[r, p, i, j, c] =>
      return .mapped (← dec env r) (← dec env p) (← dec env i) (← dec env j) (← dec env c)
    | _ => none

instance : Dec (ChartChange κ) where
  dec env s := match view env s with
    | .anon #[src, sp, dst, dp] => return ⟨← dec env src, ← dec env sp, ← dec env dst, ← dec env dp⟩
    | _ => none

end Dec

end Nieuwland.Cert
