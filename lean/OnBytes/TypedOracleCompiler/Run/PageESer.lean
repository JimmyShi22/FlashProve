-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageESer.lean: a serialiser of the seeds of a table's record that compiles to code;
so the total code behind the escape of an entry's page (OnBytes/TypedOracleCompiler/Run/PageEBack.lean: `backE2`) at
the interface `LXEs` (that is, at `earlyTwo d₁` and `seedEntry lg s`), as a term that compiles.

Why. `backE2` takes a serialiser ss of what stands in the seeds' place of an instance.
PageEBack.lean offered `serFinite`, an enumeration by choice: it has no code, and a page that is to
be evaluated must compile whole, also where it is never run. The seeds of one table's record are
`Fin s → (Fin lg → GE) × NZ` (`Sd1 lg s`, OnBytes/TypedOracleCompiler/Slice/EntryDelivers.lean); GE is three
elements of the prime field; NZ its elements other than 0.

 - `vecEquiv`, `serVec A n`: functions on `Fin n`, entry by entry;
 - `serSub A p`: a subtype with a test that computes;
 - `serFGold` (an element of the prime field as a number below the prime), `serCubic`, `serGE`,
 `serNZ`;
 - `serSd1 lg s` : Ser (Sd1 lg s), `serSd2 lg s`: of a pair of these;
 - `backEs`: `backE2` at `earlyTwo d₁`, `seedEntry lg s` and `serSd2 lg s`: the total code at `LXEs
 (An := List T3) (Bd := List Bool) lg s D d₁` and D.K + 1 blocks.

Main definitions: `serVec`, `serSub`, `serSd1`, `serSd2`, `backEs`.

What is not said. The bodies' data B and the serialiser sg of stored symbols stay letters. What the
strings are is of no weight: any total code serves. Nothing was evaluated. Nothing on soundness. The
sibling is a second version of the library's soundness road, under OnBytes/TypedOracleCompiler/.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageEBack
import OnBytes.TypedOracleCompiler.Slice.EntryDelivers

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PageESer
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (GE NZ seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-! ## Functions on Fin n; subtypes -/

/-- A function on n + 1 numbers as its first value and the others. -/
def vecEquiv (α : Type) (n : ℕ) : (Fin (n + 1) → α) ≃ α × (Fin n → α) where
  toFun := fun f => (f 0, fun i => f i.succ)
  invFun := fun p => Fin.cons p.1 p.2
  left_inv := fun f => funext fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv := fun _ => rfl

/-- Functions on `Fin n`, entry by entry. -/
def serVec {α : Type} (A : Ser α) : (n : ℕ) → Ser (Fin n → α)
  | 0 => Ser.ofEquiv ⟨fun _ => (), fun _ i => i.elim0, fun _ => funext fun i => i.elim0,
      fun _ => rfl⟩ Ser.unit
  | n + 1 => Ser.ofEquiv (vecEquiv α n) (Ser.prod A (serVec A n))

/-- A subtype with a test that computes. -/
def serSub {α : Type} (A : Ser α) (p : α → Prop) [DecidablePred p] : Ser { x // p x } where
  put := fun x => A.put x.val
  get := fun s => (A.get s).bind fun y => if h : p y.1 then some (⟨y.1, h⟩, y.2) else none
  get_put := fun a rest => by
    rw [A.get_put, Option.bind_some]
    exact dif_pos a.property
  put_get := fun s a rest h => by
    obtain ⟨y, hy, h'⟩ := Option.bind_eq_some_iff.1 h
    by_cases hp : p y.1
    · rw [dif_pos hp] at h'
      have e := Option.some.inj h'
      have e1 : a = ⟨y.1, hp⟩ := (congrArg Prod.fst e).symm
      have e2 : rest = y.2 := (congrArg Prod.snd e).symm
      rw [e1, e2]
      exact A.put_get s y.1 y.2 hy
    · rw [dif_neg hp] at h'
      cases h'

/-! ## The field's elements -/

/-- An element of the prime field, as a number below the prime. -/
def serFGold : Ser Code.FGold := (Ser.fin (2 ^ 64 - 2 ^ 32 + 1) : Ser (Fin (2 ^ 64 - 2 ^ 32 + 1)))

/-- Three elements. -/
def serCubic {K : Type} {c : K} (A : Ser K) : Ser (Code.Cubic K c) :=
  Ser.ofEquiv (β := K × K × K)
    ⟨fun x => (x.c0, x.c1, x.c2), fun y => ⟨y.1, y.2.1, y.2.2⟩, fun _ => rfl, fun _ => rfl⟩
    (Ser.prod A (Ser.prod A A))

/-- An element of the extension field. -/
def serGE : Ser GE := serCubic serFGold

/-- One other than 0. -/
def serNZ : Ser NZ := serSub serGE fun β => β ≠ 0

/-! ## The seeds -/

/-- The seeds of one table's record. -/
def serSd1 (lg s : ℕ) : Ser (Sd1 lg s) := serVec (Ser.prod (serVec serGE lg) serNZ) s

/-- Of both tables' records. -/
def serSd2 (lg s : ℕ) : Ser (Sd1 lg s × Sd1 lg s) := Ser.prod (serSd1 lg s) (serSd1 lg s)

/-- The total code behind the escape at the interface `LXEs` (that is, at `earlyTwo d₁` and
`seedEntry lg s`), as a term that compiles. -/
def backEs {lg s : ℕ} (D : PQ.XD) (d₁ : Sd1 lg s) (B : PQ.BodyD (List Bool)) (sg : Ser SgX) :
    StrCode (AllPts 256 (D.K + 1) (LXEs (An := List T3) (Bd := List Bool) lg s D d₁)) :=
  PageEBack.backE2 D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) (serSd2 lg s) B sg

end TypedOracleCompiler.Run.PageESer
