-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Wire.lean: parts of the wire record: what the compiler needs besides the protocols.

The file has definitions only. `Dig`, `Enum` and `WireE` are read by the compiled scheme, which the
compiler writes as an explicit term, with nothing obtained from a statement of existence. `WireR`,
`WireS`: the record of a round without components; the statements on sizes read it
(Compile/Size.lean, `flatS` of Compile/Batch/Size.lean). The wire record of protocols with slots is
Iop/BatchWire.lean.
-/
import Iop.InteractiveOracleProof

namespace Iop

/-- a hash block (a digest or a chaining value): lam bits -/
abbrev Dig (lam : ℕ) : Type := Fin lam → Bool

/-- an explicit enumeration of a finite non-empty type, from which the scheme samples -/
structure Enum (β : Type) where
  n : ℕ
  e : Fin (n + 1) → β

/-- One round: its oracle is a string; which of the 2^depth leaves of its tree holds which position;
how K hash blocks give its challenge. -/
structure WireR (lam K : ℕ) (r : Round) where
  pt : r.IsPoint
  depth : ℕ
  place : r.Pos → ℕ
  posAt : ℕ → Option r.Pos
  chal : (Fin K → Dig lam) → r.Chal

def WireS (lam K : ℕ) : Shape → Type
  | [] => Unit
  | r :: s => WireR lam K r × WireS lam K s

/-- External strings: a list of all positions; under which root a position is; its leaf; a string
built from given symbols. -/
structure WireE (E : ExtSpec) where
  all : List E.Pos
  which : E.Pos → ℕ
  leaf : E.Pos → ℕ
  /-- the depth of the trees over the external strings: the length of every Merkle path is checked
  against it -/
  depth : ℕ
  build : (E.Pos → Option E.Sym) → E.Str
  dec : DecidableEq E.Pos
  /-- are the opened leaves of the trees over the external strings checked together, by pruned
  Merkle paths (true), or each along a separate path (false)? Read only by the compiled scheme
  (Compile/Batch/Verifier.lean); no condition on a wire record mentions it, but for `ExtAscOK`
  (Compile/Batch/SizeO.lean). -/
  pr : Bool := false

/-! ## The conditions on a wire record (whoever builds one proves them) -/
open Prob

def Enum.OK {β : Type} (e : Enum β) : Prop := Function.Bijective e.e

structure WireE.OK {E : ExtSpec} (we : WireE E) : Prop where
  nodup : we.all.Nodup
  complete : ∀ p, p ∈ we.all
  build_rd : ∀ f p a, f p = some a → E.rd (we.build f) p = a

end Iop
