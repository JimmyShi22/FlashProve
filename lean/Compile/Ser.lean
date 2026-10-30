-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Ser.lean: serialisers (`Ser`, Iop/Ser.lean) of parts of the compiled scheme's typed queries
and proofs, each explicit and self-delimiting. The serialiser of the whole queries is in
Compile/Batch/Ser.lean.
  `Ser.toStrCode`      a serialiser as an injective encoding as bit strings, with a parser
                       (`StrCode`, Rom/Hotel.lean)
  `serSymAny`          a symbol of some prover oracle of a shape, with its position (`SymAny`,
                       Compile/Oracles.lean)
  `serTag`             the name of a protocol (`Tag`, Compile/Oracles.lean)
  `serBits`            a string of bits
  `serDig`, `serDigs`  a digest; a list of digests

Each is written as a term. `serSymAny` is made from the serialisers of the rounds' symbols. These
are data (`SerS`, Iop/SerS.lean), supplied by whoever builds the protocol; for finite types
Mathlib's FinEnum gives them. No serialiser is obtained from a statement of existence. (Lean's list
of axioms does not show this: the head of Iop/Ser.lean.)

Format: sums have one leading bit; lists and strings of bits have a length prefix; digests are lam
raw bits; lengths are written in the self-delimiting binary code Ser.natG.
-/
import Iop.SerS
import Compile.Oracles
import Rom.Hotel

set_option autoImplicit false

namespace Compile
open Iop Rom

/-- a serialiser as an injective encoding as bit strings, with a parser (`StrCode`,
Rom/Hotel.lean) -/
def _root_.Iop.Ser.toStrCode {α : Type} (A : Ser α) : StrCode α :=
  ⟨A.put, A.parse, A.parse_put, fun _ _ h => A.put_of_parse h⟩

variable {I X : Type}

/-! ## The parts -/

def serSymAny : (s : Shape) → SerS s → Ser (SymAny s)
  | [], _ =>
      { put := fun x => (show Empty from x.1).elim
        get := fun _ => none
        get_put := fun x _ => (show Empty from x.1).elim
        put_get := fun _ x _ _ => (show Empty from x.1).elim }
  | r :: s, ((a, _), e) =>
      Ser.ofEquiv (Equiv.sumSigmaDistrib (α := r.Pos) (β := OPos s) (OSym (r :: s)))
        (Ser.sum a (serSymAny s e))

/-- test: 0; link: 10; onl: 11 -/
def serTag : Ser Tag :=
  Ser.ofEquiv (β := Unit ⊕ (Unit ⊕ Unit))
    ⟨fun t => match t with
      | .test => .inl ()
      | .link => .inr (.inl ())
      | .onl => .inr (.inr ()),
     fun x => match x with
      | .inl _ => .test
      | .inr (.inl _) => .link
      | .inr (.inr _) => .onl,
     fun t => by cases t <;> rfl,
     fun x => by rcases x with _ | _ | _ <;> rfl⟩
    (Ser.sum Ser.unit (Ser.sum Ser.unit Ser.unit))

/-- a string of bits: its length, then the bits -/
def serBits : Ser Bits := Ser.lenList Ser.bool

/-- a digest: lam raw bits -/
def serDig (lam : ℕ) : Ser (Dig lam) := Ser.bits lam

/-- a list of digests: their number, then the digests -/
def serDigs (lam : ℕ) : Ser (List (Dig lam)) := Ser.lenList (serDig lam)

end Compile
