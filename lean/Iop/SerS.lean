-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SerS.lean: what the serialization of the scheme's queries needs of a protocol, as data.

The compiled scheme's typed queries are encoded as strings (Iop/Ser.lean). For each round: a
serializer (Iop/Ser.lean) of the pairs (position, symbol) of its oracle and one of its plain part
(`SerS`) (words of this library: lean/GLOSSARY.md). The data of a record of protocols:
Iop/SerB.lean. `Round` and `Shape` do not contain these data. The file also has widths and numbers
of opened positions, round by round (`BitsS`, `SerS.Within`, `OpenList`, `InteractiveOracleProof.OpensLe`).

Notation: `Round` (a structure, Iop/Shape.lean): one round: a prover message, which consists of an
oracle part and a plain part that is read in full, and then a challenge (among its fields:
`Pos : Type`, `Sym : Pos → Type`, `Plain : Type`); `Samplers s : Type 1` (Iop/Pull.lean): one
sampler for each round; `ExtSpec` (a structure, Iop/InteractiveOracleProof.lean): external strings: oracles that are
fixed before the first message.
-/
import Iop.Ser
import Iop.Pull
import Mathlib.Data.Finset.Sum

set_option autoImplicit false

namespace Iop

/-- the two serializers of one round: of (position, symbol), and of the plain part -/
abbrev SerR (r : Round) : Type := Ser (Σ p : r.Pos, r.Sym p) × Ser r.Plain

/-- For each round of a list its two serializers. -/
def SerS : Shape → Type
  | [] => Unit
  | r :: s => SerR r × SerS s

/-- Rounds whose challenges are computed by samplers (`Shape.pull`) have the same positions, symbols
and plain parts. -/
def SerS.pull : (s : Shape) → (σ : Samplers s) → SerS s → SerS (Shape.pull s σ)
  | [], _, _ => ()
  | _ :: s, (_, σs), (a, e) => (a, SerS.pull s σs e)

/-! ## Widths, and numbers of opened positions, round by round -/

/-- For each round two numbers: the bits of a pair (position, symbol), and the bits of the plain
part. -/
def BitsS : Shape → Type
  | [] => Unit
  | _ :: s => (ℕ × ℕ) × BitsS s

/-- The serializers of all rounds encode within the given numbers of bits. -/
def SerS.Within : (s : Shape) → SerS s → BitsS s → Prop
  | [], _, _ => True
  | _ :: s, ((a, b), e), ((x, y), t) =>
    (∀ z, (a.put z).length ≤ x) ∧ (∀ z, (b.put z).length ≤ y) ∧ SerS.Within s e t

/-- the bits of all plain parts together -/
def BitsS.plainBits : (s : Shape) → BitsS s → ℕ
  | [], _ => 0
  | _ :: s, ((_, y), t) => y + BitsS.plainBits s t

/-- For each round a number: how many positions of its oracle are opened at most. -/
def OpenList : Shape → Type
  | [] => Unit
  | _ :: s => ℕ × OpenList s

/-- A set of positions has, in each round, at most the given number of elements. -/
def OpenList.Bounds : (s : Shape) → OpenList s → Finset (OPos s) → Prop
  | [], _, _ => True
  | r :: s, (n, o), A =>
      (Finset.toLeft (show Finset (r.Pos ⊕ OPos s) from A)).card ≤ n ∧
        OpenList.Bounds s o (Finset.toRight (show Finset (r.Pos ⊕ OPos s) from A))

/-- The verifier reads at most o_r positions of the oracle of round r, whatever the instance, its
randomness and the plain parts. -/
def InteractiveOracleProof.OpensLe {X : Type} {E : ExtSpec} (Q : InteractiveOracleProof X E) (o : OpenList Q.shape) : Prop :=
  ∀ x ρ pl, OpenList.Bounds Q.shape o (Q.reads x ρ pl)

end Iop
