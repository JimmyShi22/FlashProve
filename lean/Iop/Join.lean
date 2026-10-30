-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Join.lean: merging two consecutive rounds into one, for ordinary IOPs. The file defines the
merged rounds and the maps from them back to the two rounds. Lemmas on them are in
Iop/JoinProofs.lean, the form for protocols with slots in Iop/BatchJoin.lean, and plans that split
and merge the rounds of a protocol in Iop/Recut.lean. (Words of this library: lean/GLOSSARY.md.)

Why. The compiler turns every round into one Fiat-Shamir query.
An implementation may hash several prover messages by one call, and may derive several challenges
from one state of its Fiat-Shamir chain, with nothing hashed between.
A protocol that is composed of blocks (single sub-protocols) has a round for each of these.
Two consecutive rounds can be merged, without any change of the protocol's meaning, in two cases.
  (J1) "msg":  the challenge of the first round has one value u. (m1 . u) (m2 . c2) becomes
               ((m1, m2) . c2). It undoes a split of Iop/Split.lean, up to the form of the types.
  (J2) "chal": the prover message of the second round has one value (the maps back of positions
               and symbols also ask that it has no position: `noPos`). (m1 . c1) (() . c2) becomes
               (m1 . (c1, c2)).
In all other cases the second prover message may depend on the first challenge, and the two rounds
cannot be merged.

Main names: `Round.joinMsg r1 r2` (J1), `Round.joinChal r1 r2` (J2); the maps back: `Tr.unMsg`,
`Tr.unChal`, `OPos.unMsg`, `OPos.unChal`, `OSym.unMsg`, `OSym.unChal`.
Order of the steps. Rounds are merged before challenges are computed from other uniform strings
(Iop/Pull.lean, Iop/Univ.lean). After that step the challenge of a round with
`Chal = Unit` may be a tuple of hash blocks, so that it has more than one value and (J1) does not
apply.
What that step then makes of a pair (c1, c2) depends on the sampler: with the one sampler of
Iop/Univ.lean the pair is one number modulo card C1 * card C2, not two samples side by side.
Notation: (m . c): one round of a transcript: the prover message m, then the challenge c (`Tr`,
Iop/Shape.lean: `r.Msg × r.Chal × Tr s`); C1, C2: `r1.Chal`, `r2.Chal`; `Round`: a structure
(Iop/Shape.lean): one round: a prover message, which consists of an oracle part and a plain part
that is read in full, and then a challenge, uniform in the finite set `Chal`; the oracle part: an
element of `Orc` that is read by queries p : `Pos` with answers in `Sym p` (the field `rd`);
`Plain`: the type of the plain part; `dOrc`, `dPlain`: a fixed message of the right format;
`r.Msg : Type` (there): `r.Orc × r.Plain`: a prover message of the round; `Shape : Type 1` (there):
the list of a protocol's rounds, in order; `Tr s : Type` (there): full transcripts; `OPos s : Type`
(there): positions of all prover oracles; `OSym s p : Type` (there): the alphabet at a position.
Limits:
  Nothing is said on which rounds of an instance should be merged.
  (J1) puts two trees side by side under one root (each position of each message is a separate leaf,
       the first message's leaves before the second's). It does not put two symbols into one leaf.
  (J2) only merges. A challenge cannot be split again for free: from a count over pairs one gets no
       small count for the first coordinate only. So where an implementation samples, hashes the
       empty string, and samples again, (J2) gives one query where the implementation has two.
  For (oracle . one value) (nothing . c2) both steps apply to an ordinary IOP; (J2) keeps the prover
  message of r1 as it is, and its challenge Unit × C2 has as many values as C2. In a protocol with
  slots (J2) applies only if the two rounds have the same kind (shared by all slots, or local:
  Iop/Batch.lean).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Iop.InteractiveOracleProof

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. The merged rounds -/

/-- (J1) Two prover messages as one; the challenge of the second round. -/
@[reducible] def Round.joinMsg (r1 r2 : Round) : Round where
  Orc := r1.Orc × r2.Orc
  Pos := r1.Pos ⊕ r2.Pos
  Sym := fun p => match p with
    | .inl p => r1.Sym p
    | .inr p => r2.Sym p
  rd := fun o p => match p with
    | .inl p => r1.rd o.1 p
    | .inr p => r2.rd o.2 p
  Plain := r1.Plain × r2.Plain
  Chal := r2.Chal
  dOrc := (r1.dOrc, r2.dOrc)
  dPlain := (r1.dPlain, r2.dPlain)

/-- (J2) The prover message of the first round; the two challenges as one. -/
@[reducible] def Round.joinChal (r1 r2 : Round) : Round where
  Orc := r1.Orc
  Pos := r1.Pos
  Sym := r1.Sym
  rd := r1.rd
  Plain := r1.Plain
  Chal := r1.Chal × r2.Chal
  dOrc := r1.dOrc
  dPlain := r1.dPlain

section OneStep
variable {r1 r2 : Round} {s : Shape}

/-- the two messages of a merged message -/
def Round.msgFst (m : (r1.joinMsg r2).Msg) : r1.Msg := (m.1.1, m.2.1)
def Round.msgSnd (m : (r1.joinMsg r2).Msg) : r2.Msg := (m.1.2, m.2.2)
/-- the merged message -/
def Round.msgPair (m1 : r1.Msg) (m2 : r2.Msg) : (r1.joinMsg r2).Msg := ((m1.1, m2.1), (m1.2, m2.2))

/-- the default message of a round (`dOrc`, `dPlain`) -/
def Round.dMsg (r : Round) : r.Msg := (r.dOrc, r.dPlain)

/-- A transcript that begins with a round merged by (J1), with the two rounds again. -/
def Tr.unMsg (u : r1.Chal) (z : Tr (r1.joinMsg r2 :: s)) : Tr (r1 :: r2 :: s) :=
  (Round.msgFst z.1, u, Round.msgSnd z.1, z.2.1, z.2.2)

/-- A transcript that begins with a round merged by (J2), with the two rounds again. -/
def Tr.unChal (z : Tr (r1.joinChal r2 :: s)) : Tr (r1 :: r2 :: s) :=
  (z.1, z.2.1.1, r2.dMsg, z.2.1.2, z.2.2)

variable (r1 r2 s)

def OPos.unMsg : OPos (r1.joinMsg r2 :: s) ≃ OPos (r1 :: r2 :: s) :=
  Equiv.sumAssoc r1.Pos r2.Pos (OPos s)

def OPos.unChal (noPos : r2.Pos → Empty) : OPos (r1.joinChal r2 :: s) ≃ OPos (r1 :: r2 :: s) where
  toFun := fun z => match z with
    | .inl p => .inl p
    | .inr q => .inr (.inr q)
  invFun := fun z => match z with
    | .inl p => .inl p
    | .inr (.inl p) => (noPos p).elim
    | .inr (.inr q) => .inr q
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by
    rintro (_ | p | _)
    · rfl
    · exact (noPos p).elim
    · rfl

variable {r1 r2 s}

/-- The alphabet at a position does not change. -/
def OSym.unMsg :
    (z : OPos (r1.joinMsg r2 :: s)) → OSym (r1.joinMsg r2 :: s) z →
    OSym (r1 :: r2 :: s) (OPos.unMsg r1 r2 s z)
  | .inl (.inl _), a => a
  | .inl (.inr _), a => a
  | .inr _, a => a

def OSym.reMsg :
    (z : OPos (r1.joinMsg r2 :: s)) →
    OSym (r1 :: r2 :: s) (OPos.unMsg r1 r2 s z) → OSym (r1.joinMsg r2 :: s) z
  | .inl (.inl _), a => a
  | .inl (.inr _), a => a
  | .inr _, a => a

def OSym.unChal (noPos : r2.Pos → Empty) :
    (z : OPos (r1.joinChal r2 :: s)) → OSym (r1.joinChal r2 :: s) z →
    OSym (r1 :: r2 :: s) (OPos.unChal r1 r2 s noPos z)
  | .inl _, a => a
  | .inr _, a => a

def OSym.reChal (noPos : r2.Pos → Empty) :
    (z : OPos (r1.joinChal r2 :: s)) →
    OSym (r1 :: r2 :: s) (OPos.unChal r1 r2 s noPos z) → OSym (r1.joinChal r2 :: s) z
  | .inl _, a => a
  | .inr _, a => a

end OneStep


















variable {X : Type} {E : ExtSpec}

end Iop
