-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/JoinData.lean: numberings and serializers of a round merged by (J1) (Iop/Join.lean,
Iop/BatchJoin.lean). All of it is built from the data of the two rounds. Iop/RecutData.lean uses
them. (Words of this library: lean/GLOSSARY.md.)

Positions: those of the first round are numbered before those of the second (`numSum`, `numSubSum`),
so in a tree of the merged round the leaves of the first message come before those of the second.
  `SerR.joinMsg`             the serializer of the merged round
  `NumRB`, `NumRB.joinMsg`   the two numberings of one round of a protocol with slots; those of the
                             merged round
Limits: the file has no widths (bounds in bits on the encodings) and no lists of opened positions,
round by round.
-/
import Iop.JoinProofs
import Iop.BatchJoin
import Iop.BatchWireOf
import Iop.SerB

namespace Iop

/-! ## 1. Numberings and serializers of merged rounds -/

/-- a sum: the elements of the first type before those of the second -/
def numSum {α β : Type} (fa : Fintype α) (fb : Fintype β)
    (na : α ≃ Fin (@Fintype.card α fa)) (nb : β ≃ Fin (@Fintype.card β fb)) :
    α ⊕ β ≃ Fin (@Fintype.card (α ⊕ β) (@instFintypeSum α β fa fb)) :=
  letI := fa
  letI := fb
  ((Equiv.sumCongr na nb).trans finSumFinEquiv).trans (finCongr Fintype.card_sum.symm)

/-- a subtype of a sum: its elements in the first type before those in the second -/
def numSubSum {α β : Type} (P : α ⊕ β → Prop) [Fintype {c // P c}] [Fintype {a // P (.inl a)}]
    [Fintype {b // P (.inr b)}] (na : {a // P (.inl a)} ≃ Fin (Fintype.card {a // P (.inl a)}))
    (nb : {b // P (.inr b)} ≃ Fin (Fintype.card {b // P (.inr b)})) :
    {c // P c} ≃ Fin (Fintype.card {c // P c}) :=
  ((Equiv.subtypeSum.trans (Equiv.sumCongr na nb)).trans finSumFinEquiv).trans
    (finCongr ((Fintype.card_congr Equiv.subtypeSum).trans Fintype.card_sum).symm)

/-- (J1): one bit that says to which message a position belongs, then the old encoding; the two
plain parts one after the other -/
def SerR.joinMsg {r1 r2 : Round} (a : SerR r1) (b : SerR r2) : SerR (r1.joinMsg r2) :=
  (Ser.ofEquiv (Equiv.sumSigmaDistrib fun p => (r1.joinMsg r2).Sym p) (Ser.sum a.1 b.1),
    Ser.prod a.2 b.2)

/-! ## 2. Numberings for a protocol with slots -/


/-- the two numberings of one round of a protocol with slots -/
abbrev NumRB {r : Round} (a : RAnn r) (pt : r.IsPoint) : Type :=
  ({p : r.Pos // a.own p = false} ≃ Fin (a.card0 pt)) ×
    ({p : r.Pos // a.own p = true} ≃ Fin (a.cardJ pt))

def NumRB.joinMsg {r1 r2 : Round} {a1 : RAnn r1} {a2 : RAnn r2} {p1 : r1.IsPoint} {p2 : r2.IsPoint}
    (n1 : NumRB a1 p1) (n2 : NumRB a2 p2) :
    NumRB (a1.joinMsg a2) (p1.joinMsg p2) :=
  letI := p1.finPos
  letI := p2.finPos
  (numSubSum (fun p : r1.Pos ⊕ r2.Pos => (a1.joinMsg a2).own p = false) n1.1 n2.1,
    numSubSum (fun p : r1.Pos ⊕ r2.Pos => (a1.joinMsg a2).own p = true) n1.2 n2.2)



variable {I X : Type} {L : BatchProtocol I X}




end Iop
