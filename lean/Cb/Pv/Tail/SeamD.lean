-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/SeamD.lean: from the smallness test's round to the lookup on its digits: what the lookup
takes in, at the early and the late messages, gives what the round leaves, at the early ones.
Definitions, statements and proofs.

The round (Cb/Pv/Tail/Block.lean) ends with digits that are a part of the further witness: they may
depend on the drawn matrix. Then the prover sends them in a late message, and the lookup reads its
keys off that message. To join two blocks with a sending between them one needs a seam: the relaxed
relation from which the block behind starts, at a pair of an early and a late tuple of messages and
a further witness, gives the relaxed relation at which the block in front ends, at the early tuple
and the further witness that is made from the messages and the one behind (`bk`). The join itself is
not made in this file.

Main names:
  `DIx s`: the name of a digit of one kind: matrix, combination, row of cells.
  `Late`: the letters: the late messages; the further witness behind the sending, and `bk`; the
    entries of both kinds of messages; the numbering of the lookup's keys with the places of its
    digits among the entries (a `CbQ.DatQ I J`, I any type); `ix`: which of the numbering's digits
    a digit of the test is. No law is asked of `ix`.
  `Late.digs`: the digits read off the messages at their places.
  `Late.Reads`: the law of `bk`: the witness that it makes holds the digits of the messages.
  `relOut_of_in`: under the laws of the numbering at the two tables' sizes
    (`DatQ.DatOK s.lo s.hi pp`): every tie and every read at these digits, and each key in the rows
    of its call, give the relation after the round at these digits.
  `in_of_relOut`: the converse, under the same premise and if `ix` is onto.
  `Late.eqs`: what rides along through the lookup: `ride`, at the witness that `bk` makes; every tie
    and every read at the digits of the messages.
  `Late.inD`: the lookup's joint at its start: `eqs`, and each key is in the rows of its call: the
    shift's own joint (`ShiftQ.jIn`, Cb/Pv/Lookup/Shift/ShiftQ.lean) over `eqs`.
  `seam`: under `DatOK` and `Late.Reads`: the seam.

Limits: no `Late` is shown to exist, and no numbering with `DatOK`. The lookup does not occur: no
lookup is shown to be knowledge sound from `inD`. Where `ix` is not onto the lookup shows more
digits to be in their tables than the test has. That `ix` names the right digits is not said by any
law here: with another `ix` the statements hold of other entries. Nothing on an honest prover: the
exact relations are the relaxed ones.


Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.Block
import Cb.Pv.Lookup.Shift.ShiftQAsm
import Cb.Pv.Lookup.Digits.DatQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open Iop Cb.LdLkp CbQ

/-- The name of a digit of one kind: matrix, combination, row of cells. -/
abbrev DIx (s : Size) : Type := (μ : Fin s.NM) × (Fin s.tau × Fin (s.m μ))

/-- The late messages, the entries, and the numbering of the lookup's keys. -/
structure Late {K : Type} {s : Size} (Λ : Letters K s) where
  /-- the late messages; the further witness behind the sending -/
  U : Type
  W₀ : Type
  /-- the names of the numbering's digits of one kind; the entries' names -/
  I : Type
  J : Type
  /-- the further witness in front of the sending, made from the messages and the one behind -/
  bk : Λ.M × U → W₀ → Λ.W
  /-- the entries of an early and a late tuple of messages -/
  ent : Λ.M × U → J → K
  /-- which of the numbering's digits a digit of the test is -/
  ix : DIx s → I
  /-- the numbering of the lookup's keys, and the places of its digits among the entries -/
  Q : DatQ I J

namespace Late
variable {K : Type} [Field K] {s : Size} {Λ : Letters K s} (T : Late Λ)

/-- The digits, read off the messages at their places. -/
def digs (m : Λ.M × T.U) : Dig K s :=
  ⟨fun μ u i => T.ent m (T.Q.lo (T.ix ⟨μ, u, i⟩)), fun μ u i => T.ent m (T.Q.hi (T.ix ⟨μ, u, i⟩))⟩

/-- Every tie and every read at the drawn matrix, at given digits. -/
def Eqs (x : Λ.X) (β : Dr s) (msg : Λ.M) (Z : Dig K s) : Prop :=
  (∀ (μ : Fin s.NM) u (i' : Fin (Alg.symRows (s.m μ))),
    ∑ c, (((β μ u c).val : ℤ) : K) * Λ.sym msg μ i' c = Alg.pack (s.rad : ℤ) (comb Z μ u) i') ∧
  (∀ μ u r,
    ∑ c, (((β μ u c).val : ℤ) : K) * Λ.tab msg μ r c = ∑ i, Λ.w x μ r i * comb Z μ u i)

/-- Each key of the lookup is in the rows of its call. -/
def AllIn (m : Λ.M × T.U) : Prop :=
  AllInQ T.Q.v T.Q.d T.Q.fK T.Q.fT (T.Q.key (T.ent m)) (T.Q.tab (E := K))

/-- The law of `bk`: the witness that it makes holds the digits of the messages. -/
def Reads : Prop := ∀ m w, Λ.dig (T.bk m w) = T.digs m

/-- What rides along through the lookup. -/
def eqs : IOR.Rels Unit (Λ.X × Dr s) Λ.E ((Λ.M × T.U) × T.W₀) where
  rel x y v := Λ.ride (x.1, y) v.1.1 (T.bk v.1 v.2) ∧ Eqs x.1 x.2 v.1.1 (T.digs v.1)
  relR b v := Λ.ride (b.1.1, b.2) v.1.1 (T.bk v.1 v.2) ∧ Eqs b.1.1 b.1.2 v.1.1 (T.digs v.1)
  on _ := True
  core _ := ()

/-- The lookup's joint at its start: the shift's own joint over `eqs`. -/
def inD : IOR.Rels Unit (Λ.X × Dr s) Λ.E ((Λ.M × T.U) × T.W₀) :=
  ((T.Q.sh (E := K) (Λ.X × Dr s)).on T.ent).jIn T.eqs

end Late

variable {K : Type} [Field K] {s : Size} {Λ : Letters K s} (T : Late Λ)

/-- Under the numbering's laws: ties, reads and "each key in the rows of its call" give the relation
after the round, at the digits read off the messages. No law of `ix` is used. -/
theorem relOut_of_in {pp : ℕ} (h : T.Q.DatOK s.lo s.hi pp) (x : Λ.X) (β : Dr s) (m : Λ.M × T.U)
    (he : Late.Eqs x β m.1 (T.digs m)) (hi : T.AllIn m) : relOut Λ x β m.1 (T.digs m) :=
  have hd := (dgQ_in T.Q h (T.ent m)).1 hi
  ⟨fun μ u i => ⟨hd.1 (T.ix ⟨μ, u, i⟩), hd.2 (T.ix ⟨μ, u, i⟩)⟩, he.1, he.2⟩

/-- The converse, if every digit of the numbering is a digit of the test. -/
theorem in_of_relOut {pp : ℕ} (h : T.Q.DatOK s.lo s.hi pp) (hx : Function.Surjective T.ix)
    (x : Λ.X) (β : Dr s) (m : Λ.M × T.U) (ho : relOut Λ x β m.1 (T.digs m)) :
    Late.Eqs x β m.1 (T.digs m) ∧ T.AllIn m := by
  refine ⟨⟨ho.2.1, ho.2.2⟩, (dgQ_in T.Q h (T.ent m)).2 ⟨fun i => ?_, fun i => ?_⟩⟩
  · obtain ⟨j, rfl⟩ := hx i
    exact (ho.1 j.1 j.2.1 j.2.2).1
  · obtain ⟨j, rfl⟩ := hx i
    exact (ho.1 j.1 j.2.1 j.2.2).2

/-- Under the numbering's laws and the law of `bk`: the seam. -/
theorem seam {pp : ℕ} (h : T.Q.DatOK s.lo s.hi pp) (hr : T.Reads) :
    ∀ b m u w, T.inD.relR b ((m, u), w) → (B Λ).relR b (m, T.bk (m, u) w) := by
  intro b m u w hw
  obtain ⟨⟨h1, hq⟩, hi⟩ :
      (Λ.ride (b.1.1, b.2) m (T.bk (m, u) w) ∧ Late.Eqs b.1.1 b.1.2 m (T.digs (m, u))) ∧
        T.AllIn (m, u) := hw
  refine ⟨h1, ?_⟩
  rw [hr (m, u) w]
  exact relOut_of_in T h b.1.1 b.1.2 (m, u) hq hi

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.relOut_of_in
#print axioms Cb.Pv.Tail.in_of_relOut
#print axioms Cb.Pv.Tail.seam
