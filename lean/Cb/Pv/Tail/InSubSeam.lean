-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/InSubSeam.lean: the seam in front of the lookup on the digits, in the form that the link
of a sub-proof asks, from Cb/Pv/Tail/SeamD.lean.

The link's frame has all messages in one tuple, with a left part (what stood when the matrix was
drawn) and a right part (the late message with the digits). Its letter for the further witness in
front of the second sending reads the late part alone. SeamD.lean has the seam at a pair of an early
and a late tuple, with letters that may read both. Here the letters read the late part alone.

Main names:
  `LateU Λ U W₀`: the letters: `bk : U → W₀ → Λ.W`; the entries of a late tuple, `ent : U → J → K`;
    the numbering of the lookup's keys `Q`; `ix`.
  `LateU.late`: the record `Late` of SeamD.lean at them. `LateU.digs`, `LateU.Reads`: the digits
    read off the late tuple; the law of `bk`.
  `LateU.eqs₁`, `LateU.inD₁`: what rides through the lookup, and the lookup's joint at its start, at
    one tuple of messages with a left and a right part. `inD₁` is the shift's own joint
    (`ShiftQ.jIn`) over `eqs₁`, at the entries of the right part.
  `seam₁`: under `DatQ.DatOK s.lo s.hi pp` and `Reads`: `inD₁` at (m, w') gives the relation after
    the round at (left m, bk (right m) w').
Limits: no `LateU` is shown to exist here. The joints `eqs₁` and `inD₁` have the condition "True" on
statements: a frame that needs a condition on the statement in front past the lookup lays it beside
them. No link occurs here. Nothing on an honest prover.

-/
import Cb.Pv.Tail.InLink
import Cb.Pv.Tail.SeamD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open Iop Cb.LdLkp CbQ

/-- The letters of a seam whose late part alone is read. -/
structure LateU {K : Type} {s : Size} (Λ : Letters K s) (U W₀ : Type) where
  /-- the names of the numbering's digits of one kind; the entries' names -/
  I : Type
  J : Type
  /-- the further witness in front of the sending, made from the late messages and the one behind -/
  bk : U → W₀ → Λ.W
  /-- the entries of a late tuple of messages -/
  ent : U → J → K
  /-- which of the numbering's digits a digit of the test is -/
  ix : DIx s → I
  /-- the numbering of the lookup's keys, and the places of its digits among the entries -/
  Q : DatQ I J

namespace LateU
variable {K : Type} [Field K] {s : Size} {Λ : Letters K s} {U W₀ : Type} (T : LateU Λ U W₀)

/-- The record of Cb/Pv/Tail/SeamD.lean. -/
def late : Late Λ where
  U := U
  W₀ := W₀
  I := T.I
  J := T.J
  bk := fun m w => T.bk m.2 w
  ent := fun m => T.ent m.2
  ix := T.ix
  Q := T.Q

/-- The digits, read off the late messages at their places. -/
def digs (u : U) : Dig K s :=
  ⟨fun μ c i => T.ent u (T.Q.lo (T.ix ⟨μ, c, i⟩)), fun μ c i => T.ent u (T.Q.hi (T.ix ⟨μ, c, i⟩))⟩

/-- The law of `bk`. -/
def Reads : Prop := ∀ u w, Λ.dig (T.bk u w) = T.digs u

variable {MM Kc : Type} (left : MM → Λ.M) (right : MM → U) (k : MM × W₀ → Kc)

/-- What rides along through the lookup, at one tuple of messages. -/
def eqs₁ : IOR.Rels Kc (Λ.X × Dr s) Λ.E (MM × W₀) where
  rel x y v := T.late.eqs.rel x y ((left v.1, right v.1), v.2)
  relR b v := T.late.eqs.relR b ((left v.1, right v.1), v.2)
  on _ := True
  core := k

/-- The lookup's joint at its start, at one tuple of messages: the shift's own joint over `eqs₁`. -/
def inD₁ : IOR.Rels Kc (Λ.X × Dr s) Λ.E (MM × W₀) :=
  ((T.Q.sh (E := K) (Λ.X × Dr s)).on fun m => T.ent (right m)).jIn (T.eqs₁ left right k)

end LateU

section
variable {K : Type} [Field K] {s : Size} {Λ : Letters K s} {U W₀ : Type} (T : LateU Λ U W₀)
  {MM Kc : Type} (left : MM → Λ.M) (right : MM → U) (k : MM × W₀ → Kc)

/-- The seam, at one tuple of messages. -/
theorem seam₁ {pp : ℕ} (h : T.Q.DatOK s.lo s.hi pp) (hr : T.Reads) :
    ∀ b m w', (T.inD₁ left right k).relR b (m, w') →
      (B Λ).relR b (left m, T.bk (right m) w') :=
  fun b m w' hw => seam T.late h (fun m w => hr m.2 w) b (left m) (right m) w' hw

end

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.seam₁
