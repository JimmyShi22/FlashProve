-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawBack.lean: THE SMALLNESS TEST: FROM "EVERY SINGLE EQUATION HOLDS" BACK TO
WHAT STANDS BEHIND THE DRAW.

The test's equations (a tie for each matrix, packed row and combination; a read for each table's
segment and combination) are batched under powers of one challenge. Behind that challenge stands:
each single equation holds. The library leads from there to the proved block's second joint
(`relOut_of_rows`, OnBytes/Tie/Pv/Tail/EndsAt.lean), at letters that are read off the arrays'
entries and the verifier's record (`AtA`). Here that theorem is laid against what stands behind the
kind's block (`Reads.relB`, Johnson/Desc/First/K8/LawPiece.lean), at the library's caller at a
record's sizes (`tailCallerOf`, Johnson/Top/H/TailRngOf.lean). Nothing is counted or computed anew.
  `Reads.relB_of_relOut`: what stands behind the kind's block, from its three parts at one typed
    matrix: at any caller.
  `callerAtRecord`: the library's caller at the sizes of a record of the smallness test and ANY
    letters Θ over these sizes, with a condition. The letters stay a parameter.
  `relB_of_rows`: if the record holds the list of the typed matrix β; the witness's messages are
    those that the statement decodes to; what rides holds; the letters are read off entries A
    (`AtA`); the digits are in their tables; AND EVERY ROW OF THE LIST OF SINGLE EQUATIONS
    (`rowsTail`) IS 0 AT A: then what stands behind the kind's block holds.
Statements and proofs.
Limits. EVERY PREMISE NAMED IS A PREMISE: none is paid here. Above all: `AtA` (that the typed
letters' weights, symbols, reads and digits ARE the entries A of the committed arrays) · the digits
in their tables (the lookup on the digits) · that each single equation holds (the batching). THE
LIBRARY'S THEOREM ASKS THAT EVERY TABLE OF THE CLOSED LIST LIES ON THE THIRD VECTOR OF READS
(Fn.tree = 2): a list with a table on the first vector (Fn.tree = 0) is not covered by it. One way
alone.

-/
import Johnson.Desc.First.K8.LawOne
import Johnson.Top.H.TailRngOf
import OnBytes.Tie.Pv.Tail.EndsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

open Iop Cb Cb.Pv.Tail OnBytes OnBytes.Model OnBytes.Road.Rows OnBytes.Tie.Pv.Tail
  OnBytes.Tie.Pv.Tail.Port KObj VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound

/-- What stands behind the kind's block, from its three parts at one typed matrix: at any caller. -/
theorem Reads.relB_of_relOut {S Cl W : Type} {F : Frame} {seat : Seat S} {p : Par} {base e : ℕ}
    {d : TailCallerOn} (Q : Reads Cl W F seat p base e d) (a : S × F.E.Str) (w : W) (β : Dr d.c.s)
    (hβ : Q.cf a.1 = listOf β)
    (hdec : ∀ i, d.c.Sg.decs (Q.rd a).1.2 (Q.rd a).2.2 i = some ((Q.wit w).1 i).1)
    (hride : d.c.ride ((Q.rd a).1.1, (Q.rd a).2.1) (d.c.Sg.msgs (Q.wit w).1) (Q.wit w).2)
    (hout : relOut d.c.letters (Q.rd a).1.1 β (d.c.Sg.msgs (Q.wit w).1) (d.c.dig (Q.wit w).2)) :
    Q.relB a w :=
  Q.relB_of_one a w β hβ ⟨hdec, hride, hout⟩

section
variable (ρ : OnBytes.Model.Reading Cb.Gl.E) (tl : HTailF2)
  (Θ : TLetters Cb.Gl.E (OnBytes.Tie.Pv.Tail.sizeOf tl)) (Sg : Sig Cb.Gl.E) (rdm : Sg.Msg → Θ.M)
  (on : Θ.X × Θ.E.Str → Prop)

/-- The library's caller at the sizes of a record of the smallness test and letters over them, with
a condition on its statements. -/
@[reducible] def callerAtRecord : TailCallerOn :=
  ⟨tailCallerOf (OnBytes.Tie.Pv.Tail.sizeOf tl) Θ Sg rdm, on⟩

variable {S Cl W : Type} {F : Frame} {seat : Seat S} {p : Par} {base e : ℕ}

/-- **From the single equations back to what stands behind the kind's block.** -/
theorem relB_of_rows (Q : Reads Cl W F seat p base e (callerAtRecord tl Θ Sg rdm on))
    (a : S × F.E.Str) (w : W) (β : Dr (OnBytes.Tie.Pv.Tail.sizeOf tl).size)
    (hβ : Q.cf a.1 = listOf β)
    (hdec : ∀ i, Sg.decs (Q.rd a).1.2 (Q.rd a).2.2 i = some ((Q.wit w).1 i).1)
    (hride : Θ.ride ((Q.rd a).1.1, (Q.rd a).2.1) (rdm (Sg.msgs (Q.wit w).1)) (Q.wit w).2)
    (A : Nat → Nat → Nat → Cb.Gl.E) (pc : Nat)
    (at' : AtA ρ tl Θ (Q.rd a).1.1 (rdm (Sg.msgs (Q.wit w).1)) (Θ.dig (Q.wit w).2) β A)
    (hfit : OnBytes.Tie.Pv.Tail.Port.Fits tl) (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2)
    (hdig : ∀ μ u i,
      Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl).size.lo ((Θ.dig (Q.wit w).2).zl μ u i) ∧
      Cb.Rng.InTab (OnBytes.Tie.Pv.Tail.sizeOf tl).size.hi ((Θ.dig (Q.wit w).2).zh μ u i))
    (hrows : ∀ r ∈ rowsTail ρ tl tl.funs pc, r.2 A = 0) : Q.relB a w :=
  Q.relB_of_relOut a w β hβ hdec hride (relOut_of_rows pc at' hfit htree hdig hrows)

end

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.Reads.relB_of_relOut
#print axioms VerifiableInference.Desc.First.K8.relB_of_rows
