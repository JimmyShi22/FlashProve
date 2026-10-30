-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RidesFree.lean: AN ATTENTION SEGMENT's OWN ROUNDS (kind K5): A
RIDER THAT IS A LIST OF CLAUSES GOES ON ALONG THE KIND's CLAUSE, PAST THE KIND's MEMBER: at a list
of four shapes, and at the written list of the first chain's riders (csHead,
Honest/Thread/CsHead.lean). No filling, no prover, no thread. Two statements with
their proofs: calls alone.

  k5_rides_on         CONDITIONAL: **ridersOf hd (borderOf g) v s → K5KeepsM y s s' → ridersOf hd
                      (borderOf g + 1) v s'**, at whatever numbers y of a plan
  k5_rides_on_csHead   the same at hd := csHead ν st R, at g below 12 and at every ν, st, R, y: no
                      other premise

The premises. hg: g is below 12 · hsp: every clause c of the list hd has one of four shapes: it
begins behind border 327 · it speaks at one border alone, a number 14 l + 9 · it speaks from a
number 28 k + 5 to 28 k + 10 · it is riderAtt (14 l + 4) (14 l + 9) fun a => R a.g: a sentence on
one field of the open attention segment's part of the verifier's state. It speaks of numbers and of
the clauses' form; of no input and of no state.

THE CALLS: riders_next (Honest/Thread/Riders.lean): one border on,
each clause that spoke in front stays and each that begins here is laid · k5_hcs_laid_M and
k5_hcl_spans (Honest/Thread/K5RiderSpans.lean): no clause of the four shapes begins right behind the
kind's member, and the one shape that reaches across it stays along K5KeepsM: there by
k5KeepsM_here (Johnson/Desc/K5/Honest/Law/KeepsM.lean) · k5_hsp_csHead
(Honest/Thread/K5SpansCs.lean): every clause of the written list has one of the four shapes, at
every ν, st, R.

Limits. In the first statement THE LIST hd IS A LETTER: that a list of clauses has the four shapes
is proved here at csHead alone. The three arguments of csHead are letters: what its clauses say is
not looked at: their first and last borders, and in one shape their form. A rider that is a
conjunction of such a list with a further sentence is not spoken of. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.K5SpansCs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5

section
open OnBytes OnBytes.Model OnBytes.Maker
open H2K5.Honest (K5KeepsM)
open ProofFile.Honest.FirstThread (k5_hcs_laid_M k5_hcl_spans)
open VerifiableInference.Desc.First (S)

/-- **THE RIDER OF A LIST OF CLAUSES GOES ON ALONG THE KIND's CLAUSE, PAST THE KIND's MEMBER.**
CONDITIONAL: hsp: the clauses' four shapes; g is below 12. -/
theorem k5_rides_on {W : Type} {hd : List (RiderCl W S)}
    (hsp : ∀ c ∈ hd, 327 < c.lo ∨ (c.hi = c.lo ∧ c.lo % 14 = 9) ∨
      (c.lo % 28 = 5 ∧ c.hi = c.lo + 5) ∨
      ∃ (l : Nat) (R : Option OnBytes.Model.Forest.Heard → Prop),
        c = riderAtt (14 * l + 4) (14 * l + 9) fun a => R a.g) {g : Nat} (hg : g < 12) :
    ∀ y v s s', ridersOf hd (borderOf g) v s → K5KeepsM y s s' →
      ridersOf hd (borderOf g + 1) v s' := fun y v s s' h0 hK =>
  riders_next h0
    (fun c hc hl hh hp => (k5_hcs_laid_M (k5_hcl_spans hsp) g hg y c hc).2 hl hh v s s' hK hp)
    (fun c hc e => absurd e (k5_hcs_laid_M (k5_hcl_spans hsp) g hg y c hc).1)

end

section
open OnBytes OnBytes.Model OnBytes.Maker
open H2K5.Honest (K5KeepsM)
open ProofFile.Honest.FirstThread (k5_hsp_csHead)
open VerifiableInference.Desc.First (S)

/-- **THE RIDER OF THE WRITTEN LIST GOES ON ALONG THE KIND's CLAUSE, PAST THE KIND's MEMBER.** g is
below 12; no other premise. -/
theorem k5_rides_on_csHead {W : Type} (ν : Nat) (st : Nat → S → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) {g : Nat} (hg : g < 12) :
    ∀ y (v : W) s s', ridersOf (csHead ν st R) (borderOf g) v s → K5KeepsM y s s' →
      ridersOf (csHead ν st R) (borderOf g + 1) v s' :=
  k5_rides_on (k5_hsp_csHead ν st R) hg

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_rides_on
#print axioms ProofFile.Honest.K5.k5_rides_on_csHead
