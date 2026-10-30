-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/KeyFitsAtStart.lean: AT THE SHARED CHAIN's FIRST STATE THE INSTANCE's KEY HAS
THE PLANNED SIZES, for every instance that is written of a typed OOD sample of the full size
(RecFull; our files call the OOD sample "the record"). Theorems.

WHY. The laws on the shared chain ask "the key fits the stored table's shape" (shape1,
Johnson/Desc/K14/Law/PointCounts.lean) in the promise from border 0 on. The running text tests it
at sub-protocol 3 only ("(rec_gamma)"). So whoever makes the promise at the chain's start owes it.
Here it is had BY THE SAMPLE's TYPE: LPFD.Full.instOf_key_fits
(Johnson/Desc/Laid/ProofInstFits.lean): the key of instanceAsPlainRecord z fits every shape with the full size's
three numbers; and the seat's own shape has them wherever the planner's sizes are the full size's
(three_at_seat, Johnson/HB/LLHARD/IndexOfAtFull.lean).
  shape1_at_start   at parameters whose table has the three numbers.
  shape1_at_seat    at the seat's own parameters p14Of c bp, under AtFull c.made.
  promise_at_start  so the filled book-keeping at border 0 (pmZ, shape 0: the key fits, and no
                    message is noted) holds of the chain's first state there.
What is not claimed. AtFull c.made at the seated value: other files' (in scope, by the planner's
sizes). Nothing of an instance that is not instanceAsPlainRecord of a typed sample: there sub-protocol 3's test
alone stands. The full size alone. Nothing on soundness.

-/
import Johnson.Desc.Laid.ProofInstFits
import Johnson.Desc.K14.Law.LedgerLetters
import Johnson.HB.LLHARD.IndexOfAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice OnBytes.Maker
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc.Shared (PromMeaning)
open H2K.Sizes (AtFull)

/-- **shape1 at the chain's first state.** -/
theorem shape1_at_start (z : LPFD.Full.XF × RecFull) (p : Par) (codes : Codes)
    (hv : p.S.fold.index.v = frS.P.v) (ha : p.S.fold.index.answers = 1)
    (hc : p.S.fold.index.cubeBits = 29) :
    shape1 p (first codes (LPFD.Full.instanceAsPlainRecord z).pub.key) = true :=
  LPFD.Full.instOf_key_fits z p.S.fold.index hv ha hc

/-- **At the seat's own parameters**, where the planner's sizes are the full size's. -/
theorem shape1_at_seat (z : LPFD.Full.XF × RecFull) {c : Model.Verify.Chains}
    (h : AtFull c.made) (bp : List (Nat × Nat)) :
    shape1 (p14Of c bp).par (first (p14Of c bp).codes (LPFD.Full.instanceAsPlainRecord z).pub.key) = true := by
  obtain ⟨e1, e2, e3⟩ := three_at_seat h bp
  exact shape1_at_start z _ _ e1 e2 e3

/-- The filled book-keeping at border 0, from its two halves. -/
theorem pmZ_zero_of (p : Par) (P : PromMeaning St) (s : St) (h1 : shape1 p s = true)
    (h2 : notedU s = false) : (pmZ p P).shape 0 s = true := by
  show (shape1 p s && !notedU s) = true
  rw [h1, h2]
  rfl

/-- The first state notes no message. -/
theorem first_not_noted (codes : Codes) (key : TableKey) : notedU (first codes key) = false := rfl

/-- **The filled book-keeping at border 0 holds of the chain's first state.** -/
theorem promise_at_start (z : LPFD.Full.XF × RecFull) {c : Model.Verify.Chains}
    (h : AtFull c.made) (bp : List (Nat × Nat)) (P : PromMeaning St) :
    (pmZ (p14Of c bp).par P).shape 0
      (first (p14Of c bp).codes (LPFD.Full.instanceAsPlainRecord z).pub.key) = true :=
  pmZ_zero_of _ P _ (shape1_at_seat z h bp) (first_not_noted _ _)

end Desc.K14.Law

#print axioms Desc.K14.Law.shape1_at_start
#print axioms Desc.K14.Law.shape1_at_seat
#print axioms Desc.K14.Law.pmZ_zero_of
#print axioms Desc.K14.Law.first_not_noted
#print axioms Desc.K14.Law.promise_at_start
