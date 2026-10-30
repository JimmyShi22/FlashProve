-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
MOVED, TO THE LETTER, INTO Law/K6Claims.lean (which imports nothing of the batching kind's law):
K6HeardAt, ledger_front, k6HeardAt_front, KeepsK6, k6HeardAt_keeps, k6Ready_at, k6_border. What this
head says of them holds there.
Johnson/Desc/Kinds/Law/K6PromiseBorder.lean: THE OUTPUT HEAD's HALF OF THE PROMISE THAT ITS THREE
RUNS OF CLAIMS ASK IN FRONT OF THE BATCHING's DRAW (Law/RunsStill.lean: K6Ready;
Law/RunsStillAtS.lean: K6Promise): PAID AT THE HEAD's OWN BORDER, CARRIED ALONG WHATEVER KEEPS SEVEN
FIELDS AND A LATER LEDGER, AND TURNED INTO K6Ready AT ANY RECORD ON THE WAY. Definitions, statements
and proofs.

  K6HeardAt s      at the record s: the head's letters in front are read (given returns); what the
                   seat reads back as heard is what the head's own hearing returned from some well
                   laid ledger; the record's ledger is later than the one which that hearing left.
  k6_border        BEHIND EVERY YES OF THE HEAD's BLOCK's STEP, from a record with K6On, on
                   canonical rounds: K6HeardAt at the record behind. Whatever is drawn.
  ledger_front, k6HeardAt_front   it is carried along Law/RunsFixedFront.lean's AlikeFront.
  KeepsK6 b        WHAT A BLOCK BETWEEN MUST KEEP, as one sentence on its step: in the head's link a
                   yes leads to a record that is AlikeFront: THE LIST, one line a field:
                     the record still stands in the head's link
                     x           what the head's own rounds heard        the same
                     squaresP    the squares' level's state              the same
                     opened      the link's ledger is laid               the same
                     lookHeard   what the lookup on the calls heard      the same
                     out.reply   the heard reply                         the same
                     req         the request's words                     the same
                     F           the ledger                              LATER (what lies under a
                                 filled slot stays)
                   Nothing is asked of st, book, roots, rowsOwed, failed, check, of the link's fr,
                   kept, ids, L, t, tl, claim, wo, Fm, slot.
  k6HeardAt_keeps  a block that keeps these carries K6HeardAt over its step.
  k6Ready_at       K6HeardAt at a record is K6Ready at what the record shows and its own ledger: at
                   the head's own border too: nothing is asked of the reads.
  k6Ready_fixed    so at the fixed part of such a record (fixed9): the clause that K6Promise asks of
                   Ok.

WHAT IT IS NOT. (1) That the blocks between the head's own rounds and the draw keep these fields
(KeepsK6) is shown of NONE: each kind's files' to show. (2) Canonical rs is a premise of k6_border,
as of the head's law. (3) K6Promise speaks of EVERY q of which Ok holds: it is paid by whoever
closes Ok with this clause inside it; k6Ready_fixed is what they then owe at "ready". (4) The block
is blockOf's, not the lot's guarded block. Nothing on soundness.
LETTERS. K6HeardAt: under "there are": g: given ... s = .ok g; H: heard s = some H; F0, rs, G: tied
to H by the hearing's equation and to the record by "later". In k6_border they are the record in
front's own ledger, the step's own rounds without their digests, and the ledger behind.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RunsStillAtS
import Johnson.Desc.Kinds.Law.K6Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L

section Fixed

variable {α : Type} (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- **AT THE FIXED PART OF SUCH A RECORD: THE CLAUSE THAT K6Promise ASKS OF Ok.** -/
theorem k6Ready_fixed (φ : S → α) (kap : α → Option Seen) (hkap : ∀ e, kap (φ e) = seenOf e)
    (s : S) (k : K6HeardAt h iU3 p s) :
    ∀ z u, kap (fixed9 φ s).1 = some z → (fixed9 φ s).2 = some u → K6Ready h iU3 p z u.F := by
  intro z u hz hu
  have hz' : seenOf s = some z := by rw [← hkap]; exact hz
  have hu' : (atS.get? s).map pubOf = some u := hu
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hu'
  exact k6Ready_at h iU3 p k hz' (K9.get_fork s b hb)

end Fixed

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Ready_fixed
