-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadLedgerMade.lean.
WHAT IT DOES NOT SHOW. No soundness. It speaks of the step that opens the head's link and of "the
code switching's sub-protocol, then that step" as terms; that the IOP as written in Lean holds such
a one at the head's second place is not shown here. Nothing on what the ledger holds later.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. "The ledger": the
open link's Fork, as S.fork? reads it. "Well laid": its three lists have one entry for each of its
numbers (OnBytes/Tie/Pv/Psc/PscFork.lean: Sized; Desc/Kinds/HeadLaw.lean: WellLaid: the same three
equations in another order). "Free above": no number from its next free one on is filled
(PscRoom.lean: FreeAbove).
LETTERS. "There is" in the conclusions: F: the ledger behind: named in the proof: emptySlots
(weightsAtZero …) P.hp.ns.
OBJECT. Top/H0/Tw/K2C/Head.lean: headOpenQ, headOpened; the place's form as
Top/H0/Tw/K2C/HeadLedger.lean has it.
USER. The fact along the chain's fold "in the open output head's link the ledger is well laid",
which the law on the output head's twelve reads asks in front of the output head's own sub-protocol.
WHAT IT IS. WHERE THE HEAD's LINK IS OPENED, A LEDGER IS THERE, WELL LAID AND FREE ABOVE: THE CODE
SWITCHING's FILES' OWN LAW (Top/H0/Tw/K2C/HeadLedger.lean: headOpenQ_fork, placeH2_fork: WHICH
ledger is laid; its headOpenQ_laid has the sizes, spelt out) IN THE LIBRARY's WORDS Sized AND
FreeAbove, which the lookup's files' law at the next place takes.
  wellLaid_of_sized the two words for "well laid" are one.
  emptySlots_free   empty slots are well laid, and no number of theirs is filled.
  headOpenQ_free    at the opening step.
  placeH2_free      at the code switching's sub-protocol with that step joined behind.


NEAREST RELATIVE: Top/H0/Walk/FrameSized.lean: startFork_sized, ledger_sized_at_lay: the like where
an attention's link, a layers' link and link 0 are opened.

-/
import Johnson.Top.H0.Tw.K2C.HeadLedger
import Johnson.Desc.Kinds.HeadLaw
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized FreeAbove Filled)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2
open Johnson.Desc.First.Walk (weightsAtZero emptySlots)

/-- The two words for "well laid" are one. -/
theorem wellLaid_of_sized {F : Fork} (h : Sized F) : WellLaid F := ⟨h.2.2, h.1, h.2.1⟩

/-- Empty slots are well laid, and free from every number on. -/
theorem emptySlots_free (F : Fork) (n : Nat) :
    Sized (emptySlots F n) ∧ ∀ j, ¬ Filled (emptySlots F n) j := by
  refine ⟨⟨by simp [emptySlots], by simp [emptySlots], by simp [emptySlots]⟩, fun j hf => ?_⟩
  unfold Filled at hf
  simp only [emptySlots, Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hf
  split at hf <;> simp at hf

/-- **Behind the step that opens the head's link.** -/
theorem headOpenQ_free {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    ∃ F, s'.fork? = some F ∧ Sized F ∧ FreeAbove F ∧ F.ns = P.hp.ns :=
  ⟨_, headOpenQ_fork h, (emptySlots_free _ _).1, fun j _ => (emptySlots_free _ _).2 j, rfl⟩

/-- **Behind the head's second place**: the code switching's sub-protocol, then the opening step. -/
theorem placeH2_free {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s') :
    ∃ F, s'.fork? = some F ∧ Sized F ∧ FreeAbove F ∧ F.ns = P.hp.ns :=
  ⟨_, placeH2_fork h, (emptySlots_free _ _).1, fun j _ => (emptySlots_free _ _).2 j, rfl⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.headOpenQ_free
#print axioms VerifiableInference.Desc.Kinds.Head.Law.placeH2_free
