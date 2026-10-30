-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/MakerProofs.lean: THE SIX STATEMENTS OF Johnson/Road/K4/Rec/MakerStatement.lean,
PROVED: "BEHIND A YES OF THE QUIET STEP THAT OPENS A LINK THE TESTS OF THE TWO PUBLIC ITEMS
frame.sentIs AND ledger.treesAre SAY YES" (the tests: Johnson/Desc/First/FillSent.lean).

How. A yes of `openLay`, `openLayZero` or `openAtt` is unfolded by the laws `openLay_ok`,
`openLayZero_ok` and `openAtt_ok` of Johnson/Top/H0/Walk/FrameLaw.lean: the chain's frame stood at
link l; behind the yes `S.link?` reads { check := the chain's own state of the calls in front,
link := l, .. } and `S.fork?` reads `startFork X ns`. No law of these steps is typed here anew.
  `trees_of_fork`: the record's ledger is F, and the plan's looks at m are F's arrays': then
    `treesAreB d m` says yes.
  `sent_of_link`: the record's open link's state of the calls is c; c's frame stands at link l;
    `checkSentB d l c`: then `sentIsB d l` says yes.
  **`openLayTrees`, `openLayZeroTrees`, `openAttTrees`, `openLaySent`, `openLayZeroSent`,
  `openAttSent`**: the six, each at its statement's name.

OBJECT: the three steps' texts (Johnson/Desc/First/Walk/Frame.lean, FrameZero.lean). USER:
Johnson/Road/K4/Rec/MakerJoin.lean; meant: the law of the block at a link's first place. LETTERS:
the steps' own (P, fvs, kCol), d, m: all bound by "for every".

Limits. HALF OF THE MAKER's DEBT: `checkSentB` in front of the step is a premise: it stands between
the two halves of one block; that the first half (the link's first sending, or the switch) leaves
it is not said here. In the three statements on the ledger "the plan's looks at m are those of
`startFork`'s arrays" is a premise on the letter d: shown at no value. THE HEAD's LINK IS OPENED BY
ANOTHER TEXT: not here. That an honest record meets the premises: no theorem here says so. K04_law,
the law of K4's block itself, IS NOT PROVED BY THIS. Nothing on soundness, on an honest prover or
on hiding.
-/
import Johnson.Road.K4.Rec.MakerStatement
import Johnson.Top.H0.Walk.FrameLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model
open Johnson.Desc.First.Walk (LayPar AttPar openLay openLayZero openAtt startFork)
open Johnson.Desc.First.Walk.Law (openLay_ok openLayZero_ok openAtt_ok)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillSent (SentData treeLook sentIsB treesAreB)

/-- The record's ledger has the plan's looks: the test says yes. -/
theorem trees_of_fork {t : S} {F : Fork} {d : SentData} {m : Nat} (hF : t.fork? = some F)
    (hd : d.trees m = F.trees.toList.map treeLook) : treesAreB d m t = true := by
  unfold treesAreB
  rw [hF]
  simp only [Option.any_some, decide_eq_true_eq]
  exact hd.symm

/-- The open link's state of the calls is c, which stands at link l and meets the four clauses: the
test says yes. -/
theorem sent_of_link {t : S} {L : LinkCtx} {c : ChainCheck} {d : SentData} {l : Nat}
    (hL : t.link? = some L) (hc : L.check = c) (hl : c.frame.link = l)
    (h : checkSentB d l c = true) : sentIsB d l t = true := by
  unfold checkSentB at h
  unfold sentIsB
  rw [hL]
  simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  rw [hc]
  exact ⟨⟨⟨⟨h.1.1.1, hl⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩

theorem openLayTrees : OpenLayTrees := by
  intro P s s' d m h hd
  obtain ⟨_, _, _, _, _, _, hF, _⟩ := openLay_ok h
  exact trees_of_fork hF hd

theorem openLayZeroTrees : OpenLayZeroTrees := by
  intro P fvs kCol s s' d m h hd
  obtain ⟨_, _, _, _, _, _, hF, _⟩ := openLayZero_ok h
  exact trees_of_fork hF hd

theorem openAttTrees : OpenAttTrees := by
  intro P s s' d m h hd
  obtain ⟨_, _, _, _, _, hF, _⟩ := openAtt_ok h
  exact trees_of_fork hF hd

theorem openLaySent : OpenLaySent := by
  intro P s s' d h hc
  obtain ⟨_, _, _, hl, _, hL, _⟩ := openLay_ok h
  exact sent_of_link hL rfl hl hc

theorem openLayZeroSent : OpenLayZeroSent := by
  intro P fvs kCol s s' d h hc
  obtain ⟨_, _, hl, _, _, hL, _⟩ := openLayZero_ok h
  exact sent_of_link hL rfl hl hc

theorem openAttSent : OpenAttSent := by
  intro P s s' d h hc
  obtain ⟨_, _, _, hl, hL, _⟩ := openAtt_ok h
  exact sent_of_link hL rfl hl hc

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.openLayTrees
#print axioms OnBytes.Road.K4.Rec.openLayZeroTrees
#print axioms OnBytes.Road.K4.Rec.openAttTrees
#print axioms OnBytes.Road.K4.Rec.openLaySent
#print axioms OnBytes.Road.K4.Rec.openLayZeroSent
#print axioms OnBytes.Road.K4.Rec.openAttSent
