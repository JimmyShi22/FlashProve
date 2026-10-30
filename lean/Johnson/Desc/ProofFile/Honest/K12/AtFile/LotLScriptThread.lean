-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLScriptThread.lean

It states no goal. No property of the protocol is claimed.

THE TIE OF THE WORDS AT A STAND IN FRONT
OF THE CLOSING PROXIMITY TEST, AT THE FIRST THREAD AS A VALUE (`firstThread`,
Honest/Thread/TheFirstThread.lean) LAID WITH THE FIRST CHAIN's SCRIPT AS A VALUE
(`firstScriptAt`, AtFullSide/K1/FirstScript.lean), AT Said := `SaidOk` AND THE SIZE
Sz.ref. The last corollary of the tie: calls, and the thread's own equation by unfolding.

  `firstThreadAtTheFirstScript`   the thread, by name: an abbreviation
  `wordsTied_at_first_thread`   the premise hw of acceptedS_stands_L (not beneath this file) at that
      thread

Paid here beyond LotLScriptStandFew.lean: hstart: the thread's valid inputs are `ReadyInput`'s, whose
first clause is okStart · hReach: `thrS_reach_below` (Honest/Thread/ReachAtHead.lean),
at SaidOk; 354 is at most the flat list's 358 (`flat_length_head`,
Honest/Thread/JoinAtHead.lean).

Hypotheses left. hh: the head at a return of the maker. hA: that return is the base prover's filling's
at Sz.ref. hf: pl is the finish (there is one: `finish_at_base`). hc: the statement of closing_at_head
(K2/Law/ClosingAtHead.lean; not imported). hbook: the public test `wordsBookB`
(ClosingWordsBook.lean) says yes at the maker's book, at the finish's part and the
test's second part.

Limits. Those of LotLScriptStand.lean. That a stand exists is not said. At Sz.ref alone; the full size
and the format's second hash function alone. Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `wordsTied_at_first_thread` bears this label; the rule is at its
home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- hh and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- hf, hc and hbook speak of the finish, of the closing's public test and of the book's entries: they
  name no coin.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- numbers (the stated numbers of the falls) is a letter under no premise.
- A run's coins k are bound inside the end. Beside k it binds the letters st, m and E (the
  verifier's state, the state of the prover's side, the available tables) under `ThrS … 354 k st m
  E`: a premise of the first kind: it names k; by its text, at fixed st, m and E it can hold at some
  values of the coins and fail at others.
- The end binds besides c under `lendRow … (k.look …) … = .ok c` and Rr under `carryRows …
  (restCoins J' c.2.1).mem = .ok Rr`: of the first kind. J' under its equation, the record R under
  `enterFinish st = .ok R` and G under `R.st.groups[R.g]? = some G` name no coin.
- One clause of the invariant is of the second kind: the thread's `valid` says that the input of m
  is w and meets `ReadyInput` (Honest/Thread/ReadyInput.lean): the instance passes the description's
  test, the index is in range, the trace is the prover's own: it reads the hidden input and no coin.
- What lifts the bar. For c and Rr the made terms are what `lendRow` and `carryRows` return:
  `carryRows_returns_at_input` (LReturnsClosing.lean) shows, from the head, the ground and the
  finish, at the rows of `Sz.ref` and at every input whose instance passes the description's test,
  that the second returns whatever is lent. For st, m and E the made terms would be those of the
  honest run at the border, as terms of w, k and the challenges, and the lemma would show the
  premises at them at every value of the coins. None is known to this file: so the bar is flat.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLScriptStandFew
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (wordsFirst)
open OnBytes.Means (layoutOf)
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers firstThread firstFalls firstClauses
  fallsAfterBatching nextSlotBehindTheHead digitsStand heardByAttention thrS_reach_below
  flat_length_head)
open ProofFile.Honest.K1 (LocB firstScriptAt readersB)
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K2.Law (SwitchCoins)
open ProofFile.Honest.K12.Light (WordsTied)
open ProofFile.Honest.K12.AtProof (plainL finishAt jobL doorAtL heardL ClosingAtEveryPlace)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **The first thread, laid with the first chain's Script at Sz.ref.** -/
abbrev firstThreadAtTheFirstScript (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (numbers : FallNumbers) (w : LocB W₀) :=
  firstThread hh ⟨firstScriptAt I Sz.ref Op A hh.firstChain, numbers⟩ w

/-- hc AND hbook ARE PREMISES. **THE TIE OF THE WORDS AT A STAND OF THE FIRST THREAD IN FRONT OF THE
CLOSING PROXIMITY TEST.** -/
theorem wordsTied_at_first_thread (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) {pl : SwitchPlace} (hf : finishAt A.Z A.G = some pl)
    (hc : ClosingAtEveryPlace files A.Z hh.places hh.firstChain)
    (hbook : AtProof.wordsBookB A.B ⟨pl.place, 0⟩ ⟨(H2U.p12OfMade A.Z.made).place, 1⟩
      pl.front.length = true) :
    ∀ k st m E R (J' : TestJob (LocB W₀) Unit),
      J' = atStand (jobL (H2U.p12OfMade A.Z.made) (doorAtL A.Z) (widerRows Sz.ref A.Z A.G)
        (readersB I A.Z) (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl) m.st.input
        (frontOf m) R →
      ∀ c : RowCoins [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'],
      ThrS (firstThreadAtTheFirstScript hh I Op numbers w) SaidOk 354 k st m E →
      enterFinish st = .ok R →
      lendRow A.B (A.B.rowsOf (firstThreadAtTheFirstScript hh I Op numbers w).chain)
        (k.look (firstThreadAtTheFirstScript hh I Op numbers w).chain) J'.p.place
        [(firstPart J' : Part (LocB W₀) (LocB W₀) Unit), restPart J'] 0 = .ok c →
      ∀ Rr : Johnson.Prover.Send.Rows,
      AtProof.carryRows (widerRows Sz.ref A.Z A.G) (readersB I A.Z)
        (K2.lotClosingAt A.G.first.layout (K2.segmentsOf A.Z A.G)) pl m.st.input
        (heardL (frontOf m)) (restCoins J' c.2.1).mem = .ok Rr →
      ∀ G, R.st.groups[R.g]? = some G →
      WordsTied R.st R.g G
        (wordsFirst (P5J.At.arr A.Z) st.st st.book
          ((firstThreadAtTheFirstScript hh I Op numbers w).wit k m.st.input (m.st.heard ++ [])))
        (layoutOf R.st G) (plainL Rr (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))) :=
  wordsTied_at_closing_stand_few hh.head hA
    (fallsAfterBatching (firstFalls A numbers) hh.firstChain) (carryExact A.Z (P5J.At.arr A.Z)) 0
    hh.description.t₁ hh.description.t₂ 339 (ReadyInput hh.description A.H)
    (ridersOf (csHead nextSlotBehindTheHead (digitsStand A.Z) (heardByAttention A.Z)))
    (kpBy (firstClauses hh)) w SaidOk hf hc (fun _ hv => hv.1)
    (fun _ _ _ _ hT => thrS_reach_below hh.head A.H _ _ _ _ _ _ _ _ _ _ w
      (by rw [flat_length_head hh.head]; decide) hT)
    hbook

end ProofFile.Honest.K12.LotL

end

#print axioms ProofFile.Honest.K12.LotL.wordsTied_at_first_thread
