-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLScriptPaidBoth.lean

It states no goal. No property of the protocol is claimed.

THE TIE OF THE WORDS AT A STAND OF THE
FIRST THREAD IN FRONT OF THE CLOSING PROXIMITY TEST, WITH NO PREMISE LEFT BUT THE HEAD AT A RETURN OF
THE MAKER AND THAT THE RETURN IS THE BASE PROVER's FILLING's AT Sz.ref. One statement with its proof:
three calls.

  `wordsTied_at_first_thread_paid`   there is a finish pl of the code switch, and at it the premise hw
      of acceptedS_stands_L (not beneath this file) holds in its own form, at the
      thread `firstThreadAtTheFirstScript hh I Op numbers w` and Said := SaidOk

By: `wordsTied_at_first_thread_closing_paid` (LotLScriptPaid.lean) · `finish_at_base`
(AtFullSide/K1/FirstScript.lean) · `wordsBookB_at_base` (LotLBookLineAtBase.lean).

Hypotheses left. hh: the head at a return of the maker. hA: that return is the base prover's filling's
at Sz.ref.

Limits. IT SPEAKS AT STANDS: that a stand of the thread in front of member 354 exists, at which the
test enters and the frame lends the row its coins, is not said: at no stand it says nothing. That hh
and hA can be met together is not said here. It is one premise of acceptedS_stands_L, not its end.
At Sz.ref and SaidOk alone; the full size and the format's second hash function alone.
K2/Law/ClosingAtHead.lean and the files beneath it lie beneath this file.
Nothing on completeness, soundness or hiding.

NOT IN FRONT OF A LAW OVER COINS: `wordsTied_at_first_thread_paid` bears this label; the rule is at
its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean.
This file's own ground, in the rule's terms.
- hh and hA speak of the public files, of the letters I and Op (how an index, an instance and the
  challenges are read, and one named member of the index's type) and of what the maker returns at
  the filling made of them. By their text they name no coin, no run's input (its index, its trace)
  and no Script: of neither kind.
- w, the run's input, is a letter under no premise in front. It holds the committer's coins (its
  field rc) and the hidden input (its fields w₀ and trace).
- numbers (the stated numbers of the falls) is a letter under no premise.
- A run's coins k are bound inside the end, behind "there is a finish pl". Beside k it binds the
  letters st, m and E (the verifier's state, the state of the prover's side, the available tables)
  under `ThrS … 354 k st m E`: a premise of the first kind: it names k; by its text, at fixed st, m
  and E it can hold at some values of the coins and fail at others.
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
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLScriptPaid
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLineAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K12.LotL
open VerifiableInference.Desc.K12 (T12 enterFinish)
open VerifiableInference.Desc.Sound (wordsFirst)
open OnBytes.Means (layoutOf)
open OnBytes.HonestTrace (Sz)
open ProofFile.Honest.FirstThread (HeadAtReturn FallNumbers)
open ProofFile.Honest.K1 (LocB readersB finish_at_base)
open ProofFile.Honest.K2 (SwitchPlace)
open ProofFile.Honest.K12.Light (WordsTied)
open ProofFile.Honest.K12.AtProof (plainL finishAt jobL doorAtL heardL wordsBookB_at_base)

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **THE TIE OF THE WORDS AT A STAND OF THE FIRST THREAD IN FRONT OF THE CLOSING PROXIMITY TEST**, under
the head at a return of the base prover's filling at Sz.ref. -/
theorem wordsTied_at_first_thread_paid (hh : HeadAtReturn files A) (I : WiderIn W₀) (Op : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (numbers : FallNumbers) (w : LocB W₀) :
    ∃ pl : SwitchPlace, finishAt A.Z A.G = some pl ∧
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
        (layoutOf R.st G) (plainL Rr (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))) := by
  obtain ⟨pl, hf⟩ := finish_at_base hh.head hA
  exact ⟨pl, hf, wordsTied_at_first_thread_closing_paid hh I Op hA numbers w hf
    (wordsBookB_at_base hh.head hA hf)⟩

end ProofFile.Honest.K12.LotL

end

#print axioms ProofFile.Honest.K12.LotL.wordsTied_at_first_thread_paid
