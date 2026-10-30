-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/FivesAtTheLetters.lean: the linear claim (kind K14): WHAT THIS KIND HAS SHOWN OF THE
PROOF FILE's SHARED AND SECOND CHAIN, STATED AT THE ONE VALUE OF EACH LETTER
(AtFullSide/Honest/TheLetters.lean): at thread₂ and thread₃, said₂ and said₃, later and last of that
file. Statements: calls alone. No definition.

  five_shared_at_letters
      FiveAtBorder at the members 1 to 8 of thread₂, at said₂, at every fall. One premise on the
      run: the key of its shared input is the committer's (KeyIsTheCommitters,
      AtFullSide/K14/AtLaidLetters.lean)
  five_last_zero_at_letters
      FiveAtBorder at the member 0 of thread₃, at said₃, at every fall
  five_last_one_at_letters
      FiveAtBorder at the member 1 of thread₃, at said₃, at every fall
  accepted_last_one_at_letters
      its fifth clause under a name of its own
  door_rides_at_letters
      the field rides of the second chain's parts at border 0, at the record that the chain's start
      returns, from stands of thread₁ and thread₂ at their last borders
  common_at_ready, common_at_stand
      the run's shared input is the shared part of its own input: where ready returns; and wherever
      thread₃ stands with said₃
  samples_at_W_at_letters
      in front of the second chain's proximity test the sample rows of all members of the own group
      say of the words of the item "rows", from a stand of thread₃ at border 2 with said₃

WHAT EACH OF THE FIVES TAKES FROM THE INVARIANT IN FRONT OF ITS MEMBER, AND DOES NOT SHOW.
  * At the member 0 of thread₃: the items (Eval) and (Dot), the form at border 0, the eleven tests
  of the
    rider doorRider and the test of the rider tiedAheadRider. Where the form's test at border 0 is
    false, two of the five hold for nothing; this file evaluates that test at no state
    (Johnson/Desc/ProofFile/Honest/K14/FiveAtLastThread.lean, AtFullSide/K14/AtLaterThreads.lean:
    their heads).
  * At the member 1 of thread₃: Tied, the very condition of the member's yes: THE YES IS MOVED, NOT
  PAID
    (AtFullSide/Frames/LastAtValues.lean). At these same letters five_last_zero_at_letters lays Tied
    at border 1, and door_rides_at_letters pays the two riders at border 0 from the two earlier
    threads' ends.
  * At the members 1 to 8 of thread₂: NOT IN FRONT OF A LAW OVER COINS: the premise hw ties the
  input's key to its
    coins. THE BASE MAKER's PROVER IS NOT THE HONEST PROVER OF THE PROTOCOL, and nothing here
    carries the five over (AtFullSide/K14/AtLaidLetters.lean: its head).

How the values fit. later has no rider, its table is tableShared and its counts fixedShared: the
three premises of k14_five_shared_laid hold by unfolding. last's riders are lastRiders at the empty
list and its keeps is lastKeeps at the clause that says nothing: by unfolding. last's field ends is
a function of the input; at a stand the input is the run's own (a clause of the invariant), and
there that field returns what the run's two earlier threads give (endsAt_at_run,
AtFullSide/Honest/TheLettersFit.lean).

Limits. Beside what is named above, every statement has these hypotheses: h : HeadAtReturn; the two
instances [Inhabited P5J.TS] and [Inhabited Desc.K14.St], which thread₃ reads through a default of
its field ends; and the open letters of TheLetters.lean (OpenShared, OpenLast), which are parameters
and hold propositions: where no value of them exists, nothing is said. made (the base maker returns
A) is a hypothesis of the first. NOTHING HERE SHOWS THAT ANY THREAD STANDS AT ANY RUN. This file
proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import AtFullSide.Honest.TheLettersFit
import AtFullSide.K14.AtLaidLetters
import AtFullSide.K14.AtTheThreeThreads
import AtFullSide.Frames.LastAtValues
import AtFullSide.K12.SamplesAtWTied

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K14
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (baseMaker)
open AtFullSide.Honest (lastAtRun)
open AtFullSide.Honest.TheLetters
open OnBytes (TableKey)
open OnBytes.Slice (rdE)
open OnBytes.Means (sampleItem)
open VerifiableInference.Desc.Third (S₃)
open Desc.K14 (St)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtW)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {O : OpenShared A} (P : OpenLast h O) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)

/-- **The five at the members 1 to 8 of the shared chain's thread.** -/
theorem five_shared_at_letters (made : baseMaker Z = .ok A) (hw : KeyIsTheCommitters A R.common)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    FiveAtBorder (thread₂ h R (O := O)) (said₂ h R (O := O)) fall b :=
  k14_five_shared_laid made h (later (h := h) O) rfl rfl
    (fun _ hc => absurd hc List.not_mem_nil) R.common hw _ fall b hb1 hb8

/-- **The five at the member 0 of the second chain's thread.** -/
theorem five_last_zero_at_letters (fall : Nat → S₃ → List Fmt.Drawn → Option String) :
    FiveAtBorder (thread₃ h P R) (said₃ h P R) fall 0 :=
  five_at_lastRiders h (first h) (last h P) (reads h) R.own _ fall
    (later := []) rfl (fun _ hc => absurd hc List.not_mem_nil)

/-- **The five at the member 1 of the second chain's thread.** -/
theorem five_last_one_at_letters (fall : Nat → S₃ → List Fmt.Drawn → Option String) :
    FiveAtBorder (thread₃ h P R) (said₃ h P R) fall 1 :=
  AtFullSide.Frames.five_at_last_one_late h (first h) (last h P) (reads h) R.own _ fall
    (later := []) rfl (fun _ hc => absurd hc List.not_mem_nil) (own := fun _ _ _ => True) rfl
    (fun _ _ _ _ _ => trivial)

/-- The fifth clause of five_last_one_at_letters: wherever the invariant holds in front of the
member 1, which brings Tied, the member's step says yes. -/
theorem accepted_last_one_at_letters (fall : Nat → S₃ → List Fmt.Drawn → Option String) :
    AcceptedS (thread₃ h P R) (said₃ h P R) fall 1 :=
  AtFullSide.Frames.acceptedS_one_last h (first h) (last h P) (reads h) R.own _ fall
    (later := []) rfl

/-- **The riders at the second chain's first border, where the chain is entered at a run.** -/
theorem door_rides_at_letters (x : ProofFile.Inst) (k : Coins A.B) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃,
      ThrS (thread₁ h R) (said₁ h R) h.description.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS (thread₂ h R (O := O)) (said₂ h R (O := O)) h.description.shared.blocksInOrder.length k e₂ m₂
        E₂ →
      h.description.start₃ x.pub e₁ e₂ = .ok s₃ →
      (lastParts h (first h) (last h P)).rides 0 R.own s₃ :=
  door_rides_at_run h (first h) (reads h) (shared h O) R (last h P) (later := []) rfl
    (fun _ hc => absurd hc List.not_mem_nil) x k

/-- Where ready returns, the run's shared input is the shared part of its own input. -/
theorem common_at_ready {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R) : R.common = toCommon (A := A) R.own := by
  obtain ⟨-, tr, -, e1, e2, -⟩ := ready_ok hR
  rw [e1, e2]

/-- Wherever thread₃ stands with said₃, the run's shared input is the shared part of its own input:
the tie holds a stand of thread₂ at that shared part, and a stand's input is its thread's. -/
theorem common_at_stand {b : Nat} {k : Coins A.B} {st : S₃}
    {m : Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit} {E : Env}
    (u : ThrS (thread₃ h P R) (said₃ h P R) b k st m E) : R.common = toCommon (A := A) R.own := by
  have hi : m.st.input = R.own := u.1.2.2.2.2.2.2.1
  obtain ⟨_, _, m₂, _, -, u₂, -, -, hin, -, -⟩ :=
    ProofFile.Honest.K14.ties_at_endsBy h (first h) (reads h) (shared h O)
      (lastParts h (first h) (last h P)) R.own R.own R.common (said₁ h R) (said₂ h R (O := O))
      u.1 u.2.2
  have e : m₂.st.input = R.common := u₂.1.2.2.2.2.2.2.1
  rw [hi] at hin
  exact e.symm.trans hin

/-- **In front of the second chain's test: the sample rows say of the words of the item "rows".** -/
theorem samples_at_W_at_letters {k : Coins A.B} {st : S₃}
    {m : Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit} {E : Env}
    (u : ThrS (thread₃ h P R) (said₃ h P R) 2 k st m E) (ds : List Fmt.Drawn) :
    ∀ G', st.st.groups[st.loc.own]? = some G' →
      sampleItem rdE st.st G'.members.toList
        (wordsAtW h (first h) (reads h) st k m.st.input (m.st.heard ++ ds)) := by
  have hi : m.st.input = R.own := u.1.2.2.2.2.2.2.1
  refine AtFullSide.K12.samples_at_W_of_tied h (first h) (reads h) (shared h O)
    (lastParts h (first h) (last h P)) R.own R.own R.common (said₁ h R) (said₂ h R (O := O))
    (fun _ _ _ g => g.1.1) u.1 u.2.2 ?_ ds
  rw [hi]
  have e := endsAt_at_run h P (common_at_stand h P R u) k (m.st.heard.take (thread₃ h P R).front)
  have e' : (lastParts h (first h) (last h P)).ends k R.own
      (m.st.heard.take (thread₃ h P R).front) =
      (lastAtRun h (first h) (reads h) (shared h O) (lastParts h (first h) (last h P)) R).ends k
        R.own (m.st.heard.take (thread₃ h P R).front) := e
  rw [e']
  exact ends_at_lastAtRun h (first h) (reads h) (shared h O) (lastParts h (first h) (last h P)) R k
    R.own _

end AtFullSide.K14

#print axioms AtFullSide.K14.five_shared_at_letters
#print axioms AtFullSide.K14.five_last_zero_at_letters
#print axioms AtFullSide.K14.five_last_one_at_letters
#print axioms AtFullSide.K14.accepted_last_one_at_letters
#print axioms AtFullSide.K14.door_rides_at_letters
#print axioms AtFullSide.K14.common_at_ready
#print axioms AtFullSide.K14.common_at_stand
#print axioms AtFullSide.K14.samples_at_W_at_letters
