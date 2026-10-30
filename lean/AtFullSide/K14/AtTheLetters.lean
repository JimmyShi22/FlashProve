-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/AtTheLetters.lean: three statements on the shared and the second chain, AT THE NAMED
VALUES OF THE THREE CHAINS' LETTERS (AtFullSide/Honest/TheLetters.lean). Statements: calls alone. No
definition.

  fixed_fields_at_the_letters   **the three sentences on the letters fixed and taken that the
                      threads' rule asks at the two later chains** (each tree available at a border
                      is fixed by the challenges heard there, at the shared and at the second chain;
                      each taken tree is declared as taken over), at later, shared, last and
                      thread₃, from the maker's return alone. That later's field fixed, last's field
                      fixed and last's field taken are the terms which the law asks holds by
                      unfolding; so does the number in front of the second chain's own test;
                      own_stages_at_the_letters has that test's stages; the like sentence on the
                      first chain is the library's treesFixed_first
  shared_door_at_the_letters    the five tests that the second chain's form at its first border
                      makes on the shared chain's end say yes, from a stand of thread₂ with said₂ at
                      its last border
  tied_enters_at_the_letters    **the second clause of said₃ (TiedToEnds,
                      Honest/K14/TiedToEnds.lean) holds at the state at which the frame begins the
                      second chain** behind stands of thread₁ with said₁ and thread₂ with said₂ at
                      their last borders, at every border's number

By what: later_fields_at_head (AtFullSide/K14/SendingRoundsAtHead.lean); shared_door_saidS
(AtFullSide/K14/SharedDoorAtTerm.lean); tied_at_door_ready (Honest/K14/TiedToEnds.lean).

WHAT THE FIRST STATEMENT READS OF OpenLast. The open letter ownMany with its clause ownIsTheFilling:
that it is the job which the filling lays. From that clause its place is the seated place of the
request's own test (letter_at_filling, Johnson/Desc/ProofFile/Honest/K12/AtFile/WFilling.lean),
whose stages are the written place's (nums_head_W, AtFullSide/K12/RestTiesAtHeadW.lean).

Limits.
  * h : HeadAtReturn and made are hypotheses. hR: that R is what the frame's routine ready returns.
    That a value of OpenLast exists is not shown here.
  * NOTHING HERE SHOWS THAT ANY THREAD STANDS AT ANY RUN.
  * tied_enters_at_the_letters pays the clause TiedToEnds alone: the first clause of said₃, and the
    second chain's invariant at its first border, are not shown here.
  * This file has no statement on this kind's payment at the return of the honest prover's own
    maker: such a statement names no letter of a thread.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import AtFullSide.Honest.TheLetters
import AtFullSide.K14.SendingRoundsAtHead
import AtFullSide.K14.SharedDoorAtTerm
import AtFullSide.K1.FirstScriptFixed
import E2E.ThruAtTerm
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes (TableKey)
open ProofFile.Honest ProofFile.Honest.K14 ProofFile.Honest.FirstThread
open H2K.Member (piWFull)
open ProofFile.Honest.Term (matrixInput matrixFilling)
open VerifiableInference.Desc.Third (sharedOfEnd)
open VerifiableInference.Desc.Last (sharedDoorB)
open AtFullSide.Honest.TheLetters

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {O : OpenShared A}

/-- The stages of the second chain's own test, as the open letter ownMany holds them, are the
written place's: that letter is the filling's job, whose place is the seated place of the request's
own test. -/
theorem own_stages_at_the_letters
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (P : OpenLast h O) :
    P.ownMany.toRun.toTest.p.nums.stages = piWFull.nums.stages := by
  obtain ⟨M, hM, hp, -⟩ := ProofFile.Honest.K12.AtFile.letter_at_filling (Wt := WtF) h.head matrixInput
    OnBytes.HonestTrace.Sz.ref openHonest made
  obtain rfl : M = P.ownMany := Option.some.inj (hM.symm.trans P.ownIsTheFilling)
  show P.ownMany.p.nums.stages = _
  rw [hp]
  exact congrArg (·.stages) (ProofFile.Honest.K12.Light.nums_head_W h.head.toAtMg)

/-- **The three sentences on fixed and taken, at the named letters.** made: the maker returns A at
the filling. -/
theorem fixed_fields_at_the_letters
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    (∀ b, b ≤ h.description.shared.blocksInOrder.length → ∀ j, j < treesTo h.description.shared.blocksInOrder b →
      (shared h O).fixed (.own j) ≤ roundsTo h.description.shared.blocksInOrder b) ∧
    (∀ b, b ≤ h.description.second.blocksInOrder.length → ∀ σ ∈ (thread₃ h P R).hand b,
      (thread₃ h P R).fixed σ ≤ (thread₃ h P R).front + roundsTo (thread₃ h P R).bs b) ∧
    ∀ σ ∈ (lastParts h (first h) (last h P)).taken, ∃ c j, σ = Fmt.TreeSource.taken c j :=
  later_fields_at_head h (first h) (reads h) (later (h := h) O) (last h P) R rfl rfl rfl
    (own_stages_at_the_letters h made P) rfl (ProofFile.Honest.K1.treesFixed_first h.head made)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The five tests on the shared chain's end say yes, from a stand of thread₂ with said₂ at its last
border. -/
theorem shared_door_at_the_letters (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    ∀ k s₂ m E, ThrS (thread₂ h R (O := O)) (said₂ h R (O := O))
        h.description.shared.blocksInOrder.length k s₂ m E →
      ∀ e, Desc.K14.ended s₂ = some e →
        sharedDoorB (ToldDesc.p14At A.Z) (sharedOfEnd e) = true :=
  shared_door_saidS h (reads h) (shared h O) R.common (said₂ h R (O := O))

/-- **The clause TiedToEnds of said₃ holds where the frame begins the second chain**, behind stands
of the two earlier threads at their last borders. -/
theorem tied_enters_at_the_letters (P : OpenLast h O) {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {x : ProofFile.Inst}
    {k₀ : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit}
    (hR : ready h.description A.B A.H w₀ rc x k₀ = .ok R) {k : Coins A.B} {e₁ : P5J.TS}
    {m₁ : Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit} {E₁ : Env}
    (u₁ : ThrS (thread₁ h R) (said₁ h R) h.description.first.blocksInOrder.length k e₁ m₁ E₁)
    {e₂ : Desc.K14.St} {m₂ : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit} {E₂ : Env}
    (u₂ : ThrS (thread₂ h R (O := O)) (said₂ h R (O := O)) h.description.shared.blocksInOrder.length k e₂
      m₂ E₂) (b : Nat) (o : Option (List VerifiableInference.Desc.OpenedColumn)) :
    TiedToEnds (thread₁ h R) (said₁ h R) h.description.first.blocksInOrder.length (thread₂ h R (O := O))
      (said₂ h R (O := O)) h.description.shared.blocksInOrder.length id
      (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) (thread₃ h P R).front b k
      { R.start₃ A.H m₁ m₂ with opened := o } :=
  tied_at_door_ready h (first h) (reads h) (shared h O) (lastParts h (first h) (last h P)) hR R.own
    (said₁ h R) (said₂ h R (O := O)) u₁ u₂ b o

end AtFullSide.K14

#print axioms AtFullSide.K14.own_stages_at_the_letters
#print axioms AtFullSide.K14.fixed_fields_at_the_letters
#print axioms AtFullSide.K14.shared_door_at_the_letters
#print axioms AtFullSide.K14.tied_enters_at_the_letters
