-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruCommitted.lean: the prover with a committer's columns and key
(Committer.proverAt, Honest/CommitterAt.lean), with no rows in front of it, at a prover read through.
The laws of Honest/ThruRows.lean and Honest/ThruThreads.lean without their letter G, for a family
that runs the committer's prover as it stands.

  proverAt_eq          under the key's equation: the prover with the committer's columns
  ready_committed_thru, runC_committed_thru, silentAt_committed_thru, outcomeC_committed_thru
  committed_of_thru    ready returns, the plan serves, there is a value of ThreadsC with the same
                       falls, at that prover
  ready_committed_made, runC_committed_made   at the maker's return at a filling read through

By what. ready_thru, runC_thru and their sisters (Honest/ThruRun.lean); ThreadsC.thru,
PlanServes.thru (Honest/ThruThreads.lean); made_thru (Honest/ThruAtPure.lean).

Limits.
  * NOT IN FRONT OF A LAW OVER COINS: committed_of_thru takes and gives a value of ThreadsC.
  * hk, hd and CommittedColumns are premises, as in Honest/ThruRows.lean.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruThreads
import Johnson.Desc.ProofFile.Honest.ThruAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {Xi W₀ W₀' Rc Rc' Ky Tr X₀ X Sd Xc : Type}

/-- **A committer's prover is the prover with the committer's columns**, where the keys are one. -/
theorem proverAt_eq (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat)
    (H' : Prover W₀' Rc' Xi Ky Tr X₀ X) (hk : Cm.key = H'.key) :
    Cm.proverAt item₀ H' = H'.withStored (Cm.columnsAt item₀) := by
  unfold Committer.proverAt Prover.withStored Committer.columnsAt
  rw [hk]

section
variable (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {F : FileDescription Xi} {B : ProverCoinCounts}
  (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B) (ρ : Draws)

/-- ready at the committer's prover of the prover read through. -/
theorem ready_committed_thru (hd : H.inRange (g d) = H.inRange H.dummy) (hk : Cm.key = H.key) :
    ready F B (Cm.proverAt item₀ (H.thru g rd d)) w rc x c =
      (ready F B H (g w) (rd rc) x c).map (Ready.thru g rd w rc) := by
  rw [proverAt_eq Cm item₀ _ hk, ready_withStored]
  exact ready_thru g rd d F B H w rc x c hd

/-- **The run at the committer's prover is the run of the prover that is read through.** -/
theorem runC_committed_thru (hd : H.inRange (g d) = H.inRange H.dummy) (hk : Cm.key = H.key)
    (hs : CommittedColumns Cm item₀ H g rd w rc) :
    runC F B (Cm.proverAt item₀ (H.thru g rd d)) w rc x c ρ =
      runC F B H (g w) (rd rc) x c ρ := by
  have hw : ((H.thru g rd d).withStored (Cm.columnsAt item₀)).storedWords w rc =
      (H.thru g rd d).storedWords w rc := by
    funext it p
    exact hs it p
  rw [proverAt_eq Cm item₀ _ hk, runC_withStored F B _ _ w rc x c ρ hw]
  exact runC_thru g rd d F B H w rc x c ρ hd

/-- Its silent set. -/
theorem silentAt_committed_thru (hk : Cm.key = H.key) :
    silentAt F (Cm.proverAt item₀ (H.thru g rd d)) w rc x ρ =
      silentAt F H (g w) (rd rc) x ρ := by
  rw [proverAt_eq Cm item₀ _ hk, silentAt_withStored]
  exact silentAt_thru g rd d F H w rc x ρ

/-- Its outcome. -/
theorem outcomeC_committed_thru (hd : H.inRange (g d) = H.inRange H.dummy) (hk : Cm.key = H.key)
    (hs : CommittedColumns Cm item₀ H g rd w rc) :
    outcomeC F B (Cm.proverAt item₀ (H.thru g rd d)) w rc x c ρ =
      outcomeC F B H (g w) (rd rc) x c ρ := by
  unfold outcomeC
  rw [silentAt_committed_thru g rd d Cm item₀ H w rc x ρ hk,
    runC_committed_thru g rd d Cm item₀ H w rc x c ρ hd hk hs]

end

/-- **At the committer's prover: ready returns, the plan serves, and there is a value of ThreadsC
with the same falls.** -/
theorem committed_of_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀')
    (rc : Rc') (x : Xi) (k : Coins Bk) (hd : H.inRange (g d) = H.inRange H.dummy)
    (hk : Cm.key = H.key) (hs : CommittedColumns Cm item₀ H g rd w rc)
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (hR : ready F Bk H (g w) (rd rc) x k = .ok R)
    (P : PlanServes H (g w) (rd rc) R) (T : ThreadsC F Bk H (g w) (rd rc) x k R) :
    ∃ R', ready F Bk (Cm.proverAt item₀ (H.thru g rd d)) w rc x k = .ok R' ∧
      PlanServes (Cm.proverAt item₀ (H.thru g rd d)) w rc R' ∧
      ∃ T' : ThreadsC F Bk (Cm.proverAt item₀ (H.thru g rd d)) w rc x k R',
        T'.f₁ = T.f₁ ∧ T'.f₂ = T.f₂ ∧ T'.f₃ = T.f₃ := by
  have hw : ((H.thru g rd d).withStored (Cm.columnsAt item₀)).storedWords w rc =
      (H.thru g rd d).storedWords w rc := by
    funext it p
    exact hs it p
  have hr := Ready.reads_thru g rd hR
  have e := proverAt_eq Cm item₀ (H.thru g rd d) hk
  have r₁ : ready F Bk ((H.thru g rd d).withStored (Cm.columnsAt item₀)) w rc x k =
      .ok (Ready.thru g rd w rc R) := by
    rw [ready_withStored, ready_thru g rd d F Bk H w rc x k hd, hR]
    rfl
  rw [e]
  exact ⟨_, r₁, (P.thru g rd d hr).withStored _ hw,
    (T.thru g rd d hr).withStored _ hw, rfl, rfl, rfl⟩

section
variable {W₀ W₀' Rc Rc' Tr X₀ X Sd Xc : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
  (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {P : OnlineProverParts W₀ Rc Tr X₀ X} {Z : Pub} {Gr : Ground}
  {F : FileDescription Inst} {B : ProverCoinCounts} {H₀ : Prover W₀ Rc Inst OnBytes.TableKey Tr X₀ X}
  {H' : Prover W₀' Rc' Inst OnBytes.TableKey Tr X₀ X} {rds₀ : W₀ → Rc → Tr → Readers}
  {rds : W₀' → Rc' → Tr → Readers} {rws₀ rws : RowDataOf Inst}
  (Cm : Committer W₀' Rc' Sd Xc Inst OnBytes.TableKey) (item₀ : Nat) (w : W₀') (rc : Rc') (x : Inst)
  (c : Coins B) (ρ : Draws)

/-- ready at the committer's prover of the filling read through. -/
theorem ready_committed_made (base : onlineProverFromPublicFiles o pol lay KL P = .ok ⟨Z, Gr, F, B, H₀, rds₀, rws₀⟩)
    (made : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d P) = .ok ⟨Z, Gr, F, B, H', rds, rws⟩)
    (hd : P.inRange (g d) = true) (hk : Cm.key = pureKey) :
    ready F B (Cm.proverAt item₀ H') w rc x c =
      (ready F B H₀ (g w) (rd rc) x c).map (Ready.thru g rd w rc) := by
  obtain rfl := made_thru g rd d base made hd
  exact ready_committed_thru g rd d Cm item₀ H₀ w rc x c (range_alike g d base hd)
    (hk.trans (key_of_atPure base).symm)

/-- **The run of the committer's prover of the filling read through is the run at the filling.** -/
theorem runC_committed_made (base : onlineProverFromPublicFiles o pol lay KL P = .ok ⟨Z, Gr, F, B, H₀, rds₀, rws₀⟩)
    (made : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d P) = .ok ⟨Z, Gr, F, B, H', rds, rws⟩)
    (hd : P.inRange (g d) = true) (hk : Cm.key = pureKey)
    (hs : CommittedColumns Cm item₀ H₀ g rd w rc) :
    runC F B (Cm.proverAt item₀ H') w rc x c ρ = runC F B H₀ (g w) (rd rc) x c ρ := by
  obtain rfl := made_thru g rd d base made hd
  exact runC_committed_thru g rd d Cm item₀ H₀ w rc x c ρ (range_alike g d base hd)
    (hk.trans (key_of_atPure base).symm) hs

end

end ProofFile.Honest

#print axioms ProofFile.Honest.proverAt_eq
#print axioms ProofFile.Honest.ready_committed_thru
#print axioms ProofFile.Honest.runC_committed_thru
#print axioms ProofFile.Honest.silentAt_committed_thru
#print axioms ProofFile.Honest.outcomeC_committed_thru
#print axioms ProofFile.Honest.committed_of_thru
#print axioms ProofFile.Honest.ready_committed_made
#print axioms ProofFile.Honest.runC_committed_made
