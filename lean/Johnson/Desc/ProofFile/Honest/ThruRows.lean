-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruRows.lean: the prover that a family of the protocol plays is not
the prover read through (Honest/ThruRun.lean) itself. It is that prover with the rows' parts and
the committer's columns and key (Sides.prover, Honest/Rule.lean; Committer.proverAt,
Honest/CommitterAt.lean). This file says what the run of that prover is, and names what it needs.

  Prover.withStored    a prover with other columns
  ready_withStored, runC_withStored, silentAt_withStored   ready and the silent set read no column;
                       runC reads them through storedWords alone, at its own index and randomness
  rows_prover_eq       under the rows' equation and the key's: the rows' prover with the committer's
                       columns is the prover with these columns
  CommittedColumns     the premise on the columns, at one index and one randomness
  ready_rows_thru, runC_rows_thru, silentAt_rows_thru, outcomeC_rows_thru   the four at that prover

Why a premise. runC hands a column to the verifier's step, so its value depends on the columns that
it reads. Where the committer's columns and the filling's are not the same the two runs are not the
same, and no equation can hold. CommittedColumns is asked at the one index and randomness of the
run, not at every index: outside the range nothing depends on it, since ready refuses there.

Limits.
  * CommittedColumns, the rows' equation (hrows) and the key's (hk) are premises. This file shows
    none of them at any filling.
  * The premise hrows is an equation of lists of parts. Nothing here says that rows with real
    simulators meet it.
  * Nothing on a measure of coins. rd need not be onto, and need not keep a measure.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruRun
import Johnson.Desc.ProofFile.Honest.CommitterAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {Xi W₀ W₀' Rc Rc' Ky Tr X₀ X Sd Xc : Type}

/-- **A prover with other columns**: its other fields stay. -/
def Prover.withStored (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F)) : Prover W₀ Rc Xi Ky Tr X₀ X :=
  { H with stored := s }

/-- ready reads no column. -/
theorem ready_withStored (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F)) (w : W₀) (rc : Rc) (x : Xi) (c : Coins B) :
    ready F B (H.withStored s) w rc x c = ready F B H w rc x c := rfl

/-- Nor does the silent set. -/
theorem silentAt_withStored (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F)) (w : W₀) (rc : Rc) (x : Xi) (ρ : Draws) :
    silentAt F (H.withStored s) w rc x ρ = silentAt F H w rc x ρ := rfl

/-- runC reads the columns at its own index and randomness, as words. -/
theorem runC_withStored (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F)) (w : W₀) (rc : Rc) (x : Xi) (c : Coins B)
    (ρ : Draws) (hs : (H.withStored s).storedWords w rc = H.storedWords w rc) :
    runC F B (H.withStored s) w rc x c ρ = runC F B H w rc x c ρ := by
  rw [runC_eq, runC_eq, hs, ready_withStored]
  cases ready F B H w rc x c with
  | error e => rfl
  | ok R => rfl

/-- **The columns that a committer lays at one item.** -/
def Committer.columnsAt (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat) :
    W₀' → Rc' → Nat → Nat → Option (List Cb.Gl.F) :=
  fun w₀ rc it x => if it == item₀ then Cm.enc w₀ rc x else none

/-- **The rows' prover with a committer's columns and key**, where the rows' parts are the prover's
and the key is the prover's: the prover with these columns. -/
theorem rows_prover_eq {F : FileDescription Xi} {B : ProverCoinCounts} (G : Sides F B W₀' Rc' Ky Tr X₀ X)
    (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat) (H' : Prover W₀' Rc' Xi Ky Tr X₀ X)
    (hrows : G.prover H' = H') (hk : Cm.key = H'.key) :
    G.prover (Cm.proverAt item₀ H') = H'.withStored (Cm.columnsAt item₀) := by
  have e : G.prover (Cm.proverAt item₀ H') = Cm.proverAt item₀ (G.prover H') := rfl
  rw [e, hrows]
  unfold Committer.proverAt Prover.withStored Committer.columnsAt
  rw [hk]

/-- **What a run asks of the committer's columns**: at its own index and randomness, at every item
and position, they show the words of the columns of the prover that is read through. -/
def CommittedColumns (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (g : W₀' → W₀) (rd : Rc' → Rc) (w : W₀') (rc : Rc') : Prop :=
  ∀ it p, (Cm.columnsAt item₀ w rc it p).map (·.map OnBytes.Slice.ofF) =
    H.storedWords (g w) (rd rc) it p

section
variable (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {F : FileDescription Xi} {B : ProverCoinCounts}
  (G : Sides F B W₀' Rc' Ky Tr X₀ X) (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat)
  (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (c : Coins B) (ρ : Draws)

/-- **ready at the rows' prover**: the same refusal, or the prepared run read through. -/
theorem ready_rows_thru (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key) :
    ready F B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x c =
      (ready F B H (g w) (rd rc) x c).map (Ready.thru g rd w rc) := by
  rw [rows_prover_eq G Cm item₀ _ hrows hk, ready_withStored]
  exact ready_thru g rd d F B H w rc x c hd

/-- **The run of the rows' prover is the run of the prover that is read through.** -/
theorem runC_rows_thru (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
    (hs : CommittedColumns Cm item₀ H g rd w rc) :
    runC F B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x c ρ =
      runC F B H (g w) (rd rc) x c ρ := by
  have hw : ((H.thru g rd d).withStored (Cm.columnsAt item₀)).storedWords w rc =
      (H.thru g rd d).storedWords w rc := by
    funext it p
    exact hs it p
  rw [rows_prover_eq G Cm item₀ _ hrows hk, runC_withStored F B _ _ w rc x c ρ hw]
  exact runC_thru g rd d F B H w rc x c ρ hd

/-- **So is its silent set.** -/
theorem silentAt_rows_thru (hrows : G.prover (H.thru g rd d) = H.thru g rd d)
    (hk : Cm.key = H.key) :
    silentAt F (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x ρ =
      silentAt F H (g w) (rd rc) x ρ := by
  rw [rows_prover_eq G Cm item₀ _ hrows hk, silentAt_withStored]
  exact silentAt_thru g rd d F H w rc x ρ

/-- **And its outcome.** -/
theorem outcomeC_rows_thru (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
    (hs : CommittedColumns Cm item₀ H g rd w rc) :
    outcomeC F B (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x c ρ =
      outcomeC F B H (g w) (rd rc) x c ρ := by
  unfold outcomeC
  rw [silentAt_rows_thru g rd d G Cm item₀ H w rc x ρ hrows hk,
    runC_rows_thru g rd d G Cm item₀ H w rc x c ρ hd hrows hk hs]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.Prover.withStored
#print axioms ProofFile.Honest.ready_withStored
#print axioms ProofFile.Honest.silentAt_withStored
#print axioms ProofFile.Honest.runC_withStored
#print axioms ProofFile.Honest.Committer.columnsAt
#print axioms ProofFile.Honest.rows_prover_eq
#print axioms ProofFile.Honest.CommittedColumns
#print axioms ProofFile.Honest.ready_rows_thru
#print axioms ProofFile.Honest.runC_rows_thru
#print axioms ProofFile.Honest.silentAt_rows_thru
#print axioms ProofFile.Honest.outcomeC_rows_thru
