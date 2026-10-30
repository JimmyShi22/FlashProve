-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/CommittedColumns.lean: the columns of the table that the committer stores are, as
words, the columns of encW, which a filling lays as its prover's stored columns. At public files in
scope, at every matrix and every randomness, in range or not. That a given prover's stored columns
are encW is for the caller.

  committerWords           at one position of the committed table.
  committedColumnsWords    at every item and position: what CommittedColumns asks, as an equation of
                           the committer's columns and encW.

By what. enc_col: a symbol of the object's table is its position with the words of the column.
home_is_ours: the object's table is strAt at the plain readers of the index and the coins. encW_inScope:
in scope encW at item 0 is encAt at the full size's numbers.
-/
import E2E.BridgeJoinAtFiles
import Johnson.Bind.ForProver.HomeIsOurs
import Johnson.Bind.ForProver.ShapeInScope
import Johnson.Desc.ProofFile.Honest.AtGoalInput

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open AtPublicFiles.Key (cellsReader padReader tailReader)
open P5J

/- These definitions are made irreducible here, as in Johnson/Bind/ForProver/HomeIsOurs.lean, so that
Lean does not unfold them while it elaborates. The kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

local instance (priority := high) padsCommittedColumns : Nonempty PadZ := pads_nonempty frS 402653181

/-- The plain entries of a matrix, at the full size. -/
abbrev entryZ (M : FullSizeMatrix) : ℕ → ℕ → UInt64 :=
  Bind.ForProver.entryAtF numsRef.kLo numsRef.rows frS.P.v (cellsReader M)

/-- The plain coins of an encoding's randomness. -/
abbrev randZ (Z : PublicFiles) (ρ : (protocolAtFiles Z).EncodingRandomness) : ProofFile.Honest.TableRand :=
  ⟨padReader (S := frS) (cut := 402653181) ρ.1, tailReader (S := frS) ρ.2⟩

/-- **At one position, the committer's column is encAt's, as words.** -/
theorem committerWords (Z : PublicFiles) (M : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness) (p : ℕ) :
    ((cmAlong (AZ Z) PadZ (holdZ Z)).enc M ρ p).map (List.map ofF) =
      (Bind.ForProver.encAt Bind.Column.shFull (entryZ M) (randZ Z ρ) p).map (List.map ofF) := by
  by_cases hp : p < 2 ^ frS.P.T.a
  · obtain ⟨e₀⟩ : Nonempty (protocolAtFiles Z).OutOfDomainSeed := inferInstance
    have h₁ := congrFun (Bind.ForProver.home_is_ours committerCoinCountLessOne Z M ρ e₀).1 ⟨p, hp⟩
    have h₂ := enc_col (AZ Z) PadZ (holdZ Z) M ρ ⟨p, hp⟩
    have h₃ : (colF (AZ Z) PadZ (holdZ Z) M ρ ⟨p, hp⟩).map ofF =
        ((Bind.ForProver.encAt Bind.Column.shFull (entryZ M) (randZ Z ρ) p).getD []).map ofF :=
      congrArg Prod.snd (h₂.symm.trans h₁)
    have h₄ : (cmAlong (AZ Z) PadZ (holdZ Z)).enc M ρ p =
        some (colF (AZ Z) PadZ (holdZ Z) M ρ ⟨p, hp⟩) := dif_pos hp
    have hlt : p < 2 ^ Bind.Column.shFull.a := by
      rw [Bind.Column.agree_full.a]
      exact hp
    obtain ⟨c, hc⟩ : ∃ c, Bind.ForProver.encAt Bind.Column.shFull (entryZ M) (randZ Z ρ) p =
        some c := ⟨_, if_pos hlt⟩
    rw [hc] at h₃ ⊢
    rw [h₄]
    exact congrArg some h₃
  · have h₄ : (cmAlong (AZ Z) PadZ (holdZ Z)).enc M ρ p = none := dif_neg hp
    have hlt : ¬ p < 2 ^ Bind.Column.shFull.a := by
      rw [Bind.Column.agree_full.a]
      exact hp
    have h₅ : Bind.ForProver.encAt Bind.Column.shFull (entryZ M) (randZ Z ρ) p = none := if_neg hlt
    rw [h₄, h₅]

/-- **What a run asks of the committer's columns, in scope**: at every matrix and randomness, every
item and position, the committer's columns as words are those of encW at the maker's public part.
o: the argument of the maker that stands for the format's second hash function. -/
theorem committedColumnsWords (Z : PublicFiles) (scope : InScope Z = true) {o : ProofFile.SecondHashFunctionArgument}
    {Zp : ProofFile.Pub} (h : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) (M : FullSizeMatrix) (ρ : (protocolAtFiles Z).EncodingRandomness)
    (it p : ℕ) :
    (if it == 0 then (cmAlong (AZ Z) PadZ (holdZ Z)).enc M ρ p else none).map (List.map ofF) =
      (Bind.ForProver.encW Zp ⟨cellsReader M⟩
        (ProofFile.Honest.randOf (S := frS) (cut := 402653181) ρ) it p).map (List.map ofF) := by
  cases it with
  | zero =>
    rw [Bind.ForProver.encW_inScope scope h]
    exact committerWords Z M ρ p
  | succ k =>
    have e : Bind.ForProver.encW Zp ⟨cellsReader M⟩
        (ProofFile.Honest.randOf (S := frS) (cut := 402653181) ρ) (k + 1) p = none :=
      if_neg fun a => Nat.succ_ne_zero k a.1
    rw [e]
    rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.committerWords
#print axioms AtPublicFiles.AtFiles.committedColumnsWords
