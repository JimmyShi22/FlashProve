-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsSharedSixAtKey.lean: "every run returns" (Owed.runs,
Johnson/Desc/ProofFile/Honest/Owed.lean) AT THE KEY FILE: WHAT ONE SUB-PROTOCOL OWES, BlockPlays
(E2E/OfflineRunsForm.lean), AT THE SIX MEMBERS OF THE KEY FILE's SHARED CHAIN AT WHICH THE KEY
FILE's PROVER HAS A HALF OF THE LINEAR CLAIM's (kind K14): the members 1, 2, 4, 5, 7, 8 of (keyFileDescription
Xs Nr Pl).shared.blocksInOrder, at the list of halves (keyProver K).shared, at every book and EVERY FORM Pre
of the state in front. In the goals' scope.

  key_flat        the key file's shared list begins with the chain's front sub-protocol and the
                  eight that the library makes of the key's parameters parKey Xs Pl
  key_halves      the prover's shared list has no place twice, and holds the kind's six halves
  key_splits      in scope the key's shape splits
  blockPlays_six_key   **BlockPlays at the six members**
  blockPlays_six_atAll   the same where K's letters bear the key file's sixteen places
                  (KeyParts.AtAll, E2E/KeyLaid.lean)

WHAT STAYS A PREMISE. Of blockPlays_six_atAll, FOUR. Two on the public files: scope: they are in the
goals' scope · hs: Xs, Nr, Pl are what the key file's description at these files is made of
(KeySourced, E2E/KeyPublic.lean). Two on the prover's letters K: hP: the two sendings are made at
the key's parameters · hK: KeyParts.AtAll, of which three fields are spent: the shape of K's data
splits, and the two proximity tests' halves stand at the pieces 9 and 10 of the shared chain.

What is not claimed. That any value of K meets hP and hK. The members 0, 3, 6, which have no half,
and 9, 10, 11. That a run returns. Nothing on completeness, soundness or hiding.
Terms. A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import E2E.OfflineRunsSharedSix
import E2E.KeySharedThread
import E2E.KeyLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim keyAsProof sharedTests)
open Desc.K14 (St blocks)
open Desc.K14.Honest (FlatOf Eight flatOf_carried)
open AtPublicFiles.AtFiles (keyFileDescription KeySourced)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared randK14 sharedChainProverSidesInOrder)
open AtPublicFiles.KeySharedThread (parKey plan_key)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **The key file's shared list begins with the front sub-protocol and the eight of the key's
parameters.** -/
theorem key_flat (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    ∃ B : Eight (parKey Xs Pl), FlatOf (keyFileDescription Xs Nr Pl).shared.blocksInOrder (keyAsProof Xs.chains)
      B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 := by
  obtain ⟨layO, hP⟩ := plan_key hs scope
  obtain ⟨B⟩ := hP.eight
  refine ⟨B, ?_⟩
  show FlatOf ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype (Cl' := Claim)).blocksInOrder
    _ _ _ _ _ _ _ _ _
  rw [VerifiableInference.Desc.Key.sharedChain_flat_eq_chainOf_flat Xs.chains Pl Claim]
  exact flatOf_carried (Cl := Claim) (keyAsProof Xs.chains) (parKey Xs Pl) B.b1 B.b2 B.b3 B.b4 B.b5
    B.b6 B.b7 B.b8 (sharedTests Pl) VerifiableInference.Desc.K12.Seat.last B.made

variable {W₀ Rc X₀ X Wk : Type}

/-- **The prover's shared list has no place twice, and holds the kind's six halves.** hA: the shape
of K's data splits. hU, hO: the two proximity tests' halves stand at the pieces 9 and 10. -/
theorem key_halves (K : KeyParts W₀ Rc X₀ X Wk) (hA : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU.place = ⟨2, none, 9, .K12⟩) (hO : K.onOmega.place = ⟨2, none, 10, .K12⟩) :
    ((keyProver K).shared.map (·.place)).Nodup ∧
      ∀ g ∈ (proverSidesOfSharedRounds K.lin K.weights ++
        proverSidesOfSharedSendings ⟨K.send.P, K.send.atPoint⟩ K.weights fun c => randK14 (K.rand c) :
          List (Placed Empty (Common W₀ Rc TableKey) X₀)), g ∈ (keyProver K).shared := by
  refine ⟨?_, fun g hg => ?_⟩
  · rw [keyProver_shared K hA, hU, hO]
    decide
  · have e : (keyProver K).shared =
        sharedChainProverSidesInOrder (proverSidesOfSharedRounds K.lin K.weights) (proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c)) ++
          [K.onU, K.onOmega] := rfl
    rw [e]
    rw [halves_eq, sendHalves_eq, if_pos hA] at hg ⊢
    simp only [sharedChainProverSidesInOrder, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hg ⊢
    tauto

/-- In scope the key's shape splits. -/
theorem key_splits (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    (parKey Xs Pl).S.sharedSplitNeeded = true := by
  show (VerifiableInference.Desc.Key.sharedPar Xs.chains
    (VerifiableInference.Desc.Key.beforeSharedPoint Pl)).S.sharedSplitNeeded = true
  rw [AtPublicFiles.AtFiles.Full.par_sourced hs scope]
  decide +kernel

/-- **BlockPlays at the members 1, 2, 4, 5, 7, 8 of the key file's shared chain**, at the key file's
prover's own list of halves, at every book and every form. hP: K's two sendings are made at the
key's parameters. hsp, hA: the shape splits, at the key's parameters and at K's data. hU, hO: the
places of the two proximity tests' halves. -/
theorem blockPlays_six_key {Bk : ProverCoinCounts} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (K : KeyParts W₀ Rc X₀ X Wk) (hP : K.send.P = parKey Xs Pl)
    (hsp : (parKey Xs Pl).S.sharedSplitNeeded = true) (hA : K.lin.S.sharedSplitNeeded = true)
    (hU : K.onU.place = ⟨2, none, 9, .K12⟩) (hO : K.onOmega.place = ⟨2, none, 10, .K12⟩)
    (Pre : Nat → Mid (Common W₀ Rc TableKey) X₀ → Prop) :
    ∀ j, j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 7 ∨ j = 8 →
      ∀ b, (keyFileDescription Xs Nr Pl).shared.blocksInOrder[j]? = some b →
        BlockPlays (Face.shared : Face Empty (Common W₀ Rc TableKey) TableKey) Bk 1
          (keyProver K).shared b (Pre j) := by
  obtain ⟨B, F⟩ := key_flat hs scope
  obtain ⟨nd, hin⟩ := key_halves K hA hU hO
  rw [hP] at hin
  exact blockPlays_six F B.made K.lin K.send.atPoint hsp hA K.weights
    (fun c => randK14 (K.rand c)) nd hin 1 Pre

/-- **The same where K's letters bear the key file's sixteen places.** hP: K's two sendings are made
at the key's parameters. -/
theorem blockPlays_six_atAll {Bk : ProverCoinCounts} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (K : KeyParts W₀ Rc X₀ X Wk) (hK : K.AtAll)
    (hP : K.send.P = parKey Xs Pl) (Pre : Nat → Mid (Common W₀ Rc TableKey) X₀ → Prop) :
    ∀ j, j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 7 ∨ j = 8 →
      ∀ b, (keyFileDescription Xs Nr Pl).shared.blocksInOrder[j]? = some b →
        BlockPlays (Face.shared : Face Empty (Common W₀ Rc TableKey) TableKey) Bk 1
          (keyProver K).shared b (Pre j) :=
  blockPlays_six_key hs scope K hP (key_splits hs scope) hK.splits hK.onU hK.onOmega Pre

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.key_flat
#print axioms AtPublicFiles.OfflineRows.key_splits
#print axioms AtPublicFiles.OfflineRows.blockPlays_six_atAll
#print axioms AtPublicFiles.OfflineRows.key_halves
#print axioms AtPublicFiles.OfflineRows.blockPlays_six_key
