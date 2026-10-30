-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnRounds.lean: CAN THE PREMISE ON THE ROUNDS BE MET: `RoundsInFrontOfOwnTest`
(LotOwnStand.lean) in scope, at every thread that plays chain 2 of the key file's description with the two earlier
chains' declared rounds in front.

  `point_is_drawn_first`   the first of the eight's declared rounds at the written plan draws the point's count. By the
                           kernel; with a control: the second does not
  `rounds_in_front`        the structure

By what. `decl_front9` (E2E/KeyFixedLines.lean), `later_sourced`, `par_sourced` (E2E/KeyShapeSharedTies.lean), `flat_four`
(OwnSeat.lean).

Limits.
- In scope, at the written sizes. The thread's three letters (chain, ahead, bs) are premises: at `lettersLastKey` they
  hold by unfolding (`sits_three`, `ahead_key`, E2E/KeyLastThread.lean).
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnStand
import E2E.KeyFixedLines
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc.Key (Source LaterPlaces Xi Claim descriptionFromSource)
open VerifiableInference.Desc.Third (S₃)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyTreesKey (declOf)
open AtPublicFiles.KeyFixedLines (decl_front9)

/-- The first of the eight's declared rounds draws the point's count. By the kernel. -/
theorem point_is_drawn_first :
    ((declOf QK).head?).map (·.entry.drawE) = some QK.par.S.kCol := by
  decide +kernel

/-- Control: the second round draws otherwise. -/
theorem point_is_not_drawn_second :
    (((declOf QK).drop 1).head?).map (·.entry.drawE) ≠ some QK.par.S.kCol := by
  decide +kernel

variable {V Pb W₀ Rc X : Type} {K₀ : KeyPub} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **`RoundsInFrontOfOwnTest` in scope.** -/
theorem rounds_in_front {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true)
    (T : Thread (keyBook K₀) S₃ Claim V (Local W₀ Rc Xi Unit) X Pb) (hchain : T.chain = 2)
    (hahead : T.ahead = declsTo (descriptionFromSource Xs Nr Pl).first.blocksInOrder (descriptionFromSource Xs Nr Pl).first.blocksInOrder.length ++
      declsTo (descriptionFromSource Xs Nr Pl).shared.blocksInOrder (descriptionFromSource Xs Nr Pl).shared.blocksInOrder.length)
    (hbs : T.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) :
    RoundsInFrontOfOwnTest T Xs Nr Pl QK.par.S.kCol := by
  have e : VerifiableInference.Desc.Key.sharedPar Xs.chains
      (VerifiableInference.Desc.Key.beforeSharedPoint Pl) = QK := par_sourced hs scope
  obtain rfl := later_sourced hs scope
  have hf := point_is_drawn_first
  have h2 : declsTo (descriptionFromSource Xs Nr PF).second.blocksInOrder 2 = [] := by
    obtain ⟨a, b, c, d, hflat, ra, rb, -, -, -, -, -⟩ := flat_four Xs Nr PF
    unfold declsTo
    rw [hflat]
    simp [ra, rb]
  have h9 := decl_front9 Xs Nr
  cases hD : declOf QK with
  | nil =>
    rw [hD] at hf
    cases hf
  | cons d tl =>
    rw [hD] at hf
    have e' : AtPublicFiles.KeySharedThread.parKey Xs PF = QK := e
    refine ⟨hchain, d, (tl ++ (H2K.JointK.keyGu PF).rounds) ++
      ((PF.O.toList.map H2K.JointK.keyOmega) ++
        [H2K.JointK.keySharedEnd Xs.chains PF]).flatMap (·.rounds), ?_, Option.some.inj hf⟩
    have h2' : declsTo T.bs 2 = [] := by
      rw [hbs]
      exact h2
    rw [hahead, h2', List.append_nil]
    unfold declsTo
    rw [List.take_length, List.take_length]
    show _ ++ AtPublicFiles.KeyThread.decl₂ (descriptionFromSource Xs Nr PF) = _
    rw [h9, e', hD]
    rfl

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.point_is_drawn_first
#print axioms ProofFile.Honest.K12.AtKey.point_is_not_drawn_second
#print axioms ProofFile.Honest.K12.AtKey.rounds_in_front
