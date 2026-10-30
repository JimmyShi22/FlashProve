-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyFixedLinesO.lean: The twin of E2E/KeyFixedLines.lean at the
test on G_omega, over lot F7 unturned: how many challenges fix that test's trees, and where
they stand in the chain's count. They can say no, with no slack.

  decl_front10   the chain's rounds: the eight's, the two tests', the end's
  seeds_closed_O, seed_own_closed   BY THE KERNEL: tree 8 + τ goes out in round 43 + seedRound τ, tree 7
                 in round 43 + 1
  roots_closed_O, rounds_closed_O   the counts behind it
  seeds_no_slack_O, seed_own_no_slack, seeds_bent_tree_O, seeds_bent_rounds_O, own_bent   controls
  send_key_O, send_own, fixed_key_O, fixed_own   at the description's rounds, at threadKey's field
  trees_key_O, rounds_key_O   seven trees and 43 rounds stand in front of member 10, at threadKey's bs

Limits. At the written places PF, under e and B. Public numbers: nothing played, no coin, no table.
Nothing on completeness, soundness or hiding.
-/
import E2E.KeyFixedLines

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

namespace AtPublicFiles.KeyFixedLines
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block sendRound)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Claim descriptionFromSource)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (threadKey parKey)
open _root_.Desc.K14 (P14 St blocksOr)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (flat₂)
open AtPublicFiles.AtFiles.Full (QK PF omega_full)
open AtPublicFiles.KeyThread (sentIn sendRound_append rootsOf decl₂)
open AtPublicFiles.KeyTreesKey (declOf)
open H2K.Member (piKOFull)
open H2K.JointK (keyGu keyOmega keySharedPre keySharedEnd keyShared_cut_omega)
open ProofFile.Honest.K12 (seedRound)

/-- The rounds up to and with the test on G_omega, at the written value. -/
abbrev declO : List Fmt.DeclaredRound :=
  (declOf QK ++ (keyGu PF).rounds) ++ (keyOmega (PF.O.getD PF.U)).rounds

/-- **The chain's rounds: the eight's, the two tests', the end's.** -/
theorem decl_front10 (Xs : Source) (Nr : H2U.PlaceNums) :
    decl₂ (descriptionFromSource Xs Nr PF) = ((declOf (parKey Xs PF) ++ (keyGu PF).rounds) ++
                       (keyOmega (PF.O.getD PF.U)).rounds) ++ (keySharedEnd Xs.chains PF).rounds := by
  show (flat₂ Xs.chains PF).flatMap (·.rounds) = _
  have hc : flat₂ Xs.chains PF = (keySharedPre Xs.chains PF ++ [keyGu PF]) ++
      keyOmega (PF.O.getD PF.U) :: [keySharedEnd Xs.chains PF] :=
    keyShared_cut_omega _ _ _ omega_full
  rw [hc]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, pre_rounds,
    List.append_assoc]

/-- **Tree 8 + τ goes out in round 43 + seedRound τ.** By the kernel. -/
theorem seeds_closed_O : ∀ τ, τ < 3 →
    sendRound declO (8 + τ) = some (43 + seedRound piKOFull.nums.stages τ) := by
  decide +kernel

/-- **Tree 7 goes out in round 43 + 1.** By the kernel. -/
theorem seed_own_closed : sendRound declO 7 = some (43 + 1) := by
  decide +kernel

theorem roots_closed_O : 11 ≤ rootsOf declO := by
  decide +kernel

theorem rounds_closed_O : (declOf QK ++ (keyGu PF).rounds).length = 43 := by
  decide +kernel

/-- Control: no slack, by one challenge either way. -/
theorem seeds_no_slack_O : ∀ τ, τ < 3 →
    sendRound declO (8 + τ) ≠ some (42 + seedRound piKOFull.nums.stages τ) ∧
      sendRound declO (8 + τ) ≠ some (44 + seedRound piKOFull.nums.stages τ) := by
  decide +kernel

/-- Control: no slack at own 7. -/
theorem seed_own_no_slack : sendRound declO 7 ≠ some 43 ∧ sendRound declO 7 ≠ some 45 := by
  decide +kernel

/-- Control: tree 7 is not the first switch's. -/
theorem seeds_bent_tree_O :
    sendRound declO 7 ≠ some (43 + seedRound piKOFull.nums.stages 0) := by
  decide +kernel

/-- Control: the test with its first round dropped. -/
theorem seeds_bent_rounds_O :
    sendRound ((declOf QK ++ (keyGu PF).rounds) ++ (keyOmega (PF.O.getD PF.U)).rounds.drop 1) 8 ≠
      some (43 + seedRound piKOFull.nums.stages 0) := by
  decide +kernel

/-- Control: tree 6 is the other test's. -/
theorem own_bent : sendRound declO 6 ≠ some (43 + 1) := by
  decide +kernel

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **At the description's own rounds.** -/
theorem send_key_O (e : parKey Xs PF = QK) {τ : ℕ} (hτ : τ < 3) :
    sendRound (decl₂ (descriptionFromSource Xs Nr PF)) (8 + τ) =
      some (43 + seedRound piKOFull.nums.stages τ) := by
  have hr : 11 ≤ rootsOf ((declOf QK ++ (keyGu PF).rounds) ++
      (keyOmega (PF.O.getD PF.U)).rounds) := roots_closed_O
  rw [decl_front10, e, sendRound_append _ _ _ (by omega)]
  exact seeds_closed_O τ hτ

theorem send_own (e : parKey Xs PF = QK) :
    sendRound (decl₂ (descriptionFromSource Xs Nr PF)) 7 = some (43 + 1) := by
  have hr : 11 ≤ rootsOf ((declOf QK ++ (keyGu PF).rounds) ++
      (keyOmega (PF.O.getD PF.U)).rounds) := roots_closed_O
  rw [decl_front10, e, sendRound_append _ _ _ (by omega)]
  exact seed_own_closed

/-- **At threadKey's field fixed, with no slack.** -/
theorem fixed_key_O (e : parKey Xs PF = QK) {τ : ℕ} (hτ : τ < 3) :
    (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).fixed (.own (8 + τ)) =
      43 + seedRound piKOFull.nums.stages τ := by
  show sentIn (decl₂ (descriptionFromSource Xs Nr PF)) (8 + τ) = _
  unfold sentIn
  rw [send_key_O Xs Nr e hτ]
  rfl

/-- **Own 7, likewise.** -/
theorem fixed_own (e : parKey Xs PF = QK) :
    (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).fixed (.own 7) = 43 + 1 := by
  show sentIn (decl₂ (descriptionFromSource Xs Nr PF)) 7 = _
  unfold sentIn
  rw [send_own Xs Nr e]
  rfl

/-- **Seven trees stand in front of member 10**: chain_counts. -/
theorem trees_key_O (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF)) :
    treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 10 = 7 :=
  (AtPublicFiles.KeyTblTrial.chain_counts Xs Nr K ℓ Nm Mg₀ tb rest Kp Vd w e B).2.1

/-- **43 rounds stand in front of member 10.** -/
theorem rounds_key_O (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF)) :
    roundsTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 10 = 43 := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w
  have hp : (keySharedPre Xs.chains PF ++ [keyGu PF]).length = 10 := by
    unfold keySharedPre
    rw [List.length_append, List.length_cons, List.length_map, AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    rfl
  have hc : flat₂ Xs.chains PF = (keySharedPre Xs.chains PF ++ [keyGu PF]) ++
      keyOmega (PF.O.getD PF.U) :: [keySharedEnd Xs.chains PF] :=
    keyShared_cut_omega _ _ _ omega_full
  unfold roundsTo declsTo
  rw [hO.bs]
  show (((flat₂ Xs.chains PF).take 10).flatMap (·.rounds)).length = 43
  rw [hc, List.take_left' hp, List.flatMap_append, pre_rounds, e]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  exact rounds_closed_O

end

end AtPublicFiles.KeyFixedLines

#print axioms AtPublicFiles.KeyFixedLines.declO
#print axioms AtPublicFiles.KeyFixedLines.decl_front10
#print axioms AtPublicFiles.KeyFixedLines.seeds_closed_O
#print axioms AtPublicFiles.KeyFixedLines.seed_own_closed
#print axioms AtPublicFiles.KeyFixedLines.roots_closed_O
#print axioms AtPublicFiles.KeyFixedLines.rounds_closed_O
#print axioms AtPublicFiles.KeyFixedLines.seeds_no_slack_O
#print axioms AtPublicFiles.KeyFixedLines.seed_own_no_slack
#print axioms AtPublicFiles.KeyFixedLines.seeds_bent_tree_O
#print axioms AtPublicFiles.KeyFixedLines.seeds_bent_rounds_O
#print axioms AtPublicFiles.KeyFixedLines.own_bent
#print axioms AtPublicFiles.KeyFixedLines.send_key_O
#print axioms AtPublicFiles.KeyFixedLines.send_own
#print axioms AtPublicFiles.KeyFixedLines.fixed_key_O
#print axioms AtPublicFiles.KeyFixedLines.fixed_own
#print axioms AtPublicFiles.KeyFixedLines.trees_key_O
#print axioms AtPublicFiles.KeyFixedLines.rounds_key_O
