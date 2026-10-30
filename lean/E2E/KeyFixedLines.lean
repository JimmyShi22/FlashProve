-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyFixedLines.lean: Closed lines at the key's thread, over
lot F7 unturned: how many challenges fix a tree of the test on G_u, and where that test's
trees stand in the chain's count. They can say no: the tie of a text to a run meets T.fixed with no
slack: one challenge fewer and it cannot be met.

  pre_rounds, decl_front9   the chain's rounds begin with the eight's, then the test's
  seeds_closed   BY THE KERNEL: at the written value the round that sends tree 3 + τ is 8 + seedRound τ
  roots_closed, rounds_closed   the counts that stand behind it
  seeds_no_slack, seeds_bent_tree, seeds_bent_rounds, counts_alone   controls: each says no
  send_key, fixed_key   the same at the description's own rounds, and at threadKey's field fixed
  trees_key      treesTo threadKey's bs 9 = 3: chain_counts, called
  rounds_key     eight rounds stand in front of member 9

Limits.
- At the written places PF, and under e : parKey Xs PF = QK and B : Eight, as chain_counts is. That
  these hold at a run's description is not said here.
- Public numbers. Nothing is played, no coin, no table.
- The test on G_omega is not here.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyTreeOwners
import Johnson.Desc.ProofFile.Honest.K12.ScriptLots

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
open AtPublicFiles.AtFiles (flat₂ flat₂_cut)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyThread (sentIn sendRound_append rootsOf decl₂)
open AtPublicFiles.KeyTreesKey (declOf treesOf5)
open H2K.Member (piKUFull)
open ProofFile.Honest.K12 (seedRound)

/-- The rounds in front of the test on G_u are the eight's. -/
theorem pre_rounds (Xs : Source) :
    (H2K.JointK.keySharedPre Xs.chains PF).flatMap (·.rounds) = declOf (parKey Xs PF) := by
  unfold H2K.JointK.keySharedPre declOf
  simp only [List.flatMap_cons, List.flatMap_map]
  rfl

/-- **The chain's rounds: the eight's, the test's, the rest.** -/
theorem decl_front9 (Xs : Source) (Nr : H2U.PlaceNums) :
    decl₂ (descriptionFromSource Xs Nr PF) = (declOf (parKey Xs PF) ++ (H2K.JointK.keyGu PF).rounds) ++
      ((PF.O.toList.map H2K.JointK.keyOmega) ++
        [H2K.JointK.keySharedEnd Xs.chains PF]).flatMap (·.rounds) := by
  show (flat₂ Xs.chains PF).flatMap (·.rounds) = _
  rw [flat₂_cut, List.flatMap_append, pre_rounds, List.flatMap_cons, List.append_assoc]

/-- **At the written value the round that sends the test's tree τ is 8 + seedRound τ.** By the
kernel. -/
theorem seeds_closed : ∀ τ, τ < 4 →
    sendRound (declOf QK ++ (H2K.JointK.keyGu PF).rounds) (3 + τ) =
      some (8 + seedRound piKUFull.nums.stages τ) := by
  decide +kernel

/-- The four trees stand within these rounds. -/
theorem roots_closed : 7 ≤ rootsOf (declOf QK ++ (H2K.JointK.keyGu PF).rounds) := by
  decide +kernel

/-- Eight rounds. -/
theorem rounds_closed : (declOf QK).length = 8 := by
  decide +kernel

/-- Control: no slack, by one challenge either way. -/
theorem seeds_no_slack : ∀ τ, τ < 4 →
    sendRound (declOf QK ++ (H2K.JointK.keyGu PF).rounds) (3 + τ) ≠
        some (7 + seedRound piKUFull.nums.stages τ) ∧
      sendRound (declOf QK ++ (H2K.JointK.keyGu PF).rounds) (3 + τ) ≠
        some (9 + seedRound piKUFull.nums.stages τ) := by
  decide +kernel

/-- Control: tree 2 is a sending's, not the test's first. -/
theorem seeds_bent_tree :
    sendRound (declOf QK ++ (H2K.JointK.keyGu PF).rounds) 2 ≠
      some (8 + seedRound piKUFull.nums.stages 0) := by
  decide +kernel

/-- Control: the test with its first round dropped. -/
theorem seeds_bent_rounds :
    sendRound (declOf QK ++ (H2K.JointK.keyGu PF).rounds.drop 1) 3 ≠
      some (8 + seedRound piKUFull.nums.stages 0) := by
  decide +kernel

/-- Control: neither sending alone sends the three. -/
theorem counts_alone : treesU QK ≠ 3 ∧ treesOf5 QK ≠ 3 := by
  decide +kernel

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **At the description's own rounds.** -/
theorem send_key (e : parKey Xs PF = QK) {τ : ℕ} (hτ : τ < 4) :
    sendRound (decl₂ (descriptionFromSource Xs Nr PF)) (3 + τ) = some (8 + seedRound piKUFull.nums.stages τ) := by
  have hr := roots_closed
  rw [decl_front9, e, sendRound_append _ _ _ (by omega)]
  exact seeds_closed τ hτ

/-- **At threadKey's field fixed, with no slack.** -/
theorem fixed_key (e : parKey Xs PF = QK) {τ : ℕ} (hτ : τ < 4) :
    (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).fixed (.own (3 + τ)) =
      8 + seedRound piKUFull.nums.stages τ := by
  show sentIn (decl₂ (descriptionFromSource Xs Nr PF)) (3 + τ) = _
  unfold sentIn
  rw [send_key Xs Nr e hτ]
  rfl

/-- **Three trees stand in front of member 9, at threadKey's own bs**: chain_counts. -/
theorem trees_key (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF)) :
    treesTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 9 = 3 :=
  (AtPublicFiles.KeyTblTrial.chain_counts Xs Nr K ℓ Nm Mg₀ tb rest Kp Vd w e B).1

/-- **Eight rounds stand in front of member 9, at threadKey's own bs.** -/
theorem rounds_key (e : parKey Xs PF = QK) (B : Eight (parKey Xs PF)) :
    roundsTo (threadKey Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w).bs 9 = 8 := by
  have hO := AtPublicFiles.KeySharedQuiet.over_key Xs Nr PF K ℓ Nm Mg₀ tb rest Kp Vd w
  have hp : (H2K.JointK.keySharedPre Xs.chains PF).length = 9 := by
    unfold H2K.JointK.keySharedPre
    rw [List.length_cons, List.length_map, AtPublicFiles.AtFiles.Full.blocksOr_eight B]
    try rfl
  unfold roundsTo declsTo
  rw [hO.bs]
  show (((flat₂ Xs.chains PF).take 9).flatMap (·.rounds)).length = 8
  rw [flat₂_cut, List.take_left' hp, pre_rounds, e]
  exact rounds_closed

end

end AtPublicFiles.KeyFixedLines

#print axioms AtPublicFiles.KeyFixedLines.pre_rounds
#print axioms AtPublicFiles.KeyFixedLines.decl_front9
#print axioms AtPublicFiles.KeyFixedLines.seeds_closed
#print axioms AtPublicFiles.KeyFixedLines.roots_closed
#print axioms AtPublicFiles.KeyFixedLines.rounds_closed
#print axioms AtPublicFiles.KeyFixedLines.seeds_no_slack
#print axioms AtPublicFiles.KeyFixedLines.seeds_bent_tree
#print axioms AtPublicFiles.KeyFixedLines.seeds_bent_rounds
#print axioms AtPublicFiles.KeyFixedLines.counts_alone
#print axioms AtPublicFiles.KeyFixedLines.send_key
#print axioms AtPublicFiles.KeyFixedLines.fixed_key
#print axioms AtPublicFiles.KeyFixedLines.trees_key
#print axioms AtPublicFiles.KeyFixedLines.rounds_key
