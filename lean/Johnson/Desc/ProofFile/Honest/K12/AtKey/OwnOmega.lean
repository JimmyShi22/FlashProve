-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnOmega.lean: the sample rows of the own test's third member, Omega's
copy, have no written-out factor.
Steps of the verifier's: nothing is shown of any prover.

  `run_nine`       the run on shapes over the shared chain's first nine blocks returns `V9`
  `pre_plain`      a fold over those nine from the chain's first state ends at a statement without a row with a
                   written-out factor
  `sample_omega`   the shared chain's end: a message that `V9` marks as sampled is sampled, with plain rows
  `copy_plain`     behind the last chain's first block the copy of Omega has plain rows, if Omega has

By what. `plain_behind_eight`'s parts (K12/PlainAtEight.lean), `shape_reach`, `flat_smp₂`, `laid_k14Second`,
`keeps_paid₂`, `keeps_paid₃`.

Limits.
- FORM ALONE: nothing on what a row holds of.
- In scope, at the written sizes; `sample_omega` asks that the key fits.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnSamples
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnShape
import E2E.KeyKeeps
import Johnson.Desc.Third.Law.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.Ground (By)
open VerifiableInference.Desc.Ground.Sh (stPlainB plain_samples stSh orc_get orcSh rowPlainB_iff
  rowPlainB_renamed)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi Claim FirstState descriptionFromSource thirdPar)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (laid_k14Second)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.K1 (SmpStay)
open _root_.Desc.K14 (St blocksOr)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold fold_split)
open Johnson.RunOne.KeyKeeps (st₁ st₂ st₃)
open Johnson.RunOne.KeyWalk (flat_smp₂ flat_smp₃)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription flat₂ flat₂_cut Z₂At sh₂)
open AtPublicFiles.AtFiles.Full (V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 gK₂ QK PF stepS0 stepS1 stepS2 stepS3 stepS4 stepS5
  stepS6 stepS7 stepS8 later_sourced par_sourced plan2_full pre_len₂ blocksOr_eight carries₂_sourced first₂_shape)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **The run on shapes over the first nine blocks.** -/
theorem run_nine (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) :
    (AtPublicFiles.AtFiles.Z₂ PF 9 gK₂ v).run 9 V0 = .ok V9 := by
  show ((((((((gK₂ 0 V0).bind (gK₂ 1)).bind (gK₂ 2)).bind (gK₂ 3)).bind (gK₂ 4)).bind
    (gK₂ 5)).bind (gK₂ 6)).bind (gK₂ 7)).bind (gK₂ 8) = _
  rw [stepS0]
  show (((((((gK₂ 1 V1).bind (gK₂ 2)).bind (gK₂ 3)).bind (gK₂ 4)).bind (gK₂ 5)).bind
    (gK₂ 6)).bind (gK₂ 7)).bind (gK₂ 8) = _
  rw [stepS1]
  show ((((((gK₂ 2 V2).bind (gK₂ 3)).bind (gK₂ 4)).bind (gK₂ 5)).bind (gK₂ 6)).bind
    (gK₂ 7)).bind (gK₂ 8) = _
  rw [stepS2]
  show (((((gK₂ 3 V3).bind (gK₂ 4)).bind (gK₂ 5)).bind (gK₂ 6)).bind (gK₂ 7)).bind (gK₂ 8) = _
  rw [stepS3]
  show ((((gK₂ 4 V4).bind (gK₂ 5)).bind (gK₂ 6)).bind (gK₂ 7)).bind (gK₂ 8) = _
  rw [stepS4]
  show (((gK₂ 5 V5).bind (gK₂ 6)).bind (gK₂ 7)).bind (gK₂ 8) = _
  rw [stepS5]
  show ((gK₂ 6 V6).bind (gK₂ 7)).bind (gK₂ 8) = _
  rw [stepS6]
  show (gK₂ 7 V7).bind (gK₂ 8) = _
  rw [stepS7]
  exact stepS8

/-- **A fold over the nine from the chain's first state ends at a statement with no written-out factor.** -/
theorem pre_plain (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) (key : TableKey)
    {rs r : List Fmt.RoundView} {cols c : List OpenedColumn} {t : St}
    (h : foldBlocks 0 (H2K.JointK.keySharedPre Xs.chains Pl) (_root_.Desc.K14.first QK.codes key) rs cols =
      .ok (t, r, c)) : stPlainB t.st = true := by
  obtain ⟨layO, hQ⟩ := AtPublicFiles.AtFiles.Full.plan2_full
  obtain ⟨B⟩ := hQ.eight
  have hP : VerifiableInference.Desc.Key.sharedPar Xs.chains
      (VerifiableInference.Desc.Key.beforeSharedPoint Pl) = QK := par_sourced hs scope
  have hk : ∀ b ∈ H2K.JointK.keySharedPre Xs.chains Pl,
      Decides (ProofFile.Honest.K12.Light.PlainStay) b := by
    intro b hb s rs' gs s' e x
    unfold H2K.JointK.keySharedPre at hb
    rw [hP, blocksOr_eight B] at hb
    rcases List.mem_cons.1 hb with rfl | hb
    · have e' : s' = s := (Except.ok.inj (show Except.ok s = Except.ok s' from e)).symm
      rw [e']
      exact x
    · obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hb
      exact ProofFile.Honest.K12.Light.blocks_plain QK _ B.made b₀ hb₀ s rs' gs s' e x
  exact VerifiableInference.Desc.Keeps.foldBlocks_keeps ProofFile.Honest.K12.Light.PlainStay
    (fun _ x => x) (fun _ _ _ x y z => y (x z)) 0 _ hk _ rs cols _ h
    (VerifiableInference.Desc.Ground.Sh.start_plain QK.codes)

/-- **The shared chain's end: a message that `V9` marks as sampled is sampled, with plain rows.** -/
theorem sample_omega (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (x : (keyFileDescription Xs Nr Pl).XiPub) (hk : keyFits x.key QK.par.S.fold.index = true) {e₂ : St}
    {rs r : List Fmt.RoundView} {cols c : List OpenedColumn}
    (h : foldBlocks 0 (keyFileDescription Xs Nr Pl).shared.blocksInOrder ((keyFileDescription Xs Nr Pl).start₂ x) rs cols =
      .ok (e₂, r, c))
    (om : ℕ) (hom : ((V9.1.core.st.oracles[om]?).any (·.sampled)) = true) :
    ∃ y : OnBytes.Oracle, e₂.st.oracles[om]? = some y ∧ y.sampled = true ∧
      ∀ r ∈ y.sampleRows.toList, PlainRow r := by
  obtain ⟨layO, hQ⟩ := AtPublicFiles.AtFiles.Full.plan2_full
  obtain ⟨B⟩ := hQ.eight
  have h9 := pre_len₂ Xs.chains Pl (par_sourced hs scope) B
  have hflat : (keyFileDescription Xs Nr Pl).shared.blocksInOrder = H2K.JointK.keySharedPre Xs.chains Pl ++
      (flat₂ Xs.chains Pl).drop 9 := by
    show flat₂ Xs.chains Pl = _
    rw [flat₂_cut]
    simp [h9]
  rw [hflat] at h
  obtain ⟨t, r₁, c₁, h₁, h₂⟩ := fold_split 0 _ _ _ rs cols _ h
  have ht9 : (flat₂ Xs.chains Pl).take 9 = H2K.JointK.keySharedPre Xs.chains Pl := by
    rw [flat₂_cut, ← h9]
    simp
  have hlen := (AtPublicFiles.KeyThread.lengths scope hs.named).2.1
  have hr : Reach 0 (flat₂ Xs.chains Pl) (fun _ : Unit => (keyFileDescription Xs Nr Pl).start₂ x) 9 ((), t) :=
    reach_of_fold 9 (Nat.le_trans (by decide : 9 ≤ 12) (le_of_eq hlen.symm)) t rs r₁ cols c₁ (by
      have h₁' := h₁
      rw [← ht9] at h₁'
      exact h₁')
  obtain rfl := later_sourced hs scope
  have e := ProofFile.Honest.shape_reach (Z₂At Xs.chains PF gK₂ fun _ _ _ _ => true)
    (carries₂_sourced hs scope 0 _) hr V9 (by
      show (Z₂At Xs.chains PF gK₂ fun _ _ _ _ => true).run 9
        (sh₂ ((keyFileDescription Xs Nr PF).start₂ x)) = _
      rw [first₂_shape hs scope x hk]
      show (AtPublicFiles.AtFiles.Z₂ PF (H2K.JointK.keySharedPre Xs.chains PF).length gK₂ _).run 9 V0 = _
      rw [h9]
      exact run_nine _)
  have ev : V9 = sh₂ t := e
  have hplain : stPlainB t.st = true := by
    have e₀ : (keyFileDescription Xs Nr PF).start₂ x = _root_.Desc.K14.first QK.codes x.key := by
      show _root_.Desc.K14.first Xs.chains.made.sized.key.codes x.key = _
      rw [AtPublicFiles.AtFiles.sized_sourced hs scope]
      rfl
    have h₁' : foldBlocks 0 (H2K.JointK.keySharedPre Xs.chains PF)
        (_root_.Desc.K14.first QK.codes x.key) rs cols = .ok (t, r₁, c₁) := by
      rw [← e₀]
      exact h₁
    exact pre_plain hs scope x.key h₁'
  have hsm : ((stSh t.st).oracles[om]?).any (·.sampled) = true := by
    have e₁ : V9.1.core.st = stSh t.st := by
      rw [ev]
      rfl
    rw [← e₁]
    exact hom
  rw [orc_get] at hsm
  cases hy : t.st.oracles[om]? with
  | none =>
    rw [hy] at hsm
    cases hsm
  | some y =>
    rw [hy] at hsm
    have hys : y.sampled = true := hsm
    have hstay : SmpStay t.st e₂.st :=
      VerifiableInference.Desc.Keeps.foldBlocks_keeps (By SmpStay st₂) (fun _ => SmpStay.refl _)
        (fun _ _ _ p q => p.trans q) 0 _
        (fun b hb => flat_smp₂ b (by
          show b ∈ flat₂ Xs.chains PF
          exact List.mem_of_mem_drop hb)) t _ _ _ h₂
    obtain ⟨z, hz, -, hzs, hzr⟩ := hstay.2 _ y hy hys
    exact ⟨z, hz, hzs, fun q hq => plain_samples hplain hy q (by rw [← hzr]; exact hq)⟩

/-- **Behind the last chain's first block the copy of Omega has plain rows, if Omega has.** -/
theorem copy_plain {S : Params.LinShape} {s s' : S₃} {b : VerifiableInference.Desc.Third.Border}
    {y : OnBytes.Oracle} {G : OnBytes.Group} {dot : OnBytes.Row}
    (L : VerifiableInference.Desc.Third.Laid S s s' b y G dot)
    (hy : ∀ r ∈ y.sampleRows.toList, PlainRow r) {x : OnBytes.Oracle}
    (hx : s'.st.oracles[s.st.oracles.size]? = some x) :
    ∀ r ∈ x.sampleRows.toList, PlainRow r := by
  intro r hr
  have ex := Option.some.inj (hx.symm.trans L.copy)
  rw [ex] at hr
  have hr' : r ∈ (y.sampleRows.map (·.renamed s.st.oracles.size)).toList := hr
  rw [Array.toList_map] at hr'
  obtain ⟨r₀, h₀, rfl⟩ := List.mem_map.1 hr'
  exact rowPlainB_iff.1 ((rowPlainB_renamed _ _).trans (rowPlainB_iff.2 (hy r₀ h₀)))

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.run_nine
#print axioms ProofFile.Honest.K12.AtKey.pre_plain
#print axioms ProofFile.Honest.K12.AtKey.sample_omega
#print axioms ProofFile.Honest.K12.AtKey.copy_plain
