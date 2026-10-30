-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadsLiveAlongFold.lean: the proofs of the three statements of
Johnson/P1K8R/ReadsLiveAlongFoldStatement.lean, to the letter. Lemmas; none of the library's goals.

A FURTHER TEXT. `member_342_of` IS THE PROOF OF `block_342` (HeadListAtBatch.lean of this folder),
SOME TWELVE LINES, WRITTEN A FURTHER TIME WITH THE RELATION AS A LETTER: that lemma is stated at one
sentence on the state behind. THE SIX LINES THAT SPLIT THE FIRST MEMBER OFF THE FOLD go as in
`own_behind_calls` (OwnBetween.lean of this folder).

How. `kept_by_reads`: the block is the commitment, then the quiet step (`andThen_yes`,
Johnson/IMR/FoldTools.lean; `quiet_arms`, Johnson/Desc/First/K8/LawCondK1.lean). The commitment
keeps what is held as heard (`kept_commit`, Johnson/Desc/Reads/LiesBehind.lean); the quiet step lays
the tables and the smallness test's structure and nothing else (`head_ok`,
Johnson/Desc/K8/ReadsQuietLaws.lean). `readsLive_along_fold`: the first member is split off the fold
(`foldBlocks_cons`, Johnson/Desc/K15/FoldInv.lean); its yes keeps x and lays the closed list of some
x' that the state behind holds (`reads_lays`, HeadListAtBatch.lean): so x' is x. The four members
behind leave the reading `wide` along the fold (`wide_stays`, WideToRun.lean). `tiesLaid_at_batch`
(TiesAtBatch.lean) at the state reached; `readsLive_of_laid` (ReadsLiveAtBatch.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.ReadsLiveAlongFoldStatement
import Johnson.P1K8R.ReadsLiveAtBatch
import Johnson.P1K8R.HeadListAtBatch
import Johnson.P1K8R.WideToRun
import Johnson.Desc.K15.FoldInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription KindName foldBlocks foldBlocks_cons)
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open VerifiableInference.Desc.First.K8 (wide wideOf)
open VerifiableInference.Desc.First.K8.Honest (tiesLaid readsLive)
open VerifiableInference.Desc.First.MergeLaw (alone_decides retype_decides flat_at)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Reads.AtSeat (Kept kept_trans kept_commit)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide step_less)

/-- **The reads' block keeps what the head's link holds as heard.** -/
theorem kept_by_reads : KeptByReads := by
  intro Z G l X pr reads hX h2 s rs gs s' h
  obtain ⟨m, h1, H⟩ := _root_.Meaning.K2.andThen_yes h
  have k1 : Kept s m := kept_commit _ _ _ _ h1
  refine kept_trans k1 ?_
  rcases VerifiableInference.Desc.First.K8.Ready.quiet_arms G l X _ _ _ _ H with
    ⟨h1', -⟩ | ⟨-, Y, hY, hL | hH⟩
  · omega
  · obtain rfl : X = Y := Option.some.inj (hX.symm.trans hY)
    have := hL.1
    omega
  · obtain ⟨a, cov, x, t, tl', ha, -, -, -, -, -, e⟩ :=
      VerifiableInference.Desc.K8.ReadsQuiet.head_ok hH.2
    intro o ho
    obtain rfl : a = o := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans ho)
    exact ⟨{ a with t := some t, tl := tl' }, by rw [e], rfl, rfl⟩

/-- **Number 342 of the flat list is such a block.** -/
theorem member_342_of : Member342Of := by
  intro P pp lay F Z Bs base c A B hS hR O R hD
  have hk : (kindsBeforeBatching .head (24 == 0))[4]? = some KindName.K1 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, eL, e, eX, hn, harm⟩ :=
    IM.k1_later O 24 .head (IM.subs_head hS hR O.pub O.blank) 4 hk (by decide)
  obtain ⟨-, Y, eY, h2, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain rfl : Xl = Y := Option.some.inj (eX.symm.trans eY)
  have hp := IM.numbers_pieces hn
  refine ⟨b, flat_at hS hR O eL e rfl, ?_⟩
  rcases harm with ⟨-, la⟩ | ⟨h5, -⟩
  · exact alone_decides (by intro k; cases k) la (retype_decides (hD Xl pr reads eX h2))
  · omega

/-- **Along the caller's own fold the test says yes.** -/
theorem readsLive_along_fold : ReadsLiveAlongFold := by
  intro P pp lay F Z Bs base c A B hS hR O sk s' o x r₂ r₃ c₂ c₃ z hsk hx hfold h347 hF
  -- the first member
  obtain ⟨b, hb, D⟩ := member_342_of P pp lay F Z Bs base c A B hS hR O
    (fun s t => Kept s t ∧ ∃ x' t', HeadListLaid Bs.G₀.W t x' t')
    (fun Xl pr reads eX h2 s rs gs t hd =>
      ⟨kept_by_reads Z Bs.G₀ 24 Xl pr reads eX h2 s rs gs t hd,
        reads_lays Z Bs.G₀ 24 Xl pr reads eX h2 s rs gs t hd⟩)
  have hb' : (c.blocksInOrder.take 347)[342]? = some b := by
    rw [List.getElem?_take, if_pos (by decide)]
    exact hb
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 hb'
  rw [List.drop_eq_getElem_cons hi, e] at hfold
  obtain ⟨sm, k, hlen, st, hrest⟩ := foldBlocks_cons 0 b _ sk r₂ c₂ _ hfold
  obtain ⟨rs, gs, hd⟩ := stepYes_decide (⟨_, _, hlen, step_less st⟩ : StepYes 0 b sk sm)
  obtain ⟨kp, x', t, ⟨a, ha, hax⟩, ⟨cov, ec⟩, tl, etl, -, c2, c3, c4⟩ := D sk rs gs sm hd
  obtain ⟨o', ho', ex, -⟩ := kp o hsk
  obtain rfl : a = o' := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans ho')
  obtain rfl : x' = x := Option.some.inj (hax.symm.trans (ex.trans hx))
  -- the four behind
  have hrest' : foldBlocks 0 ((c.blocksInOrder.drop (14 * 24 + 5 + 2)).take (3 + 1)) sm
      (r₂.drop b.rounds.length) (c₂.drop k) = .ok (s', r₃, c₃) := by
    have el : (c.blocksInOrder.take 347).drop (342 + 1) = (c.blocksInOrder.drop (14 * 24 + 5 + 2)).take (3 + 1) := by
      rw [List.drop_take]
    rw [← el]
    exact hrest
  have ew0 : wide s' = wide sm :=
    P1K8S.wide_stays hS hR O (24, 5, 3) (by decide) 0 sm _ _ _ hrest'
  have ew : wide s' = some (wideOf tl) := by
    rw [ew0]
    show sm.tl?.map wideOf = some (wideOf tl)
    rw [etl]
    rfl
  obtain ⟨tl', etl', ee⟩ := Option.map_eq_some_iff.1 ew
  have q1 : tl'.funs = tl.funs := congrArg (fun y => y.2.2.2) ee
  have q3 : tl'.mats = tl.mats := congrArg (fun y => y.1.2.2.2.2.2.2) ee
  have q4 : tl'.NM = tl.NM := congrArg (fun y => y.1.2.2.2.2.1) ee
  -- the test
  obtain ⟨tl'', e2, hT⟩ := tiesLaid_at_batch hS hR O (l := 24) (by decide)
    (show Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * 24 + (if 24 = 24 then 11 else 9)) (z, s') from h347)
  obtain rfl : tl' = tl'' := Option.some.inj (etl'.symm.trans e2)
  have hpub : Verify.publicOf P.pol P.KL (some lay) = .ok Bs.G₀.W := by
    rw [ProofFile.Law.blankBy_W O.blank]
    exact VerifiableInference.Desc.LinkJoin.public_of_pub O.pub
  exact ⟨tl', etl', readsLive_of_laid P pp (some lay) Bs.G₀.W cov x' t tl' hS hR hpub ec
    (q1.trans c2) (q3.trans c3) (q4.trans c4) hT hF⟩

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.kept_by_reads
#print axioms P1K8.member_342_of
#print axioms P1K8.readsLive_along_fold
