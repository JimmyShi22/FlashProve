-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/PlanRowsAtHead.lean: the proofs of the six statements of
Johnson/P1K8R/PlanRowsAtHeadStatement.lean, to the letter, and two helpers. Lemmas; none of the
library's goals.

How. (1) UNDER THE HEAD THE PLANNER's FIRST PLAN IS A WRITTEN VALUE: `AtMg.pins`
(Johnson/P5T/FenceAtMg.lean) hands the entry test `madeRow`, whose first part `madeIs`
(Johnson/Desc/Ok/PlanWritten/MadeTest.lean) rides the first plan along the written one; `ride_eq`
(Johnson/Desc/Ok/NumberPrices/ByRuns.lean): so they are equal. The sizes: `AtMg.sized_at_head`
(Johnson/P2LawR/IndexAtHead.lean). (2) THAT PLAN IS A LIST IN LETTERS: the description's own copy of
the planner (`ProofFile.Plain.planned`; `ProofFile.Law.madeOf_planned`) is opened by `H2K.Made.plain_parts`
(Johnson/Loose/H2K12/PlainParts.lean); then `subRuns_subproofsWith`
(OnBytes/Model/LinkRoundsList.lean) and `configure_proof_is` (OnBytes/Plan/PlanListsProof.lean), as
`configure_proof_model` goes. (3) `chain_sigmaBat`: the chain is its records' rounds
(`firstChain_frames`, OnBytes/Plan/ReqFrames.lean); a record's rounds by `TwLaw.rounds_link`
(OnBytes/Tie/Pv/Lookup/Peel/FoPlanAt.lean); `sigmaBat_mid` and `sigmaBat_family`
(Johnson/P1K8R/SigmaBat.lean). (4) `frames_written`: `TwLaw.framesFrom_some`, `TwLaw.framesOf_at`
(FoPlanAtFrames.lean) under the closed fact. (5) `linkList_last`: `Fo.list_layer2`, `Fo.list_att2`,
`Fo.list_head2` (OnBytes/Tie/Pv/Lookup/Ends/FoPlaceLists.lean). (6) TWO CLOSED FACTS AND A LINE THAT
BITES, BY LEAN's KERNEL. THE 25 NUMBERS are `full_rows`' and `k9Rows_closed`'s. (7) A sublist of
equal length is the list.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.P1K8R.PlanRowsAtHeadStatement
import Johnson.P1K8R.SigmaBat
import Johnson.P5T.FenceAtMg
import Johnson.P2LawR.IndexAtHead
import Johnson.Loose.H2K12.PlainParts
import Johnson.Desc.Ok.NumberPrices.ByRuns
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Goal.Meaning.HidOwner
import Johnson.Goal.Meaning.ScopeCore
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaceLists
import OnBytes.Model.LinkRoundsList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Params (RoundSpec Setting Scope ProofSized Subproofs batSigmaFrom batRound foldList
  forestList pscList settingOf)
open OnBytes.Plan (framesOf firstChainList FrameN)
open OnBytes.Model.Verify (linkList)
open VerifiableInference.PlanWritten (proofSizedFull proofLit)

/-- **The general law on a first chain's list.** -/
theorem chain_sigmaBat : ChainSigmaBat := by
  intro z sub L after s c r k hfr hL
  have hk : k ≤ (framesOf z sub).length := by
    by_contra hlt
    obtain ⟨n, v, hn, -⟩ := hfr (framesOf z sub).length (by omega)
    rw [List.getElem?_eq_none (Nat.le_refl _)] at hn
    cases hn
  refine ⟨((framesOf z sub).take k).map fun n => r n.l, ?_, ?_, ?_⟩
  · rw [List.length_map, List.length_take]
    omega
  · intro i hi
    obtain ⟨n, v, hn, -, -, hl⟩ := hfr i hi
    rw [List.getElem?_map, List.getElem?_take, if_pos hi, hn]
    show some (r n.l) = some (r i)
    rw [hl]
  · have e : (framesOf z sub).flatMap (FrameN.rounds z L) =
        ((framesOf z sub).take k).flatMap (FrameN.rounds z L) ++
          ((framesOf z sub).drop k).flatMap (FrameN.rounds z L) := by
      rw [← List.flatMap_append, List.take_append_drop]
    rw [OnBytes.Plan.firstChain_frames, e, List.append_assoc, List.map_append, List.map_flatMap]
    refine sigmaBat_family FrameN (fun n => (n.rounds z L).map fun y => (y.round s c).entry)
      (fun n => r n.l) ((framesOf z sub).take k) (fun n hn => ?_) _
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hn
    rw [List.getElem?_take] at hi
    split at hi
    · rename_i hik
      obtain ⟨n', v, hn', hv, hm, hl⟩ := hfr i hik
      obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hi)
      obtain ⟨pre, hp⟩ := hL n'.l (by rw [hl]; exact hik)
      have er : n'.rounds z L =
          (TwLaw.headN z n' ++ (L n'.l 0 ++ (TwLaw.momentSend z n' 1 ++ (L n'.l 1 ++
            (TwLaw.momentSend z n' 2 ++ pre))))) ++
            (batSigmaFrom s (r n'.l) 0 :: batRound z.set [n'.closed] n'.batRows ::
              foldList z.set n'.closed 0) := by
        rw [TwLaw.rounds_link z L n' v hv, hm]
        show TwLaw.headN z n' ++ (L n'.l 0 ++ ((TwLaw.momentSend z n' 1 ++ (L n'.l 1 ++
          (TwLaw.momentSend z n' 2 ++ (L n'.l 2 ++ [])))) ++
            (batRound z.set [n'.closed] n'.batRows :: foldList z.set n'.closed 0))) = _
        rw [hp]
        simp only [List.append_assoc, List.append_nil, List.cons_append, List.nil_append]
      show [r n'.l].Sublist (sigmaBat ((n'.rounds z L).map fun y => (y.round s c).entry))
      rw [er, List.map_append, List.map_cons, List.map_cons]
      exact sigmaBat_mid _ _ ((batSigmaFrom s (r n'.l) 0).round s c).entry
        ((batRound z.set [n'.closed] n'.batRows).round s c).entry rfl rfl
    · cases hi

/-- **By the kernel: the written sizes have 25 links, each with just two later moments.** -/
theorem frames_closed : FramesWritten := by
  show framesB = true
  decide +kernel

/-- **By the kernel: the marker on the written first plan.** -/
theorem sigmaBat_written : SigmaBatWritten := by
  show sigmaBat (proofLit.plan.rounds.map (·.entry)) = (List.range 25).map rowsAtLink
  decide +kernel

/-- **By the kernel: that sentence can fail.** -/
theorem sigmaBat_bites : SigmaBatBites := by
  show decide _ = false
  decide +kernel

/-- The first 25 records at the written sizes. -/
theorem frames_written (sub : Subproofs) : ∀ i, i < 25 → ∃ n v,
    (framesOf proofSizedFull sub)[i]? = some n ∧ n.link = some v ∧ n.moments = 2 ∧ n.l = i := by
  intro i hi
  have hB := frames_closed
  unfold FramesWritten framesB at hB
  rw [Bool.and_eq_true_iff] at hB
  obtain ⟨hg, hall⟩ := hB
  have hat : ∀ j, j < 25 → (proofSizedFull.request.link[j]?).isSome = true ∧
      TwLaw.laterOf (proofSizedFull.request.link[j]?) = 2 := fun j hj => by
    have q := List.all_eq_true.1 hall j (List.mem_range.2 hj)
    rw [Bool.and_eq_true_iff] at q
    exact ⟨q.1, of_decide_eq_true q.2⟩
  have hs := TwLaw.framesFrom_some proofSizedFull (reqGroups proofSizedFull.request).toList 0
    proofSizedFull.request.link sub.openRows proofSizedFull.link.group i
    (Nat.lt_of_lt_of_le hi (of_decide_eq_true hg)) fun j hj => (hat j (by omega)).1
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨a1, a2, a3⟩ := TwLaw.framesOf_at proofSizedFull sub i n hn
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hat i hi).1
  exact ⟨n, v, hn, a2.trans hv, by rw [a3, a2]; exact (hat i hi).2, a1⟩

/-- The last round of moment 2 of each of the model's 25 sub-proofs. -/
theorem linkList_last (s : Setting) (c : Scope) (X : Verify.Public) (h4 : X.p4 = true)
    (hN : X.NGr = 12) (hG : ∀ g, g < 12 → ∃ hp, X.G[g]? = some hp)
    (hA : ∀ g, g < 12 → ∃ a, X.A[g]? = some a) :
    ∀ i, i < 25 → ∃ pre, linkList s c X i 2 = pre ++ [batSigmaFrom s (planRows X i) 0] := by
  intro i hi
  have e2 : (if X.p4 then 2 else 1) = 2 := by rw [h4]; rfl
  obtain rfl | ⟨g, hg, rfl | rfl⟩ : i = 24 ∨ ∃ g, g < 12 ∧ (i = 2 * g ∨ i = 2 * g + 1) := by
    by_cases h24 : i = 24
    · exact Or.inl h24
    · exact Or.inr ⟨i / 2, by omega, by omega⟩
  · have q := Fo.list_head2 s c X
    rw [e2, hN] at q
    refine ⟨forestList s (forestSize X.H.tl.f9) ++ (batSigmaFrom s 1 0 ::
      pscList s { degree := List.replicate (X.H.own X.hS).lkW 3, degreeY := 1, values := 1 }), ?_⟩
    rw [List.append_assoc]
    exact q
  · obtain ⟨hp, hgp⟩ := hG g hg
    have q := Fo.list_layer2 s c X g hp (by rw [hN]; exact hg) hgp
    rw [e2] at q
    refine ⟨forestList s (forestSize hp.tl.f9), q.trans ?_⟩
    unfold planRows
    rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega, hgp]
    rfl
  · obtain ⟨a, ha⟩ := hA g hg
    have q := Fo.list_att2 s c X h4 g a ha
    refine ⟨forestList s (forestSize a.seam.tl.f9), q.trans ?_⟩
    unfold planRows
    rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, ha]
    rfl

/-- **Under the head each plan's rows are the written number.** -/
theorem planRows_at_head : PlanRowsAtHead := by
  intro o Z D r Zp Np cF h l hl
  obtain ⟨k4, kN, -, hAll⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads h.pubOne
  have hp : ProofFile.Plain.planned o Z.pol Z.KL (some Z.lay) = .ok Zp.p :=
    ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts Z.pol Z.lay Z.KL = .ok Zp from
              h.laid.pub))
  obtain ⟨links, shapes, rest, declared, file, rl, lay, -, -, -, -, -, hc, -, -, -, hsub⟩ :=
    H2K.Made.plain_parts hp
  have S : OnBytes.Plan.SubRuns (settingOf Zp.p.X.P.frame) shapes.sub
      (linkList (settingOf Zp.p.X.P.frame) .request Zp.p.X) [] := by
    rw [hsub]
    exact OnBytes.Model.Verify.subRuns_subproofsWith _ Zp.p.X rl
  obtain ⟨-, -, F, S2, S3, Ls, hm, -, -, hP, -, -⟩ := OnBytes.Params.configure_proof_is hc S
  have hy := h.pins.1
  unfold VerifiableInference.PlanWritten.madeRow at hy
  simp only [Bool.and_eq_true] at hy
  obtain ⟨⟨⟨h1, -⟩, -⟩, -⟩ := hy
  unfold VerifiableInference.PlanWritten.madeIs at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := h1.2
  rw [hm] at h2
  have hF : F = proofLit.plan := VerifiableInference.Number.ByRuns.ride_eq h2
  have E : proofLit.plan.rounds.map (·.entry) =
      (firstChainList proofSizedFull shapes.sub
        (linkList (settingOf Zp.p.X.P.frame) .request Zp.p.X) []).map
        fun y => (y.round (settingOf Zp.p.X.P.frame) .request).entry := by
    rw [← hF, hP.rounds, List.map_map, h.sized_at_head]
    rfl
  obtain ⟨W, hWl, hWi, hWs⟩ := chain_sigmaBat proofSizedFull shapes.sub
    (linkList (settingOf Zp.p.X.P.frame) .request Zp.p.X) [] (settingOf Zp.p.X.P.frame) .request
    (planRows Zp.p.X) 25 (frames_written shapes.sub)
    (linkList_last _ _ Zp.p.X k4 kN (fun g hg => _root_.Meaning.planG_there h.pubOne C hg)
      fun g hg => (hAll g hg).imp fun _ q => q.1)
  rw [← E, sigmaBat_written] at hWs
  have eW := hWs.eq_of_length (by rw [hWl, List.length_map, List.length_range])
  have q := hWi l hl
  rw [eW, List.getElem?_map, List.getElem?_range hl] at q
  exact (Option.some.inj q).symm

/-- **The same, plan by plan.** -/
theorem planRows_by_plan : PlanRowsByPlan := by
  intro o Z D r Zp Np cF h
  have q := planRows_at_head o Z D r Zp Np cF h
  refine ⟨fun g hg hp hgp => ?_, fun g hg a ha => ?_, q 24 (by omega)⟩
  · rw [← q (2 * g) (by omega)]
    unfold planRows
    rw [if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega, hgp]
    rfl
  · rw [← q (2 * g + 1) (by omega)]
    unfold planRows
    rw [if_neg (by omega), if_neg (by omega), show (2 * g + 1) / 2 = g by omega, ha]
    rfl

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.chain_sigmaBat
#print axioms P1K8.frames_closed
#print axioms P1K8.sigmaBat_written
#print axioms P1K8.sigmaBat_bites
#print axioms P1K8.frames_written
#print axioms P1K8.linkList_last
#print axioms P1K8.planRows_at_head
#print axioms P1K8.planRows_by_plan
