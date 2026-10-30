-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Shape/Step.lean: the proofs of `GuardIsReady`, `MergeCarries` and `MergeReturns`
(Johnson/Desc/K11/Shape/StepStatement.lean), to the letter. Lemmas; none of the library's goals.

How. ONE LAW ON THE DECISION IS SPENT: `headMergeDecideReturns`
(Johnson/Desc/K11/Returns/Decide.lean): at a state that is ready and rounds that pass the step's own
test the decision returns, and the state behind is written out, with what the ledger and what the
merge leaves are as far as they hold no field element. All else is shapes: the shape of a state that
stands in the head's open link, written out (`chainSh_head`); each test on sizes and marks read off
the shape (`claimFits_sh`, `sized_sh`, `filled_sh`); the shapes of the ledger behind
(`ledSh_behind`) and of what the merge leaves (`mergeSh_behind`, `recSh_rowPart`).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Shape.StepStatement
import Johnson.Desc.K11.Returns.Decide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.ShapeStep
open OnBytes (E)
open OnBytes.Model (Fork WsLay WsGrp WsFac WsRowFac WsClaim WsForkOut wsRowPart)
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (roundsFit noDigest)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind headMergeDecide claimFits facFits)
open Johnson.Desc.First.ForkMerge.Returns (mergeEndSlot LedgerBehind MergeBehind
  headMergeDecideReturns)

/-! ## 1 Sizes and marks, read off shapes -/

/-- The kind's test on a claim's sizes reads the claim's shape alone. -/
theorem claimFits_sh (lay : WsLay) (c : WsClaim) :
    claimFitsSh lay (wsClaimSh c) = claimFits lay c := by
  simp only [claimFitsSh, claimFits, wsClaimSh]
  cases lay.U[c.ui]? with
  | none => rfl
  | some u =>
    simp only [List.length_map, List.zip_map_left, List.all_map]
    rfl

/-- The ledger's three arrays have their size: read off its shape. -/
theorem sized_sh (F : Fork) : sizedB (ledSh F) = true ↔ Sized F := by
  unfold sizedB Sized
  show (F.vp.size == F.ns && F.mf.size == F.ns && F.gotF.toList.length == F.ns) = true ↔ _
  simp only [Bool.and_eq_true, beq_iff_eq, Array.length_toList, and_assoc]

/-- A slot's mark: read off the ledger's shape. -/
theorem filled_sh (F : Fork) (j : Nat) : (ledSh F).got.getD j false = F.gotF.getD j false := by
  show F.gotF.toList.getD j false = F.gotF.getD j false
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

/-- As many are kept by a map that drops as by the test. -/
theorem filterMap_length {α : Type} (p : Nat → Bool) (f : Nat → α) : ∀ l : List Nat,
    (l.filterMap fun i => if p i then none else some (f i)).length =
      (l.filter fun i => !p i).length
  | [] => rfl
  | i :: l => by
    rw [List.filterMap_cons, List.filter_cons]
    cases h : p i with
    | true => simpa [h] using filterMap_length p f l
    | false => simpa [h] using filterMap_length p f l

/-- The sizes of the part of a factor that is left to the rows. -/
theorem onRows_sh (x : WsFac) (g : WsGrp) :
    ((x.onRows g).HV.size, (x.onRows g).pl.size, (x.onRows g).AV.size) =
      onRowsSh (x.HV.size, x.pt.size, x.AV.size) g := by
  unfold WsFac.onRows onRowsSh
  by_cases h1 : (g.cls == 'E') = true
  · rw [if_pos h1, if_pos h1]
    show (x.HV.size, (List.filterMap _ (List.range g.z)).length, 0) = _
    rw [filterMap_length (fun i => g.takenBit (g.z - 1 - i))]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : g.aTaken = true
    · rw [if_pos h2, if_pos h2]
      rfl
    · rw [if_neg h2, if_neg h2]
      rfl

/-- The shape of what is left of a claim when the columns are bound. -/
theorem recSh_rowPart (lay : WsLay) (c : WsClaim) (ka : E) :
    recSh (wsRowPart lay c ka) = rowPartSh lay (wsClaimSh c) := by
  simp only [wsRowPart, rowPartSh, wsClaimSh]
  cases lay.U[c.ui]? with
  | none => rfl
  | some u =>
    simp only [recSh, List.zip_map_left, List.map_map]
    congr 1
    refine List.map_congr_left fun y _ => ?_
    exact onRows_sh y.1 y.2

/-! ## 2 The shapes behind -/

/-- The shape of the ledger behind. -/
theorem ledSh_behind (P : HeadMergeP) (F G : Fork) (h : LedgerBehind P.lay.lk F G) :
    ledSh { G with planClaimsF := P.nLin } = ledUpd P (ledSh F) := by
  obtain ⟨hG, hv, hm⟩ := h
  have e1 : G.ns = F.ns := by rw [hG]
  have e2 : G.gotF = F.gotF.set! (mergeEndSlot P.lay.lk F) true := by rw [hG]
  have e3 : G.owed = F.owed := by rw [hG]
  have e4 : G.trees = F.trees := by rw [hG]
  have e5 : G.next = F.next + 2 * P.lay.lk + 3 := by rw [hG]
  have e6 : G.LS = F.LS := by rw [hG]
  have e7 : G.nClaim = F.nClaim := by rw [hG]
  have e8 : G.thetaDrawnF = F.thetaDrawnF := by rw [hG]
  have e9 : G.kapMapF = F.kapMapF := by rw [hG]
  have e10 : G.doorShutF = F.doorShutF := by rw [hG]
  show LedSh.mk G.ns G.vp.size G.mf.size G.gotF.toList (G.owed.toList.map (·.added)) P.nLin
      (G.trees.toList.map treeSh) G.next G.LS.size G.nClaim G.thetaDrawnF G.kapMapF.toList
      G.doorShutF =
    LedSh.mk F.ns F.vp.size F.mf.size (F.gotF.toList.set (F.next + 2 * P.lay.lk + 2) true)
      (F.owed.toList.map (·.added)) P.nLin (F.trees.toList.map treeSh)
      (F.next + 2 * P.lay.lk + 3) F.LS.size F.nClaim F.thetaDrawnF F.kapMapF.toList F.doorShutF
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, hv, hm]
  simp [mergeEndSlot]

/-- The shape of what the merge leaves. -/
theorem mergeSh_behind (P : HeadMergeP) (claim : WsClaim) (x : OnBytes.Model.Head.Heard) (F : Fork)
    (wo : WsForkOut) (h : MergeBehind P.lay claim x.sV F wo) :
    mergeSh wo = mergeShOf P (ledSh F) (wsClaimSh claim) x.tH.sEnd := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ka, h11⟩ := h
  unfold mergeSh mergeShOf pscSh affSh
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]
  simp only [List.map_cons, List.map_nil, recSh_rowPart, List.map_append, List.map_replicate]
  rfl

/-- The shape of a state that stands in the head's open link, written out. -/
theorem chainSh_head (s : S) (a : HeadOwn) (h : s.here = .head a) (ho : a.opened = true) :
    chainSh s = ChainSh.mk s.failed.isSome 3 (some (tailSh a.tl)) (some (ledSh a.F))
      ((a.t.map (·.funs)).map fun y => y.toList.map funSh) s.rowsOwed
      (VerifiableInference.Desc.Ground.Sh.coreSh ⟨s.st, s.book, s.roots⟩) s.out.reply.isSome
      s.out.indexMasks (s.out.pending.map VerifiableInference.Desc.K13.Honest.rowSh) none
      (checkSh s.check) (some (linkSh a.L)) ((a.x.map (·.g1)).map heardAll)
      (a.lookHeard.map heardAll) none (some (headSh a)) none none := by
  simp only [chainSh, S.tl?, S.fork?, S.funs?, S.link?, S.look?, S.lookHeard?, S.own?, h, ho,
    hereNo, endSh, headOf, attOf, finOf, if_true, Option.map_some]
  rfl

/-! ## 3 The three -/

/-- **The test says yes just where the state is ready.** -/
theorem guardIsReady : GuardIsReady := by
  intro P s
  constructor
  · intro hg
    have h3 : hereNo s.here = 3 := by
      have : ((chainSh s).here == 3) = true := by
        unfold mergeGuardB at hg
        simp only [Bool.and_eq_true] at hg
        exact hg.1.1.2
      exact beq_iff_eq.1 this
    cases hs : s.here with
    | head a =>
      have ho : a.opened = true := by
        rw [hs] at h3
        by_cases ho : a.opened = true
        · exact ho
        · simp [hereNo, ho] at h3
      rw [chainSh_head s a hs ho] at hg
      cases hc : a.claim with
      | none => simp [mergeGuardB, ChainSh.mk, ChainSh.led, ChainSh.head, headSh, hc] at hg
      | some claim =>
        cases hx : a.x with
        | none =>
          simp [mergeGuardB, ChainSh.mk, ChainSh.led, ChainSh.head, headSh, HeadSh.xEnd, hc, hx]
            at hg
        | some x =>
          simp only [mergeGuardB, ChainSh.mk, ChainSh.led, ChainSh.head, ChainSh.marked,
            ChainSh.here, ChainSh.rowsOwed, headSh, HeadSh.xEnd, headHeardSh_xEnd, hc, hx,
            Option.map_some, Bool.and_eq_true,
            Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq, claimFits_sh, sized_sh, filled_sh]
            at hg
          obtain ⟨⟨⟨g1, _⟩, g3⟩, ⟨⟨⟨⟨g4, g5⟩, g6⟩, g7⟩, g8⟩, g9⟩ := hg
          refine ⟨by simpa using g1, a, claim, x, hs, ho, ?_, hc, hx, g4, g5, g6, g7, ?_, g9⟩
          · unfold S.noneWaits
            exact g3
          · intro hf
            unfold Filled mergeEndSlot at hf
            have g8' : a.F.gotF.getD (a.F.next + 2 * P.lay.lk + 2) false = false := g8
            rw [hf] at g8'
            cases g8'
    | between => rw [hs] at h3; cases h3
    | lay _ => rw [hs] at h3; cases h3
    | att _ => rw [hs] at h3; cases h3
    | fin _ => rw [hs] at h3; cases h3
    | mem _ => rw [hs] at h3; cases h3
  · rintro ⟨hf, a, claim, x, hs, ho, hw, hc, hx, r6, r7, r8, r9, r10, r11⟩
    rw [chainSh_head s a hs ho]
    simp only [mergeGuardB, ChainSh.mk, ChainSh.led, ChainSh.head, ChainSh.marked, ChainSh.here,
      ChainSh.rowsOwed, headSh, HeadSh.xEnd, headHeardSh_xEnd, hc, hx, Option.map_some,
      Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, beq_iff_eq, claimFits_sh, sized_sh, filled_sh]
    refine ⟨⟨⟨by simp [hf], trivial⟩, hw⟩, ⟨⟨⟨⟨r6, r7⟩, r8⟩, r9⟩, ?_⟩, r11⟩
    cases hb : a.F.gotF.getD (a.F.next + 2 * P.lay.lk + 2) false with
    | false => exact hb
    | true => exact absurd hb r10

/-- **The decision returns.** -/
theorem mergeReturns : MergeReturns := by
  intro P rs s hr hg
  obtain ⟨_, a, claim, x, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := (guardIsReady P s).1 hg
  obtain ⟨wo, G, hd, _, _⟩ :=
    headMergeDecideReturns P s a claim x rs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 hr
  exact ⟨_, hd⟩

/-- **The update carries.** -/
theorem mergeCarries : MergeCarries := by
  intro P rs s s' hr hd hg
  obtain ⟨_, a, claim, x, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11⟩ := (guardIsReady P s).1 hg
  obtain ⟨wo, G, hd0, hL, hM⟩ :=
    headMergeDecideReturns P s a claim x rs r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 hr
  obtain rfl : _ = s' := Except.ok.inj (hd0.symm.trans hd)
  have eN : G.next = a.F.next + 2 * P.lay.lk + 3 := by rw [hL.1]
  rw [chainSh_head s a r1 r2,
    chainSh_head _ { a with
      wo := some wo, F := { G with planClaimsF := P.nLin }, Fm := a.F, slot := some G.next }
      rfl r2]
  simp only [mergeUpd, ChainSh.mk, ChainSh.led, ChainSh.head, headSh, HeadSh.xEnd,
    headHeardSh_xEnd, r4, r5, Option.map_some,
    ChainSh.setRowsOwed, ChainSh.setLed, ChainSh.setHead, ChainSh.marked, ChainSh.here, ChainSh.tl,
    ChainSh.tables, ChainSh.rowsOwed, ChainSh.core, ChainSh.reply, ChainSh.indexMasks, ChainSh.pile,
    ChainSh.atEnd, ChainSh.check, ChainSh.link, ChainSh.look, ChainSh.lookHeard, ChainSh.own,
    ChainSh.att, ChainSh.fin, if_pos r2,
    ledSh_behind P a.F G hL, mergeSh_behind P claim x a.F wo hM]
  rw [eN]
  rfl

end Johnson.Desc.First.ForkMerge.ShapeStep

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.claimFits_sh
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.sized_sh
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.filled_sh
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.filterMap_length
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.onRows_sh
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.recSh_rowPart
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.ledSh_behind
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeSh_behind
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.chainSh_head
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.guardIsReady
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeReturns
#print axioms Johnson.Desc.First.ForkMerge.ShapeStep.mergeCarries
