-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkJoinE.lean: THE JOIN, FIFTH PART: THE LINK's DECISION ACCEPTS THE EXPLICIT
HONEST PROVER's VIEW AT THE FULL SIZE (LinkYes 97, LinkYesStm.lean), FROM THREE NAMED PREMISES.
Statement and proof. The decision is one of four conditions of the verifier's accept:
LinkYesStm.lean, common limit 1.
The join: the proof of link_yes (LinkJoinF.lean), in six files: LinkJoinA to LinkJoinF.

  Inv0    the invariant (which holds no clause on what is left untested: that is had beside it, off
          left0_full) holds in front of the first stage, and the test's front and the batching
          accept, wherever the six front sub-protocols have accepted linkAll's first five rounds and
          stored columns and the claim that the batching makes is true at the first state
  Front0  that claim is true at the first state, at an instance, stored strings and polynomials that
          are Meant
  Groups  the groups that the chain's walk reads for the stages are bodyAll's
  linkYes_of   Inv0 → Front0 → Groups → LinkYes 97

By: run_viewOf_full (ChainAtFull.lean) · rs_full | fit_full | okView_full | served_full
(LinkJoinA) · front6_walks_full | flat_split (FormWalks.lean) · want6 (FormFront6Cut.lean) ·
stored_cols (LinkJoinC) · body_left (BodyCloseS.lean) at left0_full (DoorFull.lean) · walk_tail
(LinkJoinD) · walks_append (ChainYes.lean) · cuts_full (FormCuts.lean) · planWord_full (AtD.lean) ·
okKeys_written (KeysHonest.lean).
Not shown here. The three premises: so LinkYes 97 itself is not shown here. Nothing on soundness. No
distribution is put on the prover's free parameters or on the challenges. Nothing on what any value
that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.LinkJoinA
import Johnson.Prover.Link.LinkJoinC
import Johnson.Prover.Link.LinkJoinD
import Johnson.Prover.Link.BodyCloseS
import Johnson.Prover.Link.FormWalks
import Johnson.Prover.Link.FormCuts
import Johnson.Prover.Link.DoorSeam
import Johnson.Prover.Link.KeysHonest
import OnBytes.Slice.FullRecBlkFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Plain.One (readG colsFor)
open _root_.Desc.K15 (St frP p12Of t12Of linkDescriptionAt linkDeclaredRounds linkRoundsMatchPlan frontBlock blocksOrV)
open H2K.JointK (laidOf)
open OnBytes.Flat (dsFull RecFull)
open _root_.Run.PQ (SgX)
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (drawnSL uL)
open _root_.Iop (twoExternalStrings Rho)
open Full (pF curF nxtF)

/-- The invariant in front of the first stage. -/
def Inv0 : Prop :=
  ∀ (X : LIn frS) (C : LCoins) (ρ : Rho (uL (ckP .two) dsFull)), X.keys.1.item = 0 →
    X.keys.2.item = 1 → ∀ (d' : St) (G' : Group),
    foldBlocks 0 (frontBlock frP :: blocksOrV frP) (_root_.Desc.K15.first frP.codes X.keys)
      (lFront frS 97 X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (lStoredCols frP frS X (drawsOf (drawnSL (ckP .two) dsFull ρ))) = .ok (d', [], []) →
    LinkSeats frP.par d' G' → Means.InOrder d'.st →
    G'.rows.size = 2 * frP.S.table.answers + (frP.S.columnsFirst + frP.S.columnsFurther) + 1 →
    (∀ row, Bat.combine (begun d'.st d'.loc.g G') d'.loc.g
        ⟨Means.layoutOf d'.st G', runRows d'.st G'⟩
        (drawnOf (noDigest ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩)) = some row →
      (Slf.idf (E := GE) (J := (frS.sg 97).cIn.J)).Holds (stmG (frS.sg 97) row)
        (μOf (frS.sg 97) (lPS frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ))))) →
    ∃ row,
      (guardedProximityTestParts.front pF).decide (t12Of d') [] [] = .ok (t12Of d') ∧
      (guardedProximityTestParts.bat pF (((laidOf pF).take 1).map (·.1))).decide (t12Of d')
        [noDigest ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩] [] =
        .ok (batT (t12Of d') G' row) ∧
      (guardedProximityTestParts.group (batT (t12Of d') G' row)).any (firstFits curF) = true ∧
      lT frP frS 97 X C (drawsOf (drawnSL (ckP .two) dsFull ρ)) = batT (t12Of d') G' row ∧
      BodyInv pF C.body (PlanAll pF) (drawsOf (drawnSL (ckP .two) dsFull ρ))
        (nxtF :: pF.nums.stages.drop 2) 0 curF ((laidOf pF).drop 1) 6 (batT (t12Of d') G' row)
        (lPS frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (lCol frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))

/-- The claim that the batching makes is true at the first state. -/
def Front0 : Prop :=
  ∀ (rr : RecFull × RecFull) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (M₀ M₁ : (Fin frS.P.v → Bool) → frS.Co → GE), Meant rr y M₀ M₁ →
  ∀ (C : LCoins) (ρ : Rho (uL (ckP .two) dsFull)) (d' : St) (G' : Group),
    foldBlocks 0 (frontBlock frP :: blocksOrV frP) (_root_.Desc.K15.first frP.codes (keysOf rr))
      (lFront frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (lStoredCols frP frS (linOf rr y M₀ M₁) (drawsOf (drawnSL (ckP .two) dsFull ρ))) =
      .ok (d', [], []) →
    LinkSeats frP.par d' G' → Means.InOrder d'.st →
    G'.rows.size = 2 * frP.S.table.answers + (frP.S.columnsFirst + frP.S.columnsFurther) + 1 →
    ∀ row, Bat.combine (begun d'.st d'.loc.g G') d'.loc.g
        ⟨Means.layoutOf d'.st G', runRows d'.st G'⟩
        (drawnOf (noDigest ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩)) = some row →
      (Slf.idf (E := GE) (J := (frS.sg 97).cIn.J)).Holds (stmG (frS.sg 97) row)
        (μOf (frS.sg 97) (lPS frP frS (linOf rr y M₀ M₁) C
          (drawsOf (drawnSL (ckP .two) dsFull ρ))))

/-- The groups that the walk reads for the stages are bodyAll's. -/
def Groups : Prop :=
  ∀ (X : LIn frS) (C : LCoins) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (ρ : Rho (uL (ckP .two) dsFull)),
    (groupsOf 0 (((laidOf pF).drop 1).map (·.1))
      ((bodyAll pF C.body (nxtF :: pF.nums.stages.drop 2) 0 curF ((laidOf pF).drop 1) 6
        (lT frP frS 97 X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (lPS frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (lCol frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (drawsOf (drawnSL (ckP .two) dsFull ρ))).rs.map (·.drawn))).map
      (readG (lookV dsFull frS.P.T.a (linkNext frP frS 97 X C) y (drawnSL (ckP .two) dsFull ρ))) =
    (bodyAll pF C.body (nxtF :: pF.nums.stages.drop 2) 0 curF ((laidOf pF).drop 1) 6
      (lT frP frS 97 X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (lPS frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (lCol frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (drawsOf (drawnSL (ckP .two) dsFull ρ))).gs

theorem linkYes_of (H0 : Inv0) (HF : Front0) (HG : Groups) : LinkYes 97 := by
  intro rr y M₀ M₁ hM C ρ
  have hst : (p12Of frP).nums.stages = curF :: nxtF :: pF.nums.stages.drop 2 :=
    Full.stages_two_full
  have hrs := rs_full 97 (linOf rr y M₀ M₁) C ρ
  have hA := linkAll_rs frP frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ))
    curF _ hst
  have hfit := fit_full 97 (linOf rr y M₀ M₁) C ρ
  have hdr := drawn_rvOf (linkNext frP frS 97 (linOf rr y M₀ M₁) C) dsFull 0 []
    (drawnSL (ckP .two) dsFull ρ) (length_drawnSL _ _ ρ)
  have hsv := served_full 97 (linOf rr y M₀ M₁) C y ρ hM.wide
  rw [← hdr] at hsv
  obtain ⟨d', G', c, hc, h6, hW, hSe, hO, hn⟩ := front6_walks_full rr _ _ [] hfit hsv
  have h5 : (rvOf dsFull 0 [] (linkNext frP frS 97 (linOf rr y M₀ M₁) C)
      (drawnSL (ckP .two) dsFull ρ)).take 5 =
      lFront frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)) := by
    rw [hrs, hA, List.append_assoc]
    exact List.take_left' rfl
  have hd5 : (rvOf dsFull 0 [] (linkNext frP frS 97 (linOf rr y M₀ M₁) C)
      (drawnSL (ckP .two) dsFull ρ)).drop 5 = ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 5⟩ ::
      (bodyAll pF C.body (nxtF :: pF.nums.stages.drop 2) 0 curF ((laidOf pF).drop 1) 6
        (lT frP frS 97 (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (lPS frP frS (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (lCol frP frS (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (drawsOf (drawnSL (ckP .two) dsFull ρ))).rs := by
    rw [hrs, hA, List.append_assoc]
    exact List.drop_left' rfl
  rw [h5] at hc h6 hW
  have hcs : c = lStoredCols frP frS (linOf rr y M₀ M₁)
      (drawsOf (drawnSL (ckP .two) dsFull ρ)) := by
    have hc' := hc
    unfold lFront at hc'
    have hTa : frP.S.table.tree.a = frS.P.T.a := fr_linkSizesR.logN
    rw [want6 frP _ _ _ _ _ plan_full.1, stored_cols frP frS (linOf rr y M₀ M₁)
      (drawsOf (drawnSL (ckP .two) dsFull ρ)) dsFull frS.P.T.a _ y _
      ⟨[], drawsOf (drawnSL (ckP .two) dsFull ρ) 3⟩ rfl hTa rfl] at hc'
    exact (Option.some.inj hc').symm
  rw [List.append_nil, hcs] at h6
  obtain ⟨row, f0, f1, f2, f3, f4⟩ := H0 (linOf rr y M₀ M₁) C ρ rfl rfl d' G' h6 hSe hO hn
    (HF rr y M₀ M₁ hM C ρ d' G' h6 hSe hO hn)
  obtain ⟨t', hy, hN⟩ := body_left pF C.body _ _ _ _ _ _ _ _ _ f4
    (Full.left0_full (linOf rr y M₀ M₁).keys rfl rfl d' G' _ _ _ _ h6 hSe row)
  have hg := HG (linOf rr y M₀ M₁) C y ρ
  rw [f3] at hg hd5
  obtain ⟨-, fi, re, hs', hcut, -, -⟩ := cuts_full
  have hT := walk_tail frP _ d' (drawsOf (drawnSL (ckP .two) dsFull ρ) 5) _ _ curF _ _ t'
    (_root_.Desc.K15.test_planOk frP _ _ (_root_.Desc.K15.descV_planOk frP _ _
      _root_.Desc.K15.planOk_full)) hst
    (by
      have a1 := congrArg List.length (bodyAll_items pF C.body
        (drawsOf (drawnSL (ckP .two) dsFull ρ)) (nxtF :: pF.nums.stages.drop 2) 0 curF
        ((laidOf pF).drop 1) 6 (batT (t12Of d') G' row)
        (lPS frP frS (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
        (lCol frP frS (linOf rr y M₀ M₁) C (drawsOf (drawnSL (ckP .two) dsFull ρ))))
      have a2 := congrArg List.length (show ((laidOf pF).drop 1).map asked = _ from f4.1.2)
      rw [List.length_map] at a1 a2
      exact a1.trans a2.symm)
    hcut f0 f1 f2 hy hg hN
  rw [← hd5] at hT
  refine run_viewOf_full _ _ (keysOf rr) _ y ρ
    ({ d' with st := t'.st, book := t'.book, roots := t'.roots } : St) planWord_full.1
    (okKeys_written rr.1 rr.2)
    (okView_full 97 (linOf rr y M₀ M₁) C y ρ hM.words)
    (fun j k d s hd hs h x => linkNext_wide 97 (linOf rr y M₀ M₁) C j k d s hd hs h x) hM.wide ?_
    rfl
  have len6 : (((frontBlock frP :: blocksOrV frP).map
      (fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter })).flatMap (·.rounds)).length = 5 := by
    obtain ⟨_, _, h5'⟩ := decls_split frP plan_full.1
    rw [List.flatMap_map]
    exact h5'
  show Walks 0 _ (_root_.Desc.K15.linkProtocolChain frP).blocksInOrder _ _ _
  rw [flat_split]
  refine walks_append 0 _ _ _ _ d' _ _ ?_ ?_
  · rw [len6, h5]
    exact hW
  · rw [len6]
    exact hT

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.linkYes_of
