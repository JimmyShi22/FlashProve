-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorSeam.lean: THE FORM's HALF AT THE LINK, AT THE FULL SIZE: THE SEAM TO THE
VALUES' HALF, AND STAGE 0 CLOSED. (1) The form's half of the loop's invariant at stage 0 with its
field "decl" paid, at the place's own laid rounds. (2) "The link's first tree": ColIs
(Johnson/Prover/Link/BodyInv.lean), its first arm, at the library's record of sizes frS
(OnBytes/Slice/FullRecLink.lean) and 97 positions: the sizes' letters (frS.P.R, frS.P.aR,
frS.sg 97) against the link's shape (frP.S.rows, ceilLog2 frP.S.rows, curF).

Main names (namespace Johnson.Prover.Link.Full).
  seam_sg   the place's first stage, in the library's form, is the sizes' stage of the link's group.
  seam_aR   the sizes' row variables of a member are the shape's.
  seam_wid   the first tree's width, in the sizes' letters.
  stages_two_full   the place's stages begin with curF, nxtF.
  formInv0_closed   formInv0_full (DoorFull.lean) WITHOUT THE PREMISE ON "decl".
  colIs_first_full   ColIs AT STAGE 0, at the record behind the batching.

HOW THE CLOSED FACTS ARE HAD. SEVEN OF THE FIRST ARM's ELEVEN ARE THE LIBRARY's: fr_groupFacts
(OnBytes/Slice/FullRecBlkFacts.lean), called. seam_sg: fr_sg (OnBytes/Slice/FullRecSz.lean) and one
closed equation on stages. That equation, seam_aR, seam_wid and stages_two_full: by Lean's kernel
("decide +kernel"), each on its one closed clause.

By calls besides: formInv0_full, doorPlan_full, seatPlan_full, colFirst0, ran_of_front, ran_group
(this folder); decl_full (Johnson/Prover/Link/ChainSeats.lean); plan_full (AtD.lean).

Limits. STILL PREMISES: the two keys' items; the six front blocks' yes; LinkSeats; for
formInv0_closed besides: "in order", the batching's own equation, the written column's length; for
colIs_first_full: THE TWO EQUATIONS ON THE STATE AND THE WRITTEN COLUMN (the values' half's). Of the
values' half's record at stage 0 this pays one field of three. That the parameters that run are frP
is a law in scope elsewhere. Nothing on values. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorFull
import Johnson.Prover.Link.BodyInv
import Johnson.Prover.Link.ChainSeats
import OnBytes.Slice.FullRecBlkFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link.Full
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Desc.K15 (St P15 frP frontBlock blocksOrV first ctxOf t12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open Johnson.Prover.Link.Members (seatPlan_full)

/-! ## 1 Four closed equations -/

theorem seam_sg : sgOf curF = frS.sg 97 := by
  have h : curF = frSg1.st := by decide +kernel
  rw [h, show frS.sg 97 = frSg1 from fr_sg _ _ _ _]
  rfl

theorem seam_aR : frS.P.aR = ceilLog2 frP.S.rows := by decide +kernel

theorem seam_wid :
    3 * (frS.P.R + frS.P.R) + (maskShape frP.S).maskRows * 3 = Fmt.M2.widthOf frS.P.mems 1 := by
  decide +kernel

theorem stages_two_full : pF.nums.stages = curF :: nxtF :: pF.nums.stages.drop 2 := by
  decide +kernel

/-! ## 2 Stage 0 at the full size -/

section
variable (x : TableKey × TableKey) (hi0 : x.1.item = 0) (hi1 : x.2.item = 1)
  (d' : St) (G' : Group) (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn)
  (h : foldBlocks 0 (frontBlock frP :: blocksOrV frP) (first frP.codes x) rs cols =
    .ok (d', rest, cols'))
  (hS : LinkSeats frP.par d' G')

include hi0 hi1 h hS

/-- **THE FORM's HALF OF THE LOOP's INVARIANT AT STAGE 0, AT THE FULL SIZE, AT THE PLACE's OWN LAID
ROUNDS**: formInv0_full with the field "decl" paid. -/
theorem formInv0_closed (ho : InOrder d'.st) (θ : E) (row : GroupRow)
    (hc : Bat.combine (begun d'.st d'.loc.g G') d'.loc.g
      ⟨layoutOf d'.st G', runRows d'.st G'⟩ θ = some row)
    (col : ℕ → List UInt64)
    (hcol : ∀ y, (col y).length = 3 * (frP.S.rows + (frP.S.rows + 1))) :
    ∃ T : Tree,
      FormInv pF 0 curF ((laidOf pF).drop 1) (batT (t12Of d') G' row) col row
        (layoutOf d'.st G') ⟨iF.1, iF.2, curF.k, curF.h⟩ nF 2 0 T ∧ T.number = 0 :=
  formInv0_full x hi0 hi1 d' G' rs rest cols cols' h hS ho θ row hc _ col hcol
    fun T h1 h2 h3 => decl_full curF nxtF _ stages_two_full T h1 h2 h3

/-- **"THE LINK's FIRST TREE" AT STAGE 0, AT THE FULL SIZE**: ColIs
(Johnson/Prover/Link/BodyInv.lean), its first arm, at the record behind the batching; the two
equations on the state and the written column stay premises. -/
theorem colIs_first_full (row : GroupRow) (c : IoppStage) (P : PS) (col : ℕ → List UInt64)
    (m : Bool → frS.MJ → GE) (tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE)
    (hP : P = firstPS frS m tN φN ψN) (hcW : col = firstColW frS (membN frS m) tN φN ψN) :
    ColIs curF (batT (t12Of d') G' row) (layoutOf d'.st G') c 2 P col := by
  obtain ⟨X, D, hR, e1, e2⟩ := ran_of_front frP x plan_full.2.1 plan_full.2.2.2 rfl _
    plan_full.1 [] d' rs rest cols cols' hi0 hi1 plan_full.2.2.1 h
  have hG : G' = linkGrpR frP.S D.rec0 D.rec1 D.rows0 D.rows1 D.rE 0 := by
    have a := hS.group
    have b := ran_group hR
    rw [e1] at b
    exact Option.some.inj (a.symm.trans b)
  subst hG
  obtain ⟨-, -, -, -, -, hL, hSe⟩ := colFirst0 hR doorPlan_full (t := t12Of d') rfl rfl
    seatPlan_full d'.loc.g (linkGrpR frP.S D.rec0 D.rec1 D.rows0 D.rows1 D.rE 0)
  obtain ⟨-, -, -, -, g5, -, g7, g8, g9, g10, g11, g12⟩ := fr_groupFacts
  refine ColIs.first frS 97 m tN φN ψN seam_sg hP hcW 0 1 0 (rowShape frP.S) (maskShape frP.S)
    ?_ ?_ g8 g9 g10 g11 g12 seam_wid ?_ ?_
  · rw [seam_aR]; exact g5
  · rw [seam_aR]; exact g7
  · rw [seam_aR]; exact hL
  · rw [← seam_sg]; exact hSe

end

end Johnson.Prover.Link.Full

#print axioms Johnson.Prover.Link.Full.seam_sg
#print axioms Johnson.Prover.Link.Full.seam_aR
#print axioms Johnson.Prover.Link.Full.seam_wid
#print axioms Johnson.Prover.Link.Full.stages_two_full
#print axioms Johnson.Prover.Link.Full.formInv0_closed
#print axioms Johnson.Prover.Link.Full.colIs_first_full
