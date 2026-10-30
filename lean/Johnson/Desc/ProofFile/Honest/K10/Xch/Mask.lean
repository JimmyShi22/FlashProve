-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/Mask.lean: at the first chain's thread under the library's head, at the border
before the closing of segment l (kind K10): the mask code of the group that the frame names is the one that the frame's
shape names. This is the conclusion of the premise mask of `CarryOwed` (Xch/CarryTop.lean) and the premise hMask of
`closeBase_at_stepped` (Xch/BaseAt.lean), proved from the head, `Tied` and the invariant at the border. No acceptance of
the closing is spent. No definition; six theorems; one local notation.

What it rests on. Both sides are 0. The frame's shape is the written one, whose maskCode is written 0 (`shapeFull`,
Johnson/Desc/ReqLit/Full.lean). The group's members are those of the l-th written list (`ShapesAre`); that list has a
member with a mask row under the mask code 0 (`written_codes`, Johnson/Desc/First/Close/Law/LengthsOfShapes.lean); a
group in order has the mask code of each member that has a mask row (`GroupOk.maskCode`, Johnson/Desc/Means/Says.lean).
So `mask_at_thr` is a fact of the full size's written lists and not a law of the kind: that the group was laid from the
frame's shape and never turned is not shown, and at another shape nothing is claimed.

The words are those of the head of Xch/BaseAt.lean: a thread, the head (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean, which
extends `P5J.AtMg`), a border, the block, the record `K9.recOf s`, the group. The invariant is `Thr`
(Honest/Thread/Thr.lean).

The two senses of "reached". The library's sentence on the members' shapes (`P5J.AtMg.hinge`,
Johnson/P5J/HingeAtMg.lean, and its like at the first and the last segment, HingeAtMgZero.lean and HingeAtMgHead.lean)
is stated at states reached by steps that also pass a test on the words shown, at a typed instance. The invariant gives
less: the fold over the members' own steps (`thr_reach`, Honest/Thread/ReachFacts.lean). The library's three proofs go
down to that plain fold at once (`reach_raw`, `Reach.fold`, Johnson/Top/H0/Walk/Reach.lean), and the lemmas at the
bottom of them are stated there: `members_public`, which they call outright, and `shapesAre_at_fold`, which they reach
through `AtMg.shapes_at` (Johnson/P5J/ShapesAtMg.lean) and `shapesAre_reached`
(Johnson/Desc/First/Close/Law/ShapesReached.lean); the like at the first and the last segment. `shape_clause_laid`
(Johnson/LPFE1R/ShapeAtNoFull.lean) stands at a bare state. So the three sentences are proved here anew at the plain
sense, by the library's own steps with that one call opened. The library's three also ask that the state bears no mark;
that premise served to draw hI and hsh alone, and falls away here.

  `maskCode_of_shapes`   where the test `codesZero` accepts a written list: a group in order that holds that list's
                   members has the mask code 0. Of the test its second half alone is spent. No frame, no head
  `hinge_raw`, `hinge_raw_zero`, `hinge_raw_head`   under `P5J.AtMg` at the older hash: `ShapesAre` at a state reached
                   by the members' own steps, at the borders 14 l + 12 (1 ≤ l < 24), 12 and 350. hI: the statement is in
                   order. hsh: the shapes of the statement's messages are the first of those that the planner's first
                   chain lists
  `hinge_raw_all`   the three at one number: at each l < 25, at the border 14 l + `IM.nAt l` + 5
  **`mask_at_thr`**   at a block that `Tied` names (Td): wherever the invariant holds at the border before the closing
                   of segment l: each group at the number that the frame names has the mask code that the frame's shape
                   names. hI and the shape by `facts_at_thr` (Xch/BaseAt.lean), hsh by the field msgShapes of
                   `foldFacts_thr` (Honest/Thread/ReachFacts.lean). At every value of the thread's parameter carryX

The notation, and the option in front of it. 𝕋 stands for the head's thread at a variable carryX, as in Xch/BaseAt.lean;
what is said there of it, and of `set_option quotPrecheck false in`, holds here.

Limits. Every premise of `mask_at_thr`, by name. h: the head. Td: `Tied`; of it the proof spends one member, that the
chain has a block at the closing's number: with the chain's length (`Meaning.K2.flat_358`, Johnson/IMR/EndFive.lean)
that gives l < 25. hT: the invariant holds at the border. None of the three is shown of a run, a prover, a script or a
state. hr, hI and hsh of the four `hinge_raw` theorems are premises too; they are had here under hT alone. The statement
is an implication: it is idle at a border at which the invariant holds at no state, and where the statement has no group
at the frame's number. It says nothing on whether the closing accepts. What of the head the sentences on the members'
shapes spend, as far as the heads of HingeAtMgZero.lean and HingeAtMgHead.lean have traced it for theirs: beyond the
first eight entry tests, the tests 9 and 10 (madeRow, cutRow), which are moved into the head there and not paid; that is
these heads' word, not checked here. What the rest of the road spends of the head (`facts_at_thr`, `foldFacts_thr`,
`flat_358`, `shapeAt_full`) is not traced here. `CarryOwed` is not changed here: its field mask still stands, and no
theorem of Xch/CarryTop.lean calls this file. The prover H, the book Bk and the further parameters of `lettersHead` (Sc,
test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, w) are variables. Whether the head can be had at any files is not shown
here. The full size and the older hash alone. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.BaseAt
import Johnson.P5J.HingeAtMgZero
import Johnson.P5J.HingeAtMgHead
import Johnson.Desc.First.Close.Law.LengthsOfShapes
import Johnson.IMR.EndFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Close (Par rdK ShapesAre membersOf kbAt noK10 codesZero written_codes shapes_form
  members_public members_public_zero members_public_head shapesAre_at_fold shapesAre_at_fold_zero
  shapesAre_at_fold_head t3_at_laid t3_zero_at_laid t3_head_at_laid)
open VerifiableInference.Desc.LinkJoin (shape_clause_laid)
open VerifiableInference.Desc.K12.Door (atFirstShapes msgsOfChain)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.G (linksFullLit)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Means (InOrder GroupOk)
open OnBytes.Maker (WholeD)
open P5J (AtMg AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## 1 A group in order that holds a written list's members. No frame, no head -/

/-- Where the test `codesZero` accepts a written list, a group in order that holds that list's members has the mask code
0. The twin of `exps_of_shapes` (LengthsOfShapes.lean), which says the like of the layout's two exponents. -/
theorem maskCode_of_shapes {T : OnBytes.Statement} {G : OnBytes.Group} {lo : List (OnBytes.OracleShape × Nat)}
    {kb : Fin lo.length → Bool} {no : Fin lo.length → Nat}
    (hz : codesZero lo = true) (hOk : GroupOk T G) (H : ShapesAre T G lo kb no) : G.maskCode = 0 := by
  unfold codesZero at hz
  obtain ⟨-, h2⟩ := Bool.and_eq_true _ _ ▸ hz
  obtain ⟨j, hj, cj⟩ := List.any_eq_true.1 h2
  have cj' : (lo.get j).1.maskRows ≠ 0 ∧ (lo.get j).1.maskCode = 0 := by simpa using cj
  have inj : no j ∈ G.members.toList := by rw [H.members]; exact List.mem_map_of_mem hj
  obtain ⟨x, hx, ex⟩ := Option.map_eq_some_iff.1 (H.shape j hj)
  have h3 := hOk.maskCode (no j) inj x hx
  rw [ex] at h3
  exact (h3.resolve_left cj'.1).symm.trans cj'.2

/-! ## 2 The library's sentence on the members' shapes, at what is reached by the members' own steps -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl}

/-- `P5J.AtMg.hinge` (Johnson/P5J/HingeAtMg.lean) with "reached" at the members' own steps, and the two facts that it
takes of `FoldFacts` (tidy's inOrder; msgShapes) as premises on the state. 1 ≤ l < 24. -/
theorem hinge_raw (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {z : ProofFile.InstPub} {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + 12) (z, s))
    (hI : InOrder s.st) (hsh : atFirstShapes (msgsOfChain Zp.made.proof.1) s = true) :
    ∀ Gr, (rdK s).2.2.groups[(rdK s).2.1.group]? = some Gr →
      ShapesAre (rdK s).2.2 Gr (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l []))
        (noK10 (P5J.At.seats Zp) (linksFullLit.getD l []) (P5J.At.pseats Zp) l) := by
  have N₀ : Numbers := P5J.At.N Zp cF
  have hT3 := t3_at_laid h.scope h.laid N₀ l h1 h24
  rw [← h.no_is] at hT3
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := hr.fold
  have e : 14 * l + 12 = 14 * l + 8 + 4 := by omega
  rw [e] at f
  obtain ⟨L, G, -, -, hG, hm⟩ :=
    members_public h.scope h.reads O h.laid.planOk N₀ h1 h24 (Nat.le_refl 4) f
  rw [h.shape_full] at hm
  refine shapes_form s l _ _ _
    (shapesAre_at_fold h.scope h.reads O h.laid.planOk h.shape_full N₀ h1 h24 (Nat.le_refl 4) f _ hT3
      fun i hi => ?_)
  refine shape_clause_laid h.scope h.laid (by omega) hsh i ((hI.groups l G hG).there _ ?_)
  rw [hm.trans hT3]
  exact List.mem_map_of_mem hi

/-- `P5J.AtMg.hinge_zero` (HingeAtMgZero.lean), the same way. -/
theorem hinge_raw_zero (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    {z : ProofFile.InstPub} {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 12 (z, s))
    (hI : InOrder s.st) (hsh : atFirstShapes (msgsOfChain Zp.made.proof.1) s = true) :
    ∀ Gr, (rdK s).2.2.groups[(rdK s).2.1.group]? = some Gr →
      ShapesAre (rdK s).2.2 Gr (linksFullLit.getD 0 []) (kbAt shapeFull 0 (linksFullLit.getD 0 []))
        (noK10 (P5J.At.seats Zp) (linksFullLit.getD 0 []) (P5J.At.pseats Zp) 0) := by
  have N₀ : Numbers := P5J.At.N Zp cF
  have hT3 := t3_zero_at_laid h.scope h.laid N₀
  rw [← h.no_is] at hT3
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := hr.fold
  obtain ⟨L, G, -, -, -, hG, hm, -⟩ :=
    members_public_zero h.scope h.reads O h.laid.planOk N₀ (n := 4) (Nat.le_refl 4) f
  rw [h.shape_full] at hm
  refine shapes_form s 0 _ _ _
    (shapesAre_at_fold_zero h.scope h.reads O h.laid.planOk h.shape_full N₀ (n := 4) (Nat.le_refl 4) f _ hT3
      fun i hi => ?_)
  refine shape_clause_laid h.scope h.laid (by omega) hsh i ((hI.groups 0 G hG).there _ ?_)
  rw [hm.trans hT3]
  exact List.mem_map_of_mem hi

/-- `P5J.AtMg.hinge_head` (HingeAtMgHead.lean), the same way. -/
theorem hinge_raw_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    {z : ProofFile.InstPub} {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 350 (z, s))
    (hI : InOrder s.st) (hsh : atFirstShapes (msgsOfChain Zp.made.proof.1) s = true) :
    ∀ Gr, (rdK s).2.2.groups[(rdK s).2.1.group]? = some Gr →
      ShapesAre (rdK s).2.2 Gr (linksFullLit.getD 24 []) (kbAt shapeFull 24 (linksFullLit.getD 24 []))
        (noK10 (P5J.At.seats Zp) (linksFullLit.getD 24 []) (P5J.At.pseats Zp) 24) := by
  have N₀ : Numbers := P5J.At.N Zp cF
  have hT3 := t3_head_at_laid h.scope h.laid N₀
  rw [← h.no_is] at hT3
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := hr.fold
  obtain ⟨L, G, -, -, hG, hm⟩ :=
    members_public_head h.scope h.reads O h.laid.planOk N₀ (n := 10) (by omega) (Nat.le_refl 10) f
  rw [h.shape_full] at hm
  refine shapes_form s 24 _ _ _
    (shapesAre_at_fold_head h.scope h.reads O h.laid.planOk h.shape_full N₀ (n := 10) (by omega) (Nat.le_refl 10) f _
      hT3 fun i hi => ?_)
  refine shape_clause_laid h.scope h.laid (by omega) hsh i ((hI.groups 24 G hG).there _ ?_)
  rw [hm.trans hT3]
  exact List.mem_map_of_mem hi

/-- The three at one number: at each l < 25, at the border before the closing of segment l. -/
theorem hinge_raw_all (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s))
    (hI : InOrder s.st) (hsh : atFirstShapes (msgsOfChain Zp.made.proof.1) s = true) :
    ∀ Gr, (rdK s).2.2.groups[(rdK s).2.1.group]? = some Gr →
      ShapesAre (rdK s).2.2 Gr (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l []))
        (noK10 (P5J.At.seats Zp) (linksFullLit.getD l []) (P5J.At.pseats Zp) l) := by
  rcases Nat.eq_zero_or_pos l with rfl | h1
  · exact hinge_raw_zero h hr hI hsh
  · rcases Nat.lt_or_ge l 24 with h24 | h24
    · have e : 14 * l + IM.nAt l + 5 = 14 * l + 12 := by
        have : IM.nAt l = 7 := if_neg (by omega)
        omega
      rw [e] at hr
      exact hinge_raw h h1 h24 hr hI hsh
    · obtain rfl : l = 24 := by omega
      exact hinge_raw_head h hr hI hsh

end

/-! ## 3 At the head's thread, at every value of the parameter carryX -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
variable (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. Why the option stands here: the head of Xch/BaseAt.lean.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **At a block that `Tied` names: wherever the invariant holds at the border before the closing of segment l, the mask
code of the group that the frame names is the one that the frame's shape names.** Both are 0: a fact of the full size's
written lists. -/
theorem mask_at_thr {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) :
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G →
      G.maskCode = (K9.recOf s).frame.shape.maskCode := by
  intro G hG
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hb : 14 * l + IM.nAt l + 5 ≤ cF.blocksInOrder.length := Nat.le_of_lt hlt
  -- l < 25, of the chain's length
  have hl : l < 25 := by
    obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
    rw [Meaning.K2.flat_358 h.toAtMg.scope O] at hlt
    have h7 : 7 ≤ IM.nAt l := by
      unfold IM.nAt
      split <;> omega
    omega
  obtain ⟨hI, -, hsh, -⟩ := facts_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  -- no mark, as in facts_at_thr
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hP, -, -, -, -⟩ := hT'
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 hP.1
  have hM : atFirstShapes (msgsOfChain Zp.made.proof.1) s = true :=
    (foldFacts_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).msgShapes _ (m.st.input.x.pub, s)
      ⟨hb, k, m, En, hT, rfl⟩ hf
  have hR := thr_reach h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have HS := hinge_raw_all h.toAtMg hl hR hI hM G hG
  have z0 : G.maskCode = 0 :=
    maskCode_of_shapes (List.all_eq_true.1 written_codes.1 l (List.mem_range.2 hl)) (hI.groups _ G hG) HS
  show G.maskCode = s.live.frame.shape.maskCode
  rw [z0, hsh, h.toAtMg.shapeAt_full]
  rfl

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.maskCode_of_shapes
#print axioms ProofFile.Honest.K10.hinge_raw
#print axioms ProofFile.Honest.K10.hinge_raw_zero
#print axioms ProofFile.Honest.K10.hinge_raw_head
#print axioms ProofFile.Honest.K10.hinge_raw_all
#print axioms ProofFile.Honest.K10.mask_at_thr
