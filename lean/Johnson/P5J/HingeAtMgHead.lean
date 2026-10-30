-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/HingeAtMgHead.lean (kind K10): "THE HINGE" OF K10's LAW AT THE HEAD's LINK (l = 24): IN THE VERY FORM OF `AtMg.hinge` (HingeAtMg.lean beside this file), WHICH STANDS AT THE LINKS
1 .. 23: AT THE CONSTANT's OWN STRUCTURE (`AtMg`), AT EVERY STATE THAT IS REACHED IN ITS OWN SENSE AT 350 AND BEARS NO MARK: `ShapesAre` OF THE STATE's STATEMENT, THE FRAME's GROUP, THE 24TH WRITTEN
LIST, THE WRITTEN FLAGS AND THE PLAN's PUBLIC NUMBERING noK10 AT THE CONSTANT's OWN LETTERS. Theorems: a join, in that file's make.

What is joined. `shapesAre_reached_head` (Johnson/Desc/First/Close/Law/ShapesReachedHead.lean) with its three premises paid: hsh by `AtMg.shape_full` · hT3 by
`t3_head_at_laid` (HingeMore.lean: by the kernel at the written values) · hH4 by `shape_clause_laid` (Johnson/LPFE1R/ShapeAtNoFull.lean: l < 25), whose two premises on the state are paid as
in HingeAtMg.lean: the fold's facts msgShapes and tidy, and `members_public_head`.

What is said.
  `AtMg.shapes_at_head`: `RowAsks`' field "shapes" at the constant's own «reached», at 350, under hT3 and hH4.
  `AtMg.hinge_head`: **the sentence**, at the number 350. `AtMg.hinge_head_at_border`: **the same at batchAt fullLinks At.ps 24 + 3** (`k10_border_head`: by the kernel).

PREMISES. h : AtMg OnBytes.secondHashFunction .. · FF : `FoldFacts` at h.rch, with hM · hr (reached) · hu (no mark). THE TABLE's PROMISE IS NOT SPENT.
Limits. LINK 0 IS NOT HERE. o := OnBytes.secondHashFunction alone. AtMg and FoldFacts are premises: whether they
can be met is not shown here. WHAT OF THE HEAD IS SPENT, BY NAME, AS FAR AS TRACED: OF THE PROOF
FILE's ENTRY TESTS (Johnson/Desc/Laid/ProofAsks.lean: numbered as in its head), BEYOND THE FIRST
EIGHT: TEST 10 (`cutRow`: «the cut is the written one») AND TEST 9 (`madeRow`), the latter three
times: `AtMg.shape_full` · the numbering at the written seats (`LaidAt.seats`) ·
`shape_clause_laid`. Both are moved into the head, not paid. Nothing
on soundness.

-/
import Johnson.P5J.HingeAtMg
import Johnson.Desc.First.Close.Law.ShapesReachedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Chain)
open VerifiableInference.Desc.First (Numbers ModelPart FoldFacts FoldData)
open VerifiableInference.Desc.First.Close (rdK ShapesAre membersOf membersPubHead kbAt noK10
  seatsPlanW members_public_head t3_head_at_laid shapes_form shapesAre_reached_head)
open VerifiableInference.Desc.LinkJoin (shape_clause_laid batchAt)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.ReqLit
open Johnson.G (linksFullLit)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open _root_.Run _root_.Run.PQ

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **RowAsks' FIELD "shapes" AT THE CONSTANT's OWN "REACHED", AT THE HEAD's LINK.** -/
theorem AtMg.shapes_at_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hsh : Zp.first.shape = shapeFull) (N₀ : Numbers)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch 350 a)
    (no : Fin (linksFullLit.getD 24 []).length → ℕ)
    (hT3 : membersPubHead (N₀.withTold IM.placesW (Meaning.Carry.toldOf cF.blocksInOrder)) shapeFull =
      (membersOf (linksFullLit.getD 24 [])).map no)
    (hH4 : ∀ i ∈ membersOf (linksFullLit.getD 24 []),
      (a.1.2.st.oracles[no i]?).map (fun y : OnBytes.Oracle => y.shape) =
        some ((linksFullLit.getD 24 []).get i).1) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr (linksFullLit.getD 24 [])
        (kbAt shapeFull 24 (linksFullLit.getD 24 [])) no := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact shapes_form a.1.2 24 _ _ no
    (shapesAre_reached_head h.scope h.reads O h.laid.planOk hsh N₀ (z := a.1.1) (s := a.1.2)
      (h.rch_is_reach _ a hr) no hT3 hH4)

/-- **THE HINGE, AT THE HEAD's LINK.** -/
theorem AtMg.hinge_head (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts h.rch (fun a => a.1) d reqW links ps)
    (hM : d.M = msgsOfChain Zp.made.proof.1)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch 350 a)
    (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr (linksFullLit.getD 24 [])
        (kbAt shapeFull 24 (linksFullLit.getD 24 []))
        (noK10 (At.seats Zp) (linksFullLit.getD 24 []) (At.pseats Zp) 24) := by
  have N₀ : Numbers := At.N Zp cF
  have hT3 := t3_head_at_laid h.scope h.laid N₀
  rw [← h.no_is] at hT3
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := (reach_raw (h.rch_is_reach _ a hr)).fold
  obtain ⟨L, G, -, -, hG, hm⟩ :=
    members_public_head h.scope h.reads O h.laid.planOk N₀ (n := 10) (by omega) (Nat.le_refl 10) f
  rw [h.shape_full] at hm
  have hI := (OnBytes.Means.tidy4B_iff.1 (FF.tidy _ a hr hu)).inOrder
  have hsh := FF.msgShapes _ a hr hu
  rw [hM] at hsh
  refine h.shapes_at_head h.shape_full N₀ a hr _ hT3 fun i hi => ?_
  refine shape_clause_laid h.scope h.laid (by omega) hsh i ((hI.groups 24 G hG).there _ ?_)
  rw [hm.trans hT3]
  exact List.mem_map_of_mem hi

/-- **THE SAME AT THE NUMBER OF THE CONSTANT's OWN LIST OF PLACES.** -/
theorem AtMg.hinge_head_at_border (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts h.rch (fun a => a.1) d reqW links ps)
    (hM : d.M = msgsOfChain Zp.made.proof.1)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)
    (hr : h.rch (batchAt fullLinks At.ps 24 + 3) a) (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr (linksFullLit.getD 24 [])
        (kbAt shapeFull 24 (linksFullLit.getD 24 []))
        (noK10 (At.seats Zp) (linksFullLit.getD 24 []) (At.pseats Zp) 24) := by
  rw [LPFK9.k10_border_head] at hr
  exact h.hinge_head FF hM a hr hu

end P5J

#print axioms P5J.AtMg.shapes_at_head
#print axioms P5J.AtMg.hinge_head
#print axioms P5J.AtMg.hinge_head_at_border
