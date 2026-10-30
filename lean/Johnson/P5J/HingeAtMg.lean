-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/HingeAtMg.lean (kind K10): "THE HINGE" OF K10's LAW, CLOSED AT THE LINKS 1 .. 23: AT
THE CONSTANT's OWN STRUCTURE (`AtMg`), AT EVERY STATE THAT IS REACHED IN ITS OWN SENSE IN FRONT OF
THE CLOSING KIND's OWN SUB-PROTOCOL OF LINK l AND BEARS NO MARK: `ShapesAre` OF THE STATE's
STATEMENT, THE FRAME's GROUP, THE l-TH WRITTEN LIST, THE WRITTEN FLAGS AND THE PLAN's PUBLIC
NUMBERING noK10 AT THE CONSTANT's OWN LETTERS. In the very form of the field "shapes" of `RowAsks`
(Johnson/Desc/First/Close/Law/HRowAtFa.lean). Theorems: a join.

What is joined. AtMg.shapes_at (ShapesAtMg.lean) with its three premises paid: hsh by
AtMg.shape_full (ShapeFullAtMg.lean) · hT3 by t3_at_laid
(Johnson/Desc/First/Close/Law/HingeMore.lean: by the kernel at the written values; the first
chain's cut is the written one by cuts_of_laid) · hH4 by shape_clause_laid
(Johnson/LPFE1R/ShapeAtNoFull.lean), whose two premises on the state are paid here: the listed
shapes hold of the state's messages (the fold's fact msgShapes) and "the member's number lies below
the statement's messages": the members are the public list (members_public, MembersPublic.lean),
and every member of a group of a statement in order is there (the fold's fact tidy).

What is said.
  `AtMg.no_is`: the numbering at the constant's letters is the numbering at the written plan's
    (LaidAt.seats).
  `AtMg.hinge`: **the sentence**, at the number 14 l + 12. `AtMg.hinge_at_border`: **the same at
    the number batchAt fullLinks At.ps l + 3 of the constant's own list of places** (k10_border,
    Johnson/LPFK9R/K10Border.lean: by the kernel).
  `AtMg.hinge_inj`: beside it: that numbering parts the list's members (hinj_full), at
    the constant's letters.

PREMISES. h : AtMg OnBytes.secondHashFunction .. · FF : the facts that the laws take from "reached"
(`FoldFacts`) at h.rch, with hM : its listed shapes are the chain's (d.M = msgsOfChain
Zp.made.proof.1) · hr (reached) · hu (no mark) · 1 ≤ l < 24. THE TABLE's PROMISE IS NOT SPENT.

Limits. LINKS 0 AND 24 ARE NOT HERE. o := OnBytes.secondHashFunction alone. AtMg and FoldFacts are premises:
whether they can be met is not shown here ("the cut is the written one" is moved into the head, not
paid: by report, at `cuts_of_laid`). Nothing on soundness.

-/
import Johnson.P5J.ShapesAtMg
import Johnson.P5J.ShapeFullAtMg
import Johnson.Desc.First.Close.Law.HingeMore
import Johnson.LPFE1R.ShapeAtNoFull
import Johnson.LPFK9R.K10Border
import Johnson.Desc.First.FoldFacts

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
open VerifiableInference.Desc.First.Close (rdK ShapesAre membersOf membersPub kbAt noK10
  seatsPlanW members_public t3_at_laid hinj_full)
open VerifiableInference.Desc.LinkJoin (shape_clause_laid batchAt)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.ReqLit
open Johnson.G (linksFullLit)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open _root_.Run _root_.Run.PQ

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The numbering at the constant's letters is the numbering at the written plan's. -/
theorem AtMg.no_is {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF)
    (lo : List (OracleShape × ℕ)) (l : ℕ) :
    noK10 (At.seats Zp) lo (At.pseats Zp) l = noK10 seatsPlanW lo P5T.psFull l := by
  have e1 : At.pseats Zp = P5T.psFull := h.laid.seats h.scope
  have e2 : At.seats Zp = seatsPlanW := by
    unfold At.seats
    rw [e1]
  rw [e1, e2]

/-- **THE HINGE, AT THE LINKS 1 .. 23.** -/
theorem AtMg.hinge (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts h.rch (fun a => a.1) d reqW links ps)
    (hM : d.M = msgsOfChain Zp.made.proof.1) {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch (14 * l + 12) a)
    (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr (linksFullLit.getD l [])
        (kbAt shapeFull l (linksFullLit.getD l []))
        (noK10 (At.seats Zp) (linksFullLit.getD l []) (At.pseats Zp) l) := by
  have N₀ : Numbers := At.N Zp cF
  have hT3 := t3_at_laid h.scope h.laid N₀ l h1 h24
  rw [← h.no_is] at hT3
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := (reach_raw (h.rch_is_reach _ a hr)).fold
  have e : 14 * l + 12 = 14 * l + 8 + 4 := by omega
  rw [e] at f
  obtain ⟨L, G, -, -, hG, hm⟩ :=
    members_public h.scope h.reads O h.laid.planOk N₀ h1 h24 (Nat.le_refl 4) f
  rw [h.shape_full] at hm
  have hI := (OnBytes.Means.tidy4B_iff.1 (FF.tidy _ a hr hu)).inOrder
  have hsh := FF.msgShapes _ a hr hu
  rw [hM] at hsh
  refine h.shapes_at h.shape_full N₀ h1 h24 a hr _ hT3 fun i hi => ?_
  refine shape_clause_laid h.scope h.laid (by omega) hsh i ((hI.groups l G hG).there _ ?_)
  rw [hm.trans hT3]
  exact List.mem_map_of_mem hi

/-- **THE SAME AT THE NUMBER OF THE CONSTANT's OWN LIST OF PLACES.** -/
theorem AtMg.hinge_at_border (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {d : FoldData}
    {reqW : ProofFile.InstPub → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts h.rch (fun a => a.1) d reqW links ps)
    (hM : d.M = msgsOfChain Zp.made.proof.1) {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str)
    (hr : h.rch (batchAt fullLinks At.ps l + 3) a) (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr (linksFullLit.getD l [])
        (kbAt shapeFull l (linksFullLit.getD l []))
        (noK10 (At.seats Zp) (linksFullLit.getD l []) (At.pseats Zp) l) := by
  rw [LPFK9.k10_border l h24] at hr
  exact h.hinge FF hM h1 h24 a hr hu

/-- That numbering parts the list's members. -/
theorem AtMg.hinge_inj {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF) (l : ℕ) (hl : l < 26) :
    ∀ i ∈ membersOf (linksFullLit.getD l []), ∀ j ∈ membersOf (linksFullLit.getD l []),
      noK10 (At.seats Zp) (linksFullLit.getD l []) (At.pseats Zp) l i =
        noK10 (At.seats Zp) (linksFullLit.getD l []) (At.pseats Zp) l j → i = j := by
  rw [h.no_is]
  exact hinj_full l hl

end P5J

#print axioms P5J.AtMg.no_is
#print axioms P5J.AtMg.hinge
#print axioms P5J.AtMg.hinge_at_border
#print axioms P5J.AtMg.hinge_inj
