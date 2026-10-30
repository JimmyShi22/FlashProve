-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/NoFoldAtHead.lean (kinds K9 · K10): THE FACTS THAT THE LAWS TAKE FROM «REACHED» (`FoldFacts`) NEED BE A PREMISE OF NO PAYER AT THE CONSTANT: THE FIRST CALLS, IN K9's AND K10's FILES, OF `atMgR_rch_of_head` (Johnson/P5J/StartAtHead.lean): the hinge of K10's law at the head's link and at link 0 (both lists), K9's field
Ainside, and the five comparisons of public numbers: EACH WITHOUT FoldFacts. Theorems: calls.

Why. By report: «FoldFacts at the head: all 26 fields are paid at Rch := h.toAtMg.rch, from the head alone, in one theorem». All of `AtMgA.K9Left` and `AtMgA.K10HeavyAll` lean on that theorem's fitting their letters. THIS FILE IS THAT CHECK.

What is said. h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x throughout.
  `AtMgA.fold_at`: **∃ Ld, FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps: THE FIRST CONJUNCT OF K9Sorts | K9Left, TO THE LETTER.**
  `AtMgA.hinge_head_free`, `AtMgA.hinge_zero_free`, `AtMgA.hinge_five_free`: `AtMg.hinge_head` | `hinge_zero` | `hinge_five` (beside this file) with FF and hM gone: reached and no mark alone are left.
  `AtMgA.ainside_free`: `AtMgA.ainside` (InsideAtMg.lean) with Ld and FF gone: THE FIELD Ainside FROM THE HEAD ALONE.
  `AtMgA.five_free`: `five_of_facts` (Johnson/Desc/First/Link/Law/FiveOfFacts.lean) at the constant: FF · hcs · hdc · hds gone.

Limits. AtMgA is a premise («the head»: in scope · the files are read · the value is laid, WITH THE FOURTEEN ENTRY TESTS · the options). AT THE SECOND HASH FUNCTION.
Nothing on soundness.

-/
import Johnson.P5J.StartAtHead
import Johnson.P5J.HingeAtMgHead
import Johnson.P5J.HingeFiveAtMg
import Johnson.P5J.InsideAtMg
import Johnson.P5J.CodesFullAtMg
import Johnson.Desc.First.Link.Law.FiveOfFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Link Chain)
open VerifiableInference.Desc.First (S ModelPart Numbers FoldFacts shiftAt)
open VerifiableInference.Desc.First.Close (rdK ShapesAre kbAt noK10 loFive kbFive noFiveAt planOf)
open VerifiableInference.Desc.LinkJoin (onTR five_of_facts loAt gsAt)
open OnBytes.Means
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (Inside)
open VerifiableInference.Desc.ReqLit (shapeFull)
open _root_.Run _root_.Run.PQ

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **FoldFacts AT THE CONSTANT's LETTERS, FROM THE HEAD ALONE.** -/
theorem AtMgA.fold_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Ld, FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps := by
  obtain ⟨L, R⟩ := atMgR_rch_of_head h
  exact ⟨L, R.fold⟩

/-- **THE HINGE AT THE HEAD's LINK, WITHOUT FoldFacts.** -/
theorem AtMgA.hinge_head_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.toAtMg.rch 350 a)
    (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr (linksFullLit.getD 24 [])
        (kbAt shapeFull 24 (linksFullLit.getD 24 []))
        (noK10 (At.seats Zp) (linksFullLit.getD 24 []) (At.pseats Zp) 24) := by
  obtain ⟨Ld, FF⟩ := h.fold_at
  exact h.toAtMg.hinge_head FF rfl a hr hu

/-- **AT LINK 0, AT THE SIX-LIST.** -/
theorem AtMgA.hinge_zero_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.toAtMg.rch 12 a)
    (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr (linksFullLit.getD 0 [])
        (kbAt shapeFull 0 (linksFullLit.getD 0 []))
        (noK10 (At.seats Zp) (linksFullLit.getD 0 []) (At.pseats Zp) 0) := by
  obtain ⟨Ld, FF⟩ := h.fold_at
  exact h.toAtMg.hinge_zero FF rfl a hr hu

/-- **AT LINK 0, AT THE FIVE-LIST.** -/
theorem AtMgA.hinge_five_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.toAtMg.rch 12 a)
    (hu : a.1.2.failed = none) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr loFive kbFive (noFiveAt (At.seats Zp) (At.pseats Zp)) := by
  obtain ⟨Ld, FF⟩ := h.fold_at
  exact h.toAtMg.hinge_five FF rfl a hr hu

/-- **K9's FIELD Ainside FROM THE HEAD ALONE.** -/
theorem AtMgA.ainside_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (z : (F0T OnBytes.secondHashFunction Zp Np cF).XiPub) (k : ℕ) :
    ∀ s : S × (FrK).E.Str, onTR h.𝔇.N (mgAll h.𝔇 mgBase) fullLinks At.ps (fun s : S => (z, s))
        (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (k + 1 + 1) s →
      ∀ a, atS.get? s.1 = some a → ∀ born name r,
        reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl := by
  obtain ⟨Ld, FF⟩ := h.fold_at
  exact h.ainside Ld FF z k

/-- **THE FIVE COMPARISONS AT THE CONSTANT, WITHOUT FoldFacts.** -/
theorem AtMgA.five_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : ℕ}
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.toAtMg.rch k a)
    (hu : a.1.2.failed = none) {l : ℕ} (hl : l < 25) (p : Place) (hp : At.ps[k]? = some p)
    (hpl : p.link = some l) (hpp : p.piece ≤ 11 + 2 * shiftAt fullLinks l)
    (L : OnBytes.Model.LinkCtx) (hL : a.1.2.link? = some L)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z)
    (es : List Fmt.Entry) {kb : Fin (loAt l).length → Bool} {no : Fin (loAt l).length → ℕ}
    (H : ∀ G, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some G →
      ShapesAre (rdK a.1.2).2.2 G (loAt l) kb no) :
    (planOf es (rdK a.1.2)).k = (stageOf (gsAt l) 219).h + (stageOf (gsAt l) 219).g ∧
      (planOf es (rdK a.1.2)).h = (stageOf (gsAt l) 219).h ∧
      (∀ G lay, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some G →
        (begun (rdK a.1.2).2.2 (rdK a.1.2).2.1.group G).layout
          (rdK a.1.2).2.1.group = some lay →
        2 ^ lay.logEll = (stageOf (gsAt l) 219).C.l ∧
          2 ^ lay.logEllZk = (stageOf (gsAt l) 219).Z.l) ∧
      ((rdK a.1.2).2.2.codes.mask.getD (planOf es (rdK a.1.2)).maskCode default).ell =
        (stageOf (gsAt l) 219).Z.l := by
  obtain ⟨Ld, FF⟩ := h.fold_at
  exact five_of_facts FF a hr hu hl p hp hpl hpp L hL h.toAtMg.codes_full rfl h.toAtMg.shape_full
    hM hZ es H

end P5J

#print axioms P5J.AtMgA.fold_at
#print axioms P5J.AtMgA.hinge_head_free
#print axioms P5J.AtMgA.hinge_zero_free
#print axioms P5J.AtMgA.hinge_five_free
#print axioms P5J.AtMgA.ainside_free
#print axioms P5J.AtMgA.five_free
