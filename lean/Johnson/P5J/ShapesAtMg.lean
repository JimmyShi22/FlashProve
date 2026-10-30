-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/ShapesAtMg.lean (kind K10): THE FIELD "shapes" OF `RowAsks`
(Johnson/Desc/First/Close/Law/HRowAtFa.lean: what the rows' part of K10's law asks of the statement
in
front), IN ITS VERY FORM, AT A STATE THAT IS REACHED IN THE SENSE OF THE CONSTANT's OWN CONDITION
(`AtMg.rch`, FourAtMg.lean) AT THE NUMBER 14 l + 12, 1 ≤ l < 24. Two theorems: calls.

What is said.
  `shapes_form`: from "there are the open link L, whose frame's group is l, and the group G at l,
with
    ShapesAre" to the form in which K10's law reads it: "at every group Gr that stands at the number
    that the frame names which K10's sub-protocol reads off the state (rdK)".
  `AtMg.shapes_at`: **the field, at the constant's letters**: the scope, the files' reading, the
    opening and the tests on the plan are the structure AtMg's own fields; "reached" is passed on by
    AtMg.rch_is_reach (RchAtMg.lean); the rest is shapesAre_reached (ShapesReached.lean).

PREMISES THAT ARE LEFT. hsh : Zp.first.shape = shapeFull (in scope other files hold it: by name
first_written_in_scope with request_shape_written: NOT CALLED HERE) · hT3 (closed: the public list
of the group's members is the written list's members under no: evaluated true at the 23 links, by
report; its theorem is other files' to show) · hH4 (every member's message has the
written shape at its number no i: on the state).

Limits. 1 ≤ l < 24. o := OnBytes.secondHashFunction. General in no. THE NUMBER 14 l + 12 IS THE WRITTEN LIST's
PLACE OF THE KIND K10 (k10_at_twelve); THAT IT IS THE BORDER AT WHICH THE LAW's X STANDS AT THE
CONSTANT's LIST OF PLACES IS NOT SAID HERE. Nothing on soundness.

-/
import Johnson.P5J.RchAtMg
import Johnson.Desc.First.Close.Law.ShapesReached
import Johnson.Desc.First.Close.Law.RowAsksOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model

/-- From "there are L and G" to the form in which K10's law reads it. -/
theorem shapes_form (s : VerifiableInference.Desc.First.S) (l : Nat)
    (lo : List (OracleShape × Nat)) (kb : Fin lo.length → Bool) (no : Fin lo.length → Nat)
    (H : ∃ (L : LinkCtx) (G : Group), s.link? = some L ∧ L.link = l ∧ L.check.frame.group = l ∧
      s.st.groups[l]? = some G ∧ ShapesAre s.st G lo kb no) :
    ∀ Gr, (rdK s).2.2.groups[(rdK s).2.1.group]? = some Gr → ShapesAre (rdK s).2.2 Gr lo kb no := by
  obtain ⟨L, G, hL, -, e3, hG, hA⟩ := H
  intro Gr hGr
  rw [frame_of_link s L hL, e3] at hGr
  obtain rfl : Gr = G := Option.some.inj (hGr.symm.trans hG)
  exact hA

end VerifiableInference.Desc.First.Close

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Chain)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Close (rdK ShapesAre membersOf membersPub kbAt shapes_form
  shapesAre_reached)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.ReqLit
open Johnson.G (linksFullLit)
open _root_.Run _root_.Run.PQ

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **RowAsks' FIELD "shapes" AT THE CONSTANT's OWN "REACHED".** -/
theorem AtMg.shapes_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hsh : Zp.first.shape = shapeFull) (N₀ : Numbers) {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (hr : h.rch (14 * l + 12) a)
    (no : Fin (linksFullLit.getD l []).length → ℕ)
    (hT3 : membersPub (N₀.withTold IM.placesW (Meaning.Carry.toldOf cF.blocksInOrder)) shapeFull l =
      (membersOf (linksFullLit.getD l [])).map no)
    (hH4 : ∀ i ∈ membersOf (linksFullLit.getD l []),
      (a.1.2.st.oracles[no i]?).map (fun y : OnBytes.Oracle => y.shape) =
        some ((linksFullLit.getD l []).get i).1) :
    ∀ Gr, (rdK a.1.2).2.2.groups[(rdK a.1.2).2.1.group]? = some Gr →
      ShapesAre (rdK a.1.2).2.2 Gr (linksFullLit.getD l [])
        (kbAt shapeFull l (linksFullLit.getD l [])) no := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact shapes_form a.1.2 l _ _ no
    (shapesAre_reached h.scope h.reads O h.laid.planOk hsh N₀ h1 h24 (z := a.1.1) (s := a.1.2)
      (h.rch_is_reach _ a hr) no hT3 hH4)

end P5J

#print axioms VerifiableInference.Desc.First.Close.shapes_form
#print axioms P5J.AtMg.shapes_at
