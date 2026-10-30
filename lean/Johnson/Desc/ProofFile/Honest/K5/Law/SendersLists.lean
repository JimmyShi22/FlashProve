-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SendersLists.lean: THE SENDERS' PREMISES AT THE CODE SWITCHES
AS ONE PREMISE ON LISTS: at each place of the plan that leads into a link below 24 the kind's own
list of message lots (`K2.switchMsgLots`, Honest/K2/ScriptLots.lean), at the chain 0, lies in the
list ml. A COROLLARY OVER THE TWO TIED FORMS (SendersMaskTied.lean in this folder): NO NEW STRENGTH:
THE LIST FORM IS THE STRONGER PREMISE, AND EACH ARROW GOES FROM IT TO A TIED FORM, NEVER BACK. THE
LIST FORM IS A PREMISE HERE: THIS FILE PROVES IT OF NO LIST. NO JOINED LAW STANDS IN THIS FILE: no
thread and no filling are named in it. The two arrows are CONDITIONAL: under the hypothesis h, the
library's head on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). One definition, a
premise's form; two theorems.

Main names:
  `PlanSwitchLists Zp ml Vd S G rd lay`: at every p of `K2.switchPlaces Zp G` with p.link < 24 there
    are D₀ and fx with: the list `K2.switchMsgLots 0 (K2.withSwitchData S D₀ Zp G) rd
    (K2.lotClosingAt lay (K2.segmentsOf Zp G)) p (K2.switchNum Zp p) fx` is contained in ml; each of
    its lots meets `LotsAgree ml`; hL at the chain 0; hv. The last two are the tied forms' own
    clauses.
  `planSwitchLotForMaskTied_of_lists`: h; hG; hg; the list form: `PlanSwitchLotForMaskTied Zp ml Vd
    G g lay`. Its statement names Zp, not h: h comes in by the line "include h in" in front of it.
  `planSwitchLotForFillLends_of_lists`: h; hG; l ≠ 0; l < 24; the typed seat's equation at Ad; the
    list form: `PlanSwitchLotForFillLends Zp ml Vd S G rd Ad l m' lay`.

How. THE MASK: `mask_lot_in_switch_lots` (MaskLotInList.lean in this folder): the lot of message 3
is a member of the list. THE FILLINGS: the typed seat is the switches' at l ≠ 0;
`seated_at_switch_msg` (FillSwitchHead.lean) hands a place and a message, which are p and m since
the plan's places have no double (the steps of `covers_fill_switch_head`, the same file); then the
three joints of OwnMessagesAtPlan.lean: `own_number_head`: m' = m; `own_in_range`: m is below
p.others.size - 1; `first_sender_own`; the law `K2.Law.ownNums_at_head`
(Honest/K2/Law/OwnRolesAtHead.lean): the switch's own number of its message 1 + p.sizes.kept.length
+ m is `P5J.At.num Zp p.link m`; and the fourth conjunct of `switch_notice_shape`: that message lies
below the sending's size.

Limits. WHERE THE LIST FORM ASKS MORE THAN THE TIED FORMS: whole lists: the lot of message 0 and
that of the sending's last message too, which the tied forms do not name; every place with p.link <
24 at once: it names no group; one D₀ and one fx a place, where the tied forms leave them under
"there is" at each message; the chain 0 at the fillings too, where the tied form has ch under "there
is"; and the mask's D₁ and rd', free in the tied form, are the fillings' own: one filling and one
reader for a place. WHERE IT ASKS LESS TROUBLE: at a place with 1 + p.sizes.kept.length = 3 message
3 and the own message 0 are one lot of one list; at which places that is so this file does not say.
THE GUARD p.link < 24: the laws over this file call the arrows at l = 2 g and l = 2 g + 1 with g <
12 alone; without it the form would ask its four clauses at every place of the plan, those with a
link from 24 on too. `LotsAgree` STAYS A CLAUSE OF ITS OWN, at each lot of the list; it unfolds to a
clause under "for all k w". D₀ STANDS UNDER "there is": by its type it is a function of the public
part and the ground; a term of that type may still close over what it was built from: nothing here
bars that: as in the tied form. ON WHETHER THE LIST FORM CAN BE MET NOTHING IS HELD HERE. All limits
of SendersMaskTied.lean, MaskLotInList.lean, OwnMessagesAtPlan.lean, FillSwitchHead.lean and
OwnRolesAtHead.lean hold here. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean,
and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the
earlier hash `OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SendersMaskTied
import Johnson.Desc.ProofFile.Honest.K5.Law.MaskLotInList
import Johnson.Desc.ProofFile.Honest.K5.Law.OwnMessagesAtPlan
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnRolesAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open ProofFile.Honest.FirstThread (MsgLot LotsAgree)
open P5J (AtMgA TS)

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **At each place of the plan into a link below 24 the kind's own list of message lots, at the
chain 0, lies in ml; each of its lots agrees with the others; hL; hv.** A premise's form. -/
def PlanSwitchLists
    (Zp : ProofFile.Pub)
    (ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (S : Sz)
    (G : Ground)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) :
    Prop := ∀ p ∈ K2.switchPlaces Zp G, p.link < 24 → ∃ (D₀ : Pub → Ground → RowDataOf ProofFile.Inst) (fx
            : ℕ), (K2.switchMsgLots 0 (K2.withSwitchData S D₀ Zp G) rd (K2.lotClosingAt lay (K2.segmentsOf
            Zp G)) p (K2.switchNum Zp p) fx : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))) ⊆ ml ∧ (∀ L ∈
                  (K2.switchMsgLots 0 (K2.withSwitchData S D₀ Zp G) rd (K2.lotClosingAt lay (K2.segmentsOf Zp
                  G)) p (K2.switchNum Zp p) fx : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))), LotsAgree ml L) ∧
      lendsPart Bk (Bk.rowsOf 0) (lookDue Bk 0) ⟨p.place, 0⟩ (K2.switchPart (K2.coreSender
      K2.freshTable) p.sizes p.others p.foldVars p.carries) = true ∧ ∀ w, Vd w → K2.publicOk
      (K2.withSwitchData S D₀ Zp G) lay p ((K2.segmentsOf Zp G).take p.link) w.x = true

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

include h in
/-- **The list form gives the mask's tied form.** CONDITIONAL: h; hG; hg. -/
theorem planSwitchLotForMaskTied_of_lists
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {S : Sz}
    {G : Ground}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {g : ℕ}
    {lay : OnBytes.Params.ReqLayout}
    (hG : blankBy pureRoad.links Zp = some G)
    (hg : g < 12)
    (H : PlanSwitchLists Zp ml Vd S G rd lay) :
    PlanSwitchLotForMaskTied Zp ml Vd G g lay := by
  intro p hp hl
  obtain ⟨D₀, fx, hsub, hag, hL, hv⟩ := H p hp (by omega)
  have hm := mask_lot_in_switch_lots h hG hp hg hl (Bk := Bk) (W₀ := W₀) (Rc := Rc)
    (Xi := ProofFile.Inst) (Tr := Tr) 0 (K2.withSwitchData S D₀ Zp G) rd
    (K2.lotClosingAt lay (K2.segmentsOf Zp G)) (K2.switchNum Zp p) fx
  exact ⟨K2.withSwitchData S D₀ Zp G, rd, fx, hsub hm, hag _ hm, hL, hv⟩

/-- **The list form gives the fillings' form with hL, at an address that is seated at a link from 1
to 23.** CONDITIONAL: h; hG; hl0; hl24; hAd. -/
theorem planSwitchLotForFillLends_of_lists
    {ml : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop}
    {S : Sz}
    {G : Ground}
    {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {Ad : MsgAddr}
    {l m' : ℕ}
    {lay : OnBytes.Params.ReqLayout}
    (hG : blankBy pureRoad.links Zp = some G)
    (hl0 : l ≠ 0)
    (hl24 : l < 24)
    (hAd : typedSeat h G l Ad = some (l, m'))
    (H : PlanSwitchLists Zp ml Vd S G rd lay) :
    PlanSwitchLotForFillLends Zp ml Vd S G rd Ad l m' lay := by
  have es : typedSeat h G l = K2.switchSeat Zp G := if_neg hl0
  rw [es] at hAd
  intro p hp m eA el
  subst eA
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have eG0 : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨p', hp', m₂, ea, -, hmn⟩ := seated_at_switch_msg hAd
  have hN : ((K2.switchPlaces Zp G).map (·.place)).Nodup :=
    (SwitchPlaces.k2_places_sub Zp G).nodup (H2K12.places_apart (H2K12.table_apart O).1)
  have ep : p = p' := List.inj_on_of_nodup_map hN hp hp'
    (congrArg (fun a : MsgAddr => a.sender.place) ea)
  subst ep
  have e2 : 1 + p.sizes.kept.length + m = 1 + p.sizes.kept.length + m₂ :=
    congrArg MsgAddr.msg ea
  have em : m = m₂ := by omega
  subst em
  have e1 : m' = m := own_number_head h hG hmn
  have hr : m < p.others.size - 1 := own_in_range hp hmn
  obtain ⟨_, -, -, -, hn⟩ := switch_notice_shape hp hmn
  have hnum : K2.switchNum Zp p (1 + p.sizes.kept.length + m) = P5J.At.num Zp p.link m :=
    K2.Law.ownNums_at_head h.toAtMg O p (by rw [eG0]; exact hp) m hr
  obtain ⟨D₀, fx, hsub, hag, hL, hv⟩ := H p hp (by omega)
  have hmem : (⟨K2.switchNum Zp p (1 + p.sizes.kept.length + m), fx,
      K2.switchMsgTxt 0 (K2.withSwitchData S D₀ Zp G) rd
      (K2.lotClosingAt lay (K2.segmentsOf Zp G)) p (1 + p.sizes.kept.length + m)⟩ :
      MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) ∈
      K2.switchMsgLots 0 (K2.withSwitchData S D₀ Zp G) rd
        (K2.lotClosingAt lay (K2.segmentsOf Zp G)) p (K2.switchNum Zp p) fx := by
    unfold K2.switchMsgLots
    exact List.mem_map.2 ⟨1 + p.sizes.kept.length + m,
      List.mem_filter.2 ⟨List.mem_range.2 hn, first_sender_own hp m⟩, rfl⟩
  rw [hnum] at hmem
  subst el
  subst e1
  exact ⟨D₀, fx, 0, hsub hmem, hag _ hmem, hL, hv⟩

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.PlanSwitchLists
#print axioms ProofFile.Honest.K5.planSwitchLotForMaskTied_of_lists
#print axioms ProofFile.Honest.K5.planSwitchLotForFillLends_of_lists
