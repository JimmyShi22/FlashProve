-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-

Johnson/P1K2R/HstPaid.lean: code switching (K2): THE STATE's SIDE OF WHAT IS OWED ON THE
TABLE's NUMBERS, AT REACHED STATES (Johnson/P1K2R/HstInScope.lean), WITH ITS PREMISES AT WRITTEN
CUTS PAID OUT OF THE NAMED DEBTS (Johnson/P1K2R/FoldSidePaid.lean's Owed) AT THE REACHED
STATE's OWN PUBLIC PART z.
  Owed5        FIVE NAMED DEBTS: Owed without its field noMark («the first state bears no mark»)
  owed_of_five from the five, at a z from which a state is reached at k ≥ 2: Owed (noMark by
               noMark_of_reach)
  linkCuts_of_owed · headCuts_of_owed · finishCuts_of_owed  SwLinkCuts | SwHeadCuts | SwFinishCuts
               from Owed at that z: each field is one call of paid_n | paid_n_head | paid_n_fin |
               paid_e | paid_e0
  hst_link_five · hst_head_five · hst_finish_five  hst_link | hst_head | hst_finish with the five in
               the place of the …Cuts
  d_link_five · d_head_five · d_finish_five  d_link_scope | d_head_scope | d_finish_scope likewise:
               hFk: where the fence Fk holds, the state is reached from a z at which the five hold
THE FIVE, AS FoldSidePaid.lean HAS THEM. cut: the chain's sub-protocols have the written cut ·
sends: SendDebts · shapes: ShapeDebts (both under Johnson/IMR/) · areB: the test sendsAreB at
358 accepts · written: the planner's sendings of the proof file are the written ones. cut, areB and
written do not speak of z.
THE OTHER PREMISES STAY: in scope, the files read, the opening O · hF · hpl · hcs · hsh · in d_…:
the six closed premises.
LIMITS. Joins. EACH TOP TAKES THE FIVE WHOLE: «sends» and «shapes» both
hold the code switch's own share at every one of its 25 numbers, and are asked at every border up
to 358: so, as typed, no top can be spent at any switch before all 25 shares are paid, and an
induction along the switches cannot run through these tops: it would want a prefix form. None is
wanted where both are paid whole from the tests on the plan: Johnson/P1K2R/HstPlain.lean. That the
five can be met together is not shown here: no example. No probability; no soundness is claimed.

-/
import Johnson.P1K2R.HstInScope
import Johnson.P1K2R.FoldSidePaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart Numbers blockPlaces possAt)
open VerifiableInference.Desc.First.K2 (SwState frontAt frameAt finishFrontQ LinkDebts SwitchDebts
  sentFitB)
open VerifiableInference.Desc.First.K2Hands (csW)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.G (proofSendsFull)
open IM (XK linksW placesW k2P)
open _root_.Tw.K2 (firstFront switchNotices)
open ProofFile (Cl)

/-- **The five named debts**: FoldSidePaid.lean's Owed without «the first state bears no mark». -/
structure Owed5 (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (c : Chain S Cl) (p : ProofFile.InstPub) : Prop where
  cut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull
  sends : IM.SendDebts 0 Z.first.codes (snAt Z Bs.G₀ IM.placesW) Z Bs.G₀ c (ProofFile.startS Z p)
  shapes : IM.ShapeDebts 0 (snAt Z Bs.G₀ IM.placesW) Z Bs.G₀ c (ProofFile.startS Z p)
  areB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true
  written : Z.made.proof = proofSendsFull

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- From the five, at a z from which a state is reached at k ≥ 2: all six. -/
theorem owed_of_five (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (h2 : 2 ≤ k) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) (W : Owed5 Z Bs c z) :
    Owed Z Bs c z :=
  ⟨W.cut, W.sends, W.shapes, W.areB, noMark_of_reach hS hR O h2 hr, W.written⟩

theorem linkCuts_of_owed (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (W : Owed Z Bs c z) {m : ℕ} (h23 : m < 23) : SwLinkCuts Z c z m :=
  ⟨fun _ g1 g2 => paid_n hS hR O hpl W g1 g2, paid_e hS hR O W (by omega),
    paid_e0 hS hR O hpl W (by omega)⟩

theorem headCuts_of_owed (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (W : Owed Z Bs c z) : SwHeadCuts Z c z :=
  ⟨paid_n hS hR O hpl W (g := 23) (by omega) (by omega), paid_n_head hS hR O hpl W,
    paid_e hS hR O W (k := 339) (by omega), paid_e0 hS hR O hpl W (l := 23) (by omega)⟩

theorem finishCuts_of_owed (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (W : Owed Z Bs c z) : SwFinishCuts Z c z :=
  ⟨paid_n_fin hS hR O hpl W, paid_e hS hR O W (k := 353) (by omega)⟩

/-- **AT THE SWITCH INTO GROUP m + 1, m < 23, ON THE FIVE.** -/
theorem hst_link_five (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW) {m : ℕ} (h23 : m < 23)
    (V : Owed5 Z Bs c z) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
    SwState Z.first.shape (m + 1) n.codes s ∧
      (∀ x, firstFront s.st s.check.frame = .ok x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, firstFront s.st s.check.frame = .ok x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 :=
  hst_link hS hR O hF hpl hcs hsh h23
    (linkCuts_of_owed hS hR O hpl (owed_of_five hS hR O (by omega) hr V) h23) hP hn hr

/-- **AT THE OUTPUT HEAD's SWITCH, INTO GROUP 24, ON THE FIVE.** -/
theorem hst_head_five (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    (V : Owed5 Z Bs c z) (a : Place) (nm : String) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) :
    SwState Z.first.shape 24 n.codes s ∧
      (∀ x, frontAt (k2P Z a nm .head n) s = some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z a nm .head n) s = some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 :=
  hst_head hS hR O hF hpl hcs hsh
    (headCuts_of_owed hS hR O hpl (owed_of_five hS hR O (by omega) hr V)) a nm hP hn hr

/-- **AT THE FINISH's SWITCH, INTO GROUP 25, ON THE FIVE.** -/
theorem hst_finish_five (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    (V : Owed5 Z Bs c z) (a : Place) (nm : String) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) :
    SwState Z.first.shape 25 n.codes s ∧
      (∀ x, frontAt (k2P Z a nm .finish n) t = some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z a nm .finish n) t = some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 :=
  hst_finish hS hR O hF hpl hcs hsh
    (finishCuts_of_owed hS hR O hpl (owed_of_five hS hR O (by omega) hr V)) a nm hP hn hr he

/-! ## The spender's three, on the five -/

section
variable {St Cl' : Type} {N₀ : Numbers} {links : List ModelPart} {bs : List (Block St Cl')}
  {Fk : Nat → S → Prop} {E : Nat → S → Bool}

theorem d_link_five (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW) {m : ℕ} (h23 : m < 23)
    (hFk : ∀ s, Fk (14 * (m + 1) + 2) s → ∃ z, Owed5 Z Bs c z ∧
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup) {b : Block St Cl'}
    (hbk : bs[14 * (m + 1) + 2]? = some b) (hok : reqShapeOk Z.first.shape = true)
    (hlenC : (N₀.keptOf (m + 1 - 1)).length =
      ((reqGroups Z.first.shape).getD (m + 1) {}).target.kept.size)
    (hcl : ∀ Pp n, prepOf Z Bs.G₀ = some Pp → numsAt Pp (some (m + 1)) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks Z.first.shape links bs) (m + 1) placesW[14 * (m + 1) + 2]? n.codes
        n.sent = true ∧
      possAt bs links.length (m + 1) = n.positions) :
    ∀ Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some (m + 1)) = some n →
      Fk (14 * (m + 1) + 2) s →
      XK (N₀.atBlocks Z.first.shape links bs) linksW placesW E (14 * (m + 1) + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      LinkDebts (N₀.atBlocks Z.first.shape links bs) (m + 1) placesW[14 * (m + 1) + 2]?
        placesW[14 * (m + 1) + 3]? s n.positions x W lay' :=
  d_link_scope hS hR O hF hpl hcs hsh h23 (fun s hf => by
    obtain ⟨z, V, hr⟩ := hFk s hf
    exact ⟨z, linkCuts_of_owed hS hR O hpl (owed_of_five hS hR O (by omega) hr V) h23, hr⟩)
    hps hnd hbk hok hlenC hcl

theorem d_head_five (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    (hFk : ∀ s, Fk 339 s → ∃ z, Owed5 Z Bs c z ∧
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup) {b : Block St Cl'}
    (hbk : bs[339]? = some b) (hok : reqShapeOk Z.first.shape = true)
    (hlenC : (N₀.keptOf (24 - 1)).length =
      ((reqGroups Z.first.shape).getD 24 {}).target.kept.size)
    (hcl : ∀ Pp n, prepOf Z Bs.G₀ = some Pp → numsAt Pp (some 24) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks Z.first.shape links bs) 24 placesW[339]? n.codes n.sent = true ∧
      possAt bs links.length 24 = n.positions) :
    ∀ nm Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some 24) = some n →
      Fk 339 s → XK (N₀.atBlocks Z.first.shape links bs) linksW placesW E 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (N₀.atBlocks Z.first.shape links bs) 24 placesW[339]? placesW[339 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size + x.own.length) x W lay' :=
  d_head_scope hS hR O hF hpl hcs hsh (fun s hf => by
    obtain ⟨z, V, hr⟩ := hFk s hf
    exact ⟨z, headCuts_of_owed hS hR O hpl (owed_of_five hS hR O (by omega) hr V), hr⟩)
    hps hnd hbk hok hlenC hcl

theorem d_finish_five (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    (hFk : ∀ s, Fk 353 s → ∃ z, Owed5 Z Bs c z ∧
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup) {b : Block St Cl'}
    (hbk : bs[353]? = some b) (hok : reqShapeOk Z.first.shape = true)
    (hlenC : (N₀.keptOf (25 - 1)).length =
      ((reqGroups Z.first.shape).getD 25 {}).target.kept.size)
    (hcl : ∀ Pp n, prepOf Z Bs.G₀ = some Pp → numsAt Pp none = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks Z.first.shape links bs) 25 placesW[353]? n.codes n.sent = true ∧
      possAt bs links.length 25 = n.positions) :
    ∀ nm Pp n (s t : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp none = some n →
      Fk 353 s → XK (N₀.atBlocks Z.first.shape links bs) linksW placesW E 353 s = true →
      finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (N₀.atBlocks Z.first.shape links bs) 25 placesW[353]? placesW[353 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size) x W lay' :=
  d_finish_scope hS hR O hF hpl hcs hsh (fun s hf => by
    obtain ⟨z, V, hr⟩ := hFk s hf
    exact ⟨z, finishCuts_of_owed hS hR O hpl (owed_of_five hS hR O (by omega) hr V), hr⟩)
    hps hnd hbk hok hlenC hcl

end

end

end P1K2

#print axioms P1K2.owed_of_five
#print axioms P1K2.linkCuts_of_owed
#print axioms P1K2.headCuts_of_owed
#print axioms P1K2.finishCuts_of_owed
#print axioms P1K2.hst_link_five
#print axioms P1K2.hst_head_five
#print axioms P1K2.hst_finish_five
#print axioms P1K2.d_link_five
#print axioms P1K2.d_head_five
#print axioms P1K2.d_finish_five
