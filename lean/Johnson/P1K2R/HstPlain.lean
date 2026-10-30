-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/HstPlain.lean: code switching (K2): THE STATE's SIDE OF WHAT IS OWED ON THE
TABLE's NUMBERS, AT REACHED STATES (HstInScope.lean · HstPaid.lean), ON THE HEAD AND THREE NAMED
TESTS ALONE: a maker of the five named debts.
  owed5_of_tests  Owed5 Z Bs c p AT EVERY p: cut := hcut · sends := Johnson/IMR/SendsFinal.lean's
               debts_final (all 358 numbers, from the tests on the plan) · shapes :=
               shapeDebts_fenced over k2Fences_paid and k12_shape_debt · areB := hB · written :=
               sends_in_scope (Johnson/Goal/Numbers/MadeInScope.lean), from madePinnedAt's accept.
               The terms are those of the proof of msgShapes_field (Johnson/IMR/SeatsField.lean)
  hst_link_plain · hst_head_plain · hst_finish_plain  the three arms; the ends are
               hst_link | hst_head | hst_finish's to the letter
  d_link_plain · d_head_plain · d_finish_plain  d_link | d_head | d_finish (DebtsAt.lean) with hst
               gone: hFk: where the fence Fk holds, the state is reached
SO THE CIRCLE OF HstPaid.lean's LIMITS IS NOT IN THESE TOPS: «sends» and «shapes», which hold the
code switch's own share at its 25 numbers, are paid whole by theorems that take no law of the code
switch as a premise: no induction along the switches is wanted here.
WHAT STANDS IN FRONT, BY NAME. THE HEAD: hS · hR · O (at the public files' own layout file) · hF ·
hpl. hy: madePinnedAt accepts · hcut: the chain's sub-protocols have the written cut · hB: sendsAreB
accepts at 358. In d_…: hFk and DebtsAt.lean's six closed premises.
LIMITS. Joins: every step is a call. No premise is shown met at a real value: no example. That hy,
hcut and hB can be met together with the head is shown by nobody. The sealed version of the Lean
verifier asks neither madePinnedAt nor the written cut. The full size alone. No probability; no
soundness is claimed.
-/
import Johnson.P1K2R.HstPaid
import Johnson.P1K2R.HT1Plain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart Numbers blockPlaces possAt)
open VerifiableInference.Desc.First.K2 (SwState frontAt frameAt finishFrontQ LinkDebts SwitchDebts
  sentFitB)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.PlanWritten.Joined (sends_in_scope)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (XK linksW placesW k2P)
open _root_.Tw.K2 (firstFront switchNotices)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **A MAKER OF THE FIVE NAMED DEBTS**, at every public part p of an instance. -/
theorem owed5_of_tests (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true) (p : ProofFile.InstPub) :
    Owed5 Z Bs c p :=
  ⟨hcut, IM.debts_final hS hR O p (IM.blocksOk_of_planOk O hpl),
    IM.shapeDebts_fenced hS hR O (IM.k2Fences_paid hS hR O p)
      (IM.k12_shape_debt (IM.hp_of_planOk hS hR O (IM.blocksOk_of_planOk O hpl))
        (H2K.Made.p12OfMade_own _)),
    hB, sends_in_scope hS O.pub hy⟩

/-- **AT THE SWITCH INTO GROUP m + 1, m < 23, ON NAMED TESTS ALONE.** -/
theorem hst_link_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true) {m : ℕ} (h23 : m < 23)
    {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
    SwState Z.first.shape (m + 1) n.codes s ∧
      (∀ x, firstFront s.st s.check.frame = .ok x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, firstFront s.st s.check.frame = .ok x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 :=
  hst_link_five hS hR O hF hpl (written3 hS O.pub hy).1 (written3 hS O.pub hy).2.1 h23
    (owed5_of_tests hS hR O hpl hy hcut hB z) hP hn hr

/-- **AT THE OUTPUT HEAD's SWITCH, INTO GROUP 24, ON NAMED TESTS ALONE.** -/
theorem hst_head_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (a : Place) (nm : String) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) :
    SwState Z.first.shape 24 n.codes s ∧
      (∀ x, frontAt (k2P Z a nm .head n) s = some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z a nm .head n) s = some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 :=
  hst_head_five hS hR O hF hpl (written3 hS O.pub hy).1 (written3 hS O.pub hy).2.1
    (owed5_of_tests hS hR O hpl hy hcut hB z) a nm hP hn hr

/-- **AT THE FINISH's SWITCH, INTO GROUP 25, ON NAMED TESTS ALONE.** -/
theorem hst_finish_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (a : Place) (nm : String) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) :
    SwState Z.first.shape 25 n.codes s ∧
      (∀ x, frontAt (k2P Z a nm .finish n) t = some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z a nm .finish n) t = some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 :=
  hst_finish_five hS hR O hF hpl (written3 hS O.pub hy).1 (written3 hS O.pub hy).2.1
    (owed5_of_tests hS hR O hpl hy hcut hB z) a nm hP hn hr he

/-! ## The spender's three -/

section
variable {St Cl' : Type} {N₀ : Numbers} {links : List ModelPart} {bs : List (Block St Cl')}
  {Fk : Nat → S → Prop} {E : Nat → S → Bool}

theorem d_link_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true) {m : ℕ} (h23 : m < 23)
    (hFk : ∀ s, Fk (14 * (m + 1) + 2) s → ∃ z,
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
  d_link_five hS hR O hF hpl (written3 hS O.pub hy).1 (written3 hS O.pub hy).2.1 h23 (fun s hf => by
    obtain ⟨z, hr⟩ := hFk s hf
    exact ⟨z, owed5_of_tests hS hR O hpl hy hcut hB z, hr⟩)
    hps hnd hbk hok hlenC hcl

theorem d_head_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hFk : ∀ s, Fk 339 s → ∃ z,
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
  d_head_five hS hR O hF hpl (written3 hS O.pub hy).1 (written3 hS O.pub hy).2.1 (fun s hf => by
    obtain ⟨z, hr⟩ := hFk s hf
    exact ⟨z, owed5_of_tests hS hR O hpl hy hcut hB z, hr⟩)
    hps hnd hbk hok hlenC hcl

theorem d_finish_plain (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hFk : ∀ s, Fk 353 s → ∃ z,
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
  d_finish_five hS hR O hF hpl (written3 hS O.pub hy).1 (written3 hS O.pub hy).2.1 (fun s hf => by
    obtain ⟨z, hr⟩ := hFk s hf
    exact ⟨z, owed5_of_tests hS hR O hpl hy hcut hB z, hr⟩)
    hps hnd hbk hok hlenC hcl

end

end

end P1K2

#print axioms P1K2.owed5_of_tests
#print axioms P1K2.hst_link_plain
#print axioms P1K2.hst_head_plain
#print axioms P1K2.hst_finish_plain
#print axioms P1K2.d_link_plain
#print axioms P1K2.d_head_plain
#print axioms P1K2.d_finish_plain
