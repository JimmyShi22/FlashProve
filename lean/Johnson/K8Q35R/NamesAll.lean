-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/K8Q35R/NamesAll.lean: TWO OF THE THREE CLOSED SENTENCES OF P1K8T.SmallPlan
(Johnson/P1K8R/SmallAtHead.lean), AS THEOREMS UNDER THE HEAD: names AND lawful. A payment beneath
kind K8's frozen condition (its field small). IT IMPORTS ThirdParty/. Five theorems: JOININGS: the
weight lies in the files that are called.

  names_plain   in the goals' scope, where the plain road returns the public part Z: AT EACH OF THE
                25 LINKS l and each matrix of it: the built link's list of arrays names, at the
                plan's number of that matrix's array, (owner, name) by the public parameters'
                label. THREE CALLS, one a sort of link: names_tie_plain
                (Johnson/Road/K4/NamesTie.lean: the twelve feed-forward links) · names_tie_att_plain
                (Johnson/Desc/First/Att/Door/Law/K5NamesTie.lean: the twelve attention links) ·
                names_tie_head_all (Johnson/Desc/AtSeats/NamesTieHeadStream.lean: the head's link;
                that it has eight matrices: plan_in_scope,
                Johnson/Desc/Kinds/Law/HeadPlanWritten.lean)
  **names_all** SmallPlan.names TO THE LETTER, under the head, at the blank ground's built link l:
                names_plain and built_arr (Johnson/IMR/ArraysOpen.lean)
  **lawful_at** SmallPlan.lawful TO THE LETTER, under the head: pub_layoutOk
                (Johnson/IMR/LayoutOkPub.lean)
  smallPlan_of_mats   SmallPlan from its third field alone, under the head
  small_of_mats       K8LeftT's field small, to the letter, from the head, FoldFacts and mats
Limits. THE THIRD SENTENCE, mats, IS NOT PAID HERE: it is the piece's weight. A MEMBER OF THE HEAD
IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). At OnBytes.secondHashFunction
alone. No soundness statement. Nothing on hiding.
-/
import Johnson.Road.K4.NamesTie
import Johnson.Desc.First.Att.Door.Law.K5NamesTie
import Johnson.Desc.AtSeats.NamesTieHeadStream
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.IMR.ArraysOpen
import Johnson.IMR.LayoutOkPub
import Johnson.IMR.MemberOfGate
import Johnson.P1K8R.SmallAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace K8Q35

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Place Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart FoldFacts momentAt shiftAt flatPlacesOf)
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)
open P1K8T

/-- **THE NAMES' TIE AT ALL 25 LINKS**, in the goals' scope, where the plain road returns. -/
theorem names_plain {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Z : ProofFile.Pub}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z) {l : ℕ} (hl : l ≤ 24) {μ : ℕ}
    (hμ : μ < (Meaning.tlAt Z.p.X l).NM) :
    (Meaning.K2.arrOf Z l)[(Meaning.tlAt Z.p.X l).gtTree.getD μ 0]? =
      some (Meaning.ownerK (Meaning.labAt Z.p.X l μ),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt Z.p.X l μ))) := by
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact OnBytes.Road.K4.names_tie_plain hS hR hZ (by omega) hμ
    · exact H2K5.Names.names_tie_att_plain hS hR hZ (by omega) hμ
  · obtain rfl : l = 24 := by omega
    have hpub : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := by
      rw [← VerifiableInference.PlanWritten.publicOfO_older]
      exact ProofFile.Law.pub_public
        (show ProofFile.pureRoad.pub OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z from hZ)
    have e24 : Meaning.tlAt Z.p.X 24 = Z.p.X.H.tl := by
      unfold Meaning.tlAt
      simp
    rw [e24] at hμ ⊢
    rw [(VerifiableInference.Desc.Kinds.Head.Law.InScope.plan_in_scope hS hR hpub).nm] at hμ
    exact VerifiableInference.Desc.K1.HeadNames.names_tie_head_all hS hR hZ hμ

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **SmallPlan.names, TO THE LETTER, UNDER THE HEAD.** -/
theorem names_all (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) :
    ∀ μ, μ < (Meaning.tlAt (P5J.At.X Zp) l).NM →
      Xl.arrayOf[(Meaning.tlAt (P5J.At.X Zp) l).gtTree.getD μ 0]? =
        some (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ),
          Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ))) := by
  intro μ hμ
  obtain ⟨pp, hR⟩ := IM.reads_of_scope h.scope
  rw [Meaning.K2.built_arr hG e3]
  exact names_plain h.scope hR h.laid.pub hl hμ

/-- **SmallPlan.lawful, TO THE LETTER, UNDER THE HEAD.** -/
theorem lawful_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    reqLayoutOk (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) = true :=
  Meaning.K2.pub_layoutOk h.laid.pub

/-- SmallPlan from its third field alone, under the head. -/
theorem smallPlan_of_mats (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {L₀ : VerifiableInference.Desc.K12.Door.Laid}
    (mats : ∀ μ, μ < (Meaning.tlAt (P5J.At.X Zp) l).NM → ∀ A,
      VerifiableInference.Desc.arrayOf (P5J.At.layout Zp)
        (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ))
        (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ))) = some A →
      MatPlan (P5J.At.foldD Zp cF L₀) ((P5J.At.N Zp cF).group l) (P5J.At.arr Zp) (P5J.At.num Zp) l 2
        ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)
        (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ)) A) :
    SmallPlan Zp cF L₀ l Xl :=
  ⟨names_all h hG hl e3, lawful_at h, mats⟩

/-- **THE FIELD small OF K8LeftT, TO THE LETTER, FROM THE HEAD, FoldFacts AND mats.** -/
theorem small_of_mats (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF L₀) P5J.At.reqW P5J.At.links P5J.At.ps)
    (mats : ∀ μ, μ < (Meaning.tlAt (P5J.At.X Zp) l).NM → ∀ A,
      VerifiableInference.Desc.arrayOf (P5J.At.layout Zp)
        (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ))
        (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ))) = some A →
      MatPlan (P5J.At.foldD Zp cF L₀) ((P5J.At.N Zp cF).group l) (P5J.At.arr Zp) (P5J.At.num Zp) l 2
        ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)
        (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ)) A) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) w,
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      TieAt (cellsAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
        (z, a.1)) a.1 w →
      (mgAtAll h).constr l .small (z, a.1) (strsOf Fr a.2) w :=
  small_of_plan h hG hl e3 hRch FF (smallPlan_of_mats h hG hl e3 mats)

end

end K8Q35

-- the head's link's tie bears no ask of its own in its files: asked here
#print axioms VerifiableInference.Desc.K1.HeadNames.names_tie_head
#print axioms VerifiableInference.Desc.K1.HeadNames.names_tie_head_all
#print axioms K8Q35.names_plain
#print axioms K8Q35.names_all
#print axioms K8Q35.lawful_at
#print axioms K8Q35.smallPlan_of_mats
#print axioms K8Q35.small_of_mats
