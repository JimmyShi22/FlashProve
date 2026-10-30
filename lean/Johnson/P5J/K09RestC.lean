-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09RestC.lean: ON THE SECOND ROAD: BENEATH `AtMgA.K9ListC` (K09ListC.lean): THE SISTER
OF `AtMgA.K9Rest` (K09Rest.lean, which does not turn): the same payers at the closed constant are
laid in, by the elder proof's own text with the names turned: at a link's three pieces `LinkRestC`
(Johnson/Desc/First/Link/Law/LinkRestC.lean) in `LinkRest`'s place. The elder file's lemmas are
imported, not typed again. A definition and theorems.

What is said.
  `AtMgA.K9RestC h 𝔏`: as `K9Rest`, with `LinkRestC` (37 fields). `k9ListC_of_rest`: **`h.K9ListC
    𝔏` from it**, under the tower's own three equations on the flat lists' heads.
    `k09_kind_of_restC`: **so `h.Kind 𝔏 .K9`.**

Limits. BOOK-KEEPING. `K9RestC` IS THE DEBT; no member is known; what each payer takes is said in
the elder file's head. The count of fields is no measure. AT THE SECOND HASH FUNCTION ALONE. Nothing
on soundness.

-/
import Johnson.P5J.K09Rest
import Johnson.P5J.K09ListC
import Johnson.Desc.First.Link.Law.LinkRestC

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit Link claimsInBy)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS Where)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.LinkJoin (batchAt atRec LinkRestC linkListC_of_rest ShutRest
  shutList_of_rest linkPlanB HeadSpots lowAtB oraB_of batchIx more_batch moreFit_links h01_mgR plF
  mid_behind mid_eq midFit_links listFit_links pubFitE_links ah12_of ahon3_of smpNamed_tri tri
  SameBy letters_at_list pinB_of pinQ_of pinE_of pinsFit smpNamed_bare grp_of_facts totalIn_some
  foldFacts_at)
open VerifiableInference.Desc.First (FoldFacts)
open IM (subAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF
local notation "kAt" => batchAt fullLinks At.ps
set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

/-- **WHAT IS LEFT OF THE CONDITION.** -/
def AtMgA.K9RestC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) : Prop :=
  ∃ Ld, FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps ∧
  ∀ m < 25, ∃ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ ∧ IM.k9At Zp m = some p ∧
    (∀ X, Zp.p.built.links[m]? = some X → linkPlanB Zp m X = true) ∧ (∃ nH, HeadSpots Zp nH) ∧
    (∀ qb qq qe, (h.toAtMg.row 𝔏)[kAt m]? = some qb →
      (h.toAtMg.row 𝔏)[kAt m + 1]? = some qq → (h.toAtMg.row 𝔏)[kAt m + 1 + 1]? = some qe →
      ∃ (α : Type) (φ : _) (Ok : _) (nU : _) (tmOf : _) (lenOf : _) (d N : ℕ) (items : _) (u : _)
        (π : _) (oo : _) (run : _) (xx : _) (tlD : _) (set : _) (pp : ℕ), ∀ z,
        LinkRestC (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m α (subAt m) L φ Ok nU p
          p tmOf lenOf d N b₃ (atRec qb (below L.batchB)) (atRec qq (below L.behindB))
          (atRec qe (below b₃)) items u π oo run xx tlD set pp
          (fun j => h.𝔇.l3.seat xx.link true j.1) 0 (FD).first.blocksInOrder (FD).start₁
          (At.foldD Zp cF Ld) At.reqW) ∧
    ∀ qs, (h.toAtMg.row 𝔏)[kAt m + 4]? = some qs → ∃ Zc layF Dw,
      (∃ o pol lay KL, ProofFile.pureRoad.pub o pol lay KL = .ok Zc) ∧
      (ProofFile.pAtK2 Zc 24).stands ≠ .head ∧
      ShutRest (F := FrK) h.𝔇 (atRec qs (below b₅)) Zc layF Dw

/-- **REST → CONDITION.** -/
theorem k9ListC_of_rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9RestC 𝔏) : h.K9ListC 𝔏 := by
  obtain ⟨Ld, Fo, H⟩ := H
  intro m hm
  obtain ⟨L, p, Q, b₃, b₅, St, kp, hP, ⟨nH, hH⟩, G, G5⟩ := H m hm
  have hRows := LPFK9.rowsAtFit_at h
  have hT := h.toAtMg.low_at_batch m hm
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hx : kAt m = batchIx m :=
    of_decide_eq_true (List.all_eq_true.1 batchIx_links m (List.mem_range.2 hm))
  have hlt : kAt m + 4 + 1 < 358 := by rw [hx]; exact batch_lt m hm
  obtain ⟨⟨a0, b0⟩, ⟨a1, b1⟩, ⟨a2, b2⟩, a4, b4⟩ := borders_lt hf ps_358 hlt
  have cnt := k9_counts_at h m hm
  obtain ⟨pB, pB1, hpB, hpB1, hlB, hpcB⟩ := more_batch fullLinks At.ps moreFit_links m hm
  have cm := k9_counts_mid h m hm
  obtain ⟨pQ, pQ1, hpQ, hpQ1, hlQ, hpcQ⟩ := mid_behind fullLinks At.ps midFit_links m hm
  obtain ⟨pE, pE1, hpE, hpE1, hlE, hpcE⟩ := mid_eq fullLinks At.ps midFit_links m hm
  refine ⟨L, p, Q, b₃, b₅, St, fun qb qq qe hb hq he => ?_, fun qs hs => ?_⟩
  · obtain ⟨α, φ, Ok, nU, tmOf, lenOf, d, N, items, u, π, oo, run, xx, tlD, set, pp, K⟩ :=
      G qb qq qe hb hq he
    have ora := fun z => oraB_of h.𝔇 fullLinks At.ps z
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z) (kAt m) h.toAtMg.fence
      b0 L p (K z).share (atRec qb (below L.batchB)) rfl
      (Nat.le_of_eq (row_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m) a0 b0 qb hb).symm)
      (list_hd h z) (list_smp h z)
    have bB := Nat.le_of_eq
      (row_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m) a0 b0 qb hb).symm
    have bQ := Nat.le_of_eq
      (row_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m + 1) a1 b1 qq hq).symm
    have bE := Nat.le_of_eq
      (row_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m + 1 + 1) a2 b2 qe he).symm
    have tin := fun z => LPFK9.htin_at_const_slots (α := α) (Fr := FrK) h hm St.lk hP hH z
      (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) fun a => list_rchIs h z _ a
    have a12 := fun z => ah12_of (α := α) h.𝔇 fullLinks At.ps z
      (VerifiableInference.Desc.LinkJoin.RchAt (F := FrK) h.toAtMg.rch z) (kAt m + 1) m
      linkFit_links pubFit9_links pQ pQ1 hpQ hpQ1 hlQ hpcQ cm.1.1 cm.1.2 L p (K z).share St.movesQ
      (atRec qq (below L.behindB)) rfl (list_hand h z _ _ St.atK1 qq) h.toAtMg.fence bQ
      (list_hd h z) (list_smp h z) (tin z)
    exact ⟨α, φ, Ok, nU, tmOf, lenOf, d, N, items, u, π, oo, run, xx, tlD, set, pp,
      At.foldD Zp cF Ld, At.reqW,
      fun z => linkListC_of_rest h.𝔇 fullLinks At.ps z _ _ m α (subAt m) L φ Ok nU p p tmOf lenOf d
        N b₃ _ _ _ items u π oo run xx tlD set pp _ 0 _ _ _ _ ⟨St.drawB, St.hb₃⟩ rfl rfl rfl
        (owesCaller_at h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m) a0 _ _ _ qb qq qe hb hq he)
        (fun a τ b' ha hout => h01_mgR h.𝔇 h.𝔇.N fullLinks At.ps z _ (kAt m) m pB pB1
          linkFit_links pubFit9_links hpB hpB1 hlB hpcB cnt.1.1 cnt.1.2 L p (K z).share _ rfl
          (list_hand h z _ _ St.atK qb) (ora z) a τ b' ha.1.1 hout)
        (a12 z)
        (ahon3_of h.𝔇 fullLinks At.ps z _ (kAt m + 1 + 1) m linkFit_links listFit_links
          pubFitE_links hRows hm pE pE1 hpE hpE1 hlE hpcE cm.2.1 cm.2.2 p b₃ St.hb₃ _ rfl
          (list_hand h z _ _ St.atK2 qe)
          (fun a ha y hy => (grp_of_facts h.𝔇 mgBase fullLinks At.ps z _ (kAt m + 1 + 1) m
            (foldFacts_at Fo z) pE hpE hlE rfl a ha y hy).symm)
          h.toAtMg.fence bE (list_hd h z) (list_smpE h z) (K z).notIx)
        (letters_at_list h.𝔇 mgBase fullLinks At.ps z _ (kAt m) m L p p b₃ _ _ _ _
          (fun a ha => ha.1.1)
          (pinB_of h.𝔇 mgBase fullLinks At.ps z _ (kAt m) m h.toAtMg.fence pinsFit_links pB hpB hlB
            hpcB L p (K z).share _ rfl bB (list_smp h z))
          (pinQ_of h.𝔇 mgBase fullLinks At.ps z _ (kAt m) m h.toAtMg.fence pinsFit_links pQ hpQ hlQ
            hpcQ L p (K z).share _ rfl bQ (list_smp h z))
          (pinE_of h.𝔇 mgBase fullLinks At.ps z _ (kAt m) m h.toAtMg.fence pinsFit_links pE hpE hlE
            hpcE p b₃ St.hb₃ _ rfl bE fun s s' e => funext fun sd => funext fun i =>
              (smpNamed_bare (At.cs Zp) (At.seats Zp) z e sd i).symm)
          St.drawB (K z).share.two rfl rfl St.hb₃ rfl (K z).Ahs1 (a12 z)
          fun c hc => totalIn_some _ c.1 ((K z).tot c hc))
        (tin z) (LPFK9.hrw_at h m p kp) cnt.1.1 cnt.1.2 (ora z)
        (LPFK9.hpc_at h m) (LPFK9.hn_at h m hm) (foldFacts_at Fo z)
        (LPFK9.hall_of_moments _ _ _ _ _ m (h.toAtMg.shape_moments m)) rfl
        (pinB_of h.𝔇 mgBase fullLinks At.ps z _ (kAt m) m h.toAtMg.fence pinsFit_links pB hpB hlB
          hpcB L p (K z).share _ rfl bB (list_smp h z))
        (pinQ_of h.𝔇 mgBase fullLinks At.ps z _ (kAt m) m h.toAtMg.fence pinsFit_links pQ hpQ hlQ
          hpcQ L p (K z).share _ rfl bQ (list_smp h z))
        rfl rfl (LPFK9.hdue_at h m hm)
        (low_at_row h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m) a0 b0 qb hb (hT 0 (by simp)))
        (low_at_row h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m + 1) a1 b1 qq hq (hT 1 (by simp)))
        (low_at_row h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m + 1 + 1) a2 b2 qe he
          (hT 2 (by simp)))
        (K z)⟩
  · obtain ⟨Zc, layF, Dw, ⟨o, pol, lay, KL, hZ⟩, h24, K⟩ := G5 qs hs
    exact ⟨Zc, layF, Dw, fun z => shutList_of_rest h.𝔇 fullLinks At.ps z _ (kAt m + 4) m hm
      links_eq ps_eq
      (by rw [hx]) h.toAtMg.fence b4 p (Q.piece + 1) b₅ St.hb₅ _ rfl
      (base_atRec h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m + 4) a4 b4 qs hs (below b₅))
      (list_hd h z) (list_smp h z) Zc hZ h24
      (lowS_at h.toAtMg 𝔏 q₁ q₂ q₃ (kAt m + 4) a4 b4 qs hs (below b₅)
        (hT 4 (by simp)))
      cnt.2.1 cnt.2.2 layF Dw _ _ (foldFacts_at Fo z) rfl K⟩

/-- **SO THE FIELD, UNDER THE THREE EQUATIONS ALONE.** -/
theorem k09_kind_of_restC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9RestC 𝔏) : h.Kind 𝔏 .K9 :=
  k09_kind_of_listC h 𝔏 q₁ q₂ q₃ (list_hlen h.toAtMg 𝔏 q₁ q₂ q₃) (k9ListC_of_rest h 𝔏 q₁ q₂ q₃ H)

end P5J

#print axioms P5J.k9ListC_of_rest
#print axioms P5J.k09_kind_of_restC
