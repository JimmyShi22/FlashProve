-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09Rest.lean: BENEATH THE BATCHING KIND's NAMED CONDITION AT THE CLOSED CONSTANT
(`AtMgA.K9List`, K09List.lean: its text does not turn): WHAT IS LEFT OF IT WHEN THE PAYERS THAT LIE
ARE LAID IN: `AtMgA.K9Rest`, with «rest → condition». Laid in: four facts on the plan (`hrw_at`,
`hpc_at`, `hn_at`, `hdue_at`, Johnson/LPFK9R/FactsAtConstant.lean); «behind the frame's move the one
sum can be taken» (`htin_at_const_slots`, HtinAtConstantSlots.lean); what the riders on the oracles
take over the batching and over the shutting (`oraB_of`, `oraS_of`, OraPaid.lean, with
`AtMg.fence`, Johnson/P5T/FenceAtMg.lean, and `row_base_at`, K09Cap.lean); «the riders lie low» at
the four pieces (`low_at_row`, `lowS_at`, with `AtMg.low_at_batch`,
Johnson/P5T/LowAtMg.lean: the test at the plan's own numbers, from the head); the shutting's facts
on the state and on the head (`hS_paid`, `hNH_paid`, through ShutRest.lean); the plan's two counts
stand still over the batching's and the shutting's places (`k9_counts_at`, K09Counts.lean); OF THE
LAW's PREMISE A (`LinkOwes`), CUT INTO ITS PARTS IN LinkRest.lean: the blocks (from `Sits`), what
the three pieces hold (by the making), the caller (`owesCaller_at`, K09Cap.lean) ITS THREE HAND-ONS
OF THE PROMISE (over the batching: `h01_mgR`, RidesAtMgR.lean; over the frame's sub-protocol behind
it and over the one equation: `ah12_of`, `ahon3_of`, HandsPaid.lean, with `k9_counts_mid`,
K09CountsMid.lean, K09Mid.lean's closed facts and `rowsAtFit_at`,
Johnson/LPFK9R/RowsAtFitAt.lean) and its list «letters», the three rides of the context among them
(`letters_at_list`, LettersAtList.lean, with `pinB_of`, `pinQ_of`, `pinE_of`,
PinsPaid.lean, which also pay the list's own pinB and pinQ); THE FACTS ALONG THE FOLD, ASKED ONCE,
IN THE ONE HEAD's OWN FORM, at the data of the fold (`At.foldD`, FoldAt.lean) and
carried to every public part (`foldFacts_at`, FoldComap.lean): with them the ties of the fold's data
to the plan hold by definition, and «every message of the link is among its own at moment 3» by
`hall_of_moments` and `AtMg.shape_moments`; «no fewer pieces than places» (`list_hlen`,
K09Len.lean). A definition and theorems.

What is said.
  `sits_kp`: **at every link there are letters that sit there (`AtMgA.Sits`) whose numbers p are the
    plan's own (`IM.k9At Zp m = some p`).** `list_smp`: the reader of the OOD samples answers alike
    at two states with one statement. `AtMgA.K9Rest h 𝔏`: THERE IS A LAID LIST Ld WITH THE FACTS
    ALONG THE FOLD (`FoldFacts h.rch (·.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps`: kind-free:
    the form of the field «fold» of `AtMgR`), and at every link there are letters
    that sit there, with p the plan's own, and: the link's plan fits (a test with code,
    `linkPlanB`); the head's spots (`∃ nH, HeadSpots Zp nH`: a sentence on the public part); at the
    three pieces: there are the law's letters with `LinkRest` (LinkRest.lean: 35 fields) at every
    public part; at the shutting's piece: there are letters, Zc made by the road's own maker of the
    public data, the switch that spends «carry 24» not at the head, with `ShutRest` (ShutRest.lean:
    four fields, none on a state). `k9List_of_rest`: **`h.K9List 𝔏` from it**, under the tower's
    own three equations on the flat lists' heads. `k09_kind_of_rest`: **so `h.Kind 𝔏 .K9`.**

Limits. BOOK-KEEPING. `K9Rest` IS THE DEBT; a payer may put other debts in a field's place (htin:
two sentences on the public part; hS: the facts along the fold: A STRUCTURE OF 26 SENTENCES ON EVERY
REACHED STATE, WHICH IS NOT PROVED WHOLE); IN `LinkRest` THERE STILL STAND, BY NAME, THE KINDS'
LAWS ON THEIR RUNS (Aruns); no member is known; no test named here has run in Lean; the count of
fields is no measure. AT THE SECOND HASH FUNCTION ALONE. Nothing on soundness.

-/
import Johnson.P5J.K09List
import Johnson.P5J.K09Len
import Johnson.Desc.First.Link.Law.LinkRest
import Johnson.LPFK9R.FactsAtConstant
import Johnson.LPFK9R.RowsAtFitAt
import Johnson.LPFK9R.HtinAtConstantSlots
import Johnson.Desc.First.Link.Law.ShutRest
import Johnson.P5J.K09ShutPaid
import Johnson.P5T.FenceAtMg
import Johnson.P5T.LowAtMg
import Johnson.P5T.ShapeAtMg
import Johnson.LPFK9R.HallOfMoments
import Johnson.P5J.FoldAt
import Johnson.Desc.First.Link.Law.FoldComap
import Johnson.P5J.K09Counts
import Johnson.P5J.K09CountsMid
import Johnson.Desc.First.Link.Law.HandsPaid
import Johnson.Desc.First.Link.Law.K09Mid
import Johnson.Desc.First.Link.Law.LettersAtList
import Johnson.Desc.First.Link.Law.PinsPaid

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
open VerifiableInference.Desc.LinkJoin (batchAt atRec LinkRest linkList_of_rest ShutRest
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

/-- **LETTERS THAT SIT AT THE LINK, WITH THE PLAN's OWN NUMBERS.** -/
theorem sits_kp (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) (hm : m < 25) :
    ∃ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ ∧ IM.k9At Zp m = some p := by
  obtain ⟨L, p, Q, hlk, hp, _, hs⟩ := LPFK9.sits_at_constant h.toAtMg m hm
  have hk : kAt m = 14 * m + L.hear.length + 2 := by rw [LPFK9.batchAt_full m hm, hs.hear]
  obtain ⟨b₃, _, h3, _, h3'⟩ := hs.equation
  obtain ⟨b₅, _, h5, _, h5'⟩ := hs.shut
  exact ⟨L, p, Q, b₃, b₅, ⟨LPFK9.fullLinks_sub m hm, hlk, LPFK9.segAt_of_sits hs,
    by rw [hk]; exact hs.flat, by rw [hk]; exact hs.flat₂, hs.draw, hs.behind,
    by rw [hk]; exact h3, h3', by rw [hk]; exact h5, h5'⟩, hp⟩

/-- **WHAT IS LEFT OF THE CONDITION.** -/
def AtMgA.K9Rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) : Prop :=
  ∃ Ld, FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps ∧
  ∀ m < 25, ∃ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ ∧ IM.k9At Zp m = some p ∧
    (∀ X, Zp.p.built.links[m]? = some X → linkPlanB Zp m X = true) ∧ (∃ nH, HeadSpots Zp nH) ∧
    (∀ qb qq qe, (h.toAtMg.row 𝔏)[kAt m]? = some qb →
      (h.toAtMg.row 𝔏)[kAt m + 1]? = some qq → (h.toAtMg.row 𝔏)[kAt m + 1 + 1]? = some qe →
      ∃ (α : Type) (φ : _) (Ok : _) (nU : _) (tmOf : _) (lenOf : _) (d N : ℕ) (items : _) (u : _)
        (π : _) (oo : _) (run : _) (xx : _) (tlD : _) (set : _) (pp : ℕ), ∀ z,
        LinkRest (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m α (subAt m) L φ Ok nU p
          p tmOf lenOf d N b₃ (atRec qb (below L.batchB)) (atRec qq (below L.behindB))
          (atRec qe (below b₃)) items u π oo run xx tlD set pp
          (fun j => h.𝔇.l3.seat xx.link true j.1) 0 (FD).first.blocksInOrder (FD).start₁
          (At.foldD Zp cF Ld) At.reqW) ∧
    ∀ qs, (h.toAtMg.row 𝔏)[kAt m + 4]? = some qs → ∃ Zc layF Dw,
      (∃ o pol lay KL, ProofFile.pureRoad.pub o pol lay KL = .ok Zc) ∧
      (ProofFile.pAtK2 Zc 24).stands ≠ .head ∧
      ShutRest (F := FrK) h.𝔇 (atRec qs (below b₅)) Zc layF Dw

/-- The reader of the OOD samples answers alike at two states with one statement. -/
theorem list_smp (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) :
    ∀ s s' : S, s'.st = s.st → h.𝔇.smp (z, s') = h.𝔇.smp (z, s) :=
  fun s s' e => funext fun sd => funext fun i =>
    smpNamed_same (At.cs Zp) (At.seats Zp) (z, s) (z, s') e sd i

/-- The like at two states whose statements agree in each message's shape, mark and sample rows. -/
theorem list_smpE (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (z : ProofFile.InstPub) :
    ∀ s s' : S, SameBy tri s.st s'.st → s'.book = s.book → h.𝔇.smp (z, s') = h.𝔇.smp (z, s) :=
  fun s s' e _ => funext fun sd => funext fun i =>
    smpNamed_tri (At.cs Zp) (At.seats Zp) (z, s) (z, s') e sd i

set_option maxRecDepth 1000000 in
/-- An elder Bool on the written list, at the term `fullLinks` (MeansQ.lean), by the kernel. -/
theorem pinsFit_links : pinsFit fullLinks (flatPlacesOf fullLinks true) = true := by
  decide +kernel

/-- The written fullLinks and At.ps are the law's own (stated once: each costs an evaluation). -/
theorem links_eq : fullLinks = linksFull := rfl

theorem ps_eq : At.ps = plF := rfl

/-- The borders' inequalities, at bare numbers (so that no decision procedure meets the lists). -/
theorem borders_lt {k a b : ℕ} (ha : a = 358) (hb : b = 358) (h : k + 4 + 1 < 358) :
    (k + 1 < a ∧ k ≤ b) ∧ (k + 1 + 1 < a ∧ k + 1 ≤ b) ∧ (k + 1 + 1 + 1 < a ∧ k + 1 + 1 ≤ b) ∧
      (k + 4 + 1 < a ∧ k + 4 ≤ b) := by
  subst ha hb
  omega

/-- **REST → CONDITION.** -/
theorem k9List_of_rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9Rest 𝔏) : h.K9List 𝔏 := by
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
      fun z => linkList_of_rest h.𝔇 fullLinks At.ps z _ _ m α (subAt m) L φ Ok nU p p tmOf lenOf d
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
theorem k09_kind_of_rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9Rest 𝔏) : h.Kind 𝔏 .K9 :=
  k09_kind_of_list h 𝔏 q₁ q₂ q₃ (list_hlen h.toAtMg 𝔏 q₁ q₂ q₃) (k9List_of_rest h 𝔏 q₁ q₂ q₃ H)

end P5J

#print axioms P5J.sits_kp
#print axioms P5J.list_smp
#print axioms P5J.list_smpE
#print axioms P5J.pinsFit_links
#print axioms P5J.borders_lt
#print axioms P5J.links_eq
#print axioms P5J.ps_eq
#print axioms P5J.k9List_of_rest
#print axioms P5J.k09_kind_of_rest
