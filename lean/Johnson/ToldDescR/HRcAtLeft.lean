-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/HRcAtLeft.lean: no soundness is claimed.
hRc at the one head (P5J.AtMg, Johnson/P5J/AtMg.lean), with h₄ called: rcLastB 0 (vAt Zp N₁) L (p14At Zp).codes at the first chain's reached ends. The layer above Book.hRc_at_head (Johnson/Desc/Book/RcAtHead.lean), which has the scope, the opening, the test on the list of rounds and the five facts off the head and leaves h₃ (ownSitsB) and h₄ (sampleTwoB) as premises.
  lt_of_sampleAtB        where the test accepts the message number o, that message is there
  **sampleTwoB_in**      sampleTwoB at one reached end s, from facts at s itself (ownSitsB · bookFitsB · seatsCarriedB L · as many places as messages) and two look-ups in the list L: so that what is had inside the first table's last promise can be handed in (sampleTwoB_h4_paid's hEnd asks its four facts of every reached end, with no promise in front)
  **hRc_at_left**        the head h · hB · hL (Book.hRc_at_head's two) · h₃ · six closed facts ⇒ ∀ q y, Oc q y → (EndAt₁ (F0T …) q ∧ K q) → q.2.failed = none → rcLastB 0 (vAt Zp N₁) L (p14At Zp).codes q.2 = true. Oc · K · N₁ are letters: at Oc := ocEnd …, K := the typed instance, N₁ := At.N Zp cF it is the field hRc of AtMgA.LastLeft (Johnson/P5J/L0/LastFreeT.lean), whose getL is (a.1, a.2) [by reading: that file is not imported]
The six closed facts: hc : cutOf cF.blocksInOrder = cutFirstFull (hCount_paid | hCount₂_paid, Johnson/IMR/CountsAtTwo.lean, ask it) · sendsPlanB Zp = true · L.places[4]? = some N₁.index · L.places[197]? = some N₁.w · SampleStep at vAt's two shapes (a join of sampleL_at_index | sampleL_at_W, Johnson/IMR/SampleAtW.lean, under madeRow).
Called: Book.hRc_at_head · IM.hCount_paid | hCount₂_paid · Meaning.K2.five_at_end_planOk · this folder's e1_of_first | e2_of_send | sampleAtB_at_send | hP_of_sendsPlanB | open_smpStay | open_planOk | back_smpStay | sampleTwoB_last_end | flat_358 | handsBackB_below.
The full size alone (4 · 197 · 358 are written). Does not show. h₃ · hB · the six. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.PlanAtSendB
import Johnson.ToldDescR.EndIs358
import Johnson.Desc.Book.RcAtHead
import Johnson.IMR.CountsAtTwo
import Johnson.LLT25R.LastAt
import Johnson.Desc.K12.Door.DoorGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open Meaning.K2
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB place_of_seats)
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)

theorem lt_of_sampleAtB {cs : Codes} {sh : OracleShape} {St : Statement} {o : ℕ}
    (h : sampleAtB cs sh St o = true) : o < St.oracles.size := by
  unfold sampleAtB at h
  cases hx : St.oracles[o]? with
  | none => rw [hx] at h; cases h
  | some x => exact (Array.getElem?_eq_some_iff.1 hx).1

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **sampleTwoB at one reached end, from facts at that end.** -/
theorem sampleTwoB_in (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : F.planOk = true)
    {Pp : Type} {Rch : ℕ → Pp × S → Prop} (hb : HandsBackB c.blocksInOrder Rch) {cs : Codes}
    {V : OwnSeats} {n₀ kI nW : ℕ} {L : Laid}
    (hLI : L.places[n₀ + kI]? = some V.index) (hLW : L.places[nW]? = some V.w)
    (hCount : ∀ z s₁, Rch 356 (z, s₁) → s₁.failed = none → s₁.st.oracles.size = nW)
    (hCount₂ : ∀ z s b ft rs cols s' n, Rch 2 (z, s) → c.blocksInOrder[2]? = some b →
      b.step ft s rs cols = .ok (s', n) → s'.failed = none → s.st.oracles.size = n₀)
    (hP₁ : PlanAtSend (K1.firstPar Bs.G₀.first (K1.gpOf Z)) cs V.indexShape kI)
    (hP₂ : ∀ msg, linMessageW Z.first.lin = some msg → PlanAtSend
      (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg) cs V.wShape 0)
    (hL₁ : ∀ o, P2Law.SampleStep cs V.indexShape o) (hL₂ : ∀ o, P2Law.SampleStep cs V.wShape o)
    {z : Pp} {s : S} (h : Rch 358 (z, s)) (hO : ownSitsB V s = true)
    (hB : bookFitsB s.book = true) (hSe : seatsCarriedB L s.book = true)
    (hSz : s.book.place.size = s.st.oracles.size) : sampleTwoB cs V s = true := by
  have hf := open_smpStay hF O
  have hq := open_planOk O hp
  have E₁ := e1_of_first hS hR O hb hCount₂ (cs := cs) (sh := V.indexShape) (kI := kI)
    (fun owed d₁ r₁ r₂ ids d₂ hfit hok hyes =>
      sampleAtB_at_send hP₁ owed d₁ d₂ r₁ r₂ ids hfit hok hyes (hL₁ _)) z
  have E₂ := e2_of_send hS hR O hb hCount (cs := cs) (sh := V.wShape)
    (fun msg s r₁ r₂ ids d' hm hfit hok hyes =>
      sampleAtB_at_send (hP₂ msg hm) _ _ d' r₁ r₂ ids hfit hok hyes (hL₂ _)) z
  have a1 : sampleAtB cs V.indexShape s.st (n₀ + kI) = true := by
    obtain ⟨s₀, r0, w⟩ := back_smpStay hb.plain hf hq 3 355 s h
    exact sampleAtB_stay (E₁ s₀ r0) w
  have a2 : sampleAtB cs V.wShape s.st nW = true := by
    obtain ⟨s₀, r0, w⟩ := back_smpStay hb.plain hf hq 357 1 s h
    exact sampleAtB_stay (E₂ s₀ r0) w
  have hI : s.book.place[n₀ + kI]? = some V.index := by
    rw [place_of_seats hSe _ (by rw [hSz]; exact lt_of_sampleAtB a1)]
    exact hLI
  have hW : s.book.place[nW]? = some V.w := by
    rw [place_of_seats hSe _ (by rw [hSz]; exact lt_of_sampleAtB a2)]
    exact hLW
  exact sampleTwoB_last_end hb.plain hf hq h hO hB hI hW 2 (by decide) E₁ E₂

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}

/-- **hRc at the one head, h₄ called.** -/
theorem hRc_at_left (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      K12.Door.sendsAreB Zp.made.proof.1 358 (K12.Door.snAt Zp Bs.G₀ IM.placesW) = true)
    {L : Laid} (hL : K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some L)
    {Str : Type} (N₁ : First.Numbers) (K : ProofFile.InstPub × S → Prop)
    (Oc : ProofFile.InstPub × S → Str → Prop)
    (h₃ : ∀ q y, Oc q y → (EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q) →
      q.2.failed = none → ownSitsB (LLT25.vAt Zp N₁) q.2 = true)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull)
    (hPl : sendsPlanB Zp = true) (hLI : L.places[4]? = some N₁.index)
    (hLW : L.places[197]? = some N₁.w)
    (hL₁ : ∀ o, P2Law.SampleStep (p14At Zp).codes (LLT25.vAt Zp N₁).indexShape o)
    (hL₂ : ∀ o, P2Law.SampleStep (p14At Zp).codes (LLT25.vAt Zp N₁).wShape o) :
    ∀ q y, Oc q y → (EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q) →
      q.2.failed = none → rcLastB 0 (LLT25.vAt Zp N₁) L (p14At Zp).codes q.2 = true := by
  refine Book.hRc_at_head h hB hL _ _ K Oc h₃ ?_
  intro q y ho hq hm
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hfl := open_planOk O h.laid.planOk
  have e : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) cF.blocksInOrder.length q := hq.1
  have H := five_at_end_planOk h.scope O h.laid.planOk (hB Bs base _ _ O) hL q e hm
  have e8 : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 358 (q.1, q.2) := by
    rw [flat_358 h.scope h.reads O] at e
    exact e
  obtain ⟨hP₁, hP₂⟩ := hP_of_sendsPlanB O hPl
  exact sampleTwoB_in h.scope h.reads h.laid.value O h.laid.planOk
    (handsBackB_below 0 cF.blocksInOrder (ProofFile.startS Zp)) (V := LLT25.vAt Zp N₁) (n₀ := 0) (kI := 4)
    (nW := 197) hLI hLW (IM.hCount_paid h.scope h.reads O hfl hc)
    (IM.hCount₂_paid h.scope h.reads O hfl hc) hP₁ hP₂ hL₁ hL₂ e8 (h₃ q y ho hq hm) H.2.1
    H.2.2.2.2 H.2.2.1

end

end ToldDesc

#print axioms ToldDesc.sampleTwoB_in
#print axioms ToldDesc.hRc_at_left
