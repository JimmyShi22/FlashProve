-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/ItemJoinAtLetters.lean: THE ITEMS' CLAUSE AT THE LOOKUP ARGUMENT's ENTRY (2, "join")
(the field k3i of `HitemsLeft`, Johnson/LPFE1R/HitemsAtConst.lean) AT THE TWELVE ATTENTION LINKS OF
THE CLOSED CONSTANT, IN THE LETTERS OF K9's LAST JOIN, WITH THREE OF ITS PAYER's PREMISES LAID IN.
The sister of ItemPlanesAtLetters.lean. Theorems: a tie, and one call with bridges.


Where the payment lies. In another file: k3i_join_att_at (Johnson/P1K9R/ItemJoinAt.lean). Its
premises: hK (the promise gives K3's), hAt (the lookup's bare run at the attention's own keys
STANDS at (2, "join")), hQ (the promise gives the attention's own promise on what it heard), ok
(the promise holds of what is fixed in front of the batching).

BY WHICH NAMED THEOREMS THEY ARE LAID IN. hAt: `at_join`, here: from K5's files' own
K05_join_of_open (Johnson/H2K5R/JoinAtOpen.lean: what "find?" finds under "join" in what the seated
link's block 2 states) and K9.lookup_of_find; its premises Bs.G₀.W.p4 = true and g < Bs.G₀.W.NGr:
att_facts (LookAttAtMg.lean: from the scope); that L is the chain's link: link_of_lk
(SortTiesAtMg.lean) · hK: kxAtt_k3 (SortLetters4.lean) · hQ: the named Ok's own field k5. NONE OF
THE THREE STAYS A PREMISE.

What is said. `at_join`: **At L (2, "join") (K3.joinRun (K3.seatCalls K3Lot.ofForm) (keysOfO a))**
(SortK3Join.lean's at_join_is says: whatever stands there IS that run; this says: it stands there)
· `k3i_join_att_g`: from h, O, g < 12, the sort, the link, that it is a segment, the plan A at g,
AND ok AT THE PROMISE fun q => OkAtt rdAll (parCOf A) nU tlD q ∧ kxAtt lmC jC lmD jD (parCOf A) nU
q: **ItemIn L (phiAll u psiAll) (tmA rdAll (parCOf A) entUnit tmFour (t3All lmC jC lmD jD (bvAtt A)
(pvAtt A) (kvAtt A))) (lenA rdAll (parCOf A) (l3All lmC jC lmD jD)) (h.𝔇.Rd (2 * g + 1))
(h.𝔇.N.group (2 * g + 1)) rdW a w (2, "join")** at every state a of the condition in front of the
batching.

Limits. BOOK-KEEPING ON LETTERS AND PREMISES. ok IS A PREMISE (ok0_att_hd2
ends in it). lmC, jC, lmD, jD, nU, u, tlD are letters. The head and the opening are premises.
secondHashFunction alone. Nothing on soundness.

-/
import Johnson.P1K9R.ItemJoinAt
import Johnson.Desc.First.Batch.ObjectsLawOrder
import Johnson.LPFK9R.LookAttAtMg
import Johnson.Desc.First.Link.Law.SortLetters4

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.First.Att.P (keysOfO K05_join_of_open)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound (MsgQ)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.OnPublicFiles (bvAtt pvAtt kvAtt)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMg AtMgA)

/-- **THE LOOKUP's BARE RUN AT THE ATTENTION's OWN KEYS STANDS AT (2, "join").** -/
theorem at_join {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
    (h4 : Bs.G₀.W.p4 = true) {g : ℕ} (hg : g < Bs.G₀.W.NGr) {a : Attention.Plan}
    (ha : Bs.G₀.W.A[g]? = some a) {L : Link S Claim} (hL : c.links[2 * g + 1]? = some L) :
    At L (2, "join")
      (VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm)
        (keysOfO a)) := by
  obtain ⟨Lk, h1, h2⟩ := K05_join_of_open O h4 hg ha
  obtain rfl : Lk = L := Option.some.inj (h1.symm.trans hL)
  unfold VerifiableInference.Desc.K9.statesOfLink at h2
  show ((Lk.hear[2]?).bind fun b => b.claims.lookup "join") = some _
  cases hb : Lk.hear[2]? with
  | none =>
    rw [hb] at h2
    exact nomatch h2
  | some b =>
    rw [hb] at h2
    exact (VerifiableInference.Desc.K9.lookup_of_find "join" _ _ h2).1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **THE ITEMS' CLAUSE AT (2, "join") AT THE ATTENTION LINK 2 g + 1, IN THE JOIN's LETTERS.** -/
theorem k3i_join_att_g (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hs : subAt (2 * g + 1) = .attention) (L : Link S Cl) (hlk : h.𝔇.lk (2 * g + 1) = some L)
    (seg : SegAt (2 * g + 1) (subAt (2 * g + 1)) L) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) (lmC jC lmD jD : ℕ) (nU : Array ℕ) (u tlD : HTailF2)
    (z : ProofFile.InstPub) {W : Type} (rdW : W → ℕ × ℕ → MsgQ)
    (ok : ∀ a, on0At h z (2 * g + 1) a → (fun q => OkAtt rdAll (P.parCOf A) nU tlD q ∧ kxAtt lmC jC
      lmD jD (P.parCOf A) nU q) (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z (2 * g + 1) a →
      ItemIn L (phiAll u psiAll)
        (tmA rdAll (P.parCOf A) entUnit tmFour
          (t3All lmC jC lmD jD (bvAtt A) (pvAtt A) (kvAtt A)))
        (lenA rdAll (P.parCOf A) (l3All lmC jC lmD jD)) (h.𝔇.Rd (2 * g + 1))
        (h.𝔇.N.group (2 * g + 1)) rdW a w (2, "join") := by
  have hm : 2 * g + 1 < 25 := by omega
  obtain ⟨h4, g', hg', e, _⟩ := att_facts h O (2 * g + 1) hm hs
  obtain rfl : g = g' := by omega
  rw [hs] at seg
  exact k3i_join_att_at (Ok := (fun q => OkAtt rdAll (P.parCOf A) nU tlD q ∧ kxAtt lmC jC lmD jD
    (P.parCOf A) nU q)) h z hm hs hlk seg (fun q hq => kxAtt_k3 q hq.2) A
    (at_join O h4 hg' hA (link_of_lk h O (2 * g + 1) L hlk))
    (fun q v g₁ h₁ hq hv hr => hq.1.k5 v g₁ h₁ hv hr) rdAll (P.parCOf A) rdW ok

end LPFK9

#print axioms LPFK9.at_join
#print axioms LPFK9.k3i_join_att_g
