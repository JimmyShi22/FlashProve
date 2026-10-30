-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/ItemPlanesAtLetters.lean: THE ITEMS' CLAUSE AT THE LOOKUP ARGUMENT's ENTRY "planes"
(the field k3i of `HitemsLeft`, Johnson/LPFE1R/HitemsAtConst.lean) AT THE TWELVE ATTENTION LINKS
AND THE HEAD's LINK OF THE CLOSED CONSTANT, IN THE LETTERS OF K9's LAST JOIN, WITH FOUR OF ITS
PAYER's PREMISES LAID IN. Theorems: one call each, with bridges.

Whose the payment is. Another file's: k3i_planes_att_at, k3i_planes_head_at
(Johnson/P1K9R/ItemPlanesAt.lean). Their premises: hr (the lot's readers at the link), hlm (the
calls' lookup's place's lm is lmC), hK (the promise gives K3's), at attention hQ (the promise gives
the attention's own promise on what it heard), ok (the promise holds of what is fixed in front of
the batching).

What is laid in here. hr: at attention K5's files' readersAt_att (K5RestOpen.lean), with att_facts
(LookAttAtMg.lean); at the head readersAt_head (SortK3PlanesRun.lean), with
"link 24 is the head's" from the scope (head_24) and the number of the reads' array from the ties
(ties_head_mg) · hlm: lmC := the place's own lm · hK: kxAtt_k3, kxHead_k3 (SortLetters4.lean) · hQ:
the named Ok's own field k5. The public parameters are read at P5J.At.X Zp there and at Bs.G₀.W
here: one value, by the opening.

What is said. `k3i_planes_att_g`: from h, O, g < 12, the sort, the link, that it is a segment, the
plan A at g, the place pC, AND ok AT THE PROMISE fun q => OkAtt rdAll (parCOf A) nU tlD q ∧ kxAtt
pC.lm jC lmD jD (parCOf A) nU q: **ItemIn L (phiAll u psiAll) (tmA rdAll (parCOf A) entUnit tmFour
(t3All pC.lm jC lmD jD (bvAtt A) (pvAtt A) (kvAtt A))) (lenA rdAll (parCOf A) (l3All pC.lm jC lmD
jD)) (h.𝔇.Rd (2 * g + 1)) (h.𝔇.N.group (2 * g + 1)) rdW a w (1, "planes")** at every state a of
the condition in front of the batching · `k3i_planes_head_24`: the like at (2, "planes"), at tmH,
lenH at W.hS, readsOf W, parOf W.hS (workOf W), kapAll, bvHead, pvHead (readsOf W), kv free, under
ok at OkHead .. ∧ kxHead ...

Limits. BOOK-KEEPING ON LETTERS AND PREMISES. ok IS A PREMISE (ok0_att_hd2,
ok0_head_hd2 end in it). jC, lmD, jD, nU, u, tlD are letters. The head and the opening are
premises. secondHashFunction alone. Nothing on soundness.

-/
import Johnson.P1K9R.ItemPlanesAt
import Johnson.LPFK9R.OwesAtLetters
import Johnson.Desc.First.Link.Law.SortLetters4

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (readsOf workOf)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (head_24)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound (MsgQ)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.EntryUnit (entUnit)
open VerifiableInference.OnPublicFiles (bvAtt pvAtt kvAtt bvHead pvHead readersAt_head)
open H2K5.Door (readersAt_att)
open OnBytes.Maker (WholeD)
open ProofFile (Cl)
open IM (Open subAt)
open P5J (AtMg AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place} {F : FileDescription ProofFile.Inst}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **THE ITEMS' CLAUSE AT (1, "planes") AT THE ATTENTION LINK 2 g + 1, IN THE JOIN's LETTERS.** -/
theorem k3i_planes_att_g (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hs : subAt (2 * g + 1) = .attention) (L : Link S Cl) (hlk : h.𝔇.lk (2 * g + 1) = some L)
    (seg : SegAt (2 * g + 1) (subAt (2 * g + 1)) L) {A : Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {pC : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (jC lmD jD : ℕ) (nU : Array ℕ)
    (u tlD : HTailF2) (z : ProofFile.InstPub) {W : Type} (rdW : W → ℕ × ℕ → MsgQ)
    (ok : ∀ a, on0At h z (2 * g + 1) a → (fun q => OkAtt rdAll (P.parCOf A) nU tlD q ∧ kxAtt pC.lm
      jC lmD jD (P.parCOf A) nU q) (fixed9 (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z (2 * g + 1) a →
      ItemIn L (phiAll u psiAll)
        (tmA rdAll (P.parCOf A) entUnit tmFour
          (t3All pC.lm jC lmD jD (bvAtt A) (pvAtt A) (kvAtt A)))
        (lenA rdAll (P.parCOf A) (l3All pC.lm jC lmD jD)) (h.𝔇.Rd (2 * g + 1))
        (h.𝔇.N.group (2 * g + 1)) rdW a w (1, "planes") := by
  obtain ⟨h4, _, _, _, _⟩ := att_facts h O (2 * g + 1) (by omega) hs
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  rw [eW] at h4 hA
  exact k3i_planes_att_at (Ok := (fun q => OkAtt rdAll (P.parCOf A) nU tlD q ∧ kxAtt pC.lm jC lmD
    jD (P.parCOf A) nU q)) h z hg hlk seg A (readersAt_att h4 hA)
    (fun p hp => by obtain rfl := Option.some.inj (hC.symm.trans hp); rfl)
    (fun q hq => kxAtt_k3 q hq.2) (fun q v g' h' hq hv hr => hq.1.k5 v g' h' hv hr)
    rdAll (P.parCOf A) rdW ok

/-- **THE ITEMS' CLAUSE AT (2, "planes") AT THE HEAD's LINK, IN THE JOIN's LETTERS.** -/
theorem k3i_planes_head_24 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂)
    (hs : subAt 24 = .head) (L : Link S Cl) (hlk : h.𝔇.lk 24 = some L)
    (seg : SegAt 24 (subAt 24) L) {pC : VerifiableInference.Desc.First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (jC lmD jD : ℕ) (nU : Array ℕ)
    (kv : Phi BetaAll × Option Pub9 → Bound GE8 → ℕ → GE8) (u tlD : HTailF2) (z : ProofFile.InstPub) {W :
            Type}
    (rdW : W → ℕ × ℕ → MsgQ)
    (ok : ∀ a, on0At h z 24 a → (fun q => OkHead Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS
      (workOf Bs.G₀.W)) kapAll nU tlD q ∧ kxHead pC.lm jC lmD jD (readsOf Bs.G₀.W) nU q) (fixed9
      (phiAll u psiAll) a.1)) :
    ∀ a w, on0At h z 24 a →
      ItemIn L (phiAll u psiAll)
        (tmH Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll entUnit tmFour
          (t3All pC.lm jC lmD jD (bvHead (readsOf Bs.G₀.W)) (pvHead (readsOf Bs.G₀.W)) kv))
        (lenH Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll
          (l3All pC.lm jC lmD jD)) (h.𝔇.Rd 24) (h.𝔇.N.group 24) rdW a w (2, "planes") := by
  obtain ⟨iU3, _, hi, _, _⟩ := ties_head_mg h O 24 (by omega) hs L hlk
  have e : readsOf Bs.G₀.W = iU3 := by
    unfold readsOf
    rw [hi]
    rfl
  subst e
  obtain ⟨h4, hN⟩ := head_24 h.toAtMg.scope O.public
  have hH : VerifiableInference.Desc.K3.isHead Bs.G₀.W 24 = true := by
    unfold VerifiableInference.Desc.K3.isHead
    rw [h4, hN]
    rfl
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hr := readersAt_head hH hi
  rw [show K3Lot.readersAt Bs.G₀.W 24 = K3Lot.readersAt (P5J.At.X Zp) 24 by rw [← eW]] at hr
  exact k3i_planes_head_at (Ok := (fun q => OkHead Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS
    (workOf Bs.G₀.W)) kapAll nU tlD q ∧ kxHead pC.lm jC lmD jD (readsOf Bs.G₀.W) nU q)) h z hlk seg
    (readsOf Bs.G₀.W) hr
    (fun p hp => by obtain rfl := Option.some.inj (hC.symm.trans hp); rfl)
    (fun q hq => kxHead_k3 q hq.2) Bs.G₀.W.hS (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll rdW ok

end LPFK9

#print axioms LPFK9.k3i_planes_att_g
#print axioms LPFK9.k3i_planes_head_24
