-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/AllFrontAtAll.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: `AllFront`
(Johnson/Desc/K8/Honest/LeftAtLink.lean) AT ALL 25 SEGMENTS, IN THREE FORMS: AT EVERY STATE THAT THE
FIRST CHAIN's BLOCKS WITH THE TEST ON WORDS IN FRONT (`Sound.below`) REACH IN FRONT OF A SEGMENT's
BATCHING · UNDER THE LIBRARY's HEAD `P5J.AtMgA` ALONE · ALONG EVERY PROOF TO WHICH THE VERIFIER's
GATE SAYS YES. Three joinings of the 24 segments' laws with the head's segment's; none of the
library's goals.

  **`allFront_at_all`** the scope · the files read · an opening of the description · its test on its
                   plan · l < 25 · the built segment · a state that the wrapped blocks reach at 14 l
                   + (if l = 24 then 11 else 9) ⊢ there are tl, G, g, nbW, Wn with s.tl? = some tl,
                   s.fork? = some G, tl.heard = some g and AllFront tl G g nbW Wn
  **`allFront_at_all_head`** the head · l < 25 · such a state ⊢ the same
  **`allFront_at_all_accept`** the scope · a yes of theProofGate at (z, v₁, v₂, v₃) ⊢ the files'
                   reading, an opening, a yes of the description's run, that run's own list of
                   states st (each st k steps to st (k + 1) by the block number k with the test on
                   words in front, k < 358), and the same at st (14 l + (if l = 24 then 11 else 9)),
                   for each l < 25
By: `allFront_at_wrapped_shown` (NamesAtBatch.lean: l < 24) · `allFront_at_head_seg`
(AllFrontAtHeadSeg.lean: l = 24) · the head's fields · the library's IM.member_path
(Johnson/IMR/MemberPath.lean), LPFD.Full.planOk_of_run, IM.ground_gets.
WRITTEN A FURTHER TIME: the second and the third are `allFront_at_head` (NamesAtHead.lean) and
`allFront_at_accept` (NamesAtAccept.lean) with l < 25 in the stead of l < 24: they hold these as
cases.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
four lines, on numbers of segments and borders alone.
Limits. THAT THE GATE SAYS YES TO ANY PROOF IS NOT SHOWN, from an honest prover or from anybody;
NOTHING SAYS THAT ANY STATE IS REACHED IN FRONT OF A BATCHING: where none is, all is idle. AT THE
WRAPPED FAMILY ALONE. IN SCOPE ALONE: the full size; the first chain; at OnBytes.secondHashFunction. Which of
the files beneath it are rows of the library is for the library's own list to say: it is not said
here. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.AllFrontAtHeadSeg
import Johnson.Desc.K8.Honest.NamesAtHead
import Johnson.Desc.K8.Honest.NamesAtAccept

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach StepYes)
open P5J (AtMgA)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`AllFront` AT ALL 25 SEGMENTS**, at every state that the blocks with the test on words in
front reach in front of a segment's batching. -/
theorem allFront_at_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z)
      (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ (tl : HTailF2) (G : Fork) (g : Forest.Heard) (nbW : Nat) (Wn : List HTailF2.Want),
      s.tl? = some tl ∧ s.fork? = some G ∧ tl.heard = some g ∧ AllFront tl G g nbW Wn := by
  by_cases h24 : l = 24
  · subst h24
    exact allFront_at_head_seg hS hR O hOk e3 h
  · rw [if_neg h24] at h
    exact allFront_at_wrapped_shown hS hR O hOk (by omega) e3 h

end

/-- **UNDER THE LIBRARY's HEAD ALONE, AT ALL 25.** -/
theorem allFront_at_all_head {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp)
      (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ (tl : HTailF2) (G : Fork) (g : Forest.Heard) (nbW : Nat) (Wn : List HTailF2.Want),
      s.tl? = some tl ∧ s.fork? = some G ∧ tl.heard = some g ∧ AllFront tl G g nbW Wn := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := (IM.ground_gets h.scope h.reads O.pub O.blank).1
  have e3 : Bs.G₀.built[l]? = some (Bs.G₀.built[l]'(by rw [e]; omega)) :=
    Array.getElem?_eq_getElem _
  exact allFront_at_all h.scope h.reads O h.laid.planOk hl e3 hr

/-- **ALONG EVERY ACCEPTED PROOF, AT ALL 25**: wherever the verifier's gate says yes to a proof in
scope, `AllFront` holds at that run's own state in front of each segment's batching. -/
theorem allFront_at_all_accept {P : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope P = true)
    {z : LPFD.Full.XF × OnBytes.Flat.RecFull} {v₁ v₂ v₃ : Fmt.View}
    (hg : FlashProve.theProofGate (VerifierAndGoals.asDescriptionFiles P) z v₁ v₂ v₃ = true) :
    ∃ (pp : Inst.Model.ScalesAndPolicy) (F : FileDescription ProofFile.Inst) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
      (base : List (Block S Cl)) (c : Chain S Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
      (st : ℕ → S),
      VerifierAndGoals.readFiles P = .ok pp ∧
      IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B ∧
      F.run (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ = true ∧
      st 0 = ProofFile.startS Z (LPFD.Full.instanceAsPlainRecord z).pub ∧
      (∀ k < 358, ∃ b, c.blocksInOrder[k]? = some b ∧ StepYes 0 (Sound.below b) (st k) (st (k + 1))) ∧
      ∀ l < 25, ∃ (tl : HTailF2) (G : Fork) (g : Forest.Heard) (nbW : Nat)
        (Wn : List HTailF2.Want),
        (st (14 * l + (if l = 24 then 11 else 9))).tl? = some tl ∧
          (st (14 * l + (if l = 24 then 11 else 9))).fork? = some G ∧
          tl.heard = some g ∧ AllFront tl G g nbW Wn := by
  obtain ⟨pp, F, Z, Bs, base, c, A, B, st, hR, -, O, hr, -, -, -, h0, hs, hk, -⟩ :=
    IM.member_path hS hg
  refine ⟨pp, F, Z, Bs, base, c, A, B, st, hR, O, hr, h0, hs, fun l hl => ?_⟩
  have e := (IM.ground_gets hS hR O.pub O.blank).1
  have e3 : Bs.G₀.built[l]? = some (Bs.G₀.built[l]'(by rw [e]; omega)) :=
    Array.getElem?_eq_getElem _
  exact allFront_at_all hS hR O (LPFD.Full.planOk_of_run F hr) hl e3
    (hk (14 * l + (if l = 24 then 11 else 9)) (by split_ifs <;> omega)).1

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_all
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_all_head
#print axioms VerifiableInference.Desc.First.K8.Honest.allFront_at_all_accept
