-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/DebtsLaid.lean: code switching (K2): «THE DEBTS ON THE TABLE's NUMBERS» (the
premise «D» of the three shares of «Hands»; Johnson/P1K2R/DebtsAt.lean's d_link | d_head |
d_finish) AT THE CLOSED CONSTANT's OWN NUMBERS At.N Z c, ON THE HEAD AND THREE NAMED TESTS ALONE.
  ps_written   the written list of places P5J.At.ps (Johnson/P5J/LettersAt.lean) is IM's placesW
  d_link_laid · d_head_laid · d_finish_laid  DebtsConst.lean's d_…_const with its two last premises
               paid by K2's own ties to the constant: hkeptN := AtWritten's field keptOf
               (at_written, K2Ties/WrittenAt.lean) · hT := sentFit_link | sentFit_head |
               sentFit_fin (K2Ties/SentFitAt.lean, by the kernel at the written values) over
               at_told (K2Ties/ToldAt.lean)
WHAT STANDS IN FRONT, WHOLE. THE HEAD: hS: in scope · hR: the files read · L: P5J.LaidAt at the
format's second hash function and the public files (the value is laid: it holds onlineDescription's return
and the tests on the plan) · O: an opening of that value (LaidAt's field opened holds one). THREE
NAMED TESTS: hy: madePinnedAt accepts · hcut: the chain's sub-protocols have the written cut · hB:
sendsAreB accepts at 358. hFk: what the fence Fk holds is reached.
NO CLOSED PREMISE IS LEFT; OF THE VERIFIER's STATES NOTHING IS ASKED BUT hFk.
Limits. Joins. No premise is shown met at a real value, nor hy, hcut and hB together with the head.
In scope hy and hcut follow from L: the entry tests ask madeRow and cutRow (`P5J.pins_of_laid`);
hB from madeRow and F.planOk (Johnson/IMR/EndFiveMade.lean). The shares' other premises
(HandsShares.lean) stay. The full size alone. No probability; no soundness is claimed.
-/
import Johnson.P1K2R.DebtsConst
import Johnson.Top.H0.K2Ties.SentFitAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart Numbers)
open VerifiableInference.Desc.First.K2 (frontAt frameAt finishFrontQ LinkDebts SwitchDebts)
open VerifiableInference.Desc.First.K2Ties (at_written at_told sentFit_link sentFit_head
  sentFit_fin)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach)
open IM (XK linksW placesW k2P)
open _root_.Tw.K2 (firstFront switchNotices)
open P5J (LaidAt F0T)
open ProofFile (Cl)

/-- The written list of places `P5J.At.ps` is `placesW` (Johnson/IMR/WrittenList.lean). -/
theorem ps_written : P5J.At.ps = placesW := by
  unfold P5J.At.ps placesW
  rw [LPFK9.linksW_full]
  rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Z : ProofFile.Pub} {Np : H2U.Places4} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
  {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {Fk : Nat → S → Prop} {E : Nat → S → Bool}

theorem d_link_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction P.pol P.lay P.KL D r Z Np c)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL (F0T OnBytes.secondHashFunction Z Np c) Z Bs base c A B)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    {m : ℕ} (h23 : m < 23)
    (hFk : ∀ s, Fk (14 * (m + 1) + 2) s → ∃ z,
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
        ∀ Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some (m + 1)) = some n →
      Fk (14 * (m + 1) + 2) s →
      XK (P5J.At.N Z c) linksW placesW E (14 * (m + 1) + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      LinkDebts (P5J.At.N Z c) (m + 1) placesW[14 * (m + 1) + 2]?
        placesW[14 * (m + 1) + 3]? s n.positions x W lay' := by
  have Aw := at_written hS L hy
  have hT := sentFit_link Aw (at_told hcut Aw) h23
  rw [ps_written] at hT
  exact d_link_const hS hR O L.value L.planOk hy hcut hB Aw.keptOf h23 hT hFk

theorem d_head_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction P.pol P.lay P.KL D r Z Np c)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL (F0T OnBytes.secondHashFunction Z Np c) Z Bs base c A B)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hFk : ∀ s, Fk (339) s → ∃ z,
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (339) (z, s)) :
        ∀ nm Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some 24) = some n →
      Fk 339 s → XK (P5J.At.N Z c) linksW placesW E 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (P5J.At.N Z c) 24 placesW[339]? placesW[339 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size + x.own.length) x W lay' := by
  have Aw := at_written hS L hy
  have hT := sentFit_head Aw (at_told hcut Aw)
  rw [ps_written] at hT
  exact d_head_const hS hR O L.value L.planOk hy hcut hB Aw.keptOf hT hFk

theorem d_finish_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction P.pol P.lay P.KL D r Z Np c)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL (F0T OnBytes.secondHashFunction Z Np c) Z Bs base c A B)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hcut : VerifiableInference.PlanWritten.cutOf c.blocksInOrder = cutFirstFull)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true)
    (hFk : ∀ s, Fk (353) s → ∃ z,
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (353) (z, s)) :
        ∀ nm Pp n (s t : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp none = some n →
      Fk 353 s → XK (P5J.At.N Z c) linksW placesW E 353 s = true →
      finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (P5J.At.N Z c) 25 placesW[353]? placesW[353 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size) x W lay' := by
  have Aw := at_written hS L hy
  have hT := sentFit_fin Aw (at_told hcut Aw)
  rw [ps_written] at hT
  exact d_finish_const hS hR O L.value L.planOk hy hcut hB Aw.keptOf hT hFk

end

end P1K2

#print axioms P1K2.ps_written
#print axioms P1K2.d_link_laid
#print axioms P1K2.d_head_laid
#print axioms P1K2.d_finish_laid
