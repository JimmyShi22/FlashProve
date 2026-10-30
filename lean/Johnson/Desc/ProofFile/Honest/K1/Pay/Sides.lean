-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Pay/Sides.lean: THE SIDES OF THE KIND K1 AT THE BASE PROVER (the
filling onlineProverPartsInUse, at any reader of the index): in the first chain each is a sending of K1's
lot or W's sending; in the shared chain each is one of the hash build's two sendings; the second
chain has none. Each is one part of two rounds that spends and carries nothing, and the book's count
at its address is the part's.

Limits. Under the head and a return of the maker. Public counts alone. Nothing on any property of
the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K1.Pay.BookAtK1
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.K1.Law.HasCoinsAtBook
import Johnson.Desc.ProofFile.Honest.K1.Law.LotJobsAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.Desc.ProofFile.Honest.K1.LotJobs
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.K14.AtWiderParts
import Johnson.Desc.ProofFile.Honest.K14.SharedSendsWritten
import Johnson.Desc.ProofFile.Honest.BookWritten.Small

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1.Pay
open VerifiableInference.Desc
open VerifiableInference.Desc (Block FileDescription Place KindName Chain)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open ProofFile.Honest.FirstFill

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- A job's half has the form. -/
theorem one_of_job {V W X Xi : Type} (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X) :
    OnePart (placeHalf (V := V) wit J) ((sendPart (V := V) J).lift id wit id fun _ y => y) :=
  ⟨rfl, by simp [Part.lift, sendPart], rfl, rfl⟩

/-- **The book's count at a job of K1's own lot is the part's.** -/
theorem lot_job_due (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X Xi : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (no : Place → Nat)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no Dt A.Z A.G) :
    dueAt (A.B.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride := by
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  rw [eZ, eG, lotJobs_at_head h O' no Dt] at hJ
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hJ
  rcases mem_k1Members.1 hy with rfl | ⟨l, hl, d, rfl⟩
  · exact hasCoins_two_at_book h hA _ _ (by rw [eZ, eG])
  · exact hasCoins_fifty_at_book h hA hl d _ _ (by rw [eZ, eG])

/-- **The book's count at W's sending is the part's.** -/
theorem w_job_due (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X Xi : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {msg : Array OnBytes.OracleNotice}
    (hm : OnBytes.linMessageW A.Z.first.lin = some msg) (first : Nat) (Dw : RowDataOf Xi) :
    dueAt (A.B.rowsOf 0)
        ⟨(wJobAt (X := X) A.Z.first (wGp A.Z) 4 msg first Dw).P.place, 0⟩ =
      dueR (wJobAt (X := X) A.Z.first (wGp A.Z) 4 msg first Dw).P
        (wJobAt (X := X) A.Z.first (wGp A.Z) 4 msg first Dw).ride := by
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  rw [eZ] at hm ⊢
  obtain rfl : msg = wMsgFull := Option.some.inj (hm.symm.trans (msg_w_head h O'))
  exact hasCoins_w_at_book h hA first Dw rfl

section
variable {W₀ : Type} (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- The reader at the public part. -/
abbrev witOf (Zq : ProofFile.Pub) : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → PlaceIn ProofFile.Inst :=
  fun w => ⟨w.x, ⟨w.trace, I.weights Zq w.w₀, w.rc⟩⟩

/-- **Every side of the kind K1 of the base prover's first chain** is a job's of K1's lot or W's. -/
theorem first_cases (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∀ g ∈ A.H.first, g.place.kind = .K1 →
      (∃ J ∈ lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z A.G,
        g = placeHalf (witOf I A.Z) J) ∨
      ∃ msg, OnBytes.linMessageW A.Z.first.lin = some msg ∧
        g = placeHalf (witOf I A.Z) (wJobAt (X := Unit) A.Z.first (wGp A.Z) 4 msg
          (lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩) (K13.wDataAt O.pile A.Z A.G)) := by
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := atPure_ok hA
  intro g hg hk
  rw [eH] at hg
  obtain ⟨M, hM, hgM⟩ := List.mem_flatMap.1
    (hg : g ∈ (onlineProverPartsInUse I OnBytes.secondHashFunction S O).lots.flatMap fun L => L.halves A.Z A.G)
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h1 | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h1
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h1
    have hkq := (FirstFill.widerKinds I OnBytes.secondHashFunction S O A.Z A.G).all q hq g hgM
    have k : q.2 = .K1 := hkq.symm.trans hk
    have e' : q = (HLot.byPub I.weights (LongLots.plain OnBytes.secondHashFunction S O).k1, .K1) :=
      List.inj_on_of_nodup_map widerPairs_nodup hq (List.Mem.head _) k
    rw [e'] at hgM
    have hg' : g ∈ lotHalves (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (X := Unit) (witOf I A.Z)
        (lotNo OnBytes.secondHashFunction A.Z) (lotData S) A.Z A.G := hgM
    rw [lotHalves_jobs] at hg'
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hg'
    exact .inl ⟨J, hJ, rfl⟩
  · have hk' := closeLotAt_kinds I S A.Z A.G g hgM
    rw [hk] at hk'
    cases hk'
  · have hk' := proxLotAt_kinds I S A.Z A.G g hgM
    rw [hk] at hk'
    cases hk'
  · right
    rw [wLotAt_halves] at hgM
    cases hm : OnBytes.linMessageW A.Z.first.lin with
    | none =>
      rw [hm] at hgM
      cases hgM
    | some msg =>
      rw [hm] at hgM
      exact ⟨msg, rfl, List.mem_singleton.1 hgM⟩

/-- **Each such side has the form, and the book's count at its address is its part's.** -/
theorem first_form (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∀ g ∈ A.H.first, g.place.kind = .K1 →
      ∃ p, OnePart g p ∧ p.takes = dueAt (A.B.rowsOf 0) ⟨g.place, 0⟩ := by
  intro g hg hk
  rcases first_cases I S O hA g hg hk with ⟨J, hJ, rfl⟩ | ⟨msg, hm, rfl⟩
  · exact ⟨_, one_of_job _ J, (lot_job_due h hA _ _ hJ).symm⟩
  · exact ⟨_, one_of_job _ _, (w_job_due h hA hm _ _).symm⟩

/-- **(P1) IN THE FIRST CHAIN.** -/
theorem k1_pays_first (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first .K1 := by
  obtain ⟨hpl, C, p0, p1, p2, M, hB⟩ := head_pack h hA
  have hp := Johnson.RunOne.Sound.placesOk_of_planOk _ hpl
  intro g hg hk
  obtain ⟨p, ho, hd⟩ := first_form I S O h hA g hg hk
  refine sidePays_one (atPure_tests hA).1 hp (.inl rfl) _ g p ho fun b hb e => ?_
  exact bookAt_first hB hpl C hb (by rw [e]; exact hk) (by rw [e]; exact hd)

end

end ProofFile.Honest.K1.Pay

#print axioms ProofFile.Honest.K1.Pay.first_cases
#print axioms ProofFile.Honest.K1.Pay.first_form
#print axioms ProofFile.Honest.K1.Pay.k1_pays_first
