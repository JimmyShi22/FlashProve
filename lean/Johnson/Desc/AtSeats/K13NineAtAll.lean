-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K13NineAtAll.lean: KIND K13's ONE PREMISE ALONG REACHED
STATES, hNine OF k13_kindB_tight (K13KindRowB.lean), PAID BY CALLS OF THEOREMS IN OTHER FILES;
AND SO THE KIND's ROW UNDER THE SHARED HEAD AND THE ENTRY TESTS' TWO COMPARISONS ALONE.
No law of another file is typed here: each of the nine tests on the verifier's state is another
file's theorem, called at the head's own letters.

OBJECT. hNine: at every state that is reached with a typed public part and has not failed, the nine
tests of NineK13 (K13KindRowA.lean) accept, at the constant's codes, shape and layout and
at the written L and M (d12Full).
USER. k13_kindB_tight's caller: hNine falls; nothing comes in.
LETTERS. Zl, D, r₀, Zp, Np, cF, x₀, 𝔏: the row's own.

TEST BY TEST: the payer, its file, and what it asks. hS, hR, h, hF, O: the scope, "the
files are read", "the maker returns the IOP as written in Lean", its own test on the list of rounds,
and the maker's opening: all five are fields of the head. hp (each sub-protocol's own test) is
flat_planOk at hF. "Reached" is the raw list's (Reach 0 c.blocksInOrder …): RchPub's first half by rchAt_raw.
  order    tidy: tidy_at_open_raw (Johnson/Desc/AtSeats/Fit/TidyAtOpen.lean): h, hF, O
           codes, shape, layout: codes_field, shape_field, layout_field
           (Johnson/IMR/AtReach.lean): hS, hR, O, hp
  masks    masks_reached (Johnson/LPFK9R/ThreeK13Fields.lean): hS, hR, O
  within, oneRow   within_reached (the same file): O, hp
  weights  reach_weights (Johnson/LTPileR/WeightsReached.lean): h, hp. It ends in "there are
           Z, A, B, c": weights_at ties them to the opening's own, as tidy_at does for tidy_field
  book     bookInOrder_field (Johnson/IMR/AtReach.lean): O, hp; at first tree 0
  seats    seatsCarried_field (Johnson/IMR/SeatsField.lean): hS, hR, O, hF, hB, hLd
  shapes   msgShapes_field (the same file): hS, hR, O, hF, hB
  fits     bookFits_field (Johnson/IMR/AtReach.lean): O, hp
  hB       "the sendings stand at their places": sends_pinned_paid (FivePinned.lean) from
           madeRow Zp = true, which hP1 gives in scope (pinnedAt_row, key_in_scope_pure)
  hLd      the layout of the sendings is LFull: laid_in_scope (Johnson/HB/LLHARD/PlanInScope.lean)
           under hP1; M is MFull by msgs_in_scope
Main names.
  weights_at      the weights' test at every reached state, at an opening's own Z and c
  nine_reached    the nine at an opening, general in the layout Ld
  madeRow_atAll   hP1 gives the row's accept in scope
  **nine_atAll**  hNine, to the letter, from hA and hP1
  **k13_kindC**   hA.Kind 𝔏 KindName.K13 from hA, q₁ q₂ q₃, hP1, hP2

What is not claimed. That hA, hP1 or hP2 can be met: NO MEMBER. The witnesses inside "reached" are
not the run's own. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13KindRowB
import Johnson.Desc.AtSeats.Fit.TidyAtOpen
import Johnson.Desc.AtSeats.FoldFactsPaid
import Johnson.IMR.AtReach
import Johnson.IMR.SeatsField
import Johnson.IMR.FivePinned
import Johnson.LPFK9R.ThreeK13Fields
import Johnson.LTPileR.WeightsReached
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open OnBytes.Road OnBytes.RunA
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach RchAt RchPub rchAt_raw)
open VerifiableInference.PlanWritten (madePinnedAt madeRow pinnedAt_row key_in_scope_pure cutIs)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes msgsOfChain sendsAreB snAt)

/-- **The weights' test at every reached state, at an opening's own Z and c.** -/
theorem weights_at {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {c : Chain S Cl}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hd : F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k : ℕ) (a : ProofFile.InstPub × S)
    (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) k a) : First.weightsB a.2 = true := by
  obtain ⟨Z', A', B', c', hZ', e', K⟩ := _root_.Meaning.K2.reach_weights h
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  have e := e'.symm.trans hd
  have h1 := congrArg (fun G : FileDescription ProofFile.Inst =>
    (⟨G.S₁, G.Cl, G.first⟩ : Σ (T C : Type), Chain T C)) e
  have h2 : (⟨S, Cl, c'⟩ : Σ (T C : Type), Chain T C) = ⟨S, Cl, c⟩ := h1
  have h3 := eq_of_heq (Sigma.mk.inj h2).2
  obtain rfl : c' = c := eq_of_heq (Sigma.mk.inj h3).2
  exact K hp 0 k a hr

/-- **The nine tests at every reached state without a mark, at an opening.** -/
theorem nine_reached {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (h : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hF : F.planOk = true)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hB : sendsAreB Z.made.proof.1 358 (snAt Z Bs.G₀ IM.placesW) = true) {Ld : Laid}
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some Ld) (k : ℕ) (a : ProofFile.InstPub × S)
    (hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) k a) (hu : a.2.failed = none) :
    NineK13 Z.first.codes Z.first.shape Z.first.layout ⟨0, Ld, msgsOfChain Z.made.proof.1⟩ a.2 := by
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := _root_.Meaning.K2.flat_planOk O.desc hF
  have hId : ∀ k a, Reach 0 c.blocksInOrder (ProofFile.startS Z) k a →
      Reach 0 c.blocksInOrder (ProofFile.startS Z) k (id a) := fun _ _ q => q
  have hFold : ∀ k a, Reach 0 c.blocksInOrder (ProofFile.startS Z) k a → ∃ rs cols r q,
      VerifiableInference.Desc.foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (id a).1) rs cols =
        .ok ((id a).2, r, q) := fun _ _ q => by
    obtain ⟨-, rs, cols, f⟩ := q.fold
    exact ⟨rs, cols, [], [], f⟩
  refine ⟨?_, LPFK9.masks_reached hS hR O k a hr, (LPFK9.within_reached O hp k a hr).1,
    (LPFK9.within_reached O hp k a hr).2, weights_at h O.pub O.desc hp k a hr,
    _root_.Meaning.K2.bookInOrder_field O hp _ id hId k a hr hu,
    IM.seatsCarried_field hS hR O _ id hFold hF hB hLd k a hr hu,
    IM.msgShapes_field hS hR O _ id hFold hF hB k a hr hu,
    _root_.Meaning.K2.bookFits_field O hp _ id hId k a hr hu⟩
  unfold inOrderK13
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨_root_.Meaning.K2.tidy_at_open_raw h hF O k a hr hu,
    _root_.Meaning.K2.codes_field hS hR O hp _ id hId k a hr hu⟩,
    _root_.Meaning.K2.shape_field hS hR O hp _ id hId k a hr hu⟩,
    _root_.Meaning.K2.layout_field hS hR O hp _ id hId k a hr hu⟩

/-- In scope the comparison's law form gives the row's own accept. -/
theorem madeRow_atAll {o : ProofFile.SecondHashFunctionArgument} {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA o Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    madeRow Zp = true := by
  rw [pinnedAt_row, if_pos (key_in_scope_pure hA.scope hA.laid.pub)] at hP1
  exact hP1

/-- **hNine of k13_kindB_tight, to the letter.** -/
theorem nine_atAll {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    ∀ j x,
      RchPub (Str := (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁
          0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub j x → x.1.2.failed = none →
      NineK13 hA.𝔇.cs hA.𝔇.shape hA.𝔇.layout d12Full x.1.2 := by
  intro j x hr hu
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  have hB := IM.sends_pinned_paid O (madeRow_atAll hA hP1)
    (IM.hp_of_planOk hA.scope hA.reads O (IM.blocksOk_of_planOk O hA.laid.planOk))
  have N := nine_reached hA.scope hA.reads hA.laid.value hA.laid.planOk O hB
    (laid_in_scope hA.scope hA.laid.pub hP1) j x.1 (rchAt_raw hr.1) hu
  rw [msgs_in_scope hA.scope hA.laid.pub hP1] at N
  exact N

/-- **Kind K13's row, counted form, under the shared head and the two comparisons' accepts alone.**
-/
theorem k13_kindC {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true) :
    hA.Kind 𝔏 KindName.K13 :=
  k13_kindB_tight hA 𝔏 q₁ q₂ q₃ hP1 hP2 (nine_atAll hA hP1)

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.weights_at
#print axioms VerifiableInference.Desc.K13.Law.nine_reached
#print axioms VerifiableInference.Desc.K13.Law.madeRow_atAll
#print axioms VerifiableInference.Desc.K13.Law.nine_atAll
#print axioms VerifiableInference.Desc.K13.Law.k13_kindC
