-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/PaysFirst.lean: the first chain's proximity test pays. Under the library's head, at
the book and description that onlineProverFromPublicFiles returns at any filling, the one side of proxLotAt fits, at any
index type. At onlineProverPartsInUse I no other side of the first chain stands at a place of the kind
K12.

  firstTest_fits       each side of proxLotAt fits
  firstTests_fit       every side of the kind K12 among the filling's lots fits, at any filling's book
  firstTest_pays       every side of the kind K12 in the prover's first chain pays: that kind's
                       share of the field pays₁ of ReadyDebts

By what. halves_head_L (AtFullSide/K12/FitsAtHeadL.lean): the lot has one side, at jobL; p12_at_head
(Johnson/AtFull/Shape/TestNumbersAtHead.lean): the job's parameters are piLFull; lays_first_test
(PaysLaysFirst.lean); laysB_congr; widerKinds, ten_kinds, closeLotAt_kinds, wHalf_place: the other
lots' sides stand at other kinds.

Limits.
- Conditional on the head and on onlineProverFromPublicFiles's return.
- Of jobL it reads the public fields alone. The door, the rows and the closing are free; where the
  closing refuses the job lays zeros without a warning: JobL.lean's limits stand.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.PaysAtHead
import AtFullSide.K12.PaysRoundsL
import AtFullSide.K12.PaysLaysFirst
import AtFullSide.K12.TwiceFirstW
import Johnson.Desc.ProofFile.Honest.K12.StepsAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain KindName)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K5
open H2K.Member (piLFull)
open P5J (AtMgA TS)
open AtFullSide.K14 (bookWhole_returns_written_ahead)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- An element of a list is an element of a list equal to it. -/
theorem mem_of_list_eq {α : Type} {a : α} {l l' : List α} (e : l = l') (h : a ∈ l) : a ∈ l' :=
  e ▸ h

variable {W₀ Rc Tr X₀ X W₁ : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **Each side of proxLotAt fits** at onlineProverFromPublicFiles's book and description, at any index type. -/
theorem firstTest_fits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (I : WiderIn W₁)
    (S : OnBytes.HonestTrace.Sz) :
    ∀ g ∈ (proxLotAt (X := Unit) I S).halves Zp A.G, SideFits A.B 0 A.F.first.blocksInOrder g := by
  have hZ := (atPure_at_laid h.laid hA).1
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← hZ]
    exact (atPure_ok hA).2.1
  intro g hg
  have hx := (proxLotAt_sub I S hg).1
  obtain ⟨pl, hpl, hh⟩ := halves_head_L (V := Local W₁ IndexCommitterCoins ProofFile.Inst Cells) (X := Unit) h.toAtMg hG
    (widerRows S) (fun Z _ (w : Local W₁ IndexCommitterCoins ProofFile.Inst Cells) => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
    (fun Z G => K2.lotClosingAt G.first.layout (K2.segmentsOf Z G))
  have hx' := mem_of_list_eq hh hx
  obtain ⟨J, hgJ, hp, hm, hf⟩ : ∃ J : TestJob (Local W₁ IndexCommitterCoins ProofFile.Inst Cells) Unit,
      g = proverSideOfProximityTest J ∧ J.p = piLFull ∧ J.members = membersL pl ∧ J.fresh = freshL pl :=
    ⟨_, List.mem_singleton.1 hx', Johnson.AtFull.Shape.p12_at_head h.toAtMg, rfl, rfl⟩
  subst hgJ
  have ef : finishAt Zp A.G = finishW := by
    unfold finishAt finishW
    rw [places_head h.toAtMg hG]
  have ew : finishW = some pl := ef.symm.trans hpl
  have k := lays_first_test
  rw [ew] at k
  simp only [Option.all] at k
  obtain ⟨B₀, h₀, -⟩ := bookWhole_returns_written_ahead
  have hl : laysB A.B 0 J = true := by
    rw [book_of_atPure h hA h₀, book_is_written h₀,
      laysB_congr bookW 0 J (bareJob piLFull (membersL pl) (freshL pl) : TestJob Unit Unit)
        hp hm hf]
    exact k
  obtain ⟨sh1, -, -⟩ := planOk_all (atPure_planOk h.laid hA)
  exact fits_at_numbers A.B 0 (Or.inl rfl) J _ hp two_stages_L hl
    (fun b hb => (shaped_parts (sh1 b hb).2).1)
    (rounds_of_alike (alike_at_atPure h hA).first rounds_at_L)

/-- **Every side of the kind K12 among the filling's lots fits**, at the book and description of any
filling. -/
theorem firstTests_fit (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (I : WiderIn W₁)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ L ∈ (onlineProverPartsInUse I OnBytes.secondHashFunction S O).lots, ∀ g ∈ L.halves Zp A.G,
      g.place.kind = KindName.K12 → SideFits A.B 0 A.F.first.blocksInOrder g := by
  intro L hL g hgL hk
  rw [widerFillAtCPUOWM_lots] at hL
  simp only [List.mem_append, List.mem_singleton] at hL
  rcases hL with ((h1 | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h1
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h1
    have k1 := (FirstFill.widerKinds I OnBytes.secondHashFunction S O Zp A.G).all q hq g hgL
    exact absurd (k1.symm.trans hk) (ten_kinds I OnBytes.secondHashFunction S O q hq).2
  · have k1 := closeLotAt_kinds I S Zp A.G g hgL
    rw [k1] at hk
    exact absurd hk (by decide)
  · exact firstTest_fits h hA I S g hgL
  · rw [wHalf_place I OnBytes.secondHashFunction O Zp A.G g hgL] at hk
    exact absurd hk (by decide)

/-- **At the filling every side of the kind K12 in the first chain pays.** -/
theorem firstTest_pays {W₀ : Type} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first .K12 := by
  have hZ := (atPure_at_laid h.laid hA).1
  obtain ⟨-, -, -, -, -, -, -, e1, -⟩ := atPure_ok hA
  intro g hg hk
  rw [e1, hZ] at hg
  unfold firstOf at hg
  obtain ⟨L, hL, hgL⟩ := List.mem_flatMap.1 hg
  exact sidePays_of_fits (firstTests_fit h hA I S O L hL g hgL hk)

end AtFullSide.K12

#print axioms AtFullSide.K12.mem_of_list_eq
#print axioms AtFullSide.K12.firstTest_fits
#print axioms AtFullSide.K12.firstTests_fit
#print axioms AtFullSide.K12.firstTest_pays
