-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Seal357AtAll.lean:
THE SEAL's TIE (number 357 of the first chain's 358 sub-protocols; place ⟨1, none, 5, frame⟩) AT
THE CLOSED CONSTANT (P5J.mgAtAll) AND AT THE TOWER's OWN LETTERS: the body of the counted form of a
kind's law (KindTiedR) at i := 357. It is MEANT for the field sealTie of the condition of the kind
"frame"; that field's own text spells five of the nine arguments otherwise (FrAll D · (dmOf h).N ·
mgAll (dmOf h) mgBase · linksFull · flatPlacesOf linksFull true): THAT LEAN TAKES THE ONE FOR THE
OTHER IS SHOWN NOWHERE YET. Three theorems: joinings.

  ex_quiet_357   the tower's extractor lays nothing at 357: hA.toAtMg.ex 𝔏 357 a b w = w:
                 extQAt_quiet | lays_nothing (Johnson/Desc/Sound/ExtQuiet.lean) at the
                 seal's place, whose kind is none of the four that lay.
  counts_357_atAll  no tree and no message between 357 and 358 at the constant's numbers:
                    at357_in_scope (Johnson/Desc/AtSeats/CountsInScope.lean) after atN_is
                    (Johnson/Desc/AtSeats/K13KindRow2.lean).
  seal_tie_atAll **∀ q, (hA.toAtMg.row 𝔏)[357]? = some q → TiedAtR (At.N Zp cF) (mgAtAll hA)
                 fullLinks At.ps (fun a => a) hA.toAtMg.rch 357 (q.withMap (hA.toAtMg.ex 𝔏
                 357))**: seal_tied357 (Johnson/Desc/AtSeats/Seal357.lean) at the closed form of the
                 pieces, with RowSeal | FillSeal by rowSeal_mgAll' | fillSeal_mgAll
                 (Johnson/Desc/K13/Law/AtTableSealMgAll.lean), then tiedAtR_of_tiedAt.
OF THE FIVE PREMISES THAT WERE LEFT (hE7 · hTr · hMs · hI · hV): hE7 · hTr · hMs ARE PAID HERE.
LEFT: hA (the head) · q₁ q₂ q₃ (𝔏's sub-protocols are the description's flat lists) · hI · hV:
BOUNDS: the index masks' tree's and W's tree's numbers lie below the number of trees in front of
the seal's piece (q.base): no closed facts as typed (q comes out of the row); seal_low_atAll
(Johnson/P1L20R/FrameSealLow.lean) has both from the test fenceFit. THE TIE IS IDLE:
no error is charged; it spends only "an accept returns the state".
What is not claimed. That the head can be met. No member. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.Seal357
import Johnson.Desc.AtSeats.K13KindRowA
import Johnson.Desc.K13.Law.AtTableSealMgAll
import Johnson.Desc.K13.Law.AtTableSealRow
import Johnson.Desc.Sound.ExtQuiet

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
open VerifiableInference.Desc.Sound (TiedAtR mgAll MgData CellsQ mgBase threeCap threeCap_ofDesc)

variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}

/-- The tower's extractor lays nothing at the seal. -/
theorem ex_quiet_357 (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) :
    ∀ a b w, hA.toAtMg.ex 𝔏 357 a b w = w := by
  intro a b w
  have hk := lays_nothing hA.𝔇.N Sound.linksFull placeSeal (by decide) (by decide) (by decide)
    (by decide)
  rw [P5J.kind_ex hA 𝔏]
  exact extQAt_quiet _ _ _ _ _ _ _ _ _ _ _ _ 357 placeSeal seal_place_full hk.1 hk.2.1 hk.2.2 a b w

/-- No tree and no message between 357 and 358, at the constant's numbers. -/
theorem counts_357_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    hA.𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[357 + 1]? =
        hA.𝔇.N.treesAt (flatPlacesOf Sound.linksFull true)[357]? ∧
      hA.𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[357 + 1]? =
        hA.𝔇.N.msgsAt (flatPlacesOf Sound.linksFull true)[357]? := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  show (P5J.At.N Zp cF).treesAt _ = (P5J.At.N Zp cF).treesAt _ ∧
    (P5J.At.N Zp cF).msgsAt _ = (P5J.At.N Zp cF).msgsAt _
  rw [atN_is hA]
  exact HashBuild.at357_in_scope _ _ _ hA.scope hA.reads O

set_option maxHeartbeats 1000000 in
/-- **The seal's tie at the closed constant.** -/
theorem seal_tie_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hI : ∀ q, (hA.toAtMg.row 𝔏)[357]? = some q → (P5J.At.N Zp cF).index.1 < q.base)
    (hV : ∀ q, (hA.toAtMg.row 𝔏)[357]? = some q → (P5J.At.N Zp cF).w.1 < q.base) :
    ∀ q, (hA.toAtMg.row 𝔏)[357]? = some q →
      TiedAtR (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0)
        (P5J.At.N Zp cF) (P5J.mgAtAll hA) P5J.fullLinks P5J.At.ps (fun a => a) hA.toAtMg.rch 357
        (q.withMap (hA.toAtMg.ex 𝔏 357)) := by
  intro q hq
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth hA.scope hA.laid]
    exact hA.laid.data
  have hT := threeCap_ofDesc 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd hD hA.laid.planOk q₁ q₂ q₃
  have hq' := hq
  rw [P5J.kind_row hA 𝔏] at hq'
  exact tiedAtR_of_tiedAt _ _ _ _ _ _ 357 _
    (seal_tied357 hA.scope hA.reads O hT hq' hA.𝔇.N (P5J.mgAtAll hA) _ (ex_quiet_357 hA 𝔏) placeSeal
      (rowSeal_mgAll' hA.𝔇 mgBase rfl _ (counts_357_atAll hA).1 (counts_357_atAll hA).2)
      (fillSeal_mgAll hA.𝔇 mgBase _ q.base _ _ (open_of_test _ _ 357 openSeal_both.2) (hI q hq)
        (hV q hq) (riders_of_test _ _ 357 riders_full)))

end VerifiableInference.Desc.K13.Law
