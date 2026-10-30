-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysOnline.lean: the closing of a segment (K10): at the return of the online maker every side of the kind K10
in the prover's first list pays, by the kind-free crossing (Honest/Law/KindPaysOnlineForms.lean) from the closings' lot at
the base filling (`sidePays_closeLotAt`, AtFullSide/K10/PaysAtHead.lean).

  **`kindPays_k10_at_term`**   the statement, at the head's description
  `kindPays_k10_at_return`   the same at the description that the return holds
  `closings_there`, `closings_first_at_return`   against emptiness: 25 closings at different places, each with its block, and
                    at the base filling the closing's own sender is what a search finds first at each
  `closings_first_at_online`   the same in the list read through, at the return itself
  `onlineBase_is_baseMaker`   the base filling here is the one of `baseMaker`

Limits. The head and that the maker returns are premises. A side that pays lays its steps: nothing on whether a part plays
or a verifier accepts.
-/
import AtFullSide.K10.PaysAtHead
import AtFullSide.K10.PaysByDigest
import AtFullSide.K10.PaysCount
import Johnson.Desc.ProofFile.Honest.Law.KindPaysOnlineForms
import Johnson.Desc.ProofFile.Honest.K10.Pay.AcceptedAtBase
import Johnson.Desc.ProofFile.Honest.K10.Pay.ClosingsThrough
import E2E.BaseMaker

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open VerifiableInference.Desc (Chain KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **At the return of the online maker every side of the kind K10 in the first list pays.** -/
theorem kindPays_k10_at_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first KindName.K10 := by
  obtain ⟨e1, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  refine kindPays_online_of_base_lot hA (L := closeLotAt matrixInput OnBytes.HonestTrace.Sz.ref)
    (fun q hq => ?_) (close_pair_only _ _ _ _)
  rw [eZ] at hq
  exact sidePays_closeLotAt h hA _ _ _ q hq

/-- **The same at the description that the return holds.** -/
theorem kindPays_k10_at_return (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K10 := by
  obtain ⟨-, -, e3, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  rw [eF]
  exact kindPays_k10_at_term h hA

/-- **The closings are 25, at different places, and each has its block in the chain.** -/
theorem closings_there (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    (K10.closePars Zp).length = 25 ∧ ((K10.closePars Zp).map K10.closePlace).Nodup ∧
      ∀ Q ∈ K10.closePars Zp, ∃ b ∈ cF.blocksInOrder, b.place = K10.closePlace Q := by
  have hn : (parsW.map fun P => (P.link, P.piece)).Nodup := by
    rw [pars_written]
    decide
  have e : (parsW.map fun P => (P.link, P.piece)) =
      (parsW.map K10.closePlace).map fun pl => (pl.link.getD 0, pl.piece) := by
    rw [List.map_map]
    rfl
  rw [e] at hn
  refine ⟨?_, ?_, fun Q hQ => ?_⟩
  · rw [pars_at_head h]
    exact parsW_length
  · rw [pars_at_head h]
    exact List.Nodup.of_map _ hn
  · obtain ⟨b, hb, hp, -⟩ := close_block h hQ
    exact ⟨b, hb, hp⟩

/-- **Against emptiness: at the base filling of the online maker's return, what a search finds first at each closing's place
is the closing's own sender**: one part, "BAT"'s move and then the fold's part at the lot's job of that place. -/
theorem closings_first_at_return (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    ∃ A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
      onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL onlineBase = .ok A₀ ∧ A₀.Z = A.Z ∧ A₀.G = A.G ∧ A₀.F = A.F ∧
        A₀.B = A.B ∧
        K10.ClosingsFirst A₀.H.first
          (fun w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells => (⟨w.trace, matrixInput.weights Zp w.w₀, w.rc⟩ : Readers))
          (widerRows OnBytes.HonestTrace.Sz.ref Zp A₀.G)
          (K10.stAtZero cF.blocksInOrder fun ξ : ProofFile.Inst => ProofFile.startS Zp ξ.pub) Zp A₀.G := by
  obtain ⟨A₀, h0, e1, e2, e3, e4⟩ := online_base_return hA
  exact ⟨A₀, h0, e1, e2, e3, e4, (K10.closingsFirst_baseHead h _ _ _ _ h0).2⟩

/-- **Against emptiness, in the list read through: at the online maker's return, what a search of the first list finds first at
each of the 25 closings' places is the closing's own sender.** -/
theorem closings_first_at_online (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    (K10.closePars Zp).length = 25 ∧ K10.ClosingsFirst A.H.first
      ((fun w : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells => (⟨w.trace, matrixInput.weights Zp w.w₀, w.rc⟩ : Readers)) ∘
        Local.thru id (tableCoins Z))
      (widerRows OnBytes.HonestTrace.Sz.ref Zp A.G)
      (K10.stAtZero cF.blocksInOrder fun ξ : ProofFile.Inst => ProofFile.startS Zp ξ.pub) Zp A.G := by
  obtain ⟨Bs, base, c, Sh, Se, Op, hC⟩ := K10.closingsFirst_through id (tableCoins Z) matrixInput.dummy matrixInput
    OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest hA
  have eZ : A.Z = Zp := Except.ok.inj ((atPure_ok hA).1.symm.trans h.laid.pub)
  obtain ⟨Bs', base', O'⟩ := h.laid.opened
  have e1 := ToldDesc.pureChainAt_of_open Op
  have e2 := ToldDesc.pureChainAt_of_open O'
  rw [eZ] at e1
  obtain rfl : c = cF := Except.ok.inj (e1.symm.trans e2)
  rw [eZ] at hC
  exact ⟨(closings_there h).1, hC⟩

/-- The base filling at which `closings_first_at_return` and `sidePays_closeLotAt` stand is the one that `baseMaker` makes. -/
theorem onlineBase_is_baseMaker (files : VerifierAndGoals.PublicFiles) :
    onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL onlineBase = baseMaker files := rfl

end AtFullSide.K10

#print axioms AtFullSide.K10.closings_first_at_online
#print axioms AtFullSide.K10.onlineBase_is_baseMaker
#print axioms AtFullSide.K10.closings_there
#print axioms AtFullSide.K10.closings_first_at_return
#print axioms AtFullSide.K10.kindPays_k10_at_term
#print axioms AtFullSide.K10.kindPays_k10_at_return
