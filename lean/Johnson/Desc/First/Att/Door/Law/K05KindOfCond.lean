-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K05KindOfCond.lean: kind K5: **THE KIND's SHARE AT THE CLOSED CONSTANT, UNDER THE NAME P5J.AtMgA.Kind, AT ONE HEAD, FROM K5's NAMED CONDITION (K5CondAt: what is once per head, and what is per group: Door/Law/K5LeftOfCond.lean)
AND K5Along's SEVEN** (Door/Law/K5Along.lean) at the head's own condition beside the promise.

Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)

OVER MgAtAll ALONE (the head's field opts).

Main names:
  **k05_kind_of_cond**: at one head h and one 𝔏: the three flat lists' heads · (∀ L, the listed seats are L → K5Along h.toAtMg.rch L …) · (∀ L, the listed seats are L → K5CondAt h L) → h.Kind 𝔏 .K5.
  k05_kind_of_condAt: the like at a letter L.
IS IT EMPTY HERE? IMPLICATIONS. NO MEMBER OF K5CondAt OR OF K5Along IS SHOWN. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). THE KIND's LAW IS NOT PROVED.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K05KindOfLeft
import Johnson.Desc.First.Att.Door.Law.K5LeftOfCond

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid)
open P5J (AtMg AtMgA mgAtAll F0T TS Free)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- At a letter for the listed seats. -/
theorem k05_kind_of_condAt (L : Laid)
    (A : K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.toAtMg.rch L (P5J.At.d12 Zp L).M h.𝔇.sent)
    (U : K5CondAt h L) : h.Kind 𝔏 KindName.K5 :=
  k05_kind_of_leftFullAt h 𝔏 q₁ q₂ q₃ L A fun _ hg _ hq => k5LeftAllFull_of_cond 𝔏 q₁ q₂ q₃ U hg hq

/-- **The kind's share P5J.AtMgA.Kind (RowsAtAll.lean), from the named condition and the seven.** -/
theorem k05_kind_of_cond
    (A : ∀ L, P5J.At.laid? Zp = some L →
      K5Along (Fr := frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0) h.toAtMg.rch L (P5J.At.d12 Zp L).M h.𝔇.sent)
    (U : ∀ L, P5J.At.laid? Zp = some L → K5CondAt h L) : h.Kind 𝔏 KindName.K5 := by
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  exact k05_kind_of_condAt h 𝔏 q₁ q₂ q₃ L (A L hL) (U L hL)

end

end H2K5.Door

#print axioms H2K5.Door.k05_kind_of_condAt
#print axioms H2K5.Door.k05_kind_of_cond
