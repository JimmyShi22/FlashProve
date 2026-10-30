-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CallsA.lean: K01_law: THREE CALLS, EACH TO THE LETTER OF A BINDER OF THE TOP (k01_law, Johnson/Desc/K1/Law/K01Law.lean), FROM OTHER FILES. THE THIRD, hOrder_of, IS NOT IN THIS FILE: it is declared in Johnson/Desc/K1/Law/CallsO.lean:58, with the premises h (FillsK1), hIo, hPlan, hy and hIn; Johnson/Desc/K1/Law/K01Law.lean:354 calls it.
  hMg_of      hMg   ⟸ FillsK1 (equations on Mg: nine in Johnson/Desc/K1/Law/FillsK1.lean:34-42): six projections
  hDec_of     hDec  ⟸ DecBlind decT (Johnson/Desc/K13/Law/SigDecodes.lean: decT reads the public part alone; decTop (Johnson/Desc/Sound/DecTop.lean) is so by its make)
  later_blkL  the place's block and K1's own block in it are «Later» in the text of K13's files
  hOrder_of   hOrder ⟸ FillsK1.inOrder · four lemmas (eqsBAtLater · reqIsBAtLater · inOrderK13AtLater · backReqAtLater: K1/Law/InOrderAtLater.lean) · TWO PREMISES LEFT: the base's «in order» is true throughout (hBase: whoever supplies the composed meaning's value:
              Mg₀.inOrder := fun _ => true) · K1's own block's test on the plan says yes (hPlan)
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.MgK1
import Johnson.Desc.K1.Law.FillsK1
import Johnson.Desc.K13.Law.SigDecodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Maker Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData flatPlacesOf)
open VerifiableInference.Desc.Sound (Mem MsgT linksFull)
open VerifiableInference.Desc.K13.Law (DecBlind)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix k1Reads)

variable {Pp Xi Cells Tok : Type}

section
variable {D : PubData} {G : FileDescription Xi} {arr : ℕ → ℕ → ℕ}
  {smp : Pp × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf D.cs s.l).om i).Smp}
  {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
  {shape : Params.ReqShape} {layout : Params.ReqLayout} {io0 : Pp × S → Bool}
  {base : Pub → Pp × S → Bool} {X3 : OnBytes.Model.Verify.Public} {D3 : First.Look.Sent}
  {MgP Mg : Meaning Pp (Wit Cells Tok MsgT)}

theorem hMg_of (h : FillsK1 D G arr smp ms decT shape layout io0 base X3 D3 MgP Mg) :
    MgK1 D.cs G arr smp ms decT Mg :=
  ⟨h.held, h.shown, h.noColl, h.pin, h.decodes, h.pinW⟩

theorem hDec_of (h : DecBlind decT) (B : Block S Unit) : DecLeft B decT :=
  fun _ _ c hy => h.same hy.1 c

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hMg_of
#print axioms VerifiableInference.Desc.K1.hDec_of
