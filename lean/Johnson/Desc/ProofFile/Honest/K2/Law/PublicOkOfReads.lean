-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PublicOkOfReads.lean: the kind "the code switch" (K2): UNDER
THE LIBRARY's HEAD AND THE OPENING THE LOT's PUBLIC TEST `publicOk` AT EVERY PLACE OF THE KIND HANGS
ON ONE NAMED STATEMENT ALONE: THE READS' (`ReadsLight`, LightDebts.lean of this folder). One
statement with its proof: two calls; no definition.

  `publicOk_of_reads` `ReadsLight` at an instance ⊢ at each place of the kind `publicOk` says yes at
                    that instance, at the filling `withSwitchData Sz.ref (K1.lotData Sz.ref)`, the
                    ground's layout and the segments in front of the place

By: `publicOk_of_two` (LightAtHead.lean of this folder) · `digits_light_at_head`
(DigitsLightAtHead.lean of this folder).

Limits. THE HEAD AND THE OPENING ARE PREMISES. `ReadsLight` IS A PREMISE: PROVED IN NO FILE THAT
THIS ONE STANDS ON. At `Sz.ref` alone. The full size; the format's second hash function. CLOSED FACTS BY
LEAN's KERNEL LIE BENEATH. One way alone, as the light test is. Nothing on what the data hold.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.DigitsLightAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- THE READS' STATEMENT IS A PREMISE. **UNDER THE HEAD AND THE OPENING THE LOT's PUBLIC TEST AT
EVERY PLACE OF THE KIND HANGS ON IT ALONE.** -/
theorem publicOk_of_reads (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {ξ : ProofFile.Inst} (h4 : ReadsLight Zp Bs.G₀ ξ) :
    ∀ p ∈ switchPlaces Zp Bs.G₀,
      publicOk (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) Bs.G₀.first.layout p
        ((segmentsOf Zp Bs.G₀).take p.link) ξ = true :=
  publicOk_of_two h O (digits_light_at_head h O) h4

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.publicOk_of_reads
