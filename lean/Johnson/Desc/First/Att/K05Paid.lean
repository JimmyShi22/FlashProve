-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Paid.lean: the laws of kind K5 without the three premises on the part:
each is its
namesake at the three theorems of Johnson/Desc/Part/MaskedSumTie.lean (partHearLaw, partRowLaw,
partReturns).

Main names: `K05_law_paid`, `K05_at_value_paid`, `hear_law_paid`, `hear_returns_paid`,
`hear_iff_paid`,
`value_owF_paid`. Each statement is its namesake's, less its leading premises.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Part.MaskedSumTie
import Johnson.Desc.First.Att.K05Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.Part.MaskedSum (partHearLaw partRowLaw partReturns)
open Cb.Pv.Att (OwnPar Means)

theorem K05_law_paid {S : Type} : type_of% (K05_law partHearLaw partRowLaw (S := S)) :=
  K05_law partHearLaw partRowLaw

theorem hear_law_paid : type_of% (@hear_law partHearLaw) := @hear_law partHearLaw

theorem hear_returns_paid : type_of% (hear_returns partReturns) := hear_returns partReturns

theorem hear_iff_paid : type_of% (hear_iff partReturns) := hear_iff partReturns

theorem K05_at_value_paid {K : Type} [Field K] [Fintype K] {M X : Type} (P : OwnPar K M X)
    (Mn : Means K P.D P.C P.kap) {S : Type} : type_of% (K05_at_value P Mn partHearLaw partRowLaw (S := S)) :=
  K05_at_value P Mn partHearLaw partRowLaw

theorem value_owF_paid {K : Type} [Field K] [Fintype K] {ρ : OnBytes.Model.Reading K} {M X : Type} (P : OwnPar K M X)
    (Mn : Means K P.D P.C P.kap) : type_of% (value_owF (ρ := ρ) P Mn partRowLaw) :=
  value_owF P Mn partRowLaw

end VerifiableInference.Desc.First.Att.P

open VerifiableInference.Desc.First.Att.P in
#check @K05_law_paid
open VerifiableInference.Desc.First.Att.P in
#check @hear_iff_paid
#print axioms VerifiableInference.Desc.First.Att.P.K05_law_paid
#print axioms VerifiableInference.Desc.First.Att.P.K05_at_value_paid
#print axioms VerifiableInference.Desc.First.Att.P.hear_iff_paid
#print axioms VerifiableInference.Desc.First.Att.P.hear_returns_paid
#print axioms VerifiableInference.Desc.First.Att.P.value_owF_paid
