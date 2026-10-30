-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/DefAt.lean: WHERE `closing` SAYS YES THE READINGS OF A SEED AND OF A
CHALLENGE ARE DEFINED, if they are defined at every list of one element. A statement and its proof.

`k10_leads` (Leads.lean, beside this file) asks `Rd.DefAt` (Johnson/Top/H/BatFoldPlace.lean) where
`closing` says yes. A yes of `closing` says that each of its rounds drew just one element.
  `defAt_of_yes`: for any six readings ρ: if `closing` says yes on a list p of rounds, rdZ is
    defined at every list of one element and so is rdCh: `ρ.DefAt p`.
Limits. Nothing on what the readings return. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.Inv
import Johnson.Desc.First.Close.Law.Statement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv
open OnBytes.PscRun (drawnOf)

theorem defAt_of_yes {c : BatFoldCaller GE} {rB rE rR : Round} (ρ : Rd c rB rE rR) {P : Plan}
    {T : Statement} {g : Nat} {mask : Option Nat} {p : List Fmt.RoundView}
    {x : SingleRows × Statement} (h : closing P T g mask p = .ok x)
    (hZ : ∀ e, (ρ.rdZ [e]).isSome) (hC : ∀ e, (ρ.rdCh [e]).isSome) : ρ.DefAt p := by
  obtain ⟨_, xB, _, _, _, _, vB, vE, vR, _, eps, qs, gs, _, rfl, -, a2, -, -, a5, a6, -, -⟩ :=
    closing_inv (out := x.1) (S' := x.2) h
  constructor
  · intro r hr
    have : r = vB := by simpa using hr
    subst this
    rw [drawnOf_one a2]
    exact hZ xB
  · intro r hr
    have hr' : r = vE ∨ r ∈ List.take (Yc c).k vR := by simpa using hr
    rcases hr' with rfl | hr''
    · rw [drawnOf_one a5]
      exact hC eps
    · obtain ⟨e, he⟩ := roundsHold_drawn a6 r (List.mem_of_mem_take hr'')
      rw [he]
      exact hC e

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.defAt_of_yes
