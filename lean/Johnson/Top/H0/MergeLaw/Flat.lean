-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Flat.lean: the merge's hearing against the library's flat text of the merge.
Theorems with their proofs.

Main names:
  `hear_of_flat`: where `flatForkEnd` (OnBytes/K/Kc/QuietLink.lean) returns, `mergeHear`
    (Johnson/Desc/First/Fork/MergeKind.lean) says yes and returns the same, at any number of claims.
  `flat_later`: so `flatForkEnd` keeps the ledger (`OnBytes.PscRun.Later`).

`claimFits_eq` (Johnson/Top/H0/MergeLaw/Fits.lean) is spent: the flat text asks the older test on a
claim's sizes, `mergeHear` its own.

Limits. One direction: nothing where `flatForkEnd` refuses. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Keeps
import Johnson.Top.H0.MergeLaw.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (E)
open OnBytes.K.Kc
open OnBytes.Model (Fork WsLay WsClaim WsForkOut)
open VerifiableInference.Desc (need named)
open Johnson.Desc.First.ForkMerge (mergeHear)

/-- **Where the library's flat text of the merge (`flatForkEnd`, OnBytes/K/Kc/QuietLink.lean)
returns, `mergeHear` says yes and
returns the same.** So whatever is proved of `mergeHear`'s yes holds of `flatForkEnd`'s return, at
any number of claims: wherever a text calls it. -/
theorem hear_of_flat {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F F' : Fork} {t t' : Tape}
    {wo : WsForkOut}
    (h : flatForkEnd lay cl sv F t = some (wo, F', t')) : mergeHear lay cl sv F t = .ok (wo, F', t')
        := by
  unfold flatForkEnd at h
  obtain ⟨_, F1, t1, a1, h⟩ := bind_inv h
  obtain ⟨g1, e1, e1'⟩ := must_inv a1
  obtain ⟨_, F2, t2, a2, h⟩ := bind_inv h
  obtain ⟨g2, e2, e2'⟩ := must_inv a2
  obtain ⟨_, F3, t3, a3, h⟩ := bind_inv h
  obtain ⟨g3, e3, e3'⟩ := must_inv a3
  obtain ⟨⟨o, rho⟩, F4, t4, a4, h⟩ := bind_inv h
  obtain ⟨r5, e5, e5'⟩ := ret_inv h
  subst e1 e1' e2 e2' e3 e3' e5 e5'
  unfold Fl.wsForkMerge at a4
  obtain ⟨rho', G1, u1, b1, a4⟩ := bind_inv a4
  obtain ⟨p0, G2, u2, b2, a4⟩ := bind_inv a4
  obtain ⟨⟨rm, p1⟩, G3, u3, b3, a4⟩ := bind_inv a4
  obtain ⟨⟨sFv, p2⟩, G4, u4, b4, a4⟩ := bind_inv a4
  obtain ⟨fvp, G5, u5, b5, a4⟩ := bind_inv a4
  obtain ⟨r6, e6, e6'⟩ := ret_inv a4
  subst e6 e6'
  unfold Fl.pscBegin at b2
  obtain ⟨v, H1, w1, c1, b2⟩ := bind_inv b2
  obtain ⟨q, H2, w2, c2, b2⟩ := bind_inv b2
  obtain ⟨r7, e7, e7'⟩ := ret_inv b2
  subst e7 e7' r7
  simp only [Prod.mk.injEq] at r6
  obtain ⟨ro, rr⟩ := r6
  subst ro rr r5
  have hcap : (Array.emptyWithCapacity lay.lk : Array E) = #[] := by simp
  rw [hcap] at b3
  have g3' : (cl.all fun c => Johnson.Desc.First.ForkMerge.claimFits lay c) = true := by
    simpa only [claimFits_eq] using g3
  unfold mergeHear
  simp [need, named, g1, g2, g3', b1, c1, c2, b3, b4, b5, bind, Except.bind, pure, Except.pure]

open OnBytes.PscRun (Later) in
/-- So the library's flat text of the merge keeps the ledger. -/
theorem flat_later {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F F' : Fork} {t t' : Tape}
    {wo : WsForkOut}
    (h : flatForkEnd lay cl sv F t = some (wo, F', t')) : Later F F' := hear_later (hear_of_flat h)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.hear_of_flat
