-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Wa7Meets.lean: THE STRUCTURE WaK6 (Johnson/Desc/Kinds/Law/WtJointAt.lean:
what the joining of the merge's sentence with the output head's asks of the verifier's state in
front of the merge) FROM ITS FIRST SIX CLAUSES, IN THE GOALS' SCOPE: its seventh, on LeftTies, is
paid by wa7_in_scope (Johnson/Desc/Kinds/Law/LeftTiesInScope.lean).

Why this file. wa7_in_scope was typed beside WaK6, in another file with other opened namespaces.
That its conclusion is WaK6's seventh clause was held as text alone. Here the two stand in one
file, and WaK6 is built with wa7_in_scope in the seventh place: so Lean decides the match.

Main name (namespace VerifiableInference.Desc.Kinds.Head.Law.InScope).
  waK6_of_six: the six clauses as premises, at the public numbers X in scope: WaK6 X V' sF.

Every letter under "there is": none in the statement (WaK6's own six are given by the premises'
letters).
What it does not say. THAT ANY OF THE SIX PREMISES HOLDS AT ANY STATE. Only in the goals' scope, at
the full size. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.WtJointAt
import Johnson.Desc.Kinds.Law.LeftTiesInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model.Verify (publicOf Public)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaK6)

variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Public}

/-- **WaK6 from its first six clauses, in scope.** -/
theorem waK6_of_six (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) {V' : ℕ} {s s' sF : S} {rv : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {cov : OnBytes.Model.Head.Covered}
    (t : OnBytes.Model.Head.Tables)
    (c1 : (blockAt X.hS (readsOf X) (workOf X) 24).decide s rv gs = .ok s')
    (c2 : WellLaid ((seatAt X.hS (readsOf X)).ledger s)) (c3 : Canonical rv) (c4 : KeptWFo s' sF)
    (c5 : sF.covered X.T V' = .ok cov)
    (c6 : ∀ o' x claim, sF.here = .head o' → o'.x = some x → o'.claim = some claim →
      First.Look.weightsClaim (runAt X cov x t) X.layers.wsLay = .ok claim) :
    WaK6 X V' sF :=
  ⟨s, s', rv, gs, cov, t, c1, c2, c3, c4, c5, c6, wa7_in_scope hZ hR h cov t c1 c4⟩

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.waK6_of_six
