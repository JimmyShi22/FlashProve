-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3JoinVal.lean: THE LOOKUP's CLAIM "THE JOIN" (claimJoin,
OnBytes/Tie/Pv/Lookup/Forest/FoClaims.lean) IS THE LIBRARY's LEFT SIDE OF THE JOIN AT AN ATTENTION
SUB-PROOF's END (joinVal, Cb/Pv/Att/End/Join.lean), where the lookup has four calls: at the public
part made of the lookup's own ends. One theorem: two normal forms side by side. No error term. NO
SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: two values in a field.
Used by K05KeysAt.lean and K05KeysClause.lean (Johnson/Desc/First/Att/).
  Wanted by the files of the kind K5, which owe worth "keys" at an attention
  segment: K5's half: that its own public part of the join is joinPubOf, and its hidden value at the
  end of the key side the worth of the ends' form.
LETTERS: h, lm, jLK, rs, nu, kf: claimJoin's own; E: a field.

Main names:
  `joinPubOf h lm jLK rs`: alpha, theta: the ends'; e c: the weight of call c at the ends' point of
    the trees' numbers (eK); pad: the term of the trees that hold only padding.
  `claimJoin_joinVal`: h.NC = 4 gives claimJoin h lm jLK rs nu kf = joinVal (joinPubOf h lm jLK rs)
    (fun c => kf c) (the worth of the ends' form for the end of the key side).

How it goes. claimJoin is the value of joinK; val_joinK (OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean) is
its normal form: a sum over range h.NC; joinVal's sum runs over Fin 4.

Limits. Four calls alone. Nothing on who pays either side's being 0.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoClaims
import OnBytes.Tie.Pv.Lookup.Port.FoJoin
import Cb.Pv.Att.End.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo Cb.Fo.NumsEq Cb.Fo.Pin
open FoNums Finset OnBytes.Model OnBytes.Ends
open Cb.Pv.Att.End (JoinPub joinVal)

section
variable {E : Type} [Field E]

/-- The public part of the join, off the lookup's own ends. -/
def joinPubOf (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds E) : JoinPub E where
  alpha := (endsOf h lm jLK rs).alpha
  theta := (endsOf h lm jLK rs).theta
  e := fun c => eK h (endsOf h lm jLK rs).zy c.val
  pad := ∑ i ∈ range (2 ^ h.rK - h.NT), (eqTabK (endsOf h lm jLK rs).zy).getD (h.NT + i) 0 *
    ((endsOf h lm jLK rs).alpha - padKeyK h (endsOf h lm jLK rs).theta 0)

/-- **The lookup's claim "the join" is the library's left side of the join.** -/
theorem claimJoin_joinVal (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds E) (ν : Pl → E) (kf : ℕ → E)
    (h4 : h.NC = 4) :
    claimJoin h lm jLK rs ν kf =
      joinVal (joinPubOf h lm jLK rs) (fun c => kf c.val)
        (AffK.val ((endsOf h lm jLK rs).cEndF, (endsOf h lm jLK rs).cEndC) ν) := by
  have e4 := Fin.sum_univ_eq_sum_range (fun c : ℕ => eK h (endsOf h lm jLK rs).zy c *
    ((endsOf h lm jLK rs).alpha - (c : E) * (endsOf h lm jLK rs).theta - kf c)) 4
  unfold claimJoin joinVal joinPubOf
  rw [val_joinK, h4]
  simp only [AffK.val_ofConst]
  rw [← e4]

end

end Fo

#print axioms Fo.claimJoin_joinVal
