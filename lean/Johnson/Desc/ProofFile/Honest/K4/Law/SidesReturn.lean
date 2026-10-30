-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SidesReturn.lean: CONDITIONAL. Statements with their proofs.

What is here: `Sides.of` RETURNS (Johnson/Desc/K4/Honest/Sides.lean: all that the second token
sumcheck's job and the batched sumcheck's job of the feed-forward layers' own rounds, the
sub-protocol K4, share), at every input w and all sampled values p whose lookup's point has la
coordinates and whose calls' points have the plan's sizes: WITH ONE OF ITS EIGHT RETURNS LEFT AS A
HYPOTHESIS (h8: the verifier's forms on the second token sumcheck's end values). In the place of two
hypotheses of `sides_of_plan` (Johnson/Road/K4/C/SidesOf.lean) it asks lighter ones: for h5, the
heads' weights: what they read at the blank structure (`QkRd`, Johnson/Road/K4/C/ClaimsQK.lean); for
h6, `openOf` at each claim: that the weights' layout is what the verifier's `wsLayOf` returns.
How. h5: `headWeights_some` (that file) at the blank structure, carried over by the law on two
structures of one skeleton (`headWeights_rel`, Johnson/Desc/First/K4/Returns/Pub/Claims.lean). h6:
`opens_return` (Law/OpenReturns.lean); that each claim passes the verifier's test on its sizes comes
out of `claimsB`, whose fourth test says so of the blank structure's claims, which are alike.

Not shown here. HYPOTHESES HERE: h8 (`termsForms_returns`, Johnson/Road/K4/C/TermsFormsOf.lean, has
it; Law/SidesWhole.lean joins the two); that `claimsB` is true (`claimsB_plan`,
Johnson/Road/K4/C/ClaimsBPlan.lean, has it from facts on the plan); that `QkRd` holds at the blank
structure (`qkRd_of`, Johnson/Road/K4/C/ClaimRdOf.lean, has it from the verifier's lines). That a
plan with the public facts `K4Plan` exists: `k4Plan_head` (Law/W/PlanHead.lean) has them at the
public parameters' own data of the layers, at each group below 12, under the library's hypothesis
`P5J.AtMgA` on the public files; that this hypothesis has a member at one place:
AtFullSide.Top.headMember_zFull (AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth); the two are joined by no statement. A RETURN ALONE. Nothing on soundness, on completeness
or on any other property.
No property is claimed.

  `claims_blank_fit`   out of `claimsB`: the list at zero challenges and an empty end point, each
      member passing the test on its sizes
  `heads_return`   the heads' weights, from `QkRd` at the blank structure
  `sides_return`   **`Sides.of` returns**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.OpenReturns
import Johnson.Road.K4.C.SidesOf
import Johnson.Road.K4.C.ClaimsQK

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (WsClaim WsShape HTailF2 wsClaimShape wsLayOf)
open OnBytes.Model.Layer (ClaimEnv TableAsk TableAt layTables tableAsks callsTS)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (envPub sides_of_plan QkRd headWeights_some)
open OnBytes.Flat (all_alike shape_alike)
open OnBytes.Desc.First.K4 (termsForms)
open OnBytes.Desc.First.K4.RtPub (claimsB zkFits blankClaims any_some skel_blank weightClaims_rel
  headWeights_rel claimTests_true)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)

variable {Q : K4Pub} {w : K4In} {p : Pts} {v : OnBytes.Model.Layer.Env}

/-- CONDITIONAL on the test and three facts on v. Out of `claimsB`: the panels' weight claims at
zero challenges and an empty end point return, and each passes the verifier's test on a claim's
sizes. -/
theorem claims_blank_fit (hB : claimsB Q.P Q.hp Q.g = true) (hy : v.y = Q.P.y) (hg : v.g = Q.g)
    (hz : zkFits Q.P v.zk = true) :
    ∃ TS cls, callsTS Q.P = some TS ∧
      ({ v := v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := Array.replicate Q.hp.lamS zeroE,
         rt := #[] } : ClaimEnv).weightClaims TS = some cls ∧
      ∀ c ∈ cls, (wsClaimShape Q.P.wsLay c).isOk = true := by
  unfold claimsB at hB
  obtain ⟨TS, hTS, hB⟩ := any_some hB
  obtain ⟨cP₀, hP₀, hB⟩ := any_some hB
  obtain ⟨cE₀, _, hB⟩ := any_some hB
  have S := skel_blank (hp := Q.hp) hy hg hz (rs := Array.replicate Q.hp.lamS zeroE)
    Array.size_replicate Q.P.rope #[]
  obtain ⟨cP, hP, aP⟩ := OnBytes.Desc.First.K4.RtPub.OptRel.of_right (weightClaims_rel S TS) hP₀
  have h4 := (claimTests_true hB).2.2.2
  have h5 : (cP₀ ++ cE₀).all (fun c => (wsClaimShape Q.P.wsLay c).isOk) = true := by
    simpa using h4
  rw [List.all_append, Bool.and_eq_true] at h5
  have h6 : cP.all (fun c => (wsClaimShape Q.P.wsLay c).isOk) = true :=
    (all_alike (fun _ _ hab => by rw [shape_alike Q.P.wsLay hab]) aP).trans h5.1
  exact ⟨TS, cP, hTS, hP, List.all_eq_true.1 h6⟩

/-- CONDITIONAL on `QkRd` at the blank structure and three facts on v. The heads' weights return. -/
theorem heads_return {s : WsShape} (hq : QkRd (blankClaims Q.P Q.hp Q.g) s) (hy : v.y = Q.P.y)
    (hg : v.g = Q.g) (hz : zkFits Q.P v.zk = true) :
    (({ v := v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := Array.replicate Q.hp.lamS zeroE,
        rt := #[] } : ClaimEnv).headWeights).isSome = true := by
  obtain ⟨AH, lfc, h0, _⟩ := headWeights_some hq
  have S := skel_blank (hp := Q.hp) hy hg hz (rs := Array.replicate Q.hp.lamS zeroE)
    Array.size_replicate Q.P.rope #[]
  obtain ⟨x, hx, _⟩ := OnBytes.Desc.First.K4.RtPub.OptRel.of_right (headWeights_rel S) h0
  rw [hx]
  rfl

variable {iU3 : ℕ} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}

/-- CONDITIONAL on every hypothesis named. **`Sides.of` RETURNS.** h8: the one return that stays a
hypothesis. -/
theorem sides_return (A : K4Plan hS pc Q.P Q.g tl D)
    (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hB : claimsB Q.P Q.hp Q.g = true) (hz : zkFits Q.P p.fo.zk = true)
    (hla : Q.P.y.h.la ≤ p.fo.zx.size) {sw s : WsShape} {lk : ℕ}
    (hws : wsLayOf sw true lk = .ok Q.P.wsLay) (hq : QkRd (blankClaims Q.P Q.hp Q.g) s)
    (h8 : (termsForms (envPub Q r.1 iU3 p.fo.zk)
      { fo := p.fo, PV := #[], ztF := #[], sW := 0, gp := #[], wpl := {}, sPv := 0, omV := #[],
        tV := {}, tT := some {} }).isSome = true) :
    ∃ S, Sides.of Q w p = some S := by
  have h5 := heads_return (v := envPub Q r.1 iU3 p.fo.zk) hq rfl rfl hz
  obtain ⟨⟨AH, lfc⟩, hw⟩ := Option.isSome_iff_exists.mp h5
  obtain ⟨TS₀, cls₀, hTS₀, hc₀, hs₀⟩ :=
    claims_blank_fit (v := envPub Q r.1 iU3 p.fo.zk) hB rfl rfl hz
  refine sides_of_plan A hU hl hB hz hla h5 (fun TS cls hTS hc => ?_) h8
  obtain rfl : TS₀ = TS := Option.some.inj (hTS₀.symm.trans hTS)
  obtain rfl : cls₀ = cls := Option.some.inj (hc₀.symm.trans hc)
  exact opens_return
    (c0 := { v := envPub Q r.1 iU3 p.fo.zk, wsLay := Q.P.wsLay, rope := Q.P.rope,
             rs := Array.replicate Q.hp.lamS zeroE, rt := #[] }) hws hc hw hs₀

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.claims_blank_fit
#print axioms ProofFile.Honest.K4.heads_return
#print axioms ProofFile.Honest.K4.sides_return
