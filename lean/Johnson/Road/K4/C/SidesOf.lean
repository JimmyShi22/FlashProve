-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/SidesOf.lean: CONDITIONAL. Statements with their proofs.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: WHEN `Sides.of` RETURNS
(Johnson/Desc/K4/Honest/Sides.lean: all that the second token sumcheck's job and the batched
sumcheck's job share), at every input w and all sampled values p. Its text has eight steps that can
refuse. `sides_of_parts`: where the eight return, it returns. `sides_of_plan`: FIVE OF THE EIGHT ARE
PAID from public premises: the structure that the forms read (`envOf_pub`, RowMapsOf.lean); the
numbers of the calls with terms, and the panels' weight claims at blank challenges (out of the test
with code `claimsB`, Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean, by that folder's law on two
structures of one skeleton); the last coordinates of the lookup's point; the two tensors of the
gated products (`tens_su`, ReadsNine.lean).

Not shown here. THREE OF THE EIGHT STAY HYPOTHESES OF `sides_of_plan`: h5, the heads' weights
return; h6, `openOf` returns at each claim of the list; h8, the verifier's forms on the second token
sumcheck's end values return (Johnson/Desc/ProofFile/Honest/K4/Law/SidesReturn.lean has h5 and h6
from lighter premises; TermsFormsOf.lean has h8). That `claimsB` is true: a hypothesis here
(`claimsB_plan`, ClaimsBPlan.lean, has it from facts on the plan). That a plan with the public facts
`K4Plan` exists: at the public parameters' own data of the layers that is shown on conditions
(`k4Plan_head`, Johnson/Desc/ProofFile/Honest/K4/Law/W/PlanHead.lean); no example without a
condition is known. A RETURN ALONE: nothing on what any field is worth. Nothing on soundness, on
completeness or on any other property. No property is claimed.

  `sides_of_parts`   where the eight steps return, `Sides.of` returns
  `claims_blank`   out of `claimsB`: the calls' numbers; the panels' claims at zero challenges and
      an empty end point
  `sides_of_plan`   **`Sides.of` returns**, three returns left as hypotheses
-/
import Johnson.Road.K4.C.RowMapsOf
import Johnson.Road.K4.C.ReadsNine
import Johnson.Desc.First.K4.Returns.Pub.ClaimsB
import Johnson.Desc.K4.Honest.Sides

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env ClaimEnv TableAsk TableAt layTables tableAsks callsTS)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Desc.First.K4 (termsForms)
open OnBytes.Desc.First.K4.RtPub (claimsB zkFits any_some skel_blank weightClaims_rel)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts Tab Open Sides matsOf envOf openOf gatedTabs)
open Inst.Model.FFSeg (Dim)

variable {Q : K4Pub} {w : K4In} {p : Pts} {v : Env}

/-- CONDITIONAL on the eight returns. **WHERE ITS EIGHT STEPS RETURN, `Sides.of` RETURNS.** -/
theorem sides_of_parts {TS : List Nat} {Z : Array E} {cls : List WsClaim}
    {hw : Array E × Array E} {opens : Array Open} {gt : Tab × Tab} {ends : List Aff}
    (h1 : envOf Q p = some v) (h2 : callsTS Q.P = some TS)
    (h3 : (lastOf p.fo.zx Q.P.y.h.la).toOption = some Z)
    (h4 : ({ v := v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := Array.replicate Q.hp.lamS zeroE,
             rt := #[] } : ClaimEnv).weightClaims TS = some cls)
    (h5 : ({ v := v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := Array.replicate Q.hp.lamS zeroE,
             rt := #[] } : ClaimEnv).headWeights = some hw)
    (h6 : cls.toArray.mapM (openOf Q.P.wsLay w.w (Q.g * Q.P.y.Lam)) = some opens)
    (h7 : gatedTabs Q w = some gt)
    (h8 : termsForms v
      { fo := p.fo, PV := #[], ztF := #[], sW := 0, gp := #[], wpl := {}, sPv := 0, omV := #[],
        tV := {}, tT := some {} } = some ends) :
    ∃ S, Sides.of Q w p = some S := by
  obtain ⟨hw1, hw2⟩ := hw
  obtain ⟨gl, gr⟩ := gt
  simp only [Sides.of, h1, h2, h3, h4, h5, h6, h7, h8, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]
  exact ⟨_, rfl⟩

/-- CONDITIONAL on the test and three facts on v. Out of `claimsB`: the numbers of the calls with
terms are there, and the panels' weight claims return at zero challenges and an empty end point. -/
theorem claims_blank (hB : claimsB Q.P Q.hp Q.g = true) (hy : v.y = Q.P.y) (hg : v.g = Q.g)
    (hz : zkFits Q.P v.zk = true) :
    ∃ TS cls, callsTS Q.P = some TS ∧
      ({ v := v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := Array.replicate Q.hp.lamS zeroE,
         rt := #[] } : ClaimEnv).weightClaims TS = some cls := by
  unfold claimsB at hB
  obtain ⟨TS, hTS, hB⟩ := any_some hB
  obtain ⟨cP₀, hP₀, _⟩ := any_some hB
  have S := skel_blank (hp := Q.hp) hy hg hz (rs := Array.replicate Q.hp.lamS zeroE)
    Array.size_replicate Q.P.rope #[]
  obtain ⟨cP, hP, _⟩ := OnBytes.Desc.First.K4.RtPub.OptRel.of_right (weightClaims_rel S TS) hP₀
  exact ⟨TS, cP, hTS, hP⟩

variable {iU3 : ℕ} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  {hS : Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}

/-- CONDITIONAL on every hypothesis named. **`Sides.of` RETURNS**, at every input and all sampled
values whose lookup's point has la coordinates and whose calls' points have the plan's sizes. h5,
h6, h8: three returns that stay hypotheses. -/
theorem sides_of_plan (A : K4Plan hS pc Q.P Q.g tl D)
    (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hB : claimsB Q.P Q.hp Q.g = true) (hz : zkFits Q.P p.fo.zk = true)
    (hla : Q.P.y.h.la ≤ p.fo.zx.size)
    (h5 : (({ v := envPub Q r.1 iU3 p.fo.zk, wsLay := Q.P.wsLay, rope := Q.P.rope,
              rs := Array.replicate Q.hp.lamS zeroE,
              rt := #[] } : ClaimEnv).headWeights).isSome = true)
    (h6 : ∀ TS cls, callsTS Q.P = some TS →
      ({ v := envPub Q r.1 iU3 p.fo.zk, wsLay := Q.P.wsLay, rope := Q.P.rope,
         rs := Array.replicate Q.hp.lamS zeroE, rt := #[] } : ClaimEnv).weightClaims TS = some cls →
      ∀ c ∈ cls, (openOf Q.P.wsLay w.w (Q.g * Q.P.y.Lam) c).isSome = true)
    (h8 : (termsForms (envPub Q r.1 iU3 p.fo.zk)
      { fo := p.fo, PV := #[], ztF := #[], sW := 0, gp := #[], wpl := {}, sPv := 0, omV := #[],
        tV := {}, tT := some {} }).isSome = true) :
    ∃ S, Sides.of Q w p = some S := by
  obtain ⟨TS, cls, hTS, hcl⟩ := claims_blank (v := envPub Q r.1 iU3 p.fo.zk) hB rfl rfl hz
  obtain ⟨hw, hhw⟩ := Option.isSome_iff_exists.mp h5
  obtain ⟨ends, hen⟩ := Option.isSome_iff_exists.mp h8
  obtain ⟨opens, hop⟩ := amapM_there (g := openOf Q.P.wsLay w.w (Q.g * Q.P.y.Lam)) cls.toArray
    (fun c hc => h6 TS cls hTS hcl c (by simpa using hc))
  obtain ⟨ts, tu, hts, htu⟩ := tens_su A
  have h7 : ∃ gt, gatedTabs Q w = some gt := by
    simp only [gatedTabs, hts, htu, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    exact ⟨_, rfl⟩
  obtain ⟨gt, hgt⟩ := h7
  have h3 : ∃ Z, (lastOf p.fo.zx Q.P.y.h.la).toOption = some Z := by
    unfold lastOf cutLast
    rw [if_neg (by omega)]
    exact ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ := h3
  exact sides_of_parts (envOf_pub hU hl p) hTS hZ hcl hhw hop hgt hen

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.sides_of_parts
#print axioms OnBytes.Road.K4.C.claims_blank
#print axioms OnBytes.Road.K4.C.sides_of_plan
