-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/FitStackPub.lean: CONDITIONAL.

What is here. The honest side's function for the batched sumcheck returns a job of its call's public
shape, at every input w, WITH NO RETURN LEFT AS A HYPOTHESIS OF ANY FUNCTION THAT READS THE INPUT OR
A SAMPLED VALUE (`stack_fit_pub`): from public facts on the plan and the sizes of the sampled and
shown values. It is `stack_fit` (Law/W/FitStack.lean) with its three returns paid: that the honest
side's common data are made, by `sides_whole` (Law/SidesWhole.lean); that its list of placed panels
returns, fills lamS bits and counts the plan's number of weight claims, and that the verifier's end
returns over it, by `panels_return` (Johnson/Road/K4/C/PanelsOf.lean).

  `stack_fit_pub`   the fourth of the seven jobs' clauses of k4MakersFit, general in w, p and the
      shown values.

Not shown here. THE PUBLIC HYPOTHESES: K4Plan (ITS FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE
LIBRARY's ELEVEN SWITCHES); the shape's switch p4 is on (hp4); the plan names the array of the reads
(hU); the verifier's laying of the tables returns (hl); FIVE RETURNS OF PUBLIC FUNCTIONS ARE THUS
LEFT: hl, hws, and K4Plan's lay, scales and reads; that array has a column (hK); the first free
entry's row fits 32 bits (hb); THE TWO DEAR PUBLIC TESTS claimsB AND pansB ANSWER TRUE (hB, hPB):
hypotheses HERE; Johnson/Road/K4/C/ClaimsBPlan.lean and PansBPlan.lean have them from the plan; the
weights' layout is one that wsLayOf returns for a model with routed experts (hws); QkRd at the blank
structure (hq). THE SIZES: what the lookup has sampled (hz, hla); two weights of the passes (hom);
the end point rt has lt coordinates (hrt); the shown values are as many as the second token sumcheck
shows (hsh: idle beneath; asked because Johnson/Road/K4/C/PanelsOf.lean's panels_return asks it).
That all of these hold together: under the library's h Law/MakersFitHead.lean pays them together;
the side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth); h is no hypothesis of this file's statement, and of its own hypotheses together no
example is laid here. What the job holds is not shown. By a walk of import lines the closure holds
no module under Johnson/RecCompile/, Johnson/Goal/ or Johnson/D/. Nothing on soundness, on
completeness or on any other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FitStack
import Johnson.Desc.ProofFile.Honest.K4.Law.SidesWhole
import Johnson.Road.K4.C.PanelsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E)
open OnBytes.Model (HTailF2 WsShape wsLayOf)
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks nEndT)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (panels_return QkRd)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub (claimsB zkFits blankClaims pansB blankEnv nclpOf)
open Inst.Model.FFSeg (Dim)

variable {Q : K4Pub} {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2}
  {D : Dim} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {iU3 : ℕ}

/-- **THE BATCHED SUMCHECK's JOB IS MADE AND HAS ITS CALL's SHAPE, FROM PUBLIC FACTS AND SIZES.**
CONDITIONAL: on every hypothesis named. -/
theorem stack_fit_pub (A : K4Plan hS pc Q.P Q.g tl D) (hp4 : hS.p4 = true)
    (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hK : ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 ≠ 0)
    (hb : r.2.2 / ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32)
    (hB : claimsB Q.P Q.hp Q.g = true)
    (hPB : pansB Q.P (blankEnv Q.P Q.hp Q.g iU3 r.1) Q.hp.lamS (nclpOf Q.hp Q.g) = true)
    {sw s : WsShape} {lk : ℕ} (hws : wsLayOf sw true lk = .ok Q.P.wsLay)
    (hq : QkRd (blankClaims Q.P Q.hp Q.g) s) (w : K4In) {p : Pts} {shownT : Array E}
    (hz : zkFits Q.P p.fo.zk = true) (hla : Q.P.y.h.la ≤ p.fo.zx.size)
    (hom : p.om.size = 2) (hrt : p.rt.size = Q.P.y.h.lt) (hsh : shownT.size = nEndT Q.P.y) :
    ∃ j, jobStack Q w p shownT = some j ∧
      k4JobFits (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - (if Q.g == 0 then 1 else 0)))) j = true := by
  obtain ⟨S, hS'⟩ := sides_whole (w := w) (p := p) A hp4 hU hl hK hb hB hz hla hws hq
  obtain ⟨pans, _, hPan, hc, ho, hn, hEnd⟩ := panels_return hS' hU hl hPB hsh
  exact stack_fit A hl hS' hPan hc hom (ho.trans hn)
    (fun rs om H1 V a b h1 h2 h3 h4 => hEnd rs om H1 V a b h1 h2 h3 (h4.trans (ho.trans hn)))
    hrt

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.stack_fit_pub
