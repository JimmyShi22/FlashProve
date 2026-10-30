-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ClaimsBPlan.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: THE TEST claimsB IS TRUE
AT THE PLAN's OWN ARGUMENTS, as a theorem and without evaluation
(Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean). It joins claimsB_of (ClaimsBOf.lean: the test from
what the claims read at the structure with every challenge and coordinate 0) with claimRd_of and
qkRd_of (ClaimRdOf.lean: what they read is there) and the four facts on numbers of ClaimsNums.lean.
So the test follows from the verifier's lines that make the layout, the reads and the layout of the
weights, with the ties of the sizes and two facts on the plan. THAT THE CLAIMS ARE AT MOST 4096,
THAT A BLOCK's BITS ARE AT MOST THE WIDTH's AND THAT THE VOCABULARY IS NOT EMPTY ARE NO HYPOTHESES:
they come off the program's own tests. General in the sizes. A statement and its proof.

  **`claimsB_plan`**   claimsB P hp g = true.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. AT A LAYOUT
WHOSE EIGHT LINES OF CALLS ARE THE LIBRARY's, UNDER THE LIBRARY's ELEVEN SWITCHES ALONE, at profile
4, AND A LAYOUT OF THE WEIGHTS THAT wsLayOf RETURNS FOR A MODEL WITH ROUTED EXPERTS. THE TIES OF THE
SIZES ARE HYPOTHESES: the library's sizes D agree with the layers' shape (Z) and with the weights'
shape (Zw); the two shapes have as many layers (hsL); the weights' shape has the public data's
vocabulary (hV). TWO FACTS ON THE PLAN ARE HYPOTHESES: its rounds and its weight claims are the
functions lamSOf and nclOf of the layout (h1, h2: the library's planG_sizes,
Johnson/Road/K4/PlanSizes.lean, has both where the plan is what planG returns). Public data alone:
whether a claim IS THERE and how long its parts are; nothing on its elements.
No property is claimed.
-/
import Johnson.Road.K4.C.ClaimsBOf
import Johnson.Road.K4.C.ClaimRdOf
import Johnson.Road.K4.C.ClaimsNums

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Pub HPlan2 layout readsOf lamSOf nclOf)
open OnBytes.Desc.First.K4.RtPub (claimsB)
open Inst.Model.FFSeg (Dim)

/-- **THE TEST claimsB IS TRUE AT THE PLAN's OWN ARGUMENTS.** CONDITIONAL: on the verifier's lines,
the switches, profile 4, a group of the layout, the eight lines, the ties of the sizes (Z, Zw, hsL,
hV), the layout of the weights (hlw) and two facts on the plan (h1, h2). -/
theorem claimsB_plan {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {P : Pub}
    {hp : HPlan2} {g : ℕ} {s : WsShape} {D : Dim} {lk : ℕ} (hy : layout h pc = .ok P.y)
    (S : Switches h) (h4 : h.p4 = true) (hg : g < P.y.NGr) (hrd : readsOf P.y = .ok P.rd)
    (hN : LinesAre P.y) (Z : Sized h D) (Zw : SizedW s D.P) (hsL : s.L = h.L)
    (hlw : wsLayOf s true lk = .ok P.wsLay) (hV : s.V = P.V) (h1 : hp.lamS = lamSOf P.y)
    (h2 : hp.NCL = nclOf P.y g) : claimsB P hp g = true := by
  have es := (admitted_of_layout hy S.p3).shape
  refine claimsB_of hy S hrd hN (claimRd_of hy S h4 hg hN Z Zw hsL hlw h1) (qkRd_of hy S hN Z Zw)
    (by rw [hsL, es]) hV (hV ▸ vocab_pos hlw) ?_ (ls_le_lPd hy) h2 (by rw [h2]; exact ncl_le hy g)
  rw [(OnBytes.Road.K4.laySizes_of_layout hy).lPd, es]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.claimsB_plan
