-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/Pub34At.lean: A DEFINITION.

What is here. One of the library's public structures `Pub34` (Johnson/Road/Rows/LayerEnds34.lean),
MOVED TO ANOTHER END POINT OF THE SECOND TOKEN SUMCHECK. `pub34At X z sh …` is X but for: the end
point (in the claims' environment, in the sumcheck's structure and in the hearing) is z; what stands
for the shown values is sh; the named points, the list of tables, the panels, the weight claims and
the end of the batched sumcheck are made anew. So from one structure at a hearing (the library's
`pub34_of_hear_run` makes one) there is one at each token's corner: the point of zeros and ones that
spells the token's number (`bitsOf lt i`). TokAtY.lean's `tokAll_y` asks such a structure. The moved
structure need not come from any run: its sumcheck's structure keeps the old rounds under a new end
point.

  `pub34At`   **the structure at another end point**

Limits. A definition. WHAT IS MADE ANEW IS GIVEN WITH ITS PROOF: six hypotheses, each a return of
one of the verifier's public functions at the new letters or a public fact: `pointsOf`, `funsOf`,
`panelsT`, `weightClaims`, `stackEnd` return; the number of rounds is the logarithm of the new
panels' places. Nothing here shows one of them; TokRetOf.lean's `tokRet_of` shows the six at a
token's corner, under its own hypotheses. That the rotary tables fit at the new end point is no
hypothesis: RopeAny.lean's `rope_of_pub` has it from X's own field. THE FULL SIZE ALONE (X). No
theorem says that a structure X exists (the head of Johnson/Road/Rows/LayerEnds34Ref.lean). Nothing
on a world or a value. The library's `OnBytes.Road.K4.PubAt` (Johnson/Road/K4/PubAt.lean: a
structure's ties to a hearing) is another thing.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.RopeAny

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E ceilLog2)
open OnBytes.Model (WsClaim HFun)
open OnBytes.Model.Layer (Panels StackEnd pointsOf funsOf panelsT panelsA placePanels stackEnd)
open OnBytes.Road.Rows (Pub34)

/-- **The structure X at the end point z, with sh for the shown values.** pts, funs, pans, cl, fin:
what the verifier's public functions return at the new letters. THE FULL SIZE ALONE (X). -/
noncomputable def pub34At (X : Pub34 Cb.Gl.E) (z sh : Array E) (pts : List (String × Array E))
    (funs : Array HFun) (pans : Panels) (cl : List WsClaim) (fin : StackEnd)
    (hpts : pointsOf X.p.v.y { X.H with tT := some { X.tT with r := z } } X.hd X.hd2 = some pts)
    (hfun : funsOf X.p.v.y X.H.fo pts X.r.2.1 = some funs)
    (hp : panelsT { X.p with shownT := sh } X.TS (panelsA { X.p with shownT := sh } {}) =
      some pans)
    (hcl : ({ X.c with rt := z } : OnBytes.Model.Layer.ClaimEnv).weightClaims X.TS = some cl)
    (hst : stackEnd X.p.v.y (placePanels pans.bl).1 X.c.rs X.lam X.om X.H1 X.V X.shownA X.shownB =
      some fin)
    (hlam : (ceilLog2 (placePanels pans.bl).2 == X.lam) = true) : Pub34 Cb.Gl.E :=
  { X with
    p := { X.p with shownT := sh }
    c := { X.c with rt := z }
    H := { X.H with tT := some { X.tT with r := z } }
    tT := { X.tT with r := z }
    pts := pts, funs := funs, pans := pans, cl := cl, fin := fin
    hy := X.hy, hs := X.hs, hg := X.hg, hrd := X.hrd, hl := X.hl, ht := X.ht, hN := X.hN
    hsx := X.hsx, hsy := X.hsy, hzk := X.hzk, he := X.he, hZ := X.hZ, hzt := X.hzt, hm := X.hm
    hs0 := X.hs0, hpt := X.hpt, env := X.env, hlw := X.hlw
    hcrt := rfl
    R := rope_of_pub X z
    htm := X.htm
    hpts := hpts, hfun := hfun
    hT := rfl
    hTS := X.hTS
    hp := hp, hcl := hcl, hst := hst, hlam := hlam
    hHe := X.hHe, hw := X.hw, hparts := X.hparts, hpad := X.hpad, hrs := X.hrs
    hKT := X.hKT, hinv := X.hinv, hsB0 := X.hsB0 }

end ProofFile.Honest.K4
