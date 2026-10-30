-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SigOfPub.lean: CONDITIONAL.

What is here. The library's structure `SigFits` (Johnson/Road/FormsKeysPortSig.lean), which
PassOf.lean, TokFitsOf.lean and JoinPub.lean ask as a hypothesis, as one call: at the honest side's
own environment of the panels, in every world with the true entries, from one of the library's
public structures `Pub34` (Johnson/Road/Rows/LayerEnds34.lean) whose environments of the panels and
of the claims are the honest side's. The letters come out as these three files spell them: the
second token sumcheck's end point is the claims' environment's, read; the cells are those of the
matrices Mm.

  `sig_of_pub`   **`SigFits` at the honest side's environment**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE: a `Pub34` holds the floor on the calls'
lengths among its fields, which the small public example does not meet. HYPOTHESES: such a structure
X is given, at the reading `Reading.gl`; its two environments are the honest side's (Xp, Xc):
nothing here makes one (JoinHeard.lean's `env_tied` has the two equations at a hearing); the table
of scales is X's (hscl); the world's entries are the true ones at X's tables and the matrices Mm
(hW): its slots are free. One structure serves one end point: at a token's corner another is wanted:
Pub34At.lean's `pub34At` makes it. No example is known.

No property is claimed.
-/
import Johnson.Road.K4.StackPub34
import Johnson.Road.K4.EntryTrue
import Johnson.Road.K4.C.StackPanelsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E)
open OnBytes.Model (Reading World)
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Road (pt SigFits sclOf cellsAt cellsOf zOf zetaOf Mats)
open OnBytes.Road.K4 (sigFits_of_pub34 reads_true_pub entryOf)
open OnBytes.Road.K4.C (sidesEnv)
open Inst.Model (Scl)

/-- **`SigFits` AT THE HONEST SIDE's ENVIRONMENT OF THE PANELS, IN EVERY WORLD WITH THE TRUE
ENTRIES.** CONDITIONAL: on every hypothesis named. THE FULL SIZE ALONE (X). sh: what stands in the
place of the second token sumcheck's shown values. -/
theorem sig_of_pub [scl : Scl] (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam)
    {S : OnBytes.Desc.First.K4.Honest.Sides} {sh : Array E} {c : ClaimEnv}
    (Xp : X.p = sidesEnv S sh) (Xc : X.c = c) (Wo : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (hW : Wo.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm) :
    SigFits Reading.gl Wo (sidesEnv S sh) c X.h X.pc X.s X.D X.lk (c.v.g * c.v.y.Lam)
      (cellsAt S.v.y Mm) (cellsOf X.D (cellsAt S.v.y Mm)) (pt Reading.gl X.Zp)
      (zOf Reading.gl X.H.fo.zx X.H.fo.zy) (pt Reading.gl c.rt) (zetaOf Reading.gl c X.D)
      X.tb := by
  have S0 := sigFits_of_pub34 X Wo Mm (reads_true_pub X Mm hW)
  rw [← hscl, Xρ, Xc] at S0
  have e : X.p.v.y = S.v.y := by rw [Xp]; rfl
  rw [e] at S0
  rw [← Xp]
  exact S0

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sig_of_pub
