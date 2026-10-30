-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/PublicHead.lean: CONDITIONAL.

Not shown here. THAT h : AtMgA CAN HOLD: The side library AtFullSide proves, with no hypothesis,
that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). hG: the public
parameters have a plan for the group: a field of `LaidK4` (Law/SeatedHead.lean), which follows from
h at each of the twelve groups (`laid_at`, Law/LaidAtGroup.lean): so hG asks nothing beyond h; hg: g
< 12. THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on
soundness, on completeness or on any other property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 17 modules under Johnson/Goal/ and at 5 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 22 is not counted: all the numbers are floors. They come with
h and with Johnson/Road/K4/RefInScope.lean, whose `refPub_in_scope` calls a statement of a file
under Johnson/Goal/.

Three facts on public numbers, at the library's own public parameters: the first is the hypothesis T
of Law/W/HotHead.lean; the second is the library's `deep_ref`, said again; the third is spent in
Law/W/HotStand.lean: the numbers of the plan's trees are the library's at its reference sizes
(`TreesFit`, Johnson/Road/FormsKeysLook.lean); the positions' bits are at most a tree's depth; and
they are the layout's number of position bits, at which the verifier of the feed-forward layers' own
rounds (sub-protocol K4) cuts its token point. One statement with its proof: calls of the library's
`refPub_in_scope` (Johnson/Road/K4/RefInScope.lean), `lines_calls`, `treesFit_of_layout`,
`laySizes_of_layout` and `deep_ref`, as Johnson/Road/K4/K4PinsKeysPub.lean calls the first four.

  `public_head`   **`TreesFit X.y.fo DF`, `DF.lT ≤ Dk DF` and `DF.lT = X.y.h.lt`**, X := the public
      parameters under h.
-/
import Johnson.P5J.MgAtAll
import Johnson.Road.K4.RefInScope
import Johnson.Road.K4.K4PinsRider
import Johnson.Road.FormsKeysLookT
import Johnson.Road.FormsKeysCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Road (TreesFit treesFit_of_layout lines_calls)
open OnBytes.Road.K4 (refPub_in_scope laySizes_of_layout deep_ref)
open OnBytes.Maker (WholeD)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Dk)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **THREE PUBLIC NUMBERS AT THE LIBRARY's OWN PUBLIC PARAMETERS.** CONDITIONAL: on h, hg and hG.
-/
theorem public_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} {hp : HPlan2}
    (hg : g < 12) (hG : (P5J.At.X Zp).G[g]? = some hp) :
    TreesFit (P5J.At.X Zp).y.fo DF ∧ DF.lT ≤ Dk DF ∧ DF.lT = (P5J.At.X Zp).y.h.lt := by
  obtain ⟨s0, HL, _, _⟩ := (refPub_in_scope h.scope h.reads h.pubOne hg).lines hp hG
  have PL := HL #[]
  obtain ⟨h8, Hc⟩ := lines_calls PL.hN
  refine ⟨?_, deep_ref, ?_⟩
  · exact treesFit_of_layout
      (v := ⟨(P5J.At.X Zp).layers.y, (P5J.At.X Zp).layers.sc, g, 0, 0, [], #[]⟩) PL.hy PL.S PL.Z
      PL.hc h8 fun cc => by
        obtain ⟨cd, a1, a2⟩ := Hc cc
        exact ⟨cd, a1, a2, PL.hfl cc⟩
  · have e : (P5J.At.X Zp).layers.y.h = Verify.layerShape (P5J.At.X Zp).P :=
      (laySizes_of_layout PL.hy).shape
    show DF.lT = (P5J.At.X Zp).layers.y.h.lt
    rw [e]
    exact PL.Z.lT

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.public_head
