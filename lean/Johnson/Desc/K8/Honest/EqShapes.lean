-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqShapes.lean: THE SMALLNESS TEST: A BRIDGE: what
Johnson/Desc/K8/Honest/EqReturns.lean says of a tie's and of a read's claim (`TieClaim`,
`ReadClaim`: facts on the claim's own fields) IN THE SHAPES THAT ALL KINDS SHARE
(Johnson/Desc/First/Shape/Parts.lean: `claimSh`). Two definitions and two lemmas; none of the
library's goals.

  `tieSh tl mu`                    the shape of the tie of matrix mu
  `readSh tl F Fn sg laid tU`      the shape of a read's claim
  `tieClaim_sh`, `readClaim_sh`   a claim with the stated fields has that shape
It stands in a file of its own since Parts.lean leans on three of the library's files
(OnBytes/K/Kc/Returns/FlReturns.lean, FlReturns2.lean, FlReturns6.lean) on which EqReturns.lean does
not lean.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqReturns
import Johnson.Desc.First.Shape.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.Shape

/-- A run's numbers in the shared order. -/
def toRunSh (x : Nat × Nat × Nat × Nat × Nat × Nat) : RunSh :=
  RunSh.mk x.1 x.2.1 x.2.2.1 x.2.2.2.2.2 x.2.2.2.1 x.2.2.2.2.1

theorem runSh_nums (r : Run2) : runSh r = toRunSh (runNums r) := rfl

theorem map_runSh (l : List Run2) : l.map runSh = (l.map runNums).map toRunSh := by
  rw [List.map_map]
  rfl

/-- The shape of the tie of matrix mu. -/
def tieSh (tl : HTailF2) (mu : Nat) : ClaimSh :=
  ClaimSh.mk (some (tl.eqFirst.getD mu 0)) (AffSh.mk [] [])
    [RunSh.mk tl.ix.ZZ tl.zzRowTies (tl.off.getD mu 0) (tl.shp.getD mu {}).m 0
        (tl.shp.getD mu {}).m,
      RunSh.mk tl.ix.ZZ tl.zzRowTies (tl.mz + tl.off.getD mu 0) (tl.shp.getD mu {}).m 0
        (tl.shp.getD mu {}).m,
      RunSh.mk (tl.gtTree.getD mu 0) 0 0 ((tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k) 0
        ((tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k)]

/-- The shape of a read's claim. -/
def readSh (tl : HTailF2) (F : Fork) (Fn : HFun) (sg laid tU : Nat) : ClaimSh :=
  ClaimSh.mk (some (tl.eqFirst.getD tl.NM 0 + laid * tl.stepF))
    (AffSh.mk
      ((List.range (tl.mats.getD Fn.mat {}).k).map fun col =>
        (tU, (Fn.start + col * segs tl Fn + sg) / colsOf F tU,
          (Fn.start + col * segs tl Fn + sg) % colsOf F tU)) [])
    [RunSh.mk tl.ix.ZZ tl.zzRowReads (tl.off.getD Fn.mat 0 + sg * Fn.len) Fn.phi.size 0 Fn.len,
      RunSh.mk tl.ix.ZZ tl.zzRowReads (tl.mz + tl.off.getD Fn.mat 0 + sg * Fn.len) Fn.phi.size 0
        Fn.len]

theorem tieClaim_sh {tl : HTailF2} {mu : Nat} {c : Claim} (h : TieClaim tl mu c) :
    claimSh c = tieSh tl mu := by
  unfold claimSh affSh
  rw [h.eqFirst, h.ents, h.slots, map_runSh, h.runs]
  rfl

theorem readClaim_sh {tl : HTailF2} {F : Fork} {Fn : HFun} {sg laid tU : Nat} {c : Claim}
    (h : ReadClaim tl F Fn sg laid tU c) : claimSh c = readSh tl F Fn sg laid tU := by
  have he : c.form.ents.toList.map entSh =
      (List.range (tl.mats.getD Fn.mat {}).k).map fun col =>
        (tU, (Fn.start + col * segs tl Fn + sg) / colsOf F tU,
          (Fn.start + col * segs tl Fn + sg) % colsOf F tU) := h.ents
  unfold claimSh affSh
  rw [h.eqFirst, he, h.slots, map_runSh, h.runs]
  rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.tieClaim_sh
#print axioms VerifiableInference.Desc.First.K8.Honest.readClaim_sh
