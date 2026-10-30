-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StageFitsOneFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/StageFitsOne.lean
(its part at the typed chain): the first stage fits.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `fits1F`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StageFitsOne
import Johnson.Road.K4.StageFitsMoreFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes
open OnBytes.Model (orderDefault)
open OnBytes.Tie.Pv.Lay (StgFits ordE ordE_val eDefault default_perm)
open OnBytes.Desc.First.P1 (gl levelWs)
open Inst.Model (Scl)
open Inst.Model.FFSeg (lDd)
open OnBytes.Desc.First.K4 (k0)

variable [scl : Scl] {M Xs : Type}

/-- **The product layer of the sums of squares.** -/
theorem fits1F (P : FullFPar Cb.Gl.E M Xs) (hS : P.eS = eDefault _)
    (st : P.ownF.toOwn.tail.s1.L.St) (jp : Fin (P.D.lL + 1) → Cb.Gl.E)
    (tp : Fin P.D.lT → Cb.Gl.E)
    (hst : ∀ i, P.ownF.toOwn.tail.s1.L.S.w st i =
      some (Fin.append jp (Fin.append (fun _ : Fin (lDd P.D) => (2⁻¹ : Cb.Gl.E)) tp) (P.eS i)))
    (rhoI PV : Array E) (half : E) (hI : rhoI.size = P.D.lL + 1)
    (hj : ∀ i, jp i = gl.val (rhoI.getD i.val zeroE))
    (ht : ∀ i, tp i = gl.val (PV.getD i.val zeroE)) (hh : gl.val half = 2⁻¹) :
    StgFits gl P.ownF.toOwn.tail.s1 st
      (levelWs (P.D.lL + 1 + (lDd P.D + P.D.lT))
        (rhoI ++ Array.replicate (lDd P.D) half ++ PV)
        (orderDefault (P.D.lL + 1 + (lDd P.D + P.D.lT))))
      (P.D.lL + 1 + (lDd P.D + P.D.lT)) 2 :=
  stgFits_ordE P.ownF.toOwn.tail.s1 st (orderDefault _) (default_perm _) _
    (Fin.append jp (Fin.append (fun _ : Fin (lDd P.D) => (2⁻¹ : Cb.Gl.E)) tp)) rfl (fun _ => rfl)
    (fun j => by rw [hst j, hS]; rfl)
    (fun i => by
      rw [Array.append_assoc]
      exact append_reads jp _ rhoI _ hI hj
        (append_reads _ tp (Array.replicate (lDd P.D) half) PV Array.size_replicate
          (fun i => by
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos i.isLt]
            exact hh.symm) ht) i)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fits1F
