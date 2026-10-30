-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ZxOfSilence.lean: THE LOOKUP's POINT zx, AS HEARD, WHERE THE LOOKUP's SECOND TEST ON
ITS OWN CHALLENGES (`goodK3Out`, Johnson/Desc/ProofFile/Honest/K3/GoodDraws.lean) SAYS YES: NO
COORDINATE IS 0 OR 1; AND ITS SIZE. On plain data: no block, no state, no prover. Lemmas; NONE OF
THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  `order_of_ok`   Cb.Fo.ok_parts (OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean), `orderOk_forest`
      (Johnson/Desc/K8/Honest/PublicOfPieces.lean): the lines stand inside `keyFit_of_piecesF`'s
      proof there too
  `look_zx`   by evaluation
  **`look_zx_fine`**, `look_zx_size`   `keyPt_fine`, `keyPt_size`
      (Johnson/P1K8R/DigitsOfSilence.lean)
Kin. `look_zk_fine`, `look_e_ne`, `look_point` (Johnson/P1K8R/PieceOfSilence.lean): the like for the
calls' key points zk and weights e, under the two facts that `order_of_ok` draws from the numbers'
test. In the sealed Johnson/Top/H/Keep/CEndPoint.lean stand lkPad_point and Fo.Tp.pad_point: every
coordinate of zx and zy has what every element of the tape has: at the verifier program's own
routine and its tape, where this is at the structure made of the challenges and a test on them.
`look_zx_size` HAS A STRONGER ELDER: lookHeardAt_sizes
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsPointsAt.lean): the size of zx, and of zy, at
every shape, with no hypothesis: so hok is needless there; not called. And zx_size
(MergedPoint.lean, beside it): behind the hearing.
Limits. That the test says yes, that what has been heard is the structure made of the challenges,
and that the shape passes the numbers' test are premises. Nothing on any measure. It stands over the
files of the kind "lookup" on the honest side.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.DigitsOfSilence
import Johnson.Desc.K8.Honest.PublicOfPieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K3 (goodK3Out lookHeardAt OpenSame ptsOf)

/-- A shape that passes the numbers' test has a variable, and its key side's last level binds its
variables in an order that passes the order's test. -/
theorem order_of_ok (h : Forest.Shape) (hok : FoNums.ok h = true) :
    0 < h.v ∧ ProdV.orderOk (h.v - 1) (K3.keyOrders h (h.v - 1)) = true := by
  obtain ⟨⟨a1, -, -, -, -, -, -⟩, -⟩ := Cb.Fo.ok_parts hok
  have hv : h.v = h.dT + h.rK := rfl
  refine ⟨by omega, ?_⟩
  unfold K3.keyOrders
  rw [if_pos (by omega)]
  exact orderOk_forest _ _ (by omega)

/-- The field zx of the lookup's structure made of the challenges: the first dT coordinates of the
key tree's last point. -/
theorem look_zx (h : Forest.Shape) (ds : List Fmt.Drawn) :
    (lookHeardAt h 0 ds).zx = ((ptsOf (K3.faceOf h) 0 ds).keyPt 0 h.v).extract 0 h.dT := rfl

/-- **WHERE THE LOOKUP's SECOND TEST SAYS YES AT ITS OWN CHALLENGES, NO COORDINATE OF THE POINT zx
THAT IT HAS HEARD IS 0 OR 1.** g: what has been heard, the same as the structure made of the
challenges in the eleven fields of `OpenSame`. -/
theorem look_zx_fine (h : Forest.Shape) (g : Forest.Heard) (own : List Fmt.Drawn)
    (ho : OpenSame g (lookHeardAt h 0 own)) (hs : goodK3Out (K3.faceOf h) own = true)
    (hok : FoNums.ok h = true) : ∀ w ∈ g.zx.toList, Fine w := by
  obtain ⟨hv, hord⟩ := order_of_ok h hok
  intro w hw
  rw [ho.zx, look_zx] at hw
  exact keyPt_fine h own (h.v - 1) (by omega) hord hs w (mem_extract _ _ _ _ hw)

/-- That point has dT coordinates. -/
theorem look_zx_size (h : Forest.Shape) (g : Forest.Heard) (own : List Fmt.Drawn)
    (ho : OpenSame g (lookHeardAt h 0 own)) (hok : FoNums.ok h = true) : g.zx.size = h.dT := by
  obtain ⟨hv, -⟩ := order_of_ok h hok
  have hd : h.v = h.dT + h.rK := rfl
  rw [ho.zx, look_zx, Array.size_extract, keyPt_size h own (h.v - 1) (by omega)]
  omega

end P1K8

#print axioms P1K8.order_of_ok
#print axioms P1K8.look_zx
#print axioms P1K8.look_zx_fine
#print axioms P1K8.look_zx_size
