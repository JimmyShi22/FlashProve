-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/PieceOfSilenceStatement.lean: THE KIND K8 (the sub-protocol that tests that values are
small): WHERE THE LOOKUP's SECOND TEST ON ITS OWN SAMPLES (`goodK3Out`,
Johnson/Desc/ProofFile/Honest/K3/GoodDraws.lean) SAYS YES AND WHAT IS HELD AS HEARD AGREES WITH
THESE SAMPLES IN THE ELEVEN OPEN FIELDS (`OpenSame`, `lookHeardAt`,
Johnson/Desc/ProofFile/Honest/K3/HeardWhole.lean): `PieceLive`
(Johnson/Desc/K8/Honest/SecondNz.lean): STATEMENTS ALONE: three definitions of propositions. NOTHING
IS PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements. The
sister of `digits_of_silence` (Johnson/P1K8R/DigitsOfSilence.lean), which ends in `digitsLive`.

A SECOND TEXT. THE PROOFS OF THE FIRST TWO STATEMENTS ARE STRETCHES OF `digits_of_silence`'s PROOF,
WRITTEN A SECOND TIME AND HANDED OUT AS STATEMENTS: that proof shows both on its way, at the calls 0
and 1, and hands out neither.

WHAT IT IS NOT. THAT WHAT A STATE HOLDS AS HEARD AGREES WITH THE LOOKUP's OWN SAMPLES, THAT THE TEST
SAYS YES THERE, AND THE EQUATION ON THE CALLS' WEIGHTS ARE PREMISES: shown of no state here.

  `LookZkFine`      general in the shape h: at every call q below h.NC no coordinate of the call's
                    key point g.zk[q] reads as 0 or as 1
  `LookENe`         the same premises: at every such call the call's weight g.e[q] does not read
                    as 0
  `PieceOfSilence`  at the data tl: with `KeyFit tl`, every wanted piece's call below 2, and at
                    each wanted piece g.e at its call being the weight by the second computation
                    (`callWeightAgain`, OnBytes/Model/Tail.lean): `PieceLive tl g W`

Limits. OF `KeyFit`'s FIVE FIELDS THREE ARE SPENT (level, order, calls); iota and fits are idle
here: the structure is asked whole since its one caller holds it whole. Nothing on any measure.
Nothing on any property.
-/
import Johnson.P1K8R.DigitsOfSilence
import Johnson.Desc.K8.Honest.SecondNz

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K3 (goodK3Out lookHeardAt OpenSame)

/-- The statement on the calls' key points. Not proved here; a lemma's statement, none of the
library's goals. -/
def LookZkFine : Prop :=
  ∀ (h : Forest.Shape) (g : Forest.Heard) (own : List Fmt.Drawn),
    OpenSame g (lookHeardAt h 0 own) → goodK3Out (K3.faceOf h) own = true → 0 < h.v →
    ProdV.orderOk (h.v - 1) (K3.keyOrders h (h.v - 1)) = true →
    ∀ q, q < h.NC → ∀ w ∈ (g.zk.getD q #[]).toList, Fine w

/-- The statement on the calls' weights. Not proved here; a lemma's statement, none of the library's
goals. -/
def LookENe : Prop :=
  ∀ (h : Forest.Shape) (g : Forest.Heard) (own : List Fmt.Drawn),
    OpenSame g (lookHeardAt h 0 own) → goodK3Out (K3.faceOf h) own = true → 0 < h.v →
    ProdV.orderOk (h.v - 1) (K3.keyOrders h (h.v - 1)) = true →
    ∀ q, q < h.NC → Reading.gl.val (g.e.getD q zeroE) ≠ 0

/-- The statement of the title. Not proved here; a lemma's statement, none of the library's goals.
-/
def PieceOfSilence : Prop :=
  ∀ (tl : HTailF2) (g : Forest.Heard) (own : List Fmt.Drawn) (W : List Want),
    OpenSame g (lookHeardAt tl.f9 0 own) → goodK3Out (K3.faceOf tl.f9) own = true → KeyFit tl →
    (∀ w ∈ W, w.call < 2) →
    (∀ w ∈ W, g.e.getD w.call zeroE = callWeightAgain g w.call) →
    PieceLive tl g W

end P1K8

#print axioms P1K8.LookZkFine
#print axioms P1K8.LookENe
#print axioms P1K8.PieceOfSilence
