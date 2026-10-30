-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/HeadLiveTablesStatement.lean: THE KIND K8 (the sub-protocol that tests that
values are small), AT THE OUTPUT HEAD's SEGMENT: OF THE FIFTEEN TABLES THAT THE HEAD's QUIET STEP
LAYS (`ReadsQuiet.tables`, Johnson/Desc/K8/ReadsQuiet.lean) EACH OF THE h.NHf + 4 MATRICES HAS ONE
NONE OF WHOSE WEIGHTS READS AS 0 (`LiveTable`, Johnson/Desc/K8/Honest/ReadsLiveOf.lean), WHERE FOUR
POINTS' COORDINATES READ AS NEITHER 0 NOR 1: STATEMENTS ALONE: three definitions of propositions.
NOTHING IS PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.
On plain data: no state of the verifier, no sub-protocol's step, no prover.

WHAT IT IS NOT. THAT THE FOUR POINTS ARE SUCH, THE FOUR SIZES, THE FIVE DIVISIBILITIES, AND THAT THE
DATA tl HOLD THIS LIST AND THESE MATRICES ARE PREMISES: shown of no state and of no public files
here. `readsLive_of` (ReadsLiveOf.lean) asks a table at every mu below tl.NM, and the test
`tiesLaid`: THAT tl.NM IS h.NHf + 4 IS NOT SAID HERE. ONE SEGMENT OF 25.

  `LongPhiNe`       a point of ls + lt coordinates none of which reads as 0 or 1: no entry of
                    `longPhi Z ls lt` (OnBytes/Model/Tensors.lean) below 2 ^ (ls + lt) reads as 0
  `PhiPNe`          no entry of `Forest.phiP lm` (OnBytes/Model/Look.lean) below 2 ^ lm reads as 0:
                    a power of two: public numbers
  `HeadLiveTables`  the title. WHICH TABLE SERVES WHICH MATRIX: the h.NHf parts of hf: "hf@Z" (the
                    point x.Zl) · hd: "hd@r_H" (x.tH.r) · hr: "hr@r_tV" (x.tV.r) · bH: "bH-pin"
                    (`Forest.phiP`: no point) · xbL: "xbL@Z_V" (the last h.la coordinates of
                    x.wpl.r)

NEAR. `eqTab_ne` (Johnson/Desc/K8/Honest/PlanesLiveOf.lean) is called: no entry of a table of
equality weights reads as 0 at such a point. ANOTHER GROUP OF AUTHORS' `blockRows_val_ne` AND
`blockRows_eq_val_ne` (Johnson/Desc/K5/Honest/Law/LiveValAt.lean, not imported) SAY OF THE ATTENTION
DESCRIPTION's OWN blockRows AND eqTab WHAT `LongPhiNe` SAYS OF THE LIBRARY's: a second text of one
thought. Their `LiveV` (there) is `LiveTable`'s clauses on a table without the data.

Limits. By values. Nothing on any measure. Nothing on any property.
-/
import Johnson.Desc.K8.ReadsQuiet
import Johnson.Desc.K8.Honest.ReadsLiveOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

/-- The statement on a block's weights. Not proved here; a lemma's statement, none of the library's
goals. -/
def LongPhiNe : Prop :=
  ∀ (Z : Array E) (ls lt : Nat), Z.size = ls + lt →
    (∀ w ∈ Z.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) →
    ∀ j, j < 2 ^ (ls + lt) → Reading.gl.val ((longPhi Z ls lt).getD j zeroE) ≠ 0

/-- The statement on the pin's weights. Not proved here; a lemma's statement, none of the library's
goals. -/
def PhiPNe : Prop :=
  ∀ (lm j : Nat), j < 2 ^ lm → Reading.gl.val ((Forest.phiP lm).getD j zeroE) ≠ 0

/-- The statement of the title. Not proved here; a lemma's statement, none of the library's goals.
-/
def HeadLiveTables : Prop :=
  ∀ (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered) (x : Head.Heard)
    (t : Head.Tables) (tl : HTailF2),
    VerifiableInference.Desc.K8.ReadsQuiet.tables h L hp cov x = .ok t →
    tl.funs = t.funs → tl.mats = hp.tl.mats →
    (∀ w ∈ x.Zl.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) →
    (∀ ZV, VerifiableInference.Desc.Own.tailOf x.wpl.r h.la = some ZV →
      ∀ w ∈ ZV.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) →
    (∀ w ∈ x.tH.r.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) →
    (∀ w ∈ x.tV.r.toList, Reading.gl.val w ≠ 0 ∧ Reading.gl.val w ≠ 1) →
    x.Zl.size = h.ls + h.lt → x.tH.r.size = h.lt → x.tV.r.size = h.lt → h.T = 2 ^ h.lt →
    (∀ q, q < h.NHf → (hp.tl.mats.getD q {}).m % 2 ^ h.la = 0) →
    (hp.tl.mats.getD h.NHf {}).m % h.T = 0 →
    (hp.tl.mats.getD (h.NHf + 1) {}).m % h.T = 0 →
    (hp.tl.mats.getD (h.NHf + 2) {}).m % 2 ^ h.lmbH = 0 →
    (hp.tl.mats.getD (h.NHf + 3) {}).m % 2 ^ h.la = 0 →
    ∀ mu, mu < h.NHf + 4 → ∃ Fn, LiveTable tl mu Fn

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.LongPhiNe
#print axioms VerifiableInference.Desc.First.K8.Honest.PhiPNe
#print axioms VerifiableInference.Desc.First.K8.Honest.HeadLiveTables
