-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/LayPremises.lean: the proof of the statement of
Johnson/P1K8R/LayPremisesStatement.lean, to the letter, and one helper. Lemmas; none of the
library's goals.

How. `pub34_all` (Johnson/Goal/Meaning/Pub34All.lean): in scope the layout is what `layout` returns
under the library's switches, the lists are what `readsOf` returns, there are twelve groups, the
plan's and the public part's lists of matrices both have the pairs of `matsR`, and the plan's number
is its list's length. The layers' public part bears that layout (`pub_more`, `more_of_public`,
Pub34Scope.lean). (2): `points_of_layout` (Johnson/Road/FormsKeysAdmit.lean). (3): `pairs_getD`:
inside the list `getD_map_sizes` (FormsKeysTab.lean); beyond it both sides are the defaults. (4):
`tails_size` (Johnson/Meaning/ReadsPlan.lean). (5): `tails_pair` (FormsKeysTab.lean). (6), (7): rows
and lengths are powers of two: `rows_of_laid2` (FormsKeysTab.lean); `Laid2.mrow1`, `Laid2.mrow2`
with its fields lt_ad, lt_ar (FormsKeysAddr.lean). (8): `tailsOf_b`
(OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean), as the library's `famPos_b` takes it
(Johnson/Desc/First/Link/Law/LayTablesInScope.lean). (9): `Laid2.T`. (10): `layout_caps`
(OnBytes/Model/Fit/LayoutCaps.lean).

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.P1K8R.LayPremisesStatement
import Johnson.Goal.Meaning.Pub34All
import Johnson.Meaning.ReadsPlan
import Johnson.Road.FormsKeysAdmit
import Johnson.Road.FormsKeysTab
import Johnson.Road.FormsKeysKit
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG
import OnBytes.Model.Fit.LayoutCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Road (firstM partsM rowsM colsM matsR)

/-- The pair of a list's member, at every number. -/
theorem pairs_getD (ms : Array TMat) (M : Nat) :
    (ms.map fun M => (M.m, M.k)).getD M (0, 0) = ((ms.getD M {}).m, (ms.getD M {}).k) := by
  by_cases hi : M < ms.size
  · exact OnBytes.Road.getD_map_sizes ms hi
  · have e1 : (ms.map fun M => (M.m, M.k)).getD M (0, 0) = (0, 0) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Array.size_map]; omega)]
      rfl
    have e2 : ms.getD M {} = {} := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
      rfl
    rw [e1, e2]

/-- **The premises on public data hold in scope.** -/
theorem layPremises : LayPremises := by
  intro P pp lay X g hp hS hR hpub hg hG
  obtain ⟨⟨hy, S, -, hrd, -⟩, hN, -, hT, hM, -⟩ :=
    _root_.Meaning.P34.pub34_all hS hR hpub OnBytes.Road.gl_numerals
  have ey : X.layers.y = X.y :=
    (_root_.Meaning.P34.pub_more (_root_.Meaning.P34.more_of_public hpub).2.2.2.1).1
  obtain ⟨hm, hNM⟩ := hT g hp hG
  have hg' : g < X.y.NGr := by rw [hN]; exact hg
  have L2 := OnBytes.Road.laid2_of_layout hy
  have C := OnBytes.Model.Fit.layout_caps hy
  rw [ey, hM g]
  refine ⟨hrd, OnBytes.Road.points_of_layout
    (v := { y := X.y, sc := X.layers.sc, g := 0, iU3 := 0, K3 := 0, tab := [], zk := #[] })
    hy S hrd,
    ?_, ?_, fun mat hmat q hq => OnBytes.Road.tails_pair X.y hg' hmat hq, ?_, ?_, ?_, L2.T, ?_⟩
  · intro M
    rw [← hm]
    exact pairs_getD hp.tl.mats M
  · have s1 : hp.tl.mats.size = ((Layer.tailsOf X.y).getD g {}).mats.size := by
      have k := congrArg Array.size hm
      rw [Array.size_map] at k
      rw [k]
      unfold OnBytes.Road.matsR
      rw [Array.size_map]
    rw [hNM, s1, _root_.Meaning.Reads.tails_size X.y g hg']
    rfl
  · intro mat hmat
    obtain ⟨lm, h1, h2⟩ := OnBytes.Road.rows_of_laid2 L2 mat hmat
    rw [h2]
    exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h1)
  · intro mat hmat
    rw [L2.T]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmat
    rcases hmat with rfl | rfl
    · show X.y.mrow.getD 1 0 % 2 ^ X.y.h.lt = 0
      rw [L2.mrow1]
      exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 L2.lt_ad)
    · show X.y.mrow.getD 2 0 % 2 ^ X.y.h.lt = 0
      rw [L2.mrow2]
      exact Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 L2.lt_ar)
  · obtain ⟨b1, b2⟩ := _root_.Fo.PlaneMatG.tailsOf_b X.y g hg'
    refine ⟨X.y.kbm, ?_⟩
    have hi : (Layer.matIx X.y).iB < ((Layer.tailsOf X.y).getD g {}).mats.size := by
      rw [(OnBytes.Road.tails_sizes X.y hg').1]
      show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 1 < _
      omega
    unfold OnBytes.Road.matsR
    rw [OnBytes.Road.getD_map_sizes _ hi, b1, b2]
  · have c1 := C.ls
    have c2 := C.laLt
    rw [C.yh, c1]
    omega

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.pairs_getD
#print axioms P1K8.layPremises
