-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5TabsA.lean

"TabsA S fs" (Lane5BridgeA.lean) from the sense in which HeadTabs.lean says "the call has the
library's table" (Hd.IsLut: as many rows; row by row the verifier's word is fOfNat n with n the
library's row). This file does not import HeadTabs.lean: its hypotheses "rows" and "row" are the
first two fields of Hd.IsLut (cs q).call (lut .. q). isLut_hid (Lane5AttCallsH.lean) proves
Hd.IsLut, at the table of the call's kind, for every call of the shape that the verifier's own
shapeHid returns (one shift, ldh = 7, kFD = 16, S = 12, rx = 8). The last step is made in
Lane5AttHid.lean (tabsA_of_hid), which compiles the two together. It asks three facts on the calls
besides: cs q is call number q of the shape; call q has the kind with the library's number q; the
library's "used q" is at most 2^n of call q. At the call list of four lines these are theorems
(laidA_of_hid, kinds_of_four, room_of_four, Lane5AttLaid.lean).

Main theorem: "tabsA_of_luts".
-/
import Johnson.Road.Lane5BridgeA
import OnBytes.Tie.Pv.Lookup.Ends.PortA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A
open OnBytes.Attention (ACall)
open Inst.Model.AttSeg

/-- **The premise on the tables, from "each call has the library's table".** -/
theorem tabsA_of_luts {S : Attention.Shape} {fs : Model.Forest.Shape} {cs : Fin 4 → ACall}
    (hS : ∀ q : Fin 4, S.calls[q.val]? = some (cs q))
    (hc : ∀ q : Fin 4, fs.calls[q.val]? = some (cs q).call)
    (rows : ∀ q : Fin 4,
      2 ^ (cs q).call.k = (lut (scl := sclOf S) (dimOf S) (tbOf S) q).rows)
    (row : ∀ q : Fin 4, ∀ u < (lut (scl := sclOf S) (dimOf S) (tbOf S) q).rows,
      ∃ n : ℕ, (cs q).call.tauAt u = Model.fOfNat n ∧
        (n : ℤ) = (lut (scl := sclOf S) (dimOf S) (tbOf S) q).row u)
    (room : ∀ q : Fin 4, (dimOf S).used q ≤ 2 ^ (cs q).call.n) : TabsA S fs where
  row := by
    intro c u hu
    have hk : kN fs c.val = (cs c).call.k := by
      unfold kN
      rw [hc c]
      rfl
    have ht : tauN fs c.val u = ((cs c).call.tauAt u).toNat := by
      unfold tauN
      rw [hc c]
      rfl
    rw [hk, rows c] at hu
    obtain ⟨n, hn, hr⟩ := row c u hu
    refine ⟨u, hu, ?_⟩
    rw [ht, hn, ← hr, Int.cast_natCast]
    exact toF_fOfNat n
  room := by
    intro c
    have e : S.calls.getD c.val default = cs c := by
      rw [Array.getD_eq_getD_getElem?, hS c]
      rfl
    rw [e]
    exact room c

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.tabsA_of_luts
