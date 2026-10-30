-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/SegRdOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the weight claims: WHAT A FACTOR ON A
SEGMENT's ENTRIES READS IS THERE (SegRd, ClaimsKit.lean), for every family of keys at once: some
call of the layout holds the family's segment; the segment has the family's number of entries; its
columns lie in the call; the call has room for them; and the call's point has its column
coordinates, wherever each call's point has the number of coordinates that the lookup's numbers
give it. From the layout's return, by the library's callOf_some, callOf_spec, segs_of_layout,
fo_of_layout and cl_of_layout (Johnson/Road/FormsKeysCaller.lean, FormsKeysQK.lean,
FormsKeysLaid.lean, FormsKeysShape.lean) and the law on a call's columns (ColsOfLayout.lean).
Statements and proofs. General in the sizes.

  `call_pow`      a call of the layout has two to lJ columns, with switch p3 on.
  `call_n`        the lookup's number of coordinates of a call's point.
  **`segRd_of`**    SegRd at every family.

Not shown here. That the hypotheses hold together at any plan: no example is shown here. That each
call's point has the lookup's number of coordinates (hzk): ClaimRdOf.lean has it (blank_zk) AT THE
BLANK STRUCTURE ALONE, where every coordinate is 0; at sampled challenges no statement has it. AT A
LAYOUT WHOSE EIGHT LINES OF CALLS ARE THE LIBRARY's, UNDER THE LIBRARY's ELEVEN SWITCHES ALONE.
Public data alone: numbers and sizes; nothing on an element.
No property is claimed.
-/
import Johnson.Road.K4.C.ClaimsKit
import Johnson.Road.K4.C.ColsOfLayout
import Johnson.Road.FormsKeysCaller
import Johnson.Road.FormsKeysKF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay ClaimEnv layout)
open Inst.Model.FFSeg (Fam len)

/-- A call of a layout that the verifier returns, with switch p3 on, has two to lJ columns. -/
theorem call_pow {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (h3 : h.p3 = true) {cd : CallD} (hcd : cd ∈ y.calls) :
    cd.J = 2 ^ cd.lJ := by
  obtain ⟨cl, taken, -, -, e⟩ := (admitted_of_layout hy h3).calls
  rw [e] at hcd
  obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (Array.mem_toList_iff.mpr hcd)
  exact place_J _ _ _ _

/-- The lookup's number of coordinates of the point of call number q. -/
theorem call_n {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) {q : ℕ} {cd : CallD} (hq : y.calls[q]? = some cd) :
    ((y.fo.calls[q]?).map (·.n)).getD 0 = y.h.ll + cd.lJ + y.h.lt := by
  rw [(fo_of_layout hy).1, cl_of_layout hy, Array.getElem?_mapIdx, hq]
  rfl

/-- **WHAT A FACTOR ON A SEGMENT's ENTRIES READS IS THERE**, at every family. CONDITIONAL: on the
layout's return, the switches, the eight lines, and that each call's point has the lookup's number
of coordinates (hzk). -/
theorem segRd_of {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {c : ClaimEnv}
    (hy : layout h pc = .ok c.v.y) (S : Switches h) (hN : LinesAre c.v.y)
    (hzk : ∀ q, q < c.v.y.calls.size →
      (c.v.zk.getD q #[]).size = ((c.v.y.fo.calls[q]?).map (·.n)).getD 0) (fam : Fam) :
    SegRd c (segName fam) (len (dimOf h) fam) := by
  obtain ⟨q, cd, sg, hc⟩ := callOf_some (hasSeg_of_layout hy S fam)
  obtain ⟨hq, hsg, hname⟩ := callOf_spec hc
  have hcd : cd ∈ c.v.y.calls := Array.mem_of_getElem? hq
  have hqs : q < c.v.y.calls.size := (Array.getElem?_eq_some_iff.mp hq).1
  obtain ⟨fam', a1, a2, -, a4, -⟩ := segs_of_layout hy S cd hcd sg hsg
  have ef : fam' = fam := segName_inj (a1.symm.trans hname)
  subst ef
  have h8 : c.v.y.calls.size = 8 := by
    have := congrArg List.length hN
    simpa using this
  have hq8 : q < 8 := by omega
  have eg : c.v.y.calls.getD q default = cd := by
    rw [Array.getD_eq_getD_getElem?, hq]
    rfl
  have hline : cd.segs.map (·.name) = (Inst.Model.FFSeg.fams ⟨q, hq8⟩).map segName := by
    have hl := line_at hN ⟨q, hq8⟩
    rw [eg] at hl
    exact hl
  have C : ColsOK cd := colsOK_of_layout hy S (sized_dimOf h) hcd hline
  have hJ := call_pow hy S.p3 hcd
  refine ⟨q, cd, sg, hc, a4.trans a2, fun j hj => ?_, ?_, ?_⟩
  · rw [← hJ]
    exact C.lt sg hsg j hj
  · unfold Env.zj
    rw [Array.size_extract, hzk q hqs, call_n hy hq]
    omega
  · have hle := (List.subperm_of_subset (C.each sg hsg)
      (fun j hj => List.mem_range.mpr (C.lt sg hsg j hj))).length_le
    rw [List.length_range, Array.length_toList, a4, a2, hJ] at hle
    exact hle

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.call_pow
#print axioms OnBytes.Road.K4.C.call_n
#print axioms OnBytes.Road.K4.C.segRd_of
