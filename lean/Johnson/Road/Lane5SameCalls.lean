-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5SameCalls.lean

"SameCalls" (Johnson/Road/Lane5ForIn.lean) is a theorem at what the verifier's shapeHid returns on a
configuration with the usual call list. So, with the numbers of "keys_iff_of_usual" (CfRef cf, kFD =
16, S = 12, rx = 8), all five public premises of "forInA_iff_keys" hold together there.

"SameCalls S fs" has three lines: fs.NC = 4; S.calls.size = 4; the lookup's records of calls are the
shape's. The third is "calls_of_hid" (Johnson/Road/Lane5KvAll.lean); S.calls.size = 4 is
"four_of_hid"'s (Johnson/Road/Lane5AttLaid.lean); fs.NC = 4 is shown here.

Main theorems:
* "nc_of_hid": at what shapeHid returns, fs.NC = S.calls.size. The verifier's Forest.shape sets NC
  to the number of calls that it is given ("shape_calls", Johnson/Road/FormsKeysShape.lean);
  shapeHid keeps that field, and turns the calls one by one.
* "sameCalls_of_usual": with "UsualCalls cf": "SameCalls S fs". The number 4 is "four_of_hid"'s
  (Johnson/Road/Lane5AttLaid.lean).
* "forInA_iff_keys_of_usual": under the public premises of "keys_iff_of_usual"
  (Johnson/Road/Lane5AttTabsEq.lean): "ForInA S fs cell" if and only if "KeysC S cell", for every
  reading cell of the names.

Limits. "UsualCalls cf" is no test of the verifier: a configuration that it admits may have another
list of calls, and then nothing is said. The key vectors in "ForInA" are kvA
(OnBytes/Tie/Pv/Lookup/Ends/A.lean), a term of this library over the verifier's records; the
verifier holds no key vector. That a caller of the lookup has these key vectors is said nowhere
here. No statement here is at the record that publicOf returns: that is "forInA_iff_keys_publicAt"
(Johnson/Road/Lane5SameCallsAt.lean).

-/
import Johnson.Road.Lane5ForIn
import Johnson.Road.Lane5AttTabsEq
import Johnson.Road.FormsKeysShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open OnBytes.Ends OnBytes.Ends.A
open Attention (ACall Cfg Shape Listed shape shapeHid layCall)

variable {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}

/-- **The lookup's shape counts as many calls as the shape has.** -/
theorem nc_of_hid (h : shapeHid lid cf = Except.ok (S, fs)) : fs.NC = S.calls.size := by
  unfold Attention.shapeHid at h
  obtain ⟨A, _, h⟩ := bind_ok h
  obtain ⟨fo, hfo, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Except.ok.inj h)
  subst e1
  subst e2
  show fo.NC = _
  rw [(shape_calls hfo).2]
  simp

/-- **SameCalls at what shapeHid returns on the usual call list.** -/
theorem sameCalls_of_usual (h : shapeHid lid cf = Except.ok (S, fs)) (U : UsualCalls cf) :
    SameCalls S fs :=
  sameCalls_of_hid h ((nc_of_hid h).trans (four_of_hid h U).size) (four_of_hid h U).size

/-- **All five premises together: the clause ForInA is the library's clause on looked-up values.**
-/
theorem forInA_iff_keys_of_usual (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf)
    (hkF : cf.kFD = 16) (h12 : cf.S = 12) (h8 : cf.rx = 8) (U : UsualCalls cf)
    (cell : NameA → Cb.Gl.E) : ForInA S fs cell ↔ KeysC S cell :=
  forInA_iff_keys (numsA_of_hid h hc.ldh) (laidA_of_hid h U) (tabsEq_of_usual h hc hkF h12 h8 U)
    (inside_of_four (shaped_of_hid h) (tests_of_hid h).1 (four_of_hid h U))
    (sameCalls_of_usual h U) cell

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.nc_of_hid
#print axioms OnBytes.Road.L5.sameCalls_of_usual
#print axioms OnBytes.Road.L5.forInA_iff_keys_of_usual
