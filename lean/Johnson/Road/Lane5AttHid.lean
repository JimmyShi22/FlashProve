-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttHid.lean

THE PUBLIC PREMISES OF THE SEAM BEFORE THE LOOKUP OF ATTENTION, AT THE RECORD THAT THE VERIFIER's
OWN shapeHid RETURNS, AS THEOREMS. linkOK_of_attCalls (Johnson/Road/Lane5BridgeA.lean) has the
premises AttSized S, hE (the verifier's table of exponentials holds the library's at all live rows)
and TabsA S fs. shapeHid returns the shape of the function shape with two fields set (the columns of
the matrix bA; the number iota of each call); none of the three premises reads these.

* "attSized_hid": AttSized S, from ten numbers of the configuration (CfRef), S = 12, rx = 8.
* "exp_of_hid": hE, from S = 12, rx = 8.
* "fit_hid": AttFit S, from ldh = 7 and one shift in the configuration.
* **"tabsA_of_hid"**: TabsA S fs, from AttFit S, kFD = 16, S = 12, rx = 8, and two public premises
  on the four calls: call q has the kind with the library's number q; the library's "used q" is at
  most 2^n of call q. (At the usual call list: kinds_of_four, room_of_four,
  Johnson/Road/Lane5AttLaid.lean.)

How: shaped_of_hid, sized_of_shaped (Lane5AttShape.lean), exp_of_shaped (Lane5AttExp.lean),
isLut_hid (Lane5AttCallsH.lean), tabsA_of_luts (Lane5TabsA.lean).
Not claimed: all that these files do not claim.
-/
import Johnson.Road.Lane5AttCallsH
import Johnson.Road.Lane5TabsA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open Attention (ACall Cfg Shape shapeHid)

variable {lid : ℕ} {cf : Cfg} {S : Shape} {fs : Model.Forest.Shape}

/-- **The shape that shapeHid returns at the reference numbers has the reference numbers.** -/
theorem attSized_hid (h : shapeHid lid cf = Except.ok (S, fs)) (hc : CfRef cf) (h12 : cf.S = 12)
    (h8 : cf.rx = 8) : AttSized S :=
  sized_of_shaped (shaped_of_hid h) hc (exp_of_shaped (shaped_of_hid h) h12 h8).1

/-- **Its table of exponentials holds the library's at all live rows.** -/
theorem exp_of_hid (h : shapeHid lid cf = Except.ok (S, fs)) (h12 : cf.S = 12) (h8 : cf.rx = 8) :
    ∀ ι : ℕ, ι < S.u0 → ((S.Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι :=
  (exp_of_shaped (shaped_of_hid h) h12 h8).2

/-- One shift and 128 features, from the configuration. -/
theorem fit_hid (h : shapeHid lid cf = Except.ok (S, fs)) (hl : cf.ldh = 7)
    (h1 : ∀ l < 2 ^ cf.ll, cf.sh.getD l 0 = cf.sh.getD 0 0) : AttFit S := by
  have P := shaped_of_hid h
  refine ⟨fun l hl' => ?_, ?_⟩
  · rw [P.cfg]
    exact h1 l (by rw [← P.Lam]; exact hl')
  · rw [P.cfg]
    exact hl

/-- **The premise on the tables, from the verifier's own call.** -/
theorem tabsA_of_hid (h : shapeHid lid cf = Except.ok (S, fs)) (F : AttFit S) (hkF : cf.kFD = 16)
    (h12 : cf.S = 12) (h8 : cf.rx = 8) {cs : Fin 4 → ACall}
    (hS : ∀ q : Fin 4, S.calls[q.val]? = some (cs q)) (hK : ∀ q : Fin 4, noK (cs q).kind = q)
    (room : ∀ q : Fin 4, (dimOf S).used q ≤ 2 ^ (cs q).call.n) : TabsA S fs := by
  obtain ⟨hl, hf⟩ := isLut_hid h F hkF h12 h8
  have L : ∀ q : Fin 4,
      Hd.IsLut (cs q).call (AttSeg.lut (scl := sclOf S) (dimOf S) (tbOf S) q) := by
    intro q
    have hm : cs q ∈ S.calls.toList := by simpa using Array.mem_of_getElem? (hS q)
    have e := hl (cs q) hm
    rwa [hK q] at e
  have hc : ∀ q : Fin 4, fs.calls[q.val]? = some (cs q).call := by
    intro q
    rw [hf, Array.getElem?_map, hS q]
    rfl
  exact tabsA_of_luts hS hc (fun q => (L q).rows) (fun q => (L q).row) room

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.attSized_hid
#print axioms OnBytes.Road.L5.exp_of_hid
#print axioms OnBytes.Road.L5.fit_hid
#print axioms OnBytes.Road.L5.tabsA_of_hid
