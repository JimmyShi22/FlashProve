-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5KvAll.lean

The key vectors kvA, a term written for this library over the verifier's records, are the
library's key vectors (keyVec) AT EVERY INDEX, the padding included. So their multilinear
extensions are the same at every point. This is what two statements of other files need in order
to be compared: OnBytes/Tie/Pv/Lookup/Ends/AlgAW.lean (the value of the verifier's key form is
Blocks.ext n (kvA ..) at the key point, under the premise rule of these theorems: each slot of the
world that a key form reads holds the extension of its cells (for the scores and accumulators: of
the products) at the key point) and kfExt (Inst/Model/Att/KeyFormsExt/All.lean: the library's KF
at the rule values is Blocks.ext (a c) (keyVec ..) at the call's point). Neither file is imported
here, and no term of this file joins them.

Main definitions and theorems:
* "PadEq S fs": the verifier's padding row of call c, as a number, is the library's padding value.
  Public. As a test with its theorem: "padEqB", "padEq_of_test".
* "keyVec_behind": behind "used c" the library's key vector holds its padding value.
* **"kvA_eq_keyVec_all"**: under NumsA, LaidA, InsideA, PadEq: kvA S fs cell c = keyVec (dimOf S)
  (tbOf S) (tC S cell) c, as functions, for every reading cell over the protocol's field.
* "ext_kvA_eq": so Blocks.ext n of the two agree, for every n and point.
* "calls_of_hid": the lookup's shape that the verifier's shapeHid returns has the shape's own calls'
  records, in their order. "a_eq_n": so the library's a c (callsOf fs, Lane5CallsOf.lean) is n of
  the shape's call c, which callsC and AlgAW.lean read.
The points: that the verifier's key point of call c, read, is the library's zC c z: Lane5ZkZc.lean.
-/
import Johnson.Road.Lane5KeysIff
import Johnson.Road.Lane5CallsOf
import Johnson.Road.Lane5AttShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open OnBytes.Ends OnBytes.Ends.A
open OnBytes.Attention (Shape ACall)
open Inst.Model.AttSeg

/-- **The verifier's padding rows are the library's padding values.** Public. -/
def PadEq (S : Shape) (fs : Model.Forest.Shape) : Prop :=
  ∀ c : Fin 4, ((tauN fs c.val (t0N fs c.val) : ℕ) : ℤ) =
    (lut (scl := sclOf S) (dimOf S) (tbOf S) c).pad

/-- PadEq, line by line. -/
def padEqB (S : Shape) (fs : Model.Forest.Shape) : Bool :=
  (List.finRange 4).all fun c => decide (((tauN fs c.val (t0N fs c.val) : ℕ) : ℤ) =
    (lut (scl := sclOf S) (dimOf S) (tbOf S) c).pad)

theorem padEq_of_test {S : Shape} {fs : Model.Forest.Shape} (h : padEqB S fs = true) :
    PadEq S fs := by
  simp only [padEqB, List.all_eq_true, decide_eq_true_eq] at h
  exact fun c => h c (List.mem_finRange c)

section
variable {K : Type} [Field K]

/-- Behind both families twoFam holds the padding value. -/
theorem twoFam_behind (nb l l' : ℕ) (f f' : ℕ → ℕ → K) (pad : K) {X : ℕ}
    (h : ¬X < nb * 2 ^ l + nb * 2 ^ l') : twoFam nb l l' f f' pad X = pad := by
  unfold twoFam
  rw [if_neg (by omega), if_neg (by omega)]

/-- **Behind "used c" the library's key vector holds its padding value.** -/
theorem keyVec_behind [scl : Inst.Model.Scl] (D : Dim) (tb : Inst.Model.Tables) (t : Raw → K)
    (c : Fin 4) (X : ℕ) (hX : ¬X < D.used c) :
    keyVec D tb t c X = (((lut D tb c).pad : ℤ) : K) := by
  match c, hX with
  | 0, hX => exact twoFam_behind _ _ _ _ _ _ hX
  | 1, hX => exact twoFam_behind _ _ _ _ _ _ hX
  | 2, hX =>
    rw [keyVec_two]
    exact twoFam_behind _ _ _ _ _ _ hX
  | 3, hX =>
    rw [keyVec_three]
    unfold twoFam
    have h3 : ¬X < D.nb * 2 ^ D.l4 := hX
    rw [if_neg h3]
    split_ifs <;> rfl

end

/-- **The key vectors kvA, written for this library over the verifier's records, are keyVec at every
index.** -/
theorem kvA_eq_keyVec_all {S : Shape} (N : NumsA S) {cs : Fin 4 → ACall} (L : LaidA S cs)
    (hin : InsideA S cs) {fs : Model.Forest.Shape} (hp : PadEq S fs) (cell : NameA → Cb.Gl.E)
    (c : Fin 4) :
    kvA S fs cell c.val = keyVec (scl := sclOf S) (dimOf S) (tbOf S) (tC S cell) c := by
  funext X
  by_cases hX : X < (dimOf S).used c
  · exact kvA_eq_keyVecC N L fs cell c X hX
  · rw [keyVec_behind (scl := sclOf S) _ _ _ c X hX, ← hp c, Int.cast_natCast,
      kvA_eq S fs cell c.val (cs c) (L.isCall c)]
    apply pwVec_outside
    intro p hpm hXp
    have := hin c p hpm
    omega

/-- **So their extensions agree.** -/
theorem ext_kvA_eq {S : Shape} (N : NumsA S) {cs : Fin 4 → ACall} (L : LaidA S cs)
    (hin : InsideA S cs) {fs : Model.Forest.Shape} (hp : PadEq S fs) (cell : NameA → Cb.Gl.E)
    (c : Fin 4) (n : ℕ) (pt : ℕ → Cb.Gl.E) :
    Blocks.ext n (kvA S fs cell c.val) pt =
      Blocks.ext n (keyVec (scl := sclOf S) (dimOf S) (tbOf S) (tC S cell) c) pt := by
  rw [kvA_eq_keyVec_all N L hin hp cell c]

/-! ## The same calls -/

/-- **The lookup's shape has the shape's own calls' records.** -/
theorem calls_of_hid {lid : ℕ} {cf : Attention.Cfg} {S : Shape} {fs : Model.Forest.Shape}
    (h : Attention.shapeHid lid cf = Except.ok (S, fs)) :
    fs.calls = S.calls.map fun k => k.call := by
  unfold Attention.shapeHid at h
  obtain ⟨A, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Except.ok.inj h)
  subst e1
  subst e2
  rfl

/-- **The library's a c is n of the shape's call c.** -/
theorem a_eq_n {S : Shape} {fs : Model.Forest.Shape}
    (hc : fs.calls = S.calls.map fun k => k.call) {cs : Fin 4 → ACall}
    (hS : ∀ q : Fin 4, S.calls[q.val]? = some (cs q)) (c : Fin 4) :
    (callsOf fs).a c = (S.calls.getD c.val default).call.n := by
  show ((fs.calls[c.val]?).map fun k => k.n).getD 0 = _
  rw [hc, Array.getElem?_map, hS c, Array.getD_eq_getD_getElem?, hS c]
  rfl

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.calls_of_hid
#print axioms OnBytes.Road.L5.a_eq_n
#print axioms OnBytes.Road.L5.padEq_of_test
#print axioms OnBytes.Road.L5.keyVec_behind
#print axioms OnBytes.Road.L5.kvA_eq_keyVec_all
#print axioms OnBytes.Road.L5.ext_kvA_eq
