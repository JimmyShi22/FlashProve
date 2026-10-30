-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DigNat.lean: a digest as one natural number; and the typed oracle functions with every answer
of the function O on byte strings passed through one number.

Definitions that compute, with their laws.

Why: a digest `Dig 256` (Iop/Wire.lean) is a function from 256 places to bits. The family of
Run/CodingFn.lean answers with the function "bit i of the bytes O s": each bit that is read
evaluates O s anew, in Lean's evaluator and in its kernel. The kernel keeps the value of a closed
term that is a natural number, and reads a bit of a numeral at once. So: the answer's bytes are
made one number, lowest byte first, and the digest reads that number's bits. It is the same
function.

Main names:
  `natLEL`, `dN N`: their doc comments tell them; `natLE b`: `natLEL` on a byte array.
  `bit_byte`: bit j of a byte, as Fmt/Rules1.lean reads it, is bit j of the byte's number, for j <
    8.
  `testBit_natLEL`: bit k of the number is bit (k mod 8) of byte (k div 8); 0 beyond the end.
  `dN_natLE`: dN (natLE b) = bytesToDig b, for every b.
  `ansOfN`, `famN O D K`: Run/CodingFn.lean's `ansOf`, `famOf` with dN (natLE ..) in the place of
    `bytesToDig`; `famN_eq`: famN O D K = famOf O D K.

Limits: this file does not say how much a run gains by it.
-/
import Run.CodingFn

set_option autoImplicit false

namespace Run
open Compile Compile.Batch Iop Rom

/-- The number whose digits to the base 256, lowest first, are the bytes. -/
def natLEL : List UInt8 → Nat
  | [] => 0
  | x :: l => x.toNat + 256 * natLEL l

def natLE (b : ByteArray) : Nat := natLEL b.data.toList

/-- The digest whose bit i is bit i of N. -/
def dN (N : Nat) : Dig 256 := fun i => N.testBit i.val

theorem bit_byte_fin :
    ∀ (n : Fin 256) (j : Fin 8),
      (((UInt8.ofNat n.val) >>> (UInt8.ofNat j.val)) &&& 1 == 1) = n.val.testBit j.val := by
  decide +kernel

theorem bit_byte (x : UInt8) (j : Nat) (hj : j < 8) :
    ((x >>> (UInt8.ofNat j)) &&& 1 == 1) = x.toNat.testBit j := by
  have h := bit_byte_fin ⟨x.toNat, x.toNat_lt⟩ ⟨j, hj⟩
  simpa using h

theorem testBit_natLEL :
    ∀ (l : List UInt8) (k : Nat), (natLEL l).testBit k = ((l.getD (k / 8) 0).toNat).testBit (k % 8)
  | [], k => by simp [natLEL]
  | x :: l, k => by
      have hx : x.toNat < 2 ^ 8 := x.toNat_lt
      have e : natLEL (x :: l) = 2 ^ 8 * natLEL l + x.toNat := by
        show x.toNat + 256 * natLEL l = 2 ^ 8 * natLEL l + x.toNat
        omega
      rw [e, Nat.testBit_two_pow_mul_add _ hx]
      by_cases hk : k < 8
      · rw [if_pos hk, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
        rfl
      · rw [if_neg hk, testBit_natLEL l (k - 8)]
        have e1 : k / 8 = (k - 8) / 8 + 1 := by omega
        have e2 : (k - 8) % 8 = k % 8 := by omega
        rw [e1, e2]
        rfl

/-- The digest of the number of the bytes is the digest of the bytes. -/
theorem dN_natLE (b : ByteArray) : dN (natLE b) = bytesToDig b := by
  funext i
  show (natLEL b.data.toList).testBit i.val = _root_.Fmt.bitAt b i.val
  unfold _root_.Fmt.bitAt
  rw [_root_.Fmt.byteAt_eq, testBit_natLEL, bit_byte _ _ (Nat.mod_lt _ (by decide))]
  congr 2
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

variable {I X : Type} {L : BatchProtocol I X} {t : Tag}

/-- The answer of O at a call, through one number; zeros where there is none. -/
def ansOfN (O : ByteArray → ByteArray) : Option _root_.Fmt.OQ → Dig 256
  | some c => dN (natLE (O (strOf c)))
  | none => fun _ => false

theorem ansOfN_eq (O : ByteArray → ByteArray) (c : Option _root_.Fmt.OQ) :
    ansOfN O c = ansOf O c := by
  cases c with
  | none => rfl
  | some c => exact dN_natLE _

/-- The typed oracle functions, every answer of O through one number; at the tag t of the data
(where none is written: "test": `PageD`'s default tag is `.test`). -/
def famN (O : ByteArray → ByteArray) (D : PageD L t) (K : Nat) : Fam (spec 256 K L)
  | .leaf, q => ansOfN O (leafCall D q)
  | .node, q => ansOfN O (nodeCallC D.cfg q)
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 L t) t t' q with
      | some q => (fun k => ansOfN O (fbCall D K q k.castSucc), ansOfN O (fbCall D K q (Fin.last K)))
      | none => (fun _ _ => false, fun _ => false)
  | .fbw _ _, _ => (fun _ _ => false, fun _ => false)
  | .rleaf, _ => fun _ => false
  | .rnode, _ => fun _ => false
  | .g _, _ => fun _ => false
  | .ann, _ => ()
  | .other, _ => fun _ => false

/-- It is the same family as `famOf O D K` (Run/CodingFn.lean). -/
theorem famN_eq (O : ByteArray → ByteArray) (D : PageD L t) (K : Nat) :
    famN O D K = famOf O D K := by
  funext o q
  cases o with
  | leaf => exact ansOfN_eq O (leafCall D q)
  | node => exact ansOfN_eq O (nodeCallC D.cfg q)
  | fb t' =>
      simp only [famN, famOf]
      cases castTag (F := fun t => FbIn 256 L t) t t' q with
      | none => rfl
      | some q' => exact Prod.ext (funext fun k => ansOfN_eq O _) (ansOfN_eq O _)
  | fbw t k => rfl
  | rleaf => rfl
  | rnode => rfl
  | g t => rfl
  | ann => rfl
  | other => rfl

#guard natLE ⟨#[1, 2]⟩ == 513 && natLE ByteArray.empty == 0
#guard (List.finRange 256).all fun i => dN (natLE (_root_.Fmt.pattern 32)) i == bytesToDig (_root_.Fmt.pattern 32) i

end Run
