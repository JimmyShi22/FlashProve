-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/PfrCounts.lean: sizes of the Merkle trees over the encoded vectors of a protocol that is
built from blocks.

The encoded rounds are `encShape s d`, with `encPoint s d` (Blocks/BlockFront.lean); `leaves` and
`depths` are the number of leaves of all trees and the largest depth (Blocks/Leaves.lean). (Words of
this library: lean/GLOSSARY.md.)
 * `leaves_enc_le`, `depths_enc_le`: at most one leaf for each round and twice the sum of the
   lengths of all codewords; no tree is deeper than the logarithm of that sum. The sum
   (`EncData.sum` of `lenN`) is of the form of Blocks/StageCount.lean, so that it is computed along
   the stages.
 * `depthR_enc`: the depth of the tree over one encoded round.
 * `two_pow_clog_le`: 2^⌈log₂ N⌉ ≤ 1 + 2 N.

Limits:
 * A position of a vector of several rows holds a whole column, so these counts say nothing on the
   length of a proof or on the work of hashing.
 * `leaves_enc_le` is loose by a factor of about 2, and most so where the codewords of a round have
   a power of two of symbols.
 * `depths_enc_le` is crude. (The compiled scheme's count `tVQB` takes every opening at the wire
   record's `maxDepth`, by the wire's laws a bound on the depth of all trees, that over the encoded
   index included (Compile/Batch/SpecBinding.lean, Iop/BatchWire.lean), so a crude bound below that
   depth costs nothing.)
-/
import Blocks.Opens
import Blocks.Leaves
import Blocks.StageCount
import Iop.Univ
import Iop.WireOf

set_option autoImplicit false

namespace Blocks

open Iop

/-! ## The trees over the encoded vectors of a protocol that is built from blocks -/

section Enc
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem two_pow_clog_le (N : ℕ) : 2 ^ Nat.clog 2 N ≤ 1 + 2 * N := by
  rcases Nat.lt_or_ge N 2 with h | h
  · rw [Nat.clog_of_right_le_one (by omega)]
    omega
  · have h1 : 2 ^ (Nat.clog 2 N).pred < N := Nat.pow_pred_clog_lt_self (by decide) (by omega)
    have h2 : 0 < Nat.clog 2 N := Nat.clog_pos (by decide) h
    have h3 : 2 ^ Nat.clog 2 N = 2 * 2 ^ (Nat.clog 2 N).pred := by
      rw [← pow_succ']
      congr 1
      exact (Nat.succ_pred_eq_of_pos h2).symm
    omega

/-- the length of a codeword -/
def lenN (C : Code.Enc F) (_rows _mrow : ℕ) (_role : Role) (_q : ℕ) : ℕ := C.n

omit [Algebra F E] in
theorem depthR_enc {r : Round} (e : REnc F E r) :
    depthR (wordsPoint e.A (fun a => (e.code a).n) (fun a => Fin (e.rows a) → Kf F E (e.overF a))
          r.Plain r.Chal (fun _ _ => 0) r.dPlain) =
      Nat.clog 2 (∑ a, (e.code a).n) :=
  depth_words _ _ _ _ _ _ _

omit [Algebra F E] in
/-- A bound on the leaves of the trees over the encoded vectors. -/
theorem leaves_enc_le :
    ∀ (s : Shape) (d : EncData F E s),
      leaves (encShape s d) (encPoint s d) ≤ s.length + 2 * EncData.sum lenN s d
  | [], _ => Nat.le_refl _
  | r :: s, (e, d) => by
      show 2 ^ depthR
            (wordsPoint e.A (fun a => (e.code a).n) (fun a => Fin (e.rows a) → Kf F E (e.overF a))
              r.Plain r.Chal (fun _ _ => 0) r.dPlain) +
          leaves (encShape s d) (encPoint s d) ≤
        (s.length + 1) + 2 * ((∑ a, (e.code a).n) + EncData.sum lenN s d)
      rw [depthR_enc]
      have h1 := two_pow_clog_le (∑ a, (e.code a).n)
      have h2 := leaves_enc_le s d
      omega

omit [Algebra F E] in
/-- No tree over encoded vectors is deeper than the logarithm of the sum of the lengths of all
codewords. -/
theorem depths_enc_le :
    ∀ (s : Shape) (d : EncData F E s),
      depths (encShape s d) (encPoint s d) ≤ Nat.clog 2 (EncData.sum lenN s d)
  | [], _ => Nat.zero_le _
  | r :: s, (e, d) => by
      show max (depthR
            (wordsPoint e.A (fun a => (e.code a).n) (fun a => Fin (e.rows a) → Kf F E (e.overF a))
              r.Plain r.Chal (fun _ _ => 0) r.dPlain))
          (depths (encShape s d) (encPoint s d)) ≤
        Nat.clog 2 ((∑ a, (e.code a).n) + EncData.sum lenN s d)
      rw [depthR_enc]
      exact max_le (Nat.clog_mono_right 2 (Nat.le_add_right _ _))
        (le_trans (depths_enc_le s d) (Nat.clog_mono_right 2 (Nat.le_add_left _ _)))

end Enc

end Blocks
