-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/EmbCl.lean: the verifier's claim on the stream that comes into the first group of
layers, as a form on committed entries, and what it says on cells.

In the first group one scalar more is sent, masked: the stream that comes in, summed over blocks of
features, places in a block and positions under the equality weights of two drawn points. One linear
claim ties the hidden scalar to the table of reads of that stream. This file writes the claim as a
form (Blocks/Form.lean) and shows that, on entries whose reads are true, the claim says: the scalar
less its mask entry is that sum.

Main names.
  embRhs: the sum, in the form of Cb/Pv/Lay/EmbSide.lean, on the library's stream xS at place 0.
  cEmb: the claim.
  limbs_val: the limbs' reads under the powers of 256, with the array's offset, are the read of the
    array's value.
  emb_last: on entries whose reads are true, the claim says that the hidden scalar is embRhs.

Limits. The names of the entries are letters. That the claim is a program's is not said here.
Identities alone.


-/
import Cb.Pv.Lay.End.GatedCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset Cb
open Inst.Model.FFSeg (Dim Cell Arr val xS)
open Blocks (ext eqN Form)

noncomputable section

section Sum

variable {E : Type} [Field E]

/-- The stream that comes in, summed over blocks, places in a block and positions under the equality
weights of pb and pa. -/
def embRhs (D : Dim) (t : Cell → E) (nb ls gB : ℕ) (pa pb : ℕ → E) : E :=
  ∑ kh ∈ range nb, eqN gB 0 pb kh * ∑ r ∈ range (2 ^ ls), eqN ls 0 pa r *
    ∑ p ∈ range (2 ^ D.lT), eqN D.lT ls pa p * xS D t 0 (kh * 2 ^ ls + r) p

/-- The equality weights of all numbers of s bits sum to 1. -/
theorem sum_eqN_one (s g : ℕ) (r : ℕ → E) : ∑ q ∈ range (2 ^ s), eqN s g r q = 1 := by
  have h := Blocks.ext_const s (1 : E) fun j => r (g + j)
  unfold Blocks.ext at h
  rw [← h]
  exact sum_congr rfl fun q _ => by rw [eqN_off s g r q, mul_one]

/-- The limbs' reads under the powers of 256, with the array's offset, are the read of the array's
value. -/
theorem limbs_val (D : Dim) (t : Cell → E) (A : Arr) (r : ℕ → E) (g s lam kh : ℕ) :
    ∑ l ∈ range A.nCell, (256 : E) ^ l * readAt D t A r g s l lam kh + ((A.off : ℤ) : E) =
      ∑ q ∈ range (2 ^ s), eqN s g r q *
        ext D.lT (fun p => val t A lam (kh * 2 ^ s + q) p) (fun j => r (g + s + j)) := by
  have e : ∀ q, ext D.lT (fun p => val t A lam (kh * 2 ^ s + q) p) (fun j => r (g + s + j)) =
      ∑ l ∈ range A.nCell, (256 : E) ^ l *
        ext D.lT (fun p => t ⟨A, l, lam, kh * 2 ^ s + q, p⟩) (fun j => r (g + s + j)) +
        ((A.off : ℤ) : E) := fun q => by
    unfold Inst.Model.FFSeg.val
    rw [Blocks.ext_add, Blocks.ext_const, Blocks.ext_sum]
    congr 1
    exact sum_congr rfl fun l _ => Blocks.ext_smul _ _ _ _
  simp only [e, mul_add]
  rw [sum_add_distrib, ← sum_mul, sum_eqN_one, one_mul]
  congr 1
  unfold readAt
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun q _ => sum_congr rfl fun l _ => by ring

end Sum

section Claim

variable {E J : Type} [Field E] [DecidableEq J]

/-- The claim: the hidden scalar, less the blocks' reads under the equality weights of pb. sh: the
scalar that was sent; mE: its mask entry; uX l kh: the read of limb l of block kh. -/
def cEmb (sh : E) (mE : J) (uX : ℕ → ℕ → J) (nb gB : ℕ) (pb : ℕ → E) : Form J E :=
  Form.masked sh mE - ∑ kh ∈ range nb, eqN gB 0 pb kh •
    (∑ l ∈ range Arr.x0.nCell, (256 : E) ^ l • Form.ent (uX l kh) +
      Form.const ((Arr.x0.off : ℤ) : E))

variable [Fintype J]

/-- On entries whose reads are true, the claim says that the hidden scalar is embRhs. -/
theorem emb_last (D : Dim) (t : Cell → E) (sh : E) (mE : J) (uX : ℕ → ℕ → J) (nb ls gB : ℕ)
    (pa pb : ℕ → E) (y : J → E)
    (hT : ∀ l, l < Arr.x0.nCell → ∀ kh, kh < nb →
      y (uX l kh) = readAt D t .x0 pa 0 ls l 0 kh)
    (h : Form.val y (cEmb sh mE uX nb gB pb) = 0) :
    sh - y mE = embRhs D t nb ls gB pa pb := by
  unfold cEmb at h
  rw [map_sub, Form.val_masked, map_sum] at h
  rw [sub_eq_zero.mp h]
  unfold embRhs
  refine sum_congr rfl fun kh hkh => ?_
  rw [map_smul, smul_eq_mul, map_add, Form.val_const, map_sum]
  refine congrArg (eqN gB 0 pb kh * ·) ?_
  have e1 : ∑ l ∈ range Arr.x0.nCell, Form.val y ((256 : E) ^ l • Form.ent (uX l kh)) =
      ∑ l ∈ range Arr.x0.nCell, (256 : E) ^ l * readAt D t .x0 pa 0 ls l 0 kh :=
    sum_congr rfl fun l hl => by
      rw [map_smul, smul_eq_mul, Form.val_ent, hT l (mem_range.mp hl) kh (mem_range.mp hkh)]
  rw [e1, limbs_val]
  refine sum_congr rfl fun r _ => ?_
  refine congrArg (eqN ls 0 pa r * ·) ?_
  unfold Blocks.ext
  refine sum_congr rfl fun p _ => ?_
  rw [← eqN_off D.lT (0 + ls) pa p, Nat.zero_add]
  rfl

end Claim

end

end Cb.Pv.Lay.End.Gated
