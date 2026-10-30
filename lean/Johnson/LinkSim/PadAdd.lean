-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/PadAdd.lean: out-of-domain (OOD) answers are additive in the vector, and a change of
the pad entry changes an answer by the seed's factor times that change. First for any OOD sample,
then at the library's two samples with a pad. Statements and proofs. Pure algebra.
Terms of this folder: Johnson/LinkSim/Spec.lean.

The setting. An OOD sample here is the library's structure Sample (Cb/Gen/OodDec.lean): a seed ρ
gives a matrix, and the answers of a vector u are that matrix times u (Sample.val). StdM and
csSample are the library's samples on an oracle message. In this folder they are used for the link
proof's own OOD samples on the prover's oracle messages (see Johnson/LinkSim/AtText/Defs.lean's
terms), not for the instance's two OOD samples.

What this file has.
  val_add, val_zero   the answers of a sum of two vectors are the sum of the answers; of 0, 0.
  val_add_single   adding s at position j adds (the matrix's entry at j) times s to each answer.
  mat_std_pad, mat_std_data   for a standard oracle message's sample (StdM.Z,
                   Cb/Obj/LdObjectToyKit.lean), the matrix's entry at the pad is the seed's
                   factor, and at a data entry it is the multilinear equality weight
                   Alg.eqk ρ.1 (M.plc j).
  mat_cs_pad, ne_cs_pad   for the sample of a code switch's new message (csSample,
                   OnBytes/Slice/CsData.lean), the matrix's entry at the pad's position (csPad) is
                   the seed's factor, which is a unit, so it is not 0.
  val_made_up      If the matrix's entry at position j of answer a is not 0, then any change d of
                   answer a is made by adding d divided by that entry at position j of the vector.

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean), through
Johnson/LinkSim/AtText/Pad.lean. Under Johnson/LinkSim/ no file calls val_made_up or ne_cs_pad.

Limits. That a factor is not 0 is a premise of val_made_up; at csSample it holds by type
(ne_cs_pad).
Terms: lean/GLOSSARY.md.

-/
import Cb.Obj.LdObjectToyKit
import OnBytes.Slice.CsData

set_option autoImplicit false

namespace OnBytes.LinkSim
open Cb Cb.Ood OnBytes.Slice

section Any
variable {E J : Type} [Field E] [Fintype J] (Z : Sample E J)

/-- The answers are additive in the vector. -/
theorem val_add (ρ : Z.D) (u u' : J → E) : Z.val ρ (u + u') = Z.val ρ u + Z.val ρ u' := by
  funext s
  show (∑ j, Z.mat ρ s j * (u j + u' j)) = (∑ j, Z.mat ρ s j * u j) + ∑ j, Z.mat ρ s j * u' j
  simp only [mul_add, Finset.sum_add_distrib]

/-- The answers of 0 are 0. -/
theorem val_zero (ρ : Z.D) : Z.val ρ (0 : J → E) = 0 := by
  have e := val_add Z ρ 0 0
  rw [add_zero] at e
  exact left_eq_add.mp e

/-- Adding s at position j adds the matrix's entry at j times s to each answer. -/
theorem val_add_single [DecidableEq J] (ρ : Z.D) (u : J → E) (j : J) (s : E) (a : Z.S) :
    Z.val ρ (u + Pi.single j s) a = Z.val ρ u a + Z.mat ρ a j * s := by
  rw [val_add]
  show Z.val ρ u a + ∑ i, Z.mat ρ a i * (Pi.single j s : J → E) i = _
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]

/-- Any change d of answer a is made by adding (mat ρ a j)⁻¹ * d at position j, if that entry is not
0. -/
theorem val_made_up [DecidableEq J] (ρ : Z.D) (u : J → E) (j : J) (a : Z.S)
    (h : Z.mat ρ a j ≠ 0) (d : E) :
    Z.val ρ (u + Pi.single j ((Z.mat ρ a j)⁻¹ * d)) a = Z.val ρ u a + d := by
  rw [val_add_single, mul_inv_cancel_left₀ h]

end Any

section Std
variable {E P : Type} [Fintype P] [Field E] [Fintype E] (M : StdM E P)

/-- For a standard oracle message's sample, the entry at the pad is the seed's factor. -/
theorem mat_std_pad (ρ : M.Z.D) : M.Z.mat ρ () (M.place (.inr ())) = M.b ρ.2 := by
  show Sum.elim (fun j => Alg.eqk ρ.1 (M.plc j)) (fun _ => M.b ρ.2 * 1)
    (M.place.symm (M.place (.inr ()))) = _
  rw [Equiv.symm_apply_apply]
  exact mul_one _

/-- For a standard oracle message's sample, the entry at a data position is the multilinear equality
weight of the seed's point there. -/
theorem mat_std_data (ρ : M.Z.D) (j : M.Dt) :
    M.Z.mat ρ () (M.place (.inl j)) = Alg.eqk ρ.1 (M.plc j) := by
  show Sum.elim (fun j => Alg.eqk ρ.1 (M.plc j)) (fun _ => M.b ρ.2 * 1)
    (M.place.symm (M.place (.inl j))) = _
  rw [Equiv.symm_apply_apply]
  rfl

end Std

section Switch
variable {s s' : Sg} (hf : CsFit s s')

/-- For a code switch's new message, the entry at the pad's position is the seed's factor. -/
theorem mat_cs_pad (ρ : (csSample hf).D) (n : CsK s ⊕ CsFree hf) (hn : csPlace hf n = csPad hf) :
    (csSample hf).mat ρ () n = (ρ.2 : GE) := by
  show Sum.elim _ (fun _ => (ρ.2 : GE) * 1) (splitAt (csPad hf) (csPlace hf n)) = _
  rw [hn]
  have e : splitAt (csPad hf) (csPad hf) = .inr () := dif_pos rfl
  rw [e]
  exact mul_one _

/-- That entry is not 0. -/
theorem ne_cs_pad (ρ : (csSample hf).D) (n : CsK s ⊕ CsFree hf) (hn : csPlace hf n = csPad hf) :
    (csSample hf).mat ρ () n ≠ 0 := by
  rw [mat_cs_pad hf ρ n hn]
  exact ρ.2.ne_zero

end Switch

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.val_add
#print axioms OnBytes.LinkSim.val_made_up
#print axioms OnBytes.LinkSim.mat_std_pad
#print axioms OnBytes.LinkSim.mat_cs_pad
