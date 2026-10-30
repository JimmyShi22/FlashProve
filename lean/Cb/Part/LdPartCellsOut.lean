-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartCellsOut.lean: how cells are read off a stage's open messages: the record `LdPartOut`
(Cb/Part/LdPartRide.lean), filled from a naming, and four laws on its three fields.

One definition, one statement (`Cb.Spec.ldPartCells_out`) and its proof. Generic: any parameters p
of a range check with packing (`RngPar`, Cb/Ld/LdRng.lean), any naming, any open messages. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
A naming `nm : LdPartNm p` (Cb/Part/LdPartCells.lean) has each segment's shape (`nm.R s`, `nm.C s`)
and says where the rows and columns of each segment's matrix are in the one matrix of a body. The
ghost g : `LdPartGh` is the integer cells of all segments. B, D and the radix are p's.

Main names:
  `nm.out S pkAt`: the record with the three fields (the "letters" of the limits below)
    A m := `nm.A pkAt` of the entries of m;
    pkX m g (exact) := the packed entries of m are the packing of the ghost's matrices g, laid into
      the body's matrix by the naming, all cells below the honest bound B in absolute value;
    pkR m (relaxed) := they are a packing of cells below the relaxed bound 2 D in absolute value.
  `Spec.ldPartCells_out`: four laws.
    (weak) If B ≤ 2 D, then pkX m g ⇒ pkR m.
    (ghost) Under the two conditions on the radix (`Uniq (2 * p.D) p.rdx p.P pp`, pp the
      characteristic of E), `nm.OK` and B ≤ 2 D: pkX m g ⇒ A m s r c = g s r c (in E) inside the
      shapes.
    (off) A m s r c = 0 outside the shapes.
    (small) If 0 < D, every A m s r c is the image in E of an integer below 2 D in absolute value,
      whether m is packed or not (where it is not, the reading is the zero matrix).

Limits: this file does not say how the letters at one stage are tied to those at the next (a kept
matrix is read off its re-encoding: the closing's places). Elsewhere: `LdPartKeepTie`
(Cb/Part/LdPartKeep.lean); `Spec.ldPartKeepOf` (Cb/Part/LdPartKeepOf.lean). This file says nothing
on protocols. No record is asked here: the four laws have plain premises on numbers and `nm.OK`, and
whatever the arguments hold as proofs; a naming in order, under the hypotheses of its statement:
`Spec.ldPartNmOf_ok`, Cb/Part/LdPartNmOf.lean.
-/
import Cb.Part.LdPartRide
import Cb.Part.LdPartCellsProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Blocks Finset Cb.Rng Cb.RngPk

/-- The record `LdPartOut E S` filled from the naming `nm`; `pkAt` says at which entries of the
messages the packed entries are. -/
def LdPartNm.out
    {p : RngPar} (nm : LdPartNm p) {E : Type} [Field E] (S : Sig E) (pkAt : p.Rp → p.C → S.Ent) :
    LdPartOut E S :=
  ⟨fun m => nm.A pkAt (S.ents m),
    fun m g => PackBy p.B p.rdx (nm.lay g) (fun i κ => S.ents m (pkAt i κ)),
    fun m => Packed p.P (2 * p.D) p.rdx (fun i κ => S.ents m (pkAt i κ))⟩

def Spec.ldPartCells_out : Prop :=
  ∀ (p : RngPar) (nm : LdPartNm p) (E : Type) [Field E] (S : Sig E) (pkAt : p.Rp → p.C → S.Ent),
    (p.B ≤ 2 * p.D → ∀ m g, (nm.out S pkAt).pkX m g → (nm.out S pkAt).pkR m) ∧
    (∀ (pp : ℕ) [CharP E pp], Uniq (2 * p.D) p.rdx p.P pp → nm.OK → p.B ≤ 2 * p.D →
      ∀ m g, (nm.out S pkAt).pkX m g →
        ∀ s r c, r < nm.R s → c < nm.C s → (nm.out S pkAt).A m s r c = ((g s r c : ℤ) : E)) ∧
    (∀ m s r c, ¬ (r < nm.R s ∧ c < nm.C s) → (nm.out S pkAt).A m s r c = 0) ∧
    (0 < p.D → ∀ m s r c, ∃ z : ℤ, |z| < 2 * p.D ∧ (nm.out S pkAt).A m s r c = ((z : ℤ) : E))

theorem ldPartCells_out : Spec.ldPartCells_out := by
  intro p nm E _ S pkAt
  refine ⟨fun hB m g h => ⟨nm.lay g, fun r c => lt_of_lt_of_le (h.1 r c) hB, h.2⟩,
    fun pp _ hU hOK hB m g h s r c hr hc => ?_,
    fun m s r c hn => ?_,
    fun hD m s r c => ?_⟩
  · exact ldPartCells_honest p E S.Ent pp nm pkAt (S.ents m) g p.B hOK hU hB h s r c hr hc
  · show ((nm.mats _ s r c : ℤ) : E) = 0
    unfold LdPartNm.mats
    rw [if_neg hn, Int.cast_zero]
  · refine ⟨nm.mats (cells p.P (2 * p.D) p.rdx fun i κ => S.ents m (pkAt i κ)) s r c, ?_, rfl⟩
    have h0 : (0 : ℤ) < 2 * p.D := by omega
    unfold LdPartNm.mats
    split
    · unfold cells
      split
      · rename_i hP
        exact hP.choose_spec.1 _ _
      · rw [abs_zero]
        exact h0
    · rw [abs_zero]
      exact h0

end Cb
