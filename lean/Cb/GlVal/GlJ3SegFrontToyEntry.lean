-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegFrontToyEntry.lean: the entry claim of the toy front reads
no mask; over the toy body's oracle messages it holds of some messages and fails of others that are
well packed.

A sanity check that the input claim of the toy's first sub-protocols is neither empty nor trivial.
Definitions, the statement and its proof. A part of a guard; no parameter of a protocol.
The toy front (Cb/GlVal/GlJ3SegFrontToy.lean) starts from the entry claims `EntryP` (exact) and
`EntryR` (relaxed): the two keys are in the table; a₀, a₁ are bits; in the exact one also: the four
bits are valid multiplicities. Over the toy body's oracle messages
(Cb/GlVal/GlJ3SegFrontToySeam.lean) the keys are read off the packed member.

Main names:
  `tData`: the data among the entries: the two keys, the four bits, a₀, a₁.
  `Spec.ldSegFront_toyEntry` states: `EntryP` and `EntryR` are the same at two vectors of entries
    that agree on `tData`; no entry in `tA.swAll`, no `zAt i`, no `cAt i`, not `eL idle` and not
    `eL (.inr ())` is in `tData`; at two tuples of messages whose members in `Dn` hold the same
    data, `sAll` agrees on `tData`; for cells below 2 in absolute value the packing holds of
    `msOf y bt a` (`PackBy`) and its virtual cells are y; `EntryP` holds at the cells (0, 1) (keys
    5, 7) and at (0, 0) (keys 5, 5), each with fitting bits and a₀ = a₁ = 0; `EntryR` fails at the
    cells (0, -1) (the key 3 is not in the table), and at a₀ = a₁ = 2.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, the front's data of Cb/GlVal/GlJ3SegFrontToy.lean, the facts `entry_of`,
`tPlacesOK`, Cb/GlVal/GlJ3SegFrontToyProofs.lean, `Nr`, `SS`, `sPk`, `sCell`, `sAll`,
Cb/GlVal/GlJ3SegFrontToySeam.lean, `datAt`, `datMsg`, `datAt_msg`, Cb/GlVal/GlJ3RefKit.lean,
`RefToy.p` with `RefToy.uniq`, `RefToy.So`, Cb/GlVal/GlJ3SegRefToy.lean, the toy lookup's names and
facts, Cb/GlVal/GlToyLkpNames.lean, and `pK`, Cb/GlVal/GlToyNum.lean):
the fields are F, the integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2)
(Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4,
distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: the riding joint (the encoded index, its tensor row) is not looked at here. Pads in the
subfield F are not exercised. The bounds that the toys write (one hidden position) are kept, though
this code hides 3 (said of `RefToy.D`, Cb/GlVal/GlJ3SegRefToy.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegFrontToySeamProofs
import Cb.Ld.LdRngAlgProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
namespace FrontToy
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp

/-- The data among the entries. -/
def tData : JJ → Prop := fun j => tDt j ∨ ∃ b, j = .inr (.inl b)

/-- The members that hold data: the packed one; the bits'; a₀'s, a₁'s. -/
abbrev Dn : Type := Unit ⊕ ((Bool × Bool) ⊕ Bool)
def dnAt : Dn → RefToy.So Nr
  | .inl _ => .inl ()
  | .inr (.inl ub) => .inr (.inl (.inl (.inl (.inl ub))))
  | .inr (.inr b) => .inr (.inl (.inr (.inl b)))

/-- data of all members: the packing of two cells; the bits; a₀, a₁; all else 0 -/
def vOf (y : Bool → ℤ) (bt : Bool × Bool → E) (a : Bool → E) : RefToy.So Nr → E
  | .inl _ => ((y false : ℤ) : E) + 7 * ((y true : ℤ) : E)
  | .inr (.inl (.inl (.inl (.inl ub)))) => bt ub
  | .inr (.inl (.inr (.inl b))) => a b
  | _ => 0
def msOf (y : Bool → ℤ) (bt : Bool × Bool → E) (a : Bool → E) : SS.Msg :=
  datMsg (vOf y bt a)
/-- two cells as a matrix -/
def cellsOf (y : Bool → ℤ) : RefToy.p.Cells := fun r _ => y (decide (r.2 = 1))

end FrontToy

namespace Spec
open FrontToy Cb.Gl.LkpToy Cb.LdLkp

def ldSegFront_toyEntry : Prop :=
  (∀ m m' : JJ → E, (∀ j, tData j → m j = m' j) → (EntryP m ↔ EntryP m') ∧ (EntryR m ↔ EntryR m')) ∧
  ((∀ j, tA.swAll j → ¬ tData j) ∧ (∀ i, ¬ tData (zAt i)) ∧ (∀ i, ¬ tData (FrontToy.cAt i)) ∧
    ¬ tData (eL idle) ∧ ¬ tData (eL (.inr ()))) ∧
  (∀ ms ms' : SS.Msg,
    (∀ n, datAt ms (dnAt n) = datAt ms' (dnAt n)) → ∀ j, tData j → sAll ms j = sAll ms' j) ∧
  (∀ (y : Bool → ℤ) bt a, (∀ b, |y b| < 2) →
    RngPk.PackBy RefToy.p.B RefToy.p.rdx (cellsOf y) (sPk (msOf y bt a)) ∧
    ∀ b, sCell (msOf y bt a) b = ((y b : ℤ) : E)) ∧
  EntryP (sAll (msOf (fun b => if b then 1 else 0) (fun ub => if ub.2 then 0 else 1) fun _ => 0)) ∧
  EntryP (sAll
    (msOf (fun _ => 0) (fun ub => if ub.1 then 0 else if ub.2 then 1 else 0) fun _ => 0)) ∧
  ¬ EntryR (sAll (msOf (fun b => if b then -1 else 0) (fun _ => 0) fun _ => 0)) ∧
  ¬ EntryR (sAll (msOf (fun b => if b then 1 else 0) (fun ub => if ub.2 then 0 else 1) fun _ => 2))

end Spec

namespace FrontToy
open Iop Prob Hiop IOR Cb.Gl.LkpToy Cb.LdLkp Cb.Lkp

theorem key_data (b : Bool) : tData (eL (kAt b)) := Or.inl ⟨kAt b, rfl, ⟨.inl b, rfl⟩⟩
theorem bit_data (u j : ℕ) : tData (tA0.bAt u j) := Or.inl ⟨toyA.bAt u j, rfl, mkPlacesOK.bits u j⟩
theorem a_data (b : Fin 1 → Bool) : tData (aAt b) := Or.inr ⟨b 0, rfl⟩

theorem entryP_congr (m m' : JJ → E) (h : ∀ j, tData j → m j = m' j) :
    (EntryP m → EntryP m') ∧ (EntryR m → EntryR m') := by
  have ek : tP.key () m = tP.key () m' := funext fun f => funext fun i => h _ (key_data _)
  have eb : ∀ f, (fun u j => m (tA0.bAt (f * 2 ^ tP.d + u) j)) =
      fun u j => m' (tA0.bAt (f * 2 ^ tP.d + u) j) :=
    fun f => funext fun u => funext fun j => h _ (bit_data _ _)
  have ea : tBit.AllBits m → tBit.AllBits m' := fun ha b => by
    have e : m' (aAt b) = m (aAt b) := (h _ (a_data b)).symm
    show m' (aAt b) * (m' (aAt b) - 1) = 0
    rw [e]
    exact ha b
  refine ⟨fun ⟨h1, h2, h3⟩ => ⟨ek ▸ h1, ea h2, fun f hf => ?_⟩, fun ⟨h1, h2⟩ => ⟨ek ▸ h1, ea h2⟩⟩
  have h4 := h3 f hf
  rw [ek, eb f] at h4
  exact h4

theorem data_inl_or (j : JJ) (h : tData j) :
    (∃ p : Bool ⊕ (Bool × Bool), j = .inl (.inl (.inl p))) ∨ ∃ b, j = .inr (.inl b) := by
  rcases h with ⟨j0, rfl, p, rfl⟩ | h
  · exact Or.inl ⟨p, rfl⟩
  · exact Or.inr h

theorem sAll_data (ms ms' : SS.Msg) (h : ∀ n, datAt ms (dnAt n) = datAt ms' (dnAt n))
    (j : JJ) (hj : tData j) : sAll ms j = sAll ms' j := by
  have hp : sPk ms = sPk ms' := funext fun _ => funext fun _ => h (.inl ())
  rcases data_inl_or j hj with ⟨b | ub, rfl⟩ | ⟨b, rfl⟩
  · show 5 + 2 * sCell ms b = 5 + 2 * sCell ms' b
    unfold sCell
    rw [hp]
  · exact h (.inr (.inl ub))
  · exact h (.inr (.inr b))

theorem pack_of (y : Bool → ℤ) (bt : Bool × Bool → E) (a : Bool → E) (hy : ∀ b, |y b| < 2) :
    RngPk.PackBy RefToy.p.B RefToy.p.rdx (cellsOf y) (sPk (msOf y bt a)) := by
  refine ⟨fun r _ => hy _, fun i c => ?_⟩
  show datAt (datMsg (vOf y bt a)) (.inl ()) = RngPk.pack 7 (fun r => ((cellsOf y r c : ℤ) : E)) i
  rw [datAt_msg]
  unfold RngPk.pack
  rw [Fin.sum_univ_two]
  show ((y false : ℤ) : E) + 7 * ((y true : ℤ) : E) =
    ((7 : ℤ) : E) ^ 0 * ((y false : ℤ) : E) + ((7 : ℤ) : E) ^ 1 * ((y true : ℤ) : E)
  push_cast
  ring

theorem cell_of (y : Bool → ℤ) (bt : Bool × Bool → E) (a : Bool → E)
    (hy : ∀ b, |y b| < 2) (b : Bool) :
    sCell (msOf y bt a) b = ((y b : ℤ) : E) := by
  have e := rngPk_cells E pK Unit Unit 2 (2 * 2) 2 7 (cellsOf y) (sPk (msOf y bt a)) RefToy.uniq
    (by norm_num) (pack_of y bt a hy)
  unfold sCell
  have e' : RngPk.cells RefToy.p.P (2 * RefToy.p.D) RefToy.p.rdx (sPk (msOf y bt a)) = cellsOf y :=
    e
  rw [e']
  cases b <;> rfl

theorem sAll_of (y : Bool → ℤ) (bt : Bool × Bool → E) (a : Bool → E) (hy : ∀ b, |y b| < 2)
    (r : Rw → E) (hk : ∀ b, r (kAt b) = 5 + 2 * ((y b : ℤ) : E))
    (hb : ∀ ub : Bool × Bool, r (Cb.Gl.LkpToy.bitAt ub.1 ub.2) = bt ub) (j : JJ) (hj : tData j) :
    ent r a j = sAll (msOf y bt a) j := by
  rcases data_inl_or j hj with ⟨b | ub, rfl⟩ | ⟨b, rfl⟩
  · show r (kAt b) = 5 + 2 * sCell (msOf y bt a) b
    rw [cell_of y bt a hy, hk]
  · show r (Cb.Gl.LkpToy.bitAt ub.1 ub.2) =
      datAt (datMsg (vOf y bt a)) (.inr (.inl (.inl (.inl (.inl ub)))))
    rw [datAt_msg, hb]
    rfl
  · show a b = datAt (datMsg (vOf y bt a)) (.inr (.inl (.inr (.inl b))))
    rw [datAt_msg]
    rfl

end FrontToy

open FrontToy Cb.Gl.LkpToy Cb.LdLkp in
theorem ldSegFront_toyEntry : Spec.ldSegFront_toyEntry := by
  refine ⟨fun m m' h =>
      ⟨⟨(entryP_congr m m' h).1, (entryP_congr m' m fun j hj => (h j hj).symm).1⟩,
        ⟨(entryP_congr m m' h).2, (entryP_congr m' m fun j hj => (h j hj).symm).2⟩⟩,
    ⟨?_, ?_, ?_, ?_, ?_⟩,
    sAll_data,
    fun y bt a hy => ⟨pack_of y bt a hy, cell_of y bt a hy⟩,
    ?_, ?_, ?_, ?_⟩
  · intro j hw hd
    obtain ⟨i, rfl⟩ := (ldLkpPlaces2_sw E tA j).1 hw
    rcases hd with hd | ⟨b, e⟩
    · exact tPlacesOK.out i hd
    · exact Sum.inl_ne_inr ((re2_plN toyA eL _ _ i).symm.trans e)
  · rintro i (⟨j0, e, _⟩ | ⟨b, e⟩)
    · exact Sum.inr_ne_inl e
    · exact Sum.inr_ne_inl (Sum.inr_injective e)
  · rintro i (⟨j0, e, _⟩ | ⟨b, e⟩)
    · exact Sum.inr_ne_inl e
    · exact Sum.inr_ne_inl (Sum.inr_injective e)
  · rintro (⟨j0, e, p, rfl⟩ | ⟨b, e⟩)
    · exact Sum.inr_ne_inl (Sum.inl_injective (Sum.inl_injective e))
    · exact Sum.inl_ne_inr e
  · rintro (⟨j0, e, p, rfl⟩ | ⟨b, e⟩)
    · exact Sum.inr_ne_inl (Sum.inl_injective e)
    · exact Sum.inl_ne_inr e
  · refine (entryP_congr _ _ (sAll_of _ _ _ (fun b => by cases b <;> norm_num) w57 (fun b => by
      cases b
      · show (5 : E) = 5 + 2 * ((0 : ℤ) : E)
        simp
      · show (7 : E) = 5 + 2 * ((1 : ℤ) : E)
        norm_num) fun _ => rfl)).1 (entry_of w57 _ in57 fun _ => by simp)
  · refine (entryP_congr _ _ (sAll_of _ _ _ (fun b => by norm_num) w55 (fun b => by
      show (5 : E) = 5 + 2 * ((0 : ℤ) : E)
      simp) fun _ => rfl)).1 (entry_of w55 _ in55 fun _ => by simp)
  · intro h
    obtain ⟨u, hu, he⟩ := h.1 0 Nat.one_pos 1 (by decide)
    have hc := cell_of (fun b => if b then -1 else 0) (fun _ => 0) (fun _ => 0)
      (fun b => by cases b <;> norm_num) true
    have he' : (5 : E) +
        2 * sCell (msOf (fun b => if b then -1 else 0) (fun _ => 0) fun _ => 0) true =
      if u = 0 then 5 else 7 := he
    rw [hc] at he'
    by_cases h0 : u = 0
    · rw [if_pos h0] at he'
      revert he'
      decide
    · rw [if_neg h0] at he'
      revert he'
      decide
  · intro h
    have h1 := h.2 fun _ => false
    have h2 : sAll (msOf (fun b => if b then 1 else 0) (fun ub => if ub.2 then 0 else 1) fun _ => 2)
          (aAt fun _ => false) = 2 := datAt_msg _ _
    have h3 : sAll (msOf (fun b => if b then 1 else 0) (fun ub => if ub.2 then 0 else 1) fun _ => 2)
            (aAt fun _ => false) *
          (sAll (msOf (fun b => if b then 1 else 0) (fun ub => if ub.2 then 0 else 1) fun _ => 2)
              (aAt fun _ => false) - 1) = 0 := h1
    rw [h2] at h3
    exact absurd h3 (by decide)

end Cb.GlJ3
