-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchTie.lean: the dictionary of Johnson/Top/H/SwitchNames.lean tied to the
library's own, and bounds on the indices of a code switch's names.

Statements and proofs.
Main names:
  `coordAt_eq`, `entAt_eq`: the table and the index that `coordAt` gives a coordinate of a shape's
    message are the library's `partZ` and `locZ` (Johnson/Pack/PortTie.lean).
  `InTab.lt`, `InTab.lt_pow`: an index that lies in a table is below (2 ^ row bits) * (the row's
    length), so below 2 ^ (row bits + ceilLog2 of the row's length).
  `Fit.main_lt`, `Fit.rest_lt`, `Fit.kept_lt`, `Fit.row_lt`: the same of the names of a switch,
    under `Fit` (Johnson/Top/H/SwitchMapsFit.lean).
  `frame_bits`: the two numbers of index bits in a frame that the program makes.
  `tableBits_of_shape`: a table's index bits in a statement, off the message's shape.
Limits: nothing on soundness.

-/
import Johnson.Top.H.SwitchMapsFit
import Johnson.Pack.PortTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Johnson.Pack

/-- **The two dictionaries are one.** -/
theorem coordAt_eq (cs : Codes) (s : OracleShape) (j : (portCode cs s).J) :
    coordAt cs s j = (partZ cs s j, locZ cs s j) := by
  change (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell) at j
  rcases j with x | x <;> rfl

theorem entAt_eq (cs : Codes) (l : List (OracleShape × ℕ)) (n : (sigOf cs l).Ent) :
    entAt cs l n = (n.1.val, partZ cs (l.get n.1).1 n.2, locZ cs (l.get n.1).1 n.2) :=
  congrArg (fun t => (n.1.val, t)) (coordAt_eq cs (l.get n.1).1 n.2)

theorem lt_of_mod_div (R n rows ell : ℕ) (h1 : n % R < rows) (hR : rows ≤ R) (h2 : n / R < ell) :
    n < R * ell := by
  have e := Nat.mod_add_div n R
  have h3 : R * (n / R + 1) ≤ R * ell := Nat.mul_le_mul_left _ h2
  rw [Nat.mul_add, Nat.mul_one] at h3
  omega

section
variable {cs : Codes} {l : List (OracleShape × ℕ)}

/-- An index that lies in a table. -/
theorem InTab.lt {t : Nm} (h : InTab cs l t) : ∃ ho : t.1 < l.length,
    t.2.2 < 2 ^ ceilLog2 ((l.get ⟨t.1, ho⟩).1.rows t.2.1) * ellOf cs (l.get ⟨t.1, ho⟩).1 t.2.1 := by
  obtain ⟨ho, h1, h2⟩ := h
  exact ⟨ho, lt_of_mod_div _ _ _ _ h1 (le_two_pow_ceilLog2 _) h2⟩

theorem InTab.lt_pow {t : Nm} (h : InTab cs l t) : ∃ ho : t.1 < l.length,
    t.2.2 < 2 ^ (ceilLog2 ((l.get ⟨t.1, ho⟩).1.rows t.2.1) +
      ceilLog2 (ellOf cs (l.get ⟨t.1, ho⟩).1 t.2.1)) := by
  obtain ⟨ho, h1⟩ := h.lt
  refine ⟨ho, lt_of_lt_of_le h1 ?_⟩
  rw [Nat.pow_add]
  exact Nat.mul_le_mul_left _ (le_two_pow_ceilLog2 _)

variable {s : Sg} {K : Type} {W : SwitchFrame} {mem row : K → ℕ} {pl : K → KeptPlace}

/-- The index of an entry of the main row's message. -/
theorem Fit.main_lt (F : Fit cs l s W mem row pl) (j : ℕ) (hj : j < s.C.l) :
    cutIndex W.mainCut W.rowBits j <
      2 ^ (W.rowBits + ceilLog2 (pMain cs (l.get ⟨0, F.g⟩).1).ell) := by
  obtain ⟨_, h⟩ := (inTab_main cs l W F.g F.mainBits F.mainFits F.mainRows j
    (lt_of_lt_of_le hj F.mainLen)).lt_pow
  have h' : cutIndex W.mainCut W.rowBits j < 2 ^ (ceilLog2 (l.get ⟨0, F.g⟩).1.mainRows +
      ceilLog2 (pMain cs (l.get ⟨0, F.g⟩).1).ell) := h
  rw [← F.mainBits] at h'
  exact h'

/-- The index of an entry of the rest. -/
theorem Fit.rest_lt (F : Fit cs l s W mem row pl) (i : ℕ) (hi : i < W.parts.length) :
    W.places.get i <
      2 ^ (W.places.rowBits + ceilLog2 (ellOf cs (l.get ⟨0, F.g⟩).1 W.restPart)) := by
  obtain ⟨_, h⟩ := (F.rest i hi).lt_pow
  rw [F.restBits]
  exact h

/-- A kept row's number is below 2 ^ (its member's row bits). -/
theorem Fit.row_lt (F : Fit cs l s W mem row pl) (k : K) : row k < 2 ^ (pl k).rowBits := by
  obtain ⟨h, hb, hr, -⟩ := F.keptMsg k
  rw [hb]
  exact lt_of_lt_of_le hr (le_two_pow_ceilLog2 _)

/-- The index of an entry of a kept row, in its member's table. -/
theorem Fit.kept_lt (F : Fit cs l s W mem row pl) (k : K) (j : ℕ) (hj : j < s.C.l) :
    row k + 2 ^ (pl k).rowBits * j < 2 ^ ((pl k).rowBits + ceilLog2 s.C.l) := by
  have h1 := F.row_lt k
  have h2 : 2 ^ (pl k).rowBits * (j + 1) ≤ 2 ^ (pl k).rowBits * s.C.l := Nat.mul_le_mul_left _ hj
  have h3 : 2 ^ (pl k).rowBits * s.C.l ≤ 2 ^ (pl k).rowBits * 2 ^ ceilLog2 s.C.l :=
    Nat.mul_le_mul_left _ (le_two_pow_ceilLog2 _)
  rw [Nat.mul_add, Nat.mul_one] at h2
  rw [Nat.pow_add]
  omega

end

/-- The two numbers of index bits in a frame. -/
theorem frame_bits (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : ℕ)
    (anew : Array ℕ) (W : SwitchFrame) (h : switchFrame S old T g anew = some W) :
    ∃ nc, S.codes.base[T.shape.code]? = some nc ∧ W.tableBits = W.rowBits + nc.logEll ∧
      W.restBits = S.tableBits g T.rest.part := by
  unfold switchFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨code, hc, zk, hz, nc, hn, -, -, rfl⟩ := h
  exact ⟨nc, hn, rfl, rfl⟩

/-- A table's index bits in a statement, off the message's shape. -/
theorem tableBits_of_shape (S : Statement) (o : ℕ) (x : Oracle) (h : S.oracles[o]? = some x)
    (part : Part) (hr : x.shape.rows part ≠ 0) :
    S.tableBits o part =
      ceilLog2 (x.shape.rows part) + ceilLog2 (ellOf S.codes x.shape part) := by
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [h]
  have hb : (x.shape.rows part == 0) = false := beq_false_of_ne hr
  simp only [hb]
  cases part <;> rfl

end Johnson.Top.H

#print axioms Johnson.Top.H.coordAt_eq
#print axioms Johnson.Top.H.entAt_eq
#print axioms Johnson.Top.H.InTab.lt_pow
#print axioms Johnson.Top.H.Fit.main_lt
#print axioms Johnson.Top.H.Fit.rest_lt
#print axioms Johnson.Top.H.Fit.kept_lt
#print axioms Johnson.Top.H.frame_bits
#print axioms Johnson.Top.H.tableBits_of_shape
