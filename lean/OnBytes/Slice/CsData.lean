-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsData.lean: the library's code switch at the sizes and layouts of two neighbouring
stages of the written proximity test.

The library's code switch (Cb/Ld/LdSwitch.lean) is stated for parameters: an old code, a new code,
names for the coordinates of a new message, a sample on new messages, a number of positions,
coefficients for the batching. This file gives each of them the value that the format's code switch
has (Fmt/M1Cs.lean, Fmt/M1Send.lean), for an old stage s and a new stage s'.

The values.
 The old code: the three folded rows (`Sg.cMid`). The new code: the new stage's main rows beside its
   mask rows (`Sg.cIn`). The old form is given as its vector of coefficients.
 The layout (`csAt`, `csPut`, `csPlace`). The folded main row's message fills the new main table:
   entry j at the index j. The new mask table holds, from the index 0 on, the folded carried mask
   row's message, the folded fresh mask row's message, the main row's tail, the carried mask row's
   tail and the fresh mask row's tail. All other entries of the mask table are free room
   (`CsFree`); the last of them is the pad of the sample (`csPad`).
 The sample (`csSample`). Both tables lie on one cube, and the last coordinate tells them apart: it
   is 0 for an entry of the main table and 1 for an entry of the mask table (`cubeAt`). An entry
   has the weight of the drawn point at its vertex. The pad has a drawn factor other than 0 and no
   weight of the point.
 The coefficients: the powers of one drawn element, in the order of `csRowNo`.

Main definitions: `CsFit`, `csAt`, `csPut`, `CsFree`, `csPlace`, `csPad`, `cubeAt`, `csSample`,
`csRowNo`, `csSw`.
Main theorems: `outAt_csPut`, `csPut_inj`, `free_at`, `csRowNo_inj`.
Not claimed. That these values are those of the format's functions: that is the matter of
OnBytes/Slice/CsSim.lean. Nothing on a protocol.
-/
import OnBytes.Slice.Stage
import OnBytes.Slice.Cells
import OnBytes.Slice.SampleOK
import OnBytes.Slice.CloseKnow
import OnBytes.Slice.LdOfFacts
import Cb.Ld.LdSwitchProofs
import Cb.Ld.LdGroupStdMsg
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

/-- What a switch asks of the sizes of the old stage s and the new stage s'. The new main table
has as many entries as an old main row's message. The new mask table has room for the two folded
mask rows, the three folded tails and the pad. The new rows' lengths are powers of two. The old mask
code is not longer than the old main code. -/
structure CsFit (s s' : Sg) : Prop where
  main : 2 ^ (s'.h + s'.g) * s'.C.l = s.C.l
  mask : 2 * s.Z.l + s.C.r + 2 * s.Z.r + 1 ≤ 2 ^ s'.h * s'.Z.l
  powC : s'.C.l = 2 ^ Fmt.M1.lg s'.C.l
  powZ : s'.Z.l = 2 ^ Fmt.M1.lg s'.Z.l
  short : s.Z.a ≤ s.C.a

section
variable (s s' : Sg)

/-- The coordinates of an old full message: the three folded rows' messages, then their tails. -/
abbrev CsK : Type := s.cMid.J ⊕ s.cMid.Q

/-- Where an entry of the old full message lies in the new tables: an index of the main table
(left) or of the mask table (right). -/
def csAt : CsK s → ℕ ⊕ ℕ
  | .inl (.inl j) => .inl j.val
  | .inl (.inr (.inl j)) => .inr j.val
  | .inl (.inr (.inr j)) => .inr (s.Z.l + j.val)
  | .inr (.inl q) => .inr (2 * s.Z.l + q.val)
  | .inr (.inr (.inl q)) => .inr (2 * s.Z.l + s.C.r + q.val)
  | .inr (.inr (.inr q)) => .inr (2 * s.Z.l + s.C.r + s.Z.r + q.val)

/-- The index of an entry of the new tables: of the main table (left) or of the mask table. -/
def outAt : s'.cIn.J → ℕ ⊕ ℕ
  | .inl x => .inl (idxOf x)
  | .inr x => .inr (idxOf x)

variable {s s'}

/-- The same as an entry of the new tables. -/
def csPut (hf : CsFit s s') : CsK s → s'.cIn.J
  | .inl (.inl j) => .inl (cell _ _ j.val (hf.main.symm ▸ j.isLt))
  | .inl (.inr (.inl j)) => .inr (cell _ _ j.val (by have := j.isLt; have := hf.mask; omega))
  | .inl (.inr (.inr j)) =>
      .inr (cell _ _ (s.Z.l + j.val) (by have := j.isLt; have := hf.mask; omega))
  | .inr (.inl q) => .inr (cell _ _ (2 * s.Z.l + q.val) (by have := q.isLt; have := hf.mask; omega))
  | .inr (.inr (.inl q)) =>
      .inr (cell _ _ (2 * s.Z.l + s.C.r + q.val) (by have := q.isLt; have := hf.mask; omega))
  | .inr (.inr (.inr q)) =>
      .inr (cell _ _ (2 * s.Z.l + s.C.r + s.Z.r + q.val)
        (by have := q.isLt; have := hf.mask; omega))

/-- An entry of the old full message lies at its index. -/
theorem outAt_csPut (hf : CsFit s s') (n : CsK s) : outAt s' (csPut hf n) = csAt s n := by
  rcases n with (j | j | j) | (q | q | q)
  · exact congrArg Sum.inl (idxOf_cell _ _ _ _)
  · exact congrArg Sum.inr (idxOf_cell _ _ _ _)
  · exact congrArg Sum.inr (idxOf_cell _ _ _ _)
  · exact congrArg Sum.inr (idxOf_cell _ _ _ _)
  · exact congrArg Sum.inr (idxOf_cell _ _ _ _)
  · exact congrArg Sum.inr (idxOf_cell _ _ _ _)

/-- Different entries of the new tables have different indices. -/
theorem outAt_inj : Function.Injective (outAt s') := by
  rintro (x | x) (y | y) h
  · exact congrArg Sum.inl (idxOf_inj (Sum.inl.inj h))
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · exact congrArg Sum.inr (idxOf_inj (Sum.inr.inj h))

/-- Different entries of the old full message lie at different indices. -/
theorem csAt_inj : Function.Injective (csAt s) := by
  rintro ((a | a | a) | (a | a | a)) ((b | b | b) | (b | b | b)) h <;>
    simp only [csAt, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h <;>
    first
      | exact absurd h (by have := a.isLt; have := b.isLt; omega)
      | (have e : a = b := Fin.ext (by omega)
         rw [e])

/-- Different entries of the old full message lie at different entries of the new tables. -/
theorem csPut_inj (hf : CsFit s s') : Function.Injective (csPut hf) := fun a b h =>
  csAt_inj (by rw [← outAt_csPut hf a, ← outAt_csPut hf b, h])

/-- The entries of the new tables at which nothing of the old full message lies: free room and the
pad of the sample. -/
abbrev CsFree (hf : CsFit s s') : Type := {j : s'.cIn.J // j ∉ Set.range (csPut hf)}

/-- Free room lies in the mask table, after the last tail. -/
theorem free_at (hf : CsFit s s') (j : CsFree hf) :
    ∃ i, outAt s' j.1 = .inr i ∧ 2 * s.Z.l + s.C.r + 2 * s.Z.r ≤ i ∧ i < 2 ^ s'.h * s'.Z.l := by
  obtain ⟨j, hj⟩ := j
  -- No entry of the old full message lies at j.
  have key : ∀ n : CsK s, outAt s' j ≠ csAt s n := fun n h =>
    hj ⟨n, outAt_inj ((outAt_csPut hf n).trans h.symm)⟩
  rcases j with x | x
  · -- Every entry of the new main table holds an entry of the old main row's message.
    have hlt : idxOf x < s.C.l := hf.main ▸ idxOf_lt x
    exact absurd rfl (key (.inl (.inl ⟨idxOf x, hlt⟩)))
  · refine ⟨idxOf x, rfl, ?_, idxOf_lt x⟩
    by_contra hc
    by_cases h1 : idxOf x < s.Z.l
    · exact key (.inl (.inr (.inl ⟨idxOf x, h1⟩))) rfl
    by_cases h2 : idxOf x < 2 * s.Z.l
    · exact key (.inl (.inr (.inr ⟨idxOf x - s.Z.l, by omega⟩)))
        (congrArg Sum.inr (show idxOf x = s.Z.l + (idxOf x - s.Z.l) by omega))
    by_cases h3 : idxOf x < 2 * s.Z.l + s.C.r
    · exact key (.inr (.inl ⟨idxOf x - 2 * s.Z.l, by omega⟩))
        (congrArg Sum.inr (show idxOf x = 2 * s.Z.l + (idxOf x - 2 * s.Z.l) by omega))
    by_cases h4 : idxOf x < 2 * s.Z.l + s.C.r + s.Z.r
    · exact key (.inr (.inr (.inl ⟨idxOf x - (2 * s.Z.l + s.C.r), by omega⟩)))
        (congrArg Sum.inr
          (show idxOf x = 2 * s.Z.l + s.C.r + (idxOf x - (2 * s.Z.l + s.C.r)) by omega))
    · exact key (.inr (.inr (.inr ⟨idxOf x - (2 * s.Z.l + s.C.r + s.Z.r), by omega⟩)))
        (congrArg Sum.inr
          (show idxOf x = 2 * s.Z.l + s.C.r + s.Z.r + (idxOf x - (2 * s.Z.l + s.C.r + s.Z.r)) by
            omega))

/-- The names of a new message's coordinates: old message, old tails, free room. -/
def csPlace (hf : CsFit s s') : CsK s ⊕ CsFree hf ≃ s'.cIn.J :=
  Equiv.ofBijective (Sum.elim (csPut hf) Subtype.val) (by
    constructor
    · rintro (a | a) (b | b) h
      · exact congrArg Sum.inl (csPut_inj hf h)
      · exact absurd ⟨a, h⟩ b.2
      · exact absurd ⟨b, h.symm⟩ a.2
      · exact congrArg Sum.inr (Subtype.val_injective h)
    · intro j
      by_cases hj : j ∈ Set.range (csPut hf)
      · obtain ⟨n, rfl⟩ := hj
        exact ⟨.inl n, rfl⟩
      · exact ⟨.inr ⟨j, hj⟩, rfl⟩)

/-- At a coordinate of the old full message, `csPlace` is `csPut`. -/
theorem csPlace_inl (hf : CsFit s s') (n : CsK s) : csPlace hf (.inl n) = csPut hf n := rfl
/-- At a coordinate of free room, `csPlace` is the entry itself. -/
theorem csPlace_inr (hf : CsFit s s') (q : CsFree hf) : csPlace hf (.inr q) = q.1 := rfl

/-- The pad's entry: the last of the mask table. -/
def csPad (hf : CsFit s s') : s'.cIn.J :=
  .inr (cell _ _ (2 ^ s'.h * s'.Z.l - 1) (by have := hf.mask; omega))

variable (s')

/-- The vertex of an entry on the cube of the sample's point, as a number. The last coordinate is 0
for an entry of the main table and 1 for an entry of the mask table; the lower ones spell the
entry's index in its table. -/
def cubeAt : s'.cIn.J → ℕ
  | .inl x => idxOf x
  | .inr x => 2 ^ (s'.st.na - 1) + idxOf x

variable {s'}

/-- The sample of the new message: the weight of the point at an entry's vertex, and a factor
other than 0 on the pad. -/
@[reducible] def csSample (hf : CsFit s s') : Sample GE (CsK s ⊕ CsFree hf) :=
  reix (Sample.pad GE (Fin s'.st.na) {j : s'.cIn.J // j ≠ csPad hf} Unit GEˣ
    (fun j t => (cubeAt s' j.1).testBit t.val) (fun _ => 1) Units.val)
    ((csPlace hf).trans (splitAt (csPad hf)))

variable (s)

/-- The number of a row in the order of batching: the carried claim; the sample row; for the
draw number i the main row's symbol, the old mask row's, the fresh mask row's. -/
def csRowNo : LdRow Unit s.t s.cMid.Aa → Fin (2 + 3 * s.t)
  | .inl _ => ⟨0, by omega⟩
  | .inr (.inl _) => ⟨1, by omega⟩
  | .inr (.inr (i, .inl _)) => ⟨2 + 3 * i.val, by have := i.isLt; omega⟩
  | .inr (.inr (i, .inr (.inl _))) => ⟨2 + 3 * i.val + 1, by have := i.isLt; omega⟩
  | .inr (.inr (i, .inr (.inr _))) => ⟨2 + 3 * i.val + 2, by have := i.isLt; omega⟩

/-- Different rows have different numbers. -/
theorem csRowNo_inj : Function.Injective (csRowNo s) := by
  rintro (⟨⟩ | ⟨⟩ | ⟨i, (⟨⟩ | ⟨⟩ | ⟨⟩)⟩) (⟨⟩ | ⟨⟩ | ⟨j, (⟨⟩ | ⟨⟩ | ⟨⟩)⟩) h <;>
    simp only [csRowNo, Fin.mk.injEq] at h <;>
    first
      | rfl
      | omega
      | (have e : i = j := Fin.ext (by omega)
         rw [e])

variable {s}

/-- The library's code switch at these sizes. -/
@[reducible] def csSw (hf : CsFit s s') : LdSw GE s.Ps s'.Ps (s.cMid.J → GE) where
  Cin := s.cMid
  Cout := s'.cIn
  Qo := CsFree hf
  finQo := Fintype.ofFinite _
  decQo := Classical.decEq _
  place := csPlace hf
  sl := Slf.idf
  Zo := csSample hf
  t := s.t
  Zb := (Evader.powers GE (2 + 3 * s.t)).comap (csRowNo s)

end

end OnBytes.Slice

#print axioms OnBytes.Slice.outAt_csPut
#print axioms OnBytes.Slice.csPut_inj
#print axioms OnBytes.Slice.free_at
#print axioms OnBytes.Slice.csRowNo_inj
