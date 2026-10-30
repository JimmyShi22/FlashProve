-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpStdPlaces2.lean: the own masks of an assembled lookup `LkAsm2` (Cb/Ld/LdLkpAsm2.lean),
named once and for all by its numbers.
This file is book-keeping on places: one type of names for the own masks of a lookup argument's
sumchecks that are played, so that where they are among the entries is given by a single map pl
(injective: a hypothesis of `ldLkpStd2_places`).

Definitions, theorems. Auxiliary definitions and lemmas for toys and instances; no protocol. The
closing has no inner mask, so there are eleven families.

Why: Cb/Ld/LdLkpMaskPlaces2.lean asks of the data `A : LkAsm2 E` that all own masks that are played
stand at pairwise different places outside the data (a set Dt of entries) (`A.PlacesOK Dt`). The
names of these masks depend on the field and the numbers n, v', d, w alone.

Main names:
  `LkNm2 E n v' d w`: the names, as a type made of sums and finite families (so it is finite as it
    stands, and can name the members of a family of oracle messages).
  `LkNm2.wS` to `LkNm2.cB`: the eleven families of places from one map pl : LkNm2 .. → J and one
    idle entry: a level or step that is never played (played: l < n, l ≤ v', l < d for the three
    pairs of families with a level or step) names the idle entry.
  `A.StdAt pl`: the eleven families of A are these, at the levels and steps that are played.
  `A.nmCode`, `A.nmDecode`: the names of Cb/Ld/LdLkpMaskPlaces2.lean (`A.Nm`) are these names.
  `ldLkpStd2_places`: `A.StdAt pl`, pl injective, no pl c in the data, the bits in the data, the
    keys read the data only ⇒ `A.PlacesOK Dt`.
  `ldLkpStd2_sw`: under `A.StdAt pl`, the places of the own masks (`A.swAll`) are the range of pl.

Limits: this file says nothing on a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskPlaces2Proofs

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E] (n v' d w : ℕ)

/-- The names of the own masks that are played. -/
abbrev LkNm2 : Type :=
  (PIdx (([] : List (PFmt E)) ++ [pDummy E 1]) ⊕ Bool) ⊕
  ((Fin n × (PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) ⊕ Bool)) ⊕
  ((Σ l : Fin (v' + 1), PIdx (List.replicate (0 + (l : ℕ)) (pfCube E 2) ++ [pDummy E 2]) ⊕ Bool) ⊕
  ((Σ l : Fin d, PIdx (List.replicate (w + (l : ℕ)) (pfCube E 2) ++ [pDummy E 2]) ⊕ Bool) ⊕
  (PIdx (List.replicate (w + d) (pfCube E 2)) ⊕
   (PIdx (List.replicate (w + d) (pfCube E 2) ++ [pDummy E 2]) ⊕ Unit)))))

end

namespace LkNm2
variable {E : Type} [Field E] [Fintype E] {n v' d w : ℕ} {J : Type}
  (pl : LkNm2 E n v' d w → J) (idle : J)

def wS (i : PIdx (([] : List (PFmt E)) ++ [pDummy E 1])) : J := pl (.inl (.inl i))
def cS (b : Bool) : J := pl (.inl (.inr b))
def wAt (l : ℕ) (i : PIdx (([] : List (PFmt E)) ++ [pDummy E 3])) : J :=
  if h : l < n then pl (.inr (.inl (⟨l, h⟩, .inl i))) else idle
def cAt (l : ℕ) (b : Bool) : J := if h : l < n then pl (.inr (.inl (⟨l, h⟩, .inr b))) else idle
def wK (l : ℕ) (i : PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2])) : J :=
  if h : l < v' + 1 then pl (.inr (.inr (.inl ⟨⟨l, h⟩, .inl i⟩))) else idle
def cK (l : ℕ) (b : Bool) : J :=
  if h : l < v' + 1 then pl (.inr (.inr (.inl ⟨⟨l, h⟩, .inr b⟩))) else idle
def wT (l : ℕ) (i : PIdx (List.replicate (w + l) (pfCube E 2) ++ [pDummy E 2])) : J :=
  if h : l < d then pl (.inr (.inr (.inr (.inl ⟨⟨l, h⟩, .inl i⟩)))) else idle
def cT (l : ℕ) (b : Bool) : J :=
  if h : l < d then pl (.inr (.inr (.inr (.inl ⟨⟨l, h⟩, .inr b⟩)))) else idle
def wE (i : PIdx (List.replicate (w + d) (pfCube E 2))) : J :=
  pl (.inr (.inr (.inr (.inr (.inl i)))))
def wB (i : PIdx (List.replicate (w + d) (pfCube E 2) ++ [pDummy E 2])) : J :=
  pl (.inr (.inr (.inr (.inr (.inr (.inl i))))))
def cB : J := pl (.inr (.inr (.inr (.inr (.inr (.inr ()))))))

/-! the families, at what is played; every place is pl of a name or the idle entry -/

theorem at_s (i) : Sum.elim (wS pl) (cS pl) i = pl (.inl i) := by cases i <;> rfl
theorem at_t (l : ℕ) (h : l < n) (i) :
    Sum.elim (wAt pl idle l) (cAt pl idle l) i = pl (.inr (.inl (⟨l, h⟩, i))) := by
  cases i
  · exact dif_pos h
  · exact dif_pos h
theorem at_k (l : ℕ) (h : l < v' + 1) (i) :
    Sum.elim (wK pl idle l) (cK pl idle l) i = pl (.inr (.inr (.inl ⟨⟨l, h⟩, i⟩))) := by
  cases i
  · exact dif_pos h
  · exact dif_pos h
theorem at_f (l : ℕ) (h : l < d) (i) :
    Sum.elim (wT pl idle l) (cT pl idle l) i = pl (.inr (.inr (.inr (.inl ⟨⟨l, h⟩, i⟩)))) := by
  cases i
  · exact dif_pos h
  · exact dif_pos h
theorem at_e (i) : wE pl i = pl (.inr (.inr (.inr (.inr (.inl i))))) := rfl
theorem at_b (i) :
    Sum.elim (wB pl) (fun _ : Unit => cB pl) i = pl (.inr (.inr (.inr (.inr (.inr i))))) := by
  cases i <;> rfl

variable (G : J → Prop) (hp : ∀ c, G (pl c)) (hi : G idle)
include hp hi

theorem in_wAt (l i) : G (wAt pl idle l i) := by unfold wAt; split; exacts [hp _, hi]
theorem in_cAt (l b) : G (cAt pl idle l b) := by unfold cAt; split; exacts [hp _, hi]
theorem in_wK (l i) : G (wK pl idle l i) := by unfold wK; split; exacts [hp _, hi]
theorem in_cK (l b) : G (cK pl idle l b) := by unfold cK; split; exacts [hp _, hi]
theorem in_wT (l i) : G (wT pl idle l i) := by unfold wT; split; exacts [hp _, hi]
theorem in_cT (l b) : G (cT pl idle l b) := by unfold cT; split; exacts [hp _, hi]

end LkNm2

namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E)

/-- The eleven families of A are the standard ones, at what is played. -/
structure StdAt (pl : LkNm2 E A.n A.v' A.d A.w → A.J) : Prop where
  s : ∀ i, Sum.elim A.wS A.cS i = pl (.inl i)
  t : ∀ l (h : l < A.n) i, Sum.elim (A.wAt l) (A.cAt l) i = pl (.inr (.inl (⟨l, h⟩, i)))
  k : ∀ l (h : l < A.v' + 1) i, Sum.elim (A.wK l) (A.cK l) i = pl (.inr (.inr (.inl ⟨⟨l, h⟩, i⟩)))
  f : ∀ l (h : l < A.d) i, Sum.elim (A.wT l) (A.cT l) i = pl (.inr (.inr (.inr (.inl ⟨⟨l, h⟩, i⟩))))
  e : ∀ i, A.wE i = pl (.inr (.inr (.inr (.inr (.inl i)))))
  b : ∀ i, Sum.elim A.wB (fun _ => A.cB) i = pl (.inr (.inr (.inr (.inr (.inr i)))))

def nmCode : A.Nm → LkNm2 E A.n A.v' A.d A.w
  | .s i => .inl i
  | .t l h i => .inr (.inl (⟨l, h⟩, i))
  | .k l h i => .inr (.inr (.inl ⟨⟨l, Nat.lt_succ_of_le h⟩, i⟩))
  | .f l h i => .inr (.inr (.inr (.inl ⟨⟨l, h⟩, i⟩)))
  | .e i => .inr (.inr (.inr (.inr (.inl i))))
  | .b i => .inr (.inr (.inr (.inr (.inr i))))

def nmDecode : LkNm2 E A.n A.v' A.d A.w → A.Nm
  | .inl i => .s i
  | .inr (.inl (l, i)) => .t l.1 l.2 i
  | .inr (.inr (.inl ⟨l, i⟩)) => .k l.1 (Nat.le_of_lt_succ l.2) i
  | .inr (.inr (.inr (.inl ⟨l, i⟩))) => .f l.1 l.2 i
  | .inr (.inr (.inr (.inr (.inl i)))) => .e i
  | .inr (.inr (.inr (.inr (.inr i)))) => .b i

theorem nmDecode_code : ∀ x, A.nmDecode (A.nmCode x) = x
  | .s _ => rfl
  | .t _ _ _ => rfl
  | .k _ _ _ => rfl
  | .f _ _ _ => rfl
  | .e _ => rfl
  | .b _ => rfl

theorem nmCode_decode : ∀ c, A.nmCode (A.nmDecode c) = c
  | .inl _ => rfl
  | .inr (.inl (_, _)) => rfl
  | .inr (.inr (.inl ⟨_, _⟩)) => rfl
  | .inr (.inr (.inr (.inl ⟨_, _⟩))) => rfl
  | .inr (.inr (.inr (.inr (.inl _)))) => rfl
  | .inr (.inr (.inr (.inr (.inr _)))) => rfl

theorem plN_std {pl : LkNm2 E A.n A.v' A.d A.w → A.J} (h : A.StdAt pl) :
    ∀ x, A.plN x = pl (A.nmCode x)
  | .s i => h.s i
  | .t l hl i => h.t l hl i
  | .k l hl i => h.k l (Nat.lt_succ_of_le hl) i
  | .f l hl i => h.f l hl i
  | .e i => h.e i
  | .b i => h.b i

end LkAsm2
end Cb.LdLkp

namespace Cb
open Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The four plain conditions, from one injection. (not all hypotheses are named here: see the
statement below) -/
theorem ldLkpStd2_places (A : LkAsm2 E) (pl : LkNm2 E A.n A.v' A.d A.w → A.J) (Dt : A.J → Prop)
    (h : A.StdAt pl) (hi : Function.Injective pl) (ho : ∀ c, ¬ Dt (pl c))
    (hb : ∀ u j, Dt (A.bAt u j))
    (hk : ∀ st m m', (∀ j, Dt j → m j = m' j) → A.key st m = A.key st m') : A.PlacesOK Dt where
  inj := fun x y e => by
    rw [A.plN_std h, A.plN_std h] at e
    have e1 := congrArg A.nmDecode (hi e)
    rwa [A.nmDecode_code, A.nmDecode_code] at e1
  out := fun i => by
    rw [A.plN_std h]
    exact ho _
  bits := hb
  keys := hk

/-- under `A.StdAt pl`, the places of the own masks are the range of pl -/
theorem ldLkpStd2_sw (A : LkAsm2 E) (pl : LkNm2 E A.n A.v' A.d A.w → A.J)
    (h : A.StdAt pl) (j : A.J) : A.swAll j ↔ ∃ c, j = pl c :=
  ⟨fun hw => by
    obtain ⟨i, rfl⟩ := (ldLkpPlaces2_sw E A j).1 hw
    exact ⟨_, A.plN_std h i⟩,
      fun ⟨c, e⟩ =>
        (ldLkpPlaces2_sw E A j).2 ⟨A.nmDecode c, by rw [e, A.plN_std h, A.nmCode_decode]⟩⟩

end
end Cb
