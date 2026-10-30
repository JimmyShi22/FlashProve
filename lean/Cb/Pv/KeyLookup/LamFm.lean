-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/LamFm.lean: the formats of a lookup's rounds, read off the list Λ; and that the
assembled lookup's formats are these, if each stretch's are its share.

A flat transcript (Cb/Pv/KeyLookup/Flat.lean) fits a list of formats if in each round as many
scalars are sent and as many elements drawn as the format says, and no element
that must not be 0 is 0. Nothing else is asked: no test on values.

It imports Cb/Pv/KeyLookup/Lam.lean and Cb/Pv/KeyLookup/AsmRuns.lean; no file of the port.

  `rowDraws S k`  how many elements the verifier draws in a round of the kind k.
  `rowFm S r`     the format of a row r of Λ: its scalars in short form; its kind's draws; whether
                  the draw must not be 0 (the further variable Y's alone).
  `lamFm S`       the formats of all rounds: `rowFm S` along Λ. It reads neither the column n nor c,
                  so it does not hang on the number of elements of the field
                  (`lamFm_eq`).
  `D.IsLam q`     what is asked of the eight stretches' formats: each is `rowFm` along its share of
                  Λ.
  `fm_isLam`      D.IsLam q ⇒ D.fm = lamFm A.toPub.
Not claimed: that stretches with such formats exist (files of their own); anything on the port's
plan.

-/
import Cb.Pv.KeyLookup.Lam
import Cb.Pv.KeyLookup.AsmRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Flat

/-- How many elements the verifier draws in a round of that kind. -/
def rowDraws (S : Pub) : Kind → ℕ
  | .vals => 0
  | .join => S.mu
  | .zero => S.mu + S.d
  | _ => 1

/-- The format of a row. -/
def rowFm (S : Pub) (r : LRow) : Fm := ⟨r.short.sent, rowDraws S r.kind, r.kind == .y⟩

/-- The formats of all rounds. -/
def lamFm (S : Pub) : List Fm := (Lam 0 S).map (rowFm S)

theorem psc_fm (S : Pub) (q q' : ℕ) (deg : List ℕ) (y : Option (ℕ × ℕ)) :
    (psc q deg y).map (rowFm S) = (psc q' deg y).map (rowFm S) := by
  rcases y with _ | ⟨a, b⟩ <;> simp [psc, rowFm, LRow.short, Function.comp_def]

theorem tree_fm (S : Pub) (q q' more levels : ℕ) :
    (tree q more levels).map (rowFm S) = (tree q' more levels).map (rowFm S) := by
  simp only [tree, List.map_flatMap, List.map_append, psc_fm S q q']
  rfl

/-- The formats do not hang on the number of elements of the field. -/
theorem lamFm_eq (q : ℕ) (S : Pub) : (Lam q S).map (rowFm S) = lamFm S := by
  simp only [lamFm, Lam, lamHead, lamParts, lamJoin, lamKeys, lamTable, lamClo, lamZero, lamBits,
    List.map_append, List.map_flatMap, psc_fm S q 0, tree_fm S q 0]
  rfl

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]

/-- What is asked of the eight stretches' formats. -/
structure RunD.IsLam {A : Dat E} (D : RunD A) (q : ℕ) : Prop where
  head  : D.fHead = (lamHead q A.toPub).map (rowFm A.toPub)
  parts : D.fParts = (lamParts q A.toPub).map (rowFm A.toPub)
  join  : D.fJoin = (lamJoin q A.toPub).map (rowFm A.toPub)
  keys  : D.fKeys = (lamKeys q A.toPub).map (rowFm A.toPub)
  table : D.fTable = (lamTable q A.toPub).map (rowFm A.toPub)
  clo   : D.fClo = (lamClo q A.toPub).map (rowFm A.toPub)
  zero  : D.fZero = (lamZero q A.toPub).map (rowFm A.toPub)
  bits  : D.fBits = (lamBits q A.toPub).map (rowFm A.toPub)

/-- The assembled lookup's formats are the list's. -/
theorem RunD.fm_isLam {A : Dat E} (D : RunD A) (q : ℕ) (h : D.IsLam q) : D.fm = lamFm A.toPub := by
  rw [← lamFm_eq q]
  simp only [RunD.fm, RunD.f7, RunD.f6, RunD.f5, RunD.f4, RunD.f3, RunD.f2, Lam, List.map_append,
    h.head, h.parts, h.join, h.keys, h.table, h.clo, h.zero, h.bits]

end Lk6

#print axioms Lk6.lamFm_eq
#print axioms Lk6.RunD.fm_isLam
