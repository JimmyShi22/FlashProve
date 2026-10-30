-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedExtLaws.lean: the two walks of
OnBytes/TypedOracleCompiler/Compile/Batch/ListedExt.lean are the compiled verifier's own two walks over the external
strings, at lists that meet three conditions.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

States.
  strictExtL_eq: if an opening stands at listed positions alone (h2) and the wiring's list holds
    every position (h3), then strictExtL sMT isRead g listed = strictExt sMT we isRead g
    (Compile/Bcs.lean).
  checksExtW_filter: the verifier's checks along a list are its checks along the list's read
    members.
  checksExtL_filter: the checks of ListedExt.lean along the read members of a list are the
    verifier's checks along the list.
  forestExtL_eq: if rd is the wiring's list cut down to the positions read (h1), then
    forestExtL we.less emb cms g rd = forestExt we emb cms isRead g
    (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean).
Who pays. h3 is "WireE.OK.complete" (Iop/Wire.lean).
h1: rd holds every position read, no other, in the order and number of the wiring's list. A list
that lacks a read position lets a missing or false opening there pass (forestExt gives none,
forestExtL a forest): so rd is computed from the verifier's messages, never taken from the proof's
side.
h2: listed is no input of its own: it is computed from the record from which the string is made, and
h2 is to be a theorem for every such record. No run can test it: g is a function on all positions.
At a list that leaves out a position where an opening stands unread, strictExt says no and
strictExtL can say yes.
strictExtL_eq has one test isRead on both sides. That a caller's test along its own list rd is the
verifier's "decide (p ∈ ..)" follows from h1 and h3, and is the caller's to show.
Limits: h1, h2 and h3 are shown at no value here. The equations are between values of functions: no
oracle occurs. Nothing on time or memory. Nothing on soundness. No example.
The program does not import this file.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.ListedExt

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- **The strict format's test along the listed positions is the verifier's.** -/
theorem strictExtL_eq (sMT : ℕ) {E : ExtSpec} (we : WireE E) (isRead : E.Pos → Bool)
    (g : E.Pos → Option (Opening lam E.Sym)) (listed : List E.Pos)
    (h2 : ∀ p, g p ≠ none → p ∈ listed) (h3 : ∀ p, p ∈ we.all) :
    strictExtL sMT isRead g listed = strictExt sMT we isRead g := by
  unfold strictExtL strictExt
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h p _
    by_cases e : g p = none
    · rw [e]
    · exact h p (h2 p e)
  · intro h p _
    exact h p (h3 p)

/-- The verifier's checks along a list are its checks along the list's read members. -/
theorem checksExtW_filter {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L)
    (cms : List (Dig lam)) (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ l : List E.Pos, checksExtW we emb cms isRead g l =
      checksExtW we emb cms isRead g (l.filter isRead)
  | [] => rfl
  | p :: ps => by
    by_cases h : isRead p = true
    · rw [List.filter_cons_of_pos h, checksExtW, checksExtW, if_pos h, if_pos h,
        ← checksExtW_filter we emb cms isRead g ps]
    · rw [List.filter_cons_of_neg h, checksExtW, if_neg h]
      exact checksExtW_filter we emb cms isRead g ps

/-- The checks along the read members of a list are the verifier's checks along the list. -/
theorem checksExtL_filter {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L)
    (cms : List (Dig lam)) (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) :
    ∀ l : List E.Pos, checksExtL we.less emb cms g (l.filter isRead) =
      checksExtW we emb cms isRead g l
  | [] => rfl
  | p :: ps => by
    by_cases h : isRead p = true
    · rw [List.filter_cons_of_pos h, checksExtL, checksExtW, if_pos h,
        checksExtL_filter we emb cms isRead g ps]
      rfl
    · rw [List.filter_cons_of_neg h, checksExtW, if_neg h]
      exact checksExtL_filter we emb cms isRead g ps

/-- **The forest along the positions read is the verifier's.** -/
theorem forestExtL_eq {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (g : E.Pos → Option (Opening lam E.Sym)) (rd : List E.Pos)
    (h1 : rd = we.all.filter isRead) :
    forestExtL we.less emb cms g rd = forestExt we emb cms isRead g := by
  subst h1
  unfold forestExtL forestExt
  rw [checksExtL_filter we emb cms isRead g we.all]
  rfl

end TypedOracleCompiler.Compile.Batch

#print axioms TypedOracleCompiler.Compile.Batch.strictExtL_eq
#print axioms TypedOracleCompiler.Compile.Batch.checksExtW_filter
#print axioms TypedOracleCompiler.Compile.Batch.checksExtL_filter
#print axioms TypedOracleCompiler.Compile.Batch.forestExtL_eq
