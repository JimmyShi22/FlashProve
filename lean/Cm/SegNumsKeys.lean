-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegNumsKeys.lean: generic bounds on the numbers of variables of the glued families of a segment,
by size of table.

Statements on data only, with their proofs.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family has one value at each vertex of a cube of 2^v
vertices; v is its number of variables. Glued: several families joined into one by further selector
variables (`SegSpec.glued`, Cb/Req/ReqGlue.lean): one family of identities in a segment, one family
of keys for each table.

Why: a lookup on a glued family of keys has 2^n keys, n its number of variables, and counts
multiplicities in W > n bits. Here the families are counted that can be glued into one.

Which tables are equal is decided classically in the glued form (Cb/Req/ReqGlue.lean). But two
equal tables have the same number of rows. So the families that are glued with a table of 2^t rows
are among the families of the segment whose tables have 2^t rows, and these can be counted. No two
tables are compared.

Main names:
  `v_glued_byT`: generic: if at most c families of keys of a segment have tables of 2^t rows, each
    on at most V variables, a glued family of keys with a table of 2^t rows has at most
    ⌈log₂ c⌉ + V variables.
  `idn_glued_le`, `tab_glued`: see their statements.
The figures, by kind: Cm/TargetPartNumKeys.lean.

Limits: these are upper bounds. If tables of 2^16 rows differ, as they do by reading (range, clamp,
function tables), fewer families are glued and the numbers are smaller.
No number here is a security level. This file says nothing on the lookups themselves.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegNums

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Finset

/-! ## Generic -/

section Gen
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

theorem v_glued_byT (S : SegSpec X F E) {t c V : ℕ}
    (hc : (S.keys.filter fun k => decide (k.2.T = t)).length ≤ c)
    (hV : ∀ k ∈ S.keys, k.2.T = t → k.1.v ≤ V) :
    ∀ q ∈ S.glued.keys, q.2.T = t → q.1.v ≤ Nat.clog 2 c + V := by
  classical
  intro q hq ht
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 hq
  have ht' : T.T = t := ht
  refine (Req.glueN_le X E _ V fun f hf => ?_).trans
    (Nat.add_le_add_right (Nat.clog_mono_right 2 ?_) V)
  · obtain ⟨k, hk2, rfl⟩ := List.mem_map.1 hf
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hk2
    exact hV k h1 (by rw [of_decide_eq_true h2]; exact ht')
  · rw [List.length_map]
    refine le_trans (List.Sublist.length_le (List.monotone_filter_right S.keys fun k hk => ?_)) hc
    exact decide_eq_true (by rw [of_decide_eq_true hk]; exact ht')

theorem idn_glued_le (S : SegSpec X F E) {c V : ℕ}
    (hc : S.idn.length ≤ c) (hV : ∀ f ∈ S.idn, f.v ≤ V) :
    ∀ f ∈ S.glued.idn, f.v ≤ Nat.clog 2 c + V := by
  intro f hf
  obtain rfl := List.mem_singleton.1 hf
  exact (Req.glueN_le X E S.idn V hV).trans (Nat.add_le_add_right (Nat.clog_mono_right 2 hc) V)

/-- the tables of the glued segment are tables of the segment -/
theorem tab_glued (S : SegSpec X F E) :
    ∀ q ∈ S.glued.keys, ∃ k ∈ S.keys, q.2 = k.2 := fun q hq => by
  obtain ⟨k, hk, e⟩ :=
    List.mem_map.1 (((Cb.glued_counts X F E S).2.2 q.2).1 (List.mem_map_of_mem hq))
  exact ⟨k, hk, e.symm⟩

end Gen

end Cm.Seg
