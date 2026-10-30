-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxShape.lean: the shape of every opening with the mark "stored" in a chain that the
strict reader has read: what `famOf_stoOk` (OnBytes/K/Left/LaxPages.lean) asks of `op.sh`.

Main names:
  `stored_shape`: of a description in order: a stored table's tree has the mark "stored", the number
    0, a width below 2^24, a depth of at most 48, and a lawful length of salts.
  `salt_small`: of a description in order: an eighth of the plan's length of salts is below 2^8.
  `sto_facts`: from the reader's equation `Fmt.readChainX h S seen b i = some (o, j)`, at a
    description D with S's stored tables, all of the depth `D.a`: for every opening op with the
    mark: `op.sh.stored = true`, `op.sh.tree = 0`, `op.sh.a = D.a`, `op.sh.W < 2^24`,
    `2^op.sh.a + 2^op.sh.a ≤ 2^64`.

Hypotheses: the reader's equation; every tree that S opens is the chain's own; the stored tables of
D are S's and have the depth `D.a` (`stored_same`, OnBytes/K/Left/LaxLens.lean, from `D.ok`).

Limits: values alone. Nothing on roots, on leaves' digests, or on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxLens

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie TypedOracleCompiler.Slice
open _root_.Run (HId)

/-- Of a description in order: what a stored table's tree is. -/
theorem stored_shape (S : Fmt.SpecX) (hS : S.ok = true) : ∀ t ∈ S.stored.flatten,
    t.sh.stored = true ∧ t.sh.tree = 0 ∧ t.sh.W < 2 ^ 24 ∧ t.sh.a ≤ 48 ∧
      Fmt.saltLenOK t.salt = true := by
  intro t ht
  obtain ⟨ts, hts, htt⟩ := List.mem_flatten.1 ht
  obtain ⟨r, hr⟩ := exists_zip_left S.base.rounds S.stored ts hts (le_of_eq (specX_len S hS))
  have h := specX_round S hS (r, ts) hr
  unfold Fmt.storedOk at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · have hE : ts = [] := List.isEmpty_iff.1 h
    rw [hE] at htt
    cases htt
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    have k := h.2 t htt
    have hd : Fmt.depthOK t.sh.a = true := k.1.1.1.1.1.1.2
    exact ⟨k.1.1.1.1.1.1.1.1, k.1.1.1.2, k.1.1.1.1.2, of_decide_eq_true hd, k.1.1.2⟩

/-- Of a description in order: an eighth of the plan's length of salts is below 2^8. -/
theorem salt_small {S₀ : Fmt.Spec} (hS : S₀.ok = true) : S₀.plan.salt / 8 < 2 ^ 8 := by
  have h := Fmt.ok_salt hS
  simp only [Fmt.saltLenOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have h64 := h.2
  omega

/-- The shape of an opening with the mark "stored". -/
theorem sto_facts {h : HId} {S : Fmt.SpecX} {seen : Fmt.Seen} {b : ByteArray} {i : ℕ}
    {o : Fmt.ChainOut} {j : ℕ} (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j))
    (hown : ∀ r ∈ S.base.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n)
    {D : TypedOracleCompiler.Run.PQ.XD}
    (hsame : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.salt = D.base.plan.salt)
    (hst : S.stored = D.stored) :
    ∀ op ∈ (opsOf 1 o).filter (fun op => op.sh.stored), op.sh.stored = true ∧ op.sh.tree = 0 ∧
      op.sh.a = D.a ∧ op.sh.W < 2 ^ 24 ∧ 2 ^ op.sh.a + 2 ^ op.sh.a ≤ 2 ^ 64 := by
  intro op hop
  obtain ⟨t, ht, hs, -, -⟩ := lens_sto e hown op hop
  obtain ⟨h1, h2, h3, h4, -⟩ := stored_shape S (readX_trace h S seen b i o j e).1 t ht
  rw [hst] at ht
  rw [hs]
  refine ⟨h1, h2, (hsame t ht).1, h3, ?_⟩
  calc 2 ^ t.sh.a + 2 ^ t.sh.a = 2 ^ (t.sh.a + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by omega)

end OnBytes.K.Left
