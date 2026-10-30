-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryWith.lean: `Entry.check` stated through what `Entry.read` returns.

`Entry.check` (OnBytes/Entry/File.lean) reads the parameter bytes, calls `Entry.read`, and runs the
block's decision on the view of the chain that `Entry.read` returned. This file says so as a
theorem, so that a statement on a yes of the check can speak of that chain itself and needs no byte
offset. OnBytes/Tie/EntryWithRec.lean writes the check again (`checkWithR`) with the chain's reader
`rd` and the seeds' function `sd` as parameters. By its text `checkWithR` calls no hash but through
these two; that is no theorem.
Main definition: `EntryPlace`. Main theorems.
- `entry_check_iff`: `Entry.check` says yes and returns `further` exactly if the parameter bytes are
  read as some q, `Entry.read` returns some r whose further table is `further`, and the decision of
  r's block says yes on the view of r's chain.
- `entrySpec_roots`: two facts on the description that `entrySpec` gives, whichever function reads
  the chain: its statement, and where the stored tables' roots stand in it.
- `entry_read_compiled`: of what `Entry.read` returned, given the decision's yes and the three
  hypotheses of `entry_check_compiled`: the compiled verifier (a term of the library's Lean theory,
  not machine code) accepts `r.chain.out`. No byte offset stands in the statement.
What is not claimed. Nothing on soundness and no probability: of a yes of the compiled verifier
nothing is proved here. For a general `rd` nothing ties the view of what it returns to its output,
or the place where it ended to the bytes. Nothing is said of the first table, which the caller hands
in. The program is the Lean port built from OnBytes/; nothing here is said of the C++ program
`cp_verify` or of how its results compare. For proofs only; the program does not import this file.
`readWithR` and `checkWithR` are no part of the program, which runs `Entry.check`.
-/
import OnBytes.Tie.EntryFile

set_option autoImplicit false

namespace OnBytes.Tie

/-- `Entry.check` through what `Entry.read` returns. The check says yes and returns `further`
exactly if: the parameter bytes are read as some q; `Entry.read` under q returns some r; r's further
table is `further`; and the decision of r's block, started as `Entry.start q` says, is true on the
view of r's chain. -/
theorem entry_check_iff (params : ByteArray) (first further : Params.TableName)
    (file : ByteArray) :
    Entry.check params first file = .ok further ↔
      ∃ (q : Params.Link) (r : Entry.EntryRead),
        Params.Link.read params = some q ∧ Entry.read q first file = .ok r ∧
        r.further = further ∧ r.block.decides (Entry.start q) r.chain.view = true := by
  constructor
  · intro h
    unfold Entry.check at h
    split at h
    · cases h
    · rename_i q hq
      split at h
      · cases h
      · rename_i r hr
        split at h
        · rename_i hj
          refine ⟨q, r, hq, hr, by injection h, ?_⟩
          rw [Blk.decides_iff_runOn]
          unfold Proof.judge at hj
          split at hj
          · rename_i a ha
            exact ha
          · cases hj
        · cases h
  · rintro ⟨q, r, hq, hr, hf, hd⟩
    rw [Blk.decides_iff_runOn] at hd
    unfold Entry.check
    rw [hq]
    dsimp only
    rw [hr]
    dsimp only
    unfold Proof.judge
    rw [hd]
    dsimp only
    rw [hf]

/-- Two facts on the description S that `entrySpec` gives, whichever function reads the chain. Its
statement is `entryStatement` at the two tables' roots. Given `withinX S` and a statement of fewer
than 2^64 bytes, each stored table that S lists has its root in the statement's item 0 or 1: the
first table's root or the further table's. -/
theorem entrySpec_roots (q : Params.Link) (first further : Params.TableName) (block : Blk Unit)
    (S : Fmt.SpecX) (hS : entrySpec q first further = some (block, S)) :
    S.base.statement = entryStatement first further first.root further.root ∧
      (withinX S = true → S.base.statement.size < 2 ^ 64 →
        ∀ t ∈ S.stored.flatten, Fmt.itemRoot S.base.statement t.item
          = some (if t.item == 1 then further.root else first.root)) := by
  have hstm : S.base.statement = entryStatement first further first.root further.root := by
    unfold entrySpec at hS
    split at hS
    · rename_i k0 k1 _ _
      obtain ⟨S', hS', he⟩ := Option.map_eq_some_iff.1 hS
      obtain ⟨rs, _, hd⟩ := Option.bind_eq_some_iff.1 hS'
      have e1 : S' = S := congrArg (·.2) he
      subst e1
      rw [Params.Given.describe_eq hd]
      rfl
    · cases hS
  refine ⟨hstm, fun hw hB t ht => ?_⟩
  have hsz : (Params.tableValue first).size ≤ S.base.statement.size ∧
      (Params.tableValue further).size ≤ S.base.statement.size := by
    rw [hstm]
    unfold entryStatement Params.Link.statement Fmt.tableItem Fmt.item Params.tableValue
    simp only [ByteArray.size_append]
    constructor <;> omega
  have hv0 : (Params.tableValue first).size < 2 ^ 64 := by omega
  have hv1 : (Params.tableValue further).size < 2 ^ 64 := by omega
  have hr0 : Fmt.itemRoot S.base.statement 0 = some first.root := by
    rw [hstm]
    exact Params.Link.statement_root0 first further hv0 hv1
  have hr1 : Fmt.itemRoot S.base.statement 1 = some further.root := by
    rw [hstm]
    exact Params.Link.statement_root1 first further hv0 hv1
  have hle : t.item ≤ 1 := by
    unfold withinX at hw
    simp only [Bool.and_eq_true] at hw
    have hk := hw.1.1
    unfold Run.PQ.XD.ok at hk
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
    exact (hk.2 t ht).2
  by_cases h1 : t.item = 1
  · rw [h1]
    exact hr1
  · have h00 : t.item = 0 := by omega
    rw [h00]
    exact hr0

/-- The tie for an entry file, stated of what `Entry.read` returned. If `Entry.read` returns r and
the decision of r's block is true on the view of r's chain, then `entrySpec` gives r's block and a
description S; and given `withinX S`, `smallFX S file` and a first root of 32 bytes, the compiled
verifier (a term of the library's Lean theory, not machine code) accepts `r.chain.out`, under the
first table's root and the root of r's further table. No byte offset stands in the statement: the
chain is the one that `Entry.read` returned and on whose view `Entry.check` decides
(`entry_check_iff`). Of the compiled verifier's yes nothing is proved here. -/
theorem entry_read_compiled (q : Params.Link) (first : Params.TableName) (file : ByteArray)
    (r : Entry.EntryRead) (hr : Entry.read q first file = .ok r)
    (hdec : r.block.decides (Entry.start q) r.chain.view = true) :
    ∃ S : Fmt.SpecX, entrySpec q first r.further = some (r.block, S) ∧
      (withinX S = true → smallFX S file = true → first.root.size = 32 →
        CompiledAcceptsX S (entryStatement first r.further) (r.block.decides (Entry.start q))
          first.root r.further.root r.chain.out) := by
  obtain ⟨j, S, s', hS, hrd, h32⟩ := entry_read_spec q first file r hr
  refine ⟨S, hS, fun hw hsm h0 => ?_⟩
  obtain ⟨hstm, hroot⟩ := entrySpec_roots q first r.further r.block S hS
  have hB : S.base.statement.size + 88 ≤ 2 ^ 32 - 144 := by
    have hsm' := hsm
    unfold smallFX Run.smallF Run.smallB at hsm'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hsm'
    exact hsm'.1.1.1.1.1.2
  exact readInX_compiled S _ _ first.root r.further.root h0 h32 hw hstm
    (hroot hw (by omega)) Session.start file j hsm r.chain s' hrd hdec

/-- Where the chain of an entry file begins, and under what it is read: the further table that the
file holds, the block, the chain's description, and the byte at which the chain begins. -/
structure EntryPlace where
  /-- the table that the file holds before its chain -/
  further : Params.TableName
  /-- the block of the chain -/
  block : Blk Unit
  /-- the chain's description -/
  spec : Fmt.SpecX
  /-- the byte of the file at which the chain begins -/
  byte : Nat

end OnBytes.Tie
