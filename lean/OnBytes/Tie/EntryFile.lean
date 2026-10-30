-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryFile.lean: the program's check of an entry file, and the compiled verifier of the
library's theory.

`Entry.check` is the function that the program runs on an entry file. This file proves: if it says
yes, then the reader `readIn` reads a chain from some byte offset j of the file, under the
description that `entrySpec` gives, and the compiled verifier accepts what was read there
(`CompiledAcceptsX`), under the first table's root and the root of the table that the check returns.
That statement does not name j, so j is not shown to be the offset that `Entry.check` used. Of
`Entry.read`, which the check calls, `entry_read_spec` says that the block and the chain that it
returns are the block that `entrySpec` gives and what `readIn` reads under that description, also
from an offset that is not named. The chain's statement is built from the two roots
(`entryStatement`), and its first two items are proved to hold them.

Two tests on that description and on the file's size are hypotheses: `withinX` and `smallFX`. Both
can be evaluated. The third hypothesis is that the first table's root has 32 bytes.

Main definitions: `entrySpec`, `entryStatement`.
Main theorems: `entry_read_spec`, `entry_check_compiled`.
It claims nothing on soundness, and nothing on the first table, which the caller hands in.
-/
import OnBytes.Entry.File
import OnBytes.Iop.GroundLaws
import OnBytes.Params.Laws
import OnBytes.Params.StatementLaws
import OnBytes.Tie.StoredMain

set_option autoImplicit false

namespace OnBytes.Tie
open Run.PQ (View)

/-- The block and the description under which `Entry.read` reads an entry file's chain. -/
def entrySpec (p : Params.Link) (first further : Params.TableName) :
    Option (Blk Unit × Fmt.SpecX) :=
  match tableKey p.given.plan.field p.given.cfg p.link.table first 0,
      tableKey p.given.plan.field p.given.cfg p.link.table further 1 with
  | some k0, some k1 =>
    (((linkVerify p.link k0 k1).rounds (Entry.start p)).bind (p.describe first further)).map
      fun S => (linkVerify p.link k0 k1, S)
  | _, _ => none

/-- The statement of an entry's chain as a function of the two roots. -/
def entryStatement (first further : Params.TableName) (r0 r1 : ByteArray) : ByteArray :=
  Params.Link.statement ⟨r0, first.answers⟩ ⟨r1, further.answers⟩

/-- A root that `readTable` has read has 32 bytes. -/
theorem readTable_root (f : Fmt.Fld) (count : ℕ) (b : ByteArray) (i : ℕ) (t : Params.TableName)
    (j : ℕ) (h : readTable f count b i = .ok (t, j)) : t.root.size = 32 := by
  unfold readTable at h
  split at h
  · cases h
  · rename_i root k hd
    split at h
    · cases h
    · injection h with h'
      have : t = ⟨root, _⟩ := (congrArg (·.1) h').symm
      rw [this]
      exact Run.PQ.tab_digest b i root k hd

/-- What is shown of `Entry.read` if it returns an entry: the block that it returns is the one that
`entrySpec` gives, and the chain that it returns is what the reader `readIn` reads under the
description that `entrySpec` gives, in a session that starts empty, from some byte offset j of the
file. The statement does not name j. The root of the further table that it returns has 32 bytes. -/
theorem entry_read_spec (p : Params.Link) (first : Params.TableName) (file : ByteArray)
    (r : Entry.EntryRead) (hr : Entry.read p first file = .ok r) :
    ∃ (j : ℕ) (S : Fmt.SpecX) (s' : Session),
      entrySpec p first r.further = some (r.block, S) ∧
      readIn S file j Session.start = some (r.chain, s') ∧ r.further.root.size = 32 := by
  unfold Entry.read at hr
  dsimp only at hr
  split at hr
  · simp [Entry.no] at hr
  · rename_i i hi
    split at hr
    · simp [Entry.noParameters] at hr
    · split at hr
      · simp [Entry.no] at hr
      · rename_i further j ht
        split at hr
        · rename_i k0 k1 hk0 hk1
          split at hr
          · simp [Entry.noParameters] at hr
          · rename_i spec hs
            split at hr
            · simp [Entry.no] at hr
            · rename_i rr hrr
              split at hr
              · simp [Entry.no] at hr
              · injection hr with hr'
                subst hr'
                have hrd : ∃ s', readIn spec file j Session.start = some (rr, s') := by
                  unfold Proof.Reading.fromStart Proof.readNamed at hrr
                  cases hq : readIn spec file j Session.start with
                  | none => rw [hq] at hrr; cases hrr
                  | some y =>
                    rw [hq] at hrr
                    injection hrr with hy
                    exact ⟨y.2, by rw [← hy]⟩
                obtain ⟨s', hs'⟩ := hrd
                refine ⟨j, spec, s', ?_, hs', readTable_root _ _ _ _ _ _ ht⟩
                unfold entrySpec
                rw [hk0, hk1]
                dsimp only
                rw [hs]
                rfl
        · simp [Entry.no] at hr

/-- If the check of an entry file says yes, the reader `readIn` reads a chain under the description
that `entrySpec` gives from some byte offset j of the file (not shown to be the one that
`Entry.check` used); given `withinX`, `smallFX` and a first root of 32 bytes, the compiled verifier
accepts what was read there. -/
theorem entry_check_compiled (params : ByteArray) (first further : Params.TableName)
    (file : ByteArray) (h : Entry.check params first file = .ok further) :
    ∃ (p : Params.Link) (block : Blk Unit) (S : Fmt.SpecX) (j : ℕ) (r : ChainRead) (s' : Session),
      Params.Link.read params = some p ∧ entrySpec p first further = some (block, S) ∧
      readIn S file j Session.start = some (r, s') ∧
      (withinX S = true → smallFX S file = true → first.root.size = 32 →
        CompiledAcceptsX S (entryStatement first further) (block.decides (Entry.start p))
          first.root further.root r.out) := by
  unfold Entry.check at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · cases h
    · rename_i r hr
      split at h
      · rename_i hj
        have hdec : r.block.decides (Entry.start p) r.chain.view = true := by
          rw [Blk.decides_iff_runOn]
          unfold Proof.judge at hj
          split at hj
          · rename_i a ha
            exact ha
          · cases hj
        have hfur : r.further = further := by
          injection h
        subst hfur
        obtain ⟨j, S, s', hS, hrd, h32⟩ := entry_read_spec p first file r hr
        refine ⟨p, r.block, S, j, r.chain, s', hp, hS, hrd, fun hw hsm h0 => ?_⟩
        have hstm : S.base.statement
            = entryStatement first r.further first.root r.further.root := by
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
        have hB : S.base.statement.size + 88 ≤ 2 ^ 32 - 144 := by
          have hsm' := hsm
          unfold smallFX Run.smallF Run.smallB at hsm'
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hsm'
          exact hsm'.1.1.1.1.1.2
        have hsz : (Params.tableValue first).size ≤ S.base.statement.size ∧
            (Params.tableValue r.further).size ≤ S.base.statement.size := by
          rw [hstm]
          unfold entryStatement Params.Link.statement Fmt.tableItem Fmt.item Params.tableValue
          simp only [ByteArray.size_append]
          constructor <;> omega
        have hv0 : (Params.tableValue first).size < 2 ^ 64 := by omega
        have hv1 : (Params.tableValue r.further).size < 2 ^ 64 := by omega
        have hr0 : Fmt.itemRoot S.base.statement 0 = some first.root := by
          rw [hstm]
          exact Params.Link.statement_root0 first r.further hv0 hv1
        have hr1 : Fmt.itemRoot S.base.statement 1 = some r.further.root := by
          rw [hstm]
          exact Params.Link.statement_root1 first r.further hv0 hv1
        have hitem : ∀ t ∈ S.stored.flatten, t.item ≤ 1 := by
          intro t ht
          unfold withinX at hw
          simp only [Bool.and_eq_true] at hw
          have hk := hw.1.1
          unfold Run.PQ.XD.ok at hk
          simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
          exact (hk.2 t ht).2
        refine readInX_compiled S _ _ first.root r.further.root h0 h32 hw hstm (fun t ht => ?_)
          Session.start file j hsm r.chain s' hrd hdec
        have hle := hitem t ht
        by_cases h1 : t.item = 1
        · rw [h1]
          exact hr1
        · have h00 : t.item = 0 := by omega
          rw [h00]
          exact hr0
      · cases h

end OnBytes.Tie

#print axioms OnBytes.Tie.entry_check_compiled
