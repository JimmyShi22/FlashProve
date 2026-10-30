-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/BlocksBelow.lean: when the one number of blocks of the three files' wiring (`kThree`,
OnBytes/Flat/WireBlocks.lean), and one more, stay below 2 ^ 48; and that the closed parts do.

Statements and proofs; one definition with its test. The tie of the entry file's arm asks of the
wiring's number K of blocks that K + 1 < 2 ^ 48. `kThree` is a maximum over the rounds of three
files: so the bound holds of it exactly if it holds round by round.

Main names:
  `BlocksFit f D`, `blocksFitB f D`, `blocksFitB_iff`: every round of D's three chains asks b blocks
    with b + 1 < 2 ^ 48: as a statement and as a test.
  `blocksT_lt_iff`, `kThree_lt_iff`: kThree f DK ds DP + 1 < 2 ^ 48 ↔ BlocksFit f DK ∧
    (the entry's greatest number) + 1 < 2 ^ 48 ∧ BlocksFit f DP.
  `entryFull_blocks`, `entrySmall_blocks`: the entry's written rounds, at both sizes;
  `descFull_blocks`, `descSmall_blocks`: the entry's description's own number;
  `seedFull_blocks`, `seedSmall_blocks`: the blocks of the record's seed: six closed terms, each
    evaluated by Lean's kernel (`decide +kernel`).

Limits: numbers of blocks alone. `BlocksFit` is shown at no data of a key file or a proof file.
Nothing on a wire's laws, on soundness, on bytes or files.


-/
import OnBytes.Flat.WireBlocks
import OnBytes.Flat.EntryTerm
import OnBytes.Flat.RecordSeed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open OnBytes.Maker OnBytes.Slice _root_.Run _root_.Run.PQ

/-- A fold by the greater stays below a bound that its start and every member's value are below. -/
theorem foldl_max_lt {α : Type} (g : α → ℕ) (B : ℕ) : ∀ (l : List α) (n : ℕ), n < B →
    (∀ d ∈ l, g d < B) → l.foldl (fun a d => max a (g d)) n < B
  | [], _, hn, _ => hn
  | x :: l, n, hn, h =>
    foldl_max_lt g B l (max n (g x)) (max_lt hn (h x List.mem_cons_self))
      fun d hd => h d (List.mem_cons_of_mem _ hd)

/-- Every round of the data asks so few blocks that the number and one more stay below 2 ^ 48. -/
def BlocksFit (f : Fmt.Fld) (D : WholeD) : Prop :=
  ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), (bsRound f d.entry d.kind).b + 1 < 2 ^ 48

/-- The same as a test. -/
def blocksFitB (f : Fmt.Fld) (D : WholeD) : Bool :=
  (D.ds₁ ++ (D.ds₂ ++ D.ds₃)).all fun d => decide ((bsRound f d.entry d.kind).b + 1 < 2 ^ 48)

theorem blocksFitB_iff (f : Fmt.Fld) (D : WholeD) : blocksFitB f D = true ↔ BlocksFit f D := by
  unfold blocksFitB BlocksFit
  simp only [List.all_eq_true, decide_eq_true_eq]

/-- The greatest number of blocks of a file's rounds, and one more, stay below 2 ^ 48 exactly if
every round's do. -/
theorem blocksT_lt_iff (f : Fmt.Fld) (D : WholeD) :
    blocksT f (D.ds₁ ++ (D.ds₂ ++ D.ds₃)) + 1 < 2 ^ 48 ↔ BlocksFit f D := by
  constructor
  · intro h d hd
    have := le_blocksT f _ d hd
    omega
  · intro h
    have h1 : blocksT f (D.ds₁ ++ (D.ds₂ ++ D.ds₃)) < 2 ^ 48 - 1 :=
      foldl_max_lt (fun d : RDT => (bsRound f d.entry d.kind).b) _ _ 0 (by norm_num)
        fun d hd => by
          have := h d hd
          show (bsRound f d.entry d.kind).b < 2 ^ 48 - 1
          omega
    omega

/-- **The one number of blocks of the three files**: it and one more stay below 2 ^ 48 exactly if
that holds of every round of the key file's data, of the entry's and of the proof file's. -/
theorem kThree_lt_iff (f : Fmt.Fld) (DK : WholeD) (ds : List RD) (DP : WholeD) :
    kThree f DK ds DP + 1 < 2 ^ 48 ↔
      BlocksFit f DK ∧ kMax (fun e k => (bsRound f e k).b) ds + 1 < 2 ^ 48 ∧ BlocksFit f DP := by
  rw [← blocksT_lt_iff, ← blocksT_lt_iff]
  unfold kThree
  omega

/-! ## The closed parts, by Lean's kernel -/

theorem entryFull_blocks : kMax (fun e k => (bsRound .two e k).b) frRds + 1 < 2 ^ 48 := by
  decide +kernel

theorem entrySmall_blocks : kMax (fun e k => (bsRound .two e k).b) srRds + 1 < 2 ^ 48 := by
  decide +kernel

theorem descFull_blocks : frD.K + 1 < 2 ^ 48 := by decide +kernel

theorem descSmall_blocks : srD.K + 1 < 2 ^ 48 := by decide +kernel

theorem seedFull_blocks : (seedBS recLg recS).b + 1 < 2 ^ 48 := by decide +kernel

theorem seedSmall_blocks : (seedBS 19 1).b + 1 < 2 ^ 48 := by decide +kernel

end OnBytes.Flat

#print axioms OnBytes.Flat.kThree_lt_iff
#print axioms OnBytes.Flat.entryFull_blocks
#print axioms OnBytes.Flat.entrySmall_blocks
#print axioms OnBytes.Flat.descFull_blocks
#print axioms OnBytes.Flat.descSmall_blocks
#print axioms OnBytes.Flat.seedFull_blocks
#print axioms OnBytes.Flat.seedSmall_blocks
