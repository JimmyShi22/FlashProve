-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ValuesAtCommitter.lean

A control: two of the library's five premises on what an honest prover's shared rounds show
(`OwnAnswers`, `OwnColumns`: Johnson/Desc/K14/Honest/ItemsEach.lean) hold, under the head `P5J.AtMg`
and at the shared chain's own parameters there, of the key and the columns that the committer in
Lean of Johnson/Bind/ForProver/ makes. One definition; two theorems.

  `rowsRead`: the committed table's rows before encoding, read.
  `ownAnswers_made`: each answer of the key `oodSh` at an index, coins and a seed is its row's own.
  `ownColumns_made`: where a view's columns for "LOC" are `storedW`'s words, each holds the rows'
      own symbols.

Why. `saysAt_run_U_six` (SaysAtRunU.lean) takes the two as premises at a run's shared view. That
folder proves their content (`fiveFields_inScope`, FiveAt.lean; `tab_inScope`, InScope.lean) and
says in FiveAt.lean's head: "THIS FILE NAMES NO STRUCTURE THAT ASKS THESE FIVE AND BUILDS NO TERM OF
ONE: THAT THEIR FORMS FIT A CALLER IS NOT COMPILED HERE." Here they are compiled at one caller's
letters.

A limit of that folder's, which binds whoever calls these two. FiveAt.lean's head, "A limit on the
coins, before the others", is to be read there, whole. Four of its sentences, to the letter: "UNDER
validAt, AT A FIXED INDEX AND KEY, THE PADS THAT THE ANSWERS READ ARE NO COINS." "BUT: a law that
takes the committer's pads as uniform and independent and ranges over w.rc with w.key a letter under
validAt (the form hw : Vd wr → validIdxAt … wr) would range over one point in the pads: hollow in
them, in silence." "In a safe form the key is never a letter: it is written as the term made of
index, coins and seed." "And no strategy or simulator may branch on validAt: it reads index and
pads." So both theorems here are typed in that form: index, coins and seed come first, the key is
the term made of them, and `validAt` stands in no statement.

Limits.
- No prover is named: that a prover's key is `oodSh` at its own index and coins, that its field
  `stored` is `encW` (then `storedWords_encW`, TabCols.lean), and that a run's columns for "LOC" are
  these words (hV) are not said here.
- H, what an honest prover holds, is a letter but for its rows (hH).
- All limits of FiveAt.lean, InScope.lean and TabCols.lean stand: one committed table; the item 0;
  one direction, from a maker that returns; at the reading `Reading.gl`.
- Under the head, which has members at the goals' two named sets of public files
  (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean). It moves no count. Nothing on
  completeness, on soundness or on what a view shows.
Terms: RunBySpec.lean.
-/
import Johnson.Bind.ForProver.FiveAt
import Johnson.Desc.K14.Honest.ItemsEach
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (rdE GE)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (P14)
open Desc.K14.Honest (Inputs View8 OwnAnswers OwnColumns)
open ProofFile.Honest (Weights TableRand)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- The committed table's rows before encoding, read: the honest side's own text of them
(`ProofFile.Honest.K14.rowsOf`, Johnson/Desc/ProofFile/Honest/K14/Parts.lean) at an index and the stored
tables' pads and encoding randomness, of which the item 0's alone are read. -/
noncomputable def rowsRead (Q : P14) (w₀ : Weights) (rc : ℕ → TableRand) : ℕ → ℕ → GE :=
  fun r j => rdE.val (ProofFile.Honest.K14.rowsOf Q.S w₀ ⟨(rc 0).pad, (rc 0).tail⟩ r j)

/-- **A control: `OwnAnswers` at the committer in Lean.** Under the head: at every index, all coins
and every seed: each answer of the key that Johnson/Bind/ForProver/ makes of these (`oodSh`) is its
row's own, at everything H whose rows are `rowsRead`. The fifth of
`Bind.ForProver.fiveFields_inScope` (FiveAt.lean), called at `validAt_oodSh`: the key is the term
made of index, coins and seed, no letter. -/
theorem ownAnswers_made (h : P5J.AtMg o Z D r₀ Zp Np cF) (w₀ : Weights) (rc : ℕ → TableRand)
    (sd : Bind.ForProver.Seed (Bind.ForProver.shapeOf Zp) × ℕ) (H : Inputs)
    (hH : H.Rw = rowsRead (K1.qAt Zp Np) w₀ rc) :
    OwnAnswers (K1.qAt Zp Np)
      (Bind.ForProver.oodSh (Bind.ForProver.shapeOf Zp) Zp ⟨w₀, rc, sd⟩) H := by
  have k := (Bind.ForProver.fiveFields_inScope h.scope h.laid.pub
    (Desc.K14.beforePointOf Np) (K1.qAt Zp Np) rfl).2.2.2.2
    ⟨w₀, rc, Bind.ForProver.oodSh (Bind.ForProver.shapeOf Zp) Zp ⟨w₀, rc, sd⟩⟩
    (Bind.ForProver.validAt_oodSh _ Zp w₀ rc sd)
  intro x hx r hr
  unfold Desc.K14.Honest.RowAnswer
  rw [hH]
  exact k x hx r hr

/-- **A control: `OwnColumns` at the committer in Lean.** Under the head: at every index and all
coins: where each column that a view holds for "LOC" is the words of that folder's column at its
position (`storedW`, TabCols.lean; the empty column where it has none), each holds the rows' own
symbols, at everything H whose rows are `rowsRead`. `Bind.ForProver.tab_inScope` (InScope.lean),
which is the second of the five with no premise on a key. -/
theorem ownColumns_made (h : P5J.AtMg o Z D r₀ Zp Np cF) (w₀ : Weights) (rc : ℕ → TableRand)
    (H : Inputs) (hH : H.Rw = rowsRead (K1.qAt Zp Np) w₀ rc) (V : View8)
    (hV : ∀ x col, V.cols.lookup x = some col →
      col = (Bind.ForProver.storedW Zp w₀ rc (K1.qAt Zp Np).item x).getD []) :
    OwnColumns (K1.qAt Zp Np) V H := by
  intro x hx col hc q hq
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  rw [hV _ col hc, hH]
  exact Bind.ForProver.tab_inScope h.scope h.laid.pub w₀ rc _
    (Nat.mod_lt _ (Nat.two_pow_pos _)) q hq

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.rowsRead
#print axioms ProofFile.Honest.K12.Light.ownAnswers_made
#print axioms ProofFile.Honest.K12.Light.ownColumns_made
