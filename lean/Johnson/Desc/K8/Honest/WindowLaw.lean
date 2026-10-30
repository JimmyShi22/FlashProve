-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/WindowLaw.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: how often a
combination leaves its window. A FEW DEFINITIONS, AND STATEMENTS OF LEMMAS, each as a definition of
a proposition; no proof stands here: four are proved in
Johnson/Desc/K8/Honest/WindowLawProofs.lean, four in Johnson/Desc/K8/Honest/WindowLawBound.lean.
LEMMAS ON ONE EVENT AT WHICH AN HONEST PROVER CANNOT GO ON; NONE OF THE LIBRARY's GOALS. NOTHING IS
CLAIMED ON COMPLETENESS, SOUNDNESS OR HIDING.

`leaves` (Johnson/Desc/K8/Honest/Window.lean) is a program on the drawn sequence as the verifier
reads it. The library has the like event on a typed matrix of coefficients, two uniform bits each
(`Prob.Win`, Prob/Window.lean), with a proved bound on its probability (`Prob.pr_win_le`), and it
has the sequence of matrix entries that a typed matrix stands for, in the verifier's order
(`listOf`, OnBytes/Tie/Pv/Tail/Draw.lean). The statements tie the program to that event and carry
the bound to the verifier messages of a written round.

  `FitsRows p s`      the place's numbers are the typed side's: matrices, columns, combinations
                       (`Fits`, Johnson/Desc/First/K8/Law.lean), and rows of cells
  `sizeOfPar p`       sizes with the place's numbers: a member of `FitsRows` at every place
  `cellsOf cell`      the cells at the typed side's indices
  `winAt cell β`      the library's window event at these cells and the window 2^17
  `writtenEntries d c`   the sequence of matrix entries that a written verifier message c of the
                       round d gives
  `windowTerm n₂`     one combination's term: 2 exp (-(2^17)^2 / (n₂ * 128^2))
  `windowBound s n₂`  (rows of cells of all matrices) * tau * that term
  `Spec.leaves_none_iff`   AT EVERY SEQUENCE: the program finds nothing just if every combination of
                       the place lies in its window
  `Spec.listOf_onto`  every sequence of the right length with entries -1, 0, 1 is that of some typed
                       matrix
  `Spec.comb_eq`      a combination, computed on the sequence of a typed matrix, is the library's
  `Spec.leaves_iff`   THE EVENT: at the sequence of a typed matrix the program finds a combination
                       outside the window just if the library's window event holds
  `Spec.pr_leaves_le` THE BOUND, over a uniform typed matrix: if the cells pass `cellsSmall`, 0 < n₂
                       and no matrix has more than n₂ columns
  `Spec.leaves_below` a lemma on the way: the number of such typed matrices, times the sampler's
                       weight, against the number of a written round's verifier messages
                       (`RoundBelow`, OnBytes/Slice/ManyErr.lean)
  `Spec.pr_written_le`  THE BOUND AT A WRITTEN ROUND that draws the matrix's entries alone, without
                       work (and whose entry in the plan states positions of at most 64 bits: the
                       library's lemmas ask it; such a round draws no position): over a uniform
                       verifier message of that round, of the event that the program finds such a
                       combination in the sequence THAT THE MESSAGE ITSELF GIVES
  `Spec.term_le`      THE NUMBER: with at least 1 and at most 2^13 columns one combination's term
                       is at most 2^-183.66

THE MEASURE. The bounds are over a uniform typed matrix, in which an entry is 0 at two of four
values and 1 and -1 at one each, and over a uniform written verifier message (the proof spends the
sampler's two laws: at most w messages give one typed matrix, and w times the number of typed
matrices is at most the number of messages).
THEY ARE NOT COUNTS OF DRAWN SEQUENCES: `listOf` is not one to one (4^n typed matrices stand for 3^n
sequences), and among the sequences, each counted once, an entry is 0 at one of three: there nothing
is proved.
Limits. That the place's numbers are the typed side's (`FitsRows`) is a premise of `Spec.comb_eq`,
`Spec.leaves_iff`, `Spec.pr_leaves_le`, `Spec.leaves_below` and `Spec.pr_written_le`; it has a
member at every place (`sizeOfPar`, which with its lemma `fitsRows_sizeOfPar` follows `sizeAt` and
`fits_sizeAt` of Johnson/Desc/First/K8/Law.lean, with the rows added). That the cells pass
`cellsSmall` is a premise: nothing here says that an honest prover's cells do. It is asked at every
entry of the shape of every matrix of the place's list: the matrices that hold the bits of a
lookup's multiplicities, and the cells that no other claim reads, among them. One round of one
request: no sum over segments or requests. That a proof file's chain has such a written round at the
kind's place is not said here. The bound has one number of columns for all matrices; matrix by
matrix, each at its own number of columns, in two lemmas that are not joined:
Johnson/Desc/K8/Honest/WindowLawEach.lean (`pr_leaves_sum`, `pr_winOf_le`).
Words. A written verifier message, and w: `RoundBelow` (OnBytes/Slice/ManyErr.lean). Work:
lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.Window
import Johnson.Desc.First.K8.Law
import OnBytes.Slice.ManyErr
import Prob.Window

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open Cb.Pv.Tail OnBytes.Tie.Pv.Tail OnBytes.Slice Iop
open OnBytes.Model (lbz)
open scoped ENNReal

/-- The place's numbers are the typed side's. -/
structure FitsRows (p : Par) (s : Size) : Prop where
  fits : Fits p s
  m : ∀ i, i < p.ks.length → s.m i = p.ms.getD i 0

/-- Sizes with the place's numbers; the numbers that no statement here reads are laid as 0. -/
def sizeOfPar (p : Par) : Size :=
  { NM := p.ks.length, m := fun i => p.ms.getD i 0, k := fun i => p.ks.getD i 0, nr := fun _ => 0
    tau := p.tau, rad := 0, lo := 0, hi := 0, beta := 0 }

/-- The cells at the typed side's indices. -/
def cellsOf {s : Size} (cell : CellsAt) :
    ∀ μ : Fin s.NM, Fin (s.m μ) → Fin (s.k μ) → ℤ :=
  fun μ i c => cell μ.val i.val c.val

/-- The library's window event at the place's cells and the window of this test. -/
def winAt {s : Size} (cell : CellsAt) (β : Dr s) : Prop :=
  Prob.Win (Mx := Fin s.NM) (U := Fin s.tau) (I := fun μ => Fin (s.m μ))
    (J := fun μ => Fin (s.k μ)) (cellsOf cell) ((2 : ℤ) ^ lbz) β

/-- One combination's term at n₂ columns. -/
noncomputable def windowTerm (n₂ : ℕ) : ℝ :=
  2 * Real.exp (-((((2 : ℤ) ^ lbz : ℤ) : ℝ) ^ 2 / (n₂ * ((128 : ℤ) : ℝ) ^ 2)))

/-- The bound: the number of all combinations, times one combination's term at n₂ columns. -/
noncomputable def windowBound (s : Size) (n₂ : ℕ) : ℝ≥0∞ :=
  (((∑ μ : Fin s.NM, s.m μ) * s.tau : ℕ) : ℝ≥0∞) * ENNReal.ofReal (windowTerm n₂)

/-- The sequence of matrix entries that a written verifier message gives. -/
def writtenEntries (d : Run.PQ.RD) (c : (wRound d).Chal) : Array Int :=
  ((Run.ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)).trits.toArray

namespace Spec

/-- States: at every sequence the program finds nothing just if every combination of the place lies
in its window. -/
def leaves_none_iff : Prop :=
  ∀ (p : Par) (cell : CellsAt) (drawn : Array Int),
    leaves p cell drawn = none ↔
      ∀ mu, mu < p.ks.length → ∀ i, i < p.ms.getD mu 0 → ∀ u, u < p.tau →
        inWindow (comb p cell drawn mu i u) = true

/-- States: every sequence of the right length with entries -1, 0, 1 is that of a typed matrix. -/
def listOf_onto : Prop :=
  ∀ (s : Size) (l : List Int), l.length = s.columns * s.tau →
    (∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1) → ∃ β : Dr s, l.toArray = listOf β

/-- States: a combination on the sequence of a typed matrix is the library's combination. -/
def comb_eq : Prop :=
  ∀ (p : Par) (s : Size) (cell : CellsAt) (β : Dr s) (μ : Fin s.NM) (i : Fin (s.m μ))
      (u : Fin s.tau),
    FitsRows p s →
    comb p cell (listOf β) μ.val i.val u.val = Prob.comb (cellsOf cell μ i) (β μ u)

/-- States: the program finds a combination outside its window just if the library's window event
holds. -/
def leaves_iff : Prop :=
  ∀ (p : Par) (s : Size) (cell : CellsAt) (β : Dr s),
    FitsRows p s → ((leaves p cell (listOf β)).isSome = true ↔ winAt cell β)

/-- States the bound over a uniform typed matrix, for cells that pass `cellsSmall`. -/
def pr_leaves_le : Prop :=
  ∀ (p : Par) (s : Size) (cell : CellsAt) (n₂ : ℕ),
    FitsRows p s → 0 < n₂ → (∀ μ : Fin s.NM, s.k μ ≤ n₂) → cellsSmall p cell = true →
    Prob.pr (Prob.unif (Dr s)) {β | (leaves p cell (listOf β)).isSome = true} ≤ windowBound s n₂

/-- States a lemma on the way: the typed matrices at which the program finds such a combination,
times the sampler's weight, against the number of the round's written verifier messages. -/
def leaves_below : Prop :=
  ∀ (p : Par) (s : Size) (cell : CellsAt) (n₂ : ℕ) (d : Run.PQ.RD),
    FitsRows p s → 0 < n₂ → (∀ μ : Fin s.NM, s.k μ ≤ n₂) → cellsSmall p cell = true →
    OnlyTrits d (s.columns * s.tau) → d.entry.work = 0 → d.entry.logN ≤ 64 →
    RoundBelow (Prob.cnt fun β : Dr s => (leaves p cell (listOf β)).isSome = true) d
      (windowBound s n₂)

/-- States the bound, for cells that pass `cellsSmall`, at a written round that draws the matrix's
entries alone, without work, and whose entry in the plan states positions of at most 64 bits: over a
uniform verifier message of the round, of the event at the sequence that the message itself gives.
-/
def pr_written_le : Prop :=
  ∀ (p : Par) (s : Size) (cell : CellsAt) (n₂ : ℕ) (d : Run.PQ.RD),
    FitsRows p s → 0 < n₂ → (∀ μ : Fin s.NM, s.k μ ≤ n₂) → cellsSmall p cell = true →
    OnlyTrits d (s.columns * s.tau) → d.entry.work = 0 → d.entry.logN ≤ 64 →
    Prob.pr (Prob.unif (wRound d).Chal) {c | (leaves p cell (writtenEntries d c)).isSome = true} ≤
      windowBound s n₂

/-- States the number: with at least 1 and at most 2^13 columns one combination's term is at most
2^-183.66. -/
def term_le : Prop :=
  ∀ n₂ : ℕ, 0 < n₂ → n₂ ≤ 2 ^ 13 → windowTerm n₂ ≤ (2 : ℝ) ^ (-(183.66 : ℝ))

end Spec

end VerifiableInference.Desc.First.K8.Honest
