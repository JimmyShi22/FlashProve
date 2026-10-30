-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Files.lean: a key file and a proof file as interactive oracle reductions to the
trivial statement, from the verifier program's own blocks: the rounds by their dry runs, the
decision by their runs on views. Definitions, and the law that the tests on the rounds fail closed.

OnBytes/Maker/Whole.lean makes a reduction from the data of a file's three chains and a run on three
views. OnBytes/Three/Data.lean makes such data from the rounds that three dry runs state (`dry3`,
`Whole.of`). OnBytes/Maker/Decide3.lean lays the program's three decisions on a file behind each
other as such a run, behind tests that the words of the key's seeds and of the views' field elements
are below the prime.
This file puts the three together.

  `dryKey`, `dryProof`: the three lists of rounds that the dry runs of a file's blocks state, at one
    key of the table (and, for a proof file, at one first block).
  `wholeAt`: the plain data of these rounds; of three empty lists where a dry run has failed.
  `okAt`: the tests on these rounds: the dry runs have come home; `Whole.fits` at two roots a
    message; `storedFit`; `countsFit`; `WholeD.workFit`; `WholeD.depthFit`; `WholeD.runFit`
    (OnBytes/Maker/WholeOf.lean); `someFit`: the first chain has a round beside its last, the third
    has a round; `rowFitAt` (OnBytes/Maker/RowFit.lean).
  `OkParts`, `okAt_parts`: what a yes of the tests says, test by test. `someFit_iff`.
  `dataAt`: the data at which a file's reduction stands: `wholeAt` where the tests pass, the data of
    three empty lists where they do not. So what `workFit`, `depthFit`, `runFit` and `rowFitAt` ask
    holds of the data whatever the verdict is. What `Whole.fits` and `someFit` ask does not hold of
    three empty lists.
  `WholeD.workFit_iff`, `dataAt_work`: no round of these data has more than 64 bits of work.
  `WholeD.depthFit_iff`, `dataAt_depth`: no tree of these data is deeper than 63.
  `WholeD.runFit_iff`, `dataAt_run`: no tree of these data bears the mark "stored".
  `dataAt_rowFit`: these data meet `RowFit`.
  `dataAt_of_ok`, `dataAt_of_not`: which data they are.
  `keyIORAt`, `proofIORAt`: the reductions at any plain data W and any verdict ok of tests: the run
    is "ok, the tests on the key's and the views' words, and the program's three decisions".
  `keyIOR`: a key file. The instance is the stored table's record. `key` says how a record is
    written as the program's key of the table (`TableKey`, OnBytes/Iop/Foldeq.lean). rec₀: the
    record at whose key the dry runs are made.
  `proofIOR`: a proof file. The instance is a pair: what is claimed, and the record. `block` gives
    the first chain's block at what is claimed. z₀: the instance at which the dry runs are made.
  `keyAnn`, `proofAnn`: the annotations of their shapes.
  `keyIORAt_guard`, `proofIORAt_guard`, `keyIOR_guard`, `proofIOR_guard`: where the verifier says
    yes, the tests have passed. So a description whose tests fail accepts nothing.

Owed by the caller.
  An `IOR` has one shape for all instances, and here it is the shape of the dry runs AT rec₀ | z₀.
  The tests speak of these rounds. That the dry runs at another instance state the same rounds is
  not shown here. What the run on the views says at an instance whose dry runs state other rounds is
  not shown here either: a run on a view reads neither a round's kind nor its roots
  (OnBytes/Iop/Ground.lean, `Blk.close`, `Blk.recvRoot`). For a key file
  OnBytes/Maker/FilesFree.lean shows that the rounds are the same at keys that
  are alike. a: the stored table's depth; `storedFit` compares it with the rounds'. C: the choice of
  the types of verifier messages (Run/PlanQTypes.lean, `CK`). The bits of work are those of the
  rounds' entries, whatever C is. A round's verifier message is C's type at the round's entry and
  kind: that its draws have the entry's ranges is owed of C. TF, TJ, T3 with tF, tJ, t3: what the
  three silent rounds send, and their fixed messages. silent: the test of what they send against the
  instance:
  the record's answers that are sent there are compared with the instance's only if this test does
  it.

To be minded by whoever states something "at the real files". Where `okAt` says no, the reduction
stands at three empty chains and accepts nothing: every statement of the form "whatever it accepts
..." then holds for nothing. No type and no field tells such a value from another. So
`okAt a (dryKey ..) = true` and `okAt a (dryProof ..) = true` belong among the named hypotheses of
such a statement, or are to be evaluated at the parameters meant. This file shows `okAt` true at no
parameters. An evaluation of it by a program, at one key and one request of a configuration, is an
evaluation at these values: no theorem, and nothing on another key, request or configuration.

What is not claimed. What OnBytes/Maker/Decide3.lean's head lists as not said is not said here
either. That any transcript is accepted. That `okAt` says yes at any parameters.


-/
import OnBytes.Maker.WholeOf
import OnBytes.Maker.WholeLaws
import OnBytes.Maker.Decide3
import OnBytes.Maker.RowFit

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ
open OnBytes.Params (Rounds)

/-- The rounds that the dry runs of a key file's three blocks state, at the key `key` of the table.
-/
def dryKey (k : Params.KeyChains) (key : TableKey) : Option (Rounds × Rounds × Rounds) :=
  ((Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime)).bind
    (Three.dry3 (Key.tailPublic k noTable) key)

/-- The same for a proof file, at the first chain's block b. -/
def dryProof (c : Params.ProofChains) (key : TableKey) (b : Blk Proof.FirstEnd) :
    Option (Rounds × Rounds × Rounds) :=
  (b.dryRun (Proof.firstStart c.first)).bind (Three.dry3 (Proof.tailPublic c noTable) key)

/-- The plain data of three lists of rounds; of three empty lists where there are none. -/
def wholeAt (R : Option (Rounds × Rounds × Rounds)) : Three.Whole :=
  match R with
  | some R => Three.Whole.of R.1 R.2.1 R.2.2
  | none => Three.Whole.of [] [] []

/-- The first chain has a round beside its last, and the third chain has a round. -/
def someFit (R : Rounds × Rounds × Rounds) : Bool := decide (2 ≤ R.1.length) && !R.2.2.isEmpty

/-- The tests on three lists of rounds. No where there are none. -/
def okAt (a : ℕ) (R : Option (Rounds × Rounds × Rounds)) : Bool :=
  match R with
  | some R =>
    Three.Whole.fits R.1 R.2.1 R.2.2 2 && storedFit a (wholeAt (some R)) &&
      countsFit a (wholeAt (some R)) && (WholeD.of a (wholeAt (some R))).workFit &&
      (WholeD.of a (wholeAt (some R))).depthFit && (WholeD.of a (wholeAt (some R))).runFit &&
      someFit R && rowFitAt a (wholeAt (some R))
  | none => false

/-- **The data at which a file's reduction stands**: those of the rounds where the tests pass, and
of three empty lists where they do not. -/
def dataAt (a : ℕ) (R : Option (Rounds × Rounds × Rounds)) : Three.Whole :=
  if okAt a R then wholeAt R else Three.Whole.of [] [] []

/-- What a yes of the tests says, test by test. -/
structure OkParts (a : ℕ) (R : Rounds × Rounds × Rounds) : Prop where
  fits : Three.Whole.fits R.1 R.2.1 R.2.2 2 = true
  stored : storedFit a (wholeAt (some R)) = true
  counts : countsFit a (wholeAt (some R)) = true
  work : (WholeD.of a (wholeAt (some R))).workFit = true
  depth : (WholeD.of a (wholeAt (some R))).depthFit = true
  run : (WholeD.of a (wholeAt (some R))).runFit = true
  rounds : someFit R = true
  row : rowFitAt a (wholeAt (some R)) = true

theorem okAt_parts {a : ℕ} {R : Rounds × Rounds × Rounds} (h : okAt a (some R) = true) :
    OkParts a R := by
  simp only [okAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- Where the tests pass, the data are those of the rounds. -/
theorem dataAt_of_ok {a : ℕ} {R : Option (Rounds × Rounds × Rounds)} (h : okAt a R = true) :
    dataAt a R = wholeAt R := if_pos h

/-- Where they do not, the data are those of three empty lists. -/
theorem dataAt_of_not {a : ℕ} {R : Option (Rounds × Rounds × Rounds)} (h : ¬ okAt a R = true) :
    dataAt a R = Three.Whole.of [] [] [] := if_neg h

/-- What the test on the numbers of rounds says. -/
theorem someFit_iff (R : Rounds × Rounds × Rounds) :
    someFit R = true ↔ (R.1.map (·.1)).dropLast ≠ [] ∧ R.2.2.map (·.1) ≠ [] := by
  obtain ⟨R₁, R₂, R₃⟩ := R
  unfold someFit
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff]
  refine and_congr ?_ ?_
  · rw [Ne, ← List.length_eq_zero_iff, List.length_dropLast, List.length_map]
    omega
  · rw [Ne, Ne, List.map_eq_nil_iff]

theorem WholeD.workFit_iff (D : WholeD) :
    D.workFit = true ↔ ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), d.entry.work ≤ 64 := by
  unfold WholeD.workFit
  simp only [List.all_eq_true, decide_eq_true_eq]

/-- **No round of the data has more than 64 bits of work**, whether the tests pass or not. -/
theorem dataAt_work (a : ℕ) (R : Option (Rounds × Rounds × Rounds)) :
    ∀ d ∈ (WholeD.of a (dataAt a R)).ds₁ ++
      ((WholeD.of a (dataAt a R)).ds₂ ++ (WholeD.of a (dataAt a R)).ds₃), d.entry.work ≤ 64 := by
  unfold dataAt
  by_cases h : okAt a R = true
  · rw [if_pos h]
    cases R with
    | none => cases h
    | some R =>
      exact (WholeD.workFit_iff _).1 (okAt_parts h).work
  · rw [if_neg h]
    intro d hd
    cases hd

theorem WholeD.depthFit_iff (D : WholeD) :
    D.depthFit = true ↔ ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), ∀ s ∈ d.trees, s.a ≤ 63 := by
  unfold WholeD.depthFit
  simp only [List.all_eq_true, decide_eq_true_eq]

/-- **No tree of the data is deeper than 63**, whether the tests pass or not: twice its number of
leaves is at most 2 ^ 64. -/
theorem dataAt_depth (a : ℕ) (R : Option (Rounds × Rounds × Rounds)) :
    ∀ d ∈ (WholeD.of a (dataAt a R)).ds₁ ++
      ((WholeD.of a (dataAt a R)).ds₂ ++ (WholeD.of a (dataAt a R)).ds₃),
      ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64 := by
  unfold dataAt
  by_cases h : okAt a R = true
  · rw [if_pos h]
    cases R with
    | none => cases h
    | some R =>
      intro d hd s hs
      have h63 : s.a ≤ 63 := (WholeD.depthFit_iff _).1 (okAt_parts h).depth d hd s hs
      have h2 : 2 ^ s.a ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) h63
      calc 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 63 + 2 ^ 63 := Nat.add_le_add h2 h2
        _ = 2 ^ 64 := by norm_num
  · rw [if_neg h]
    intro d hd
    cases hd

theorem WholeD.runFit_iff (D : WholeD) :
    D.runFit = true ↔ ∀ d ∈ D.ds₁ ++ (D.ds₂ ++ D.ds₃), ∀ s ∈ d.trees, s.stored = false := by
  unfold WholeD.runFit
  simp only [List.all_eq_true, Bool.not_eq_true']

/-- **No tree of the data bears the mark "stored"**, whether the tests pass or not. -/
theorem dataAt_run (a : ℕ) (R : Option (Rounds × Rounds × Rounds)) :
    ∀ d ∈ (WholeD.of a (dataAt a R)).ds₁ ++
      ((WholeD.of a (dataAt a R)).ds₂ ++ (WholeD.of a (dataAt a R)).ds₃),
      ∀ s ∈ d.trees, s.stored = false := by
  unfold dataAt
  by_cases h : okAt a R = true
  · rw [if_pos h]
    cases R with
    | none => cases h
    | some R => exact (WholeD.runFit_iff _).1 (okAt_parts h).run
  · rw [if_neg h]
    intro d hd
    cases hd

/-- **The data and the two lists of trees left that are computed from them meet `RowFit`**, whether
the tests pass or not. -/
theorem dataAt_rowFit (a : ℕ) (R : Option (Rounds × Rounds × Rounds)) :
    RowFit (WholeD.of a (dataAt a R)) (leftAfter (dataAt a R) 0) (leftAfter (dataAt a R) 1) := by
  by_cases h : okAt a R = true
  · rw [dataAt_of_ok h]
    cases R with
    | none => cases h
    | some R => exact rowFit_of_rowFitAt (okAt_parts h).row
  · rw [dataAt_of_not h]
    exact rowFit_of_rowFitAt (rowFitAt_empty a)

section
variable (C : CK) (a : ℕ) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- A key file at any plain data W and any verdict ok of tests. -/
def keyIORAt {R : Type} (W : Three.Whole) (ok : Bool) (silent : R → TF → TJ → T3 → Bool)
    (key : R → TableKey) (k : Params.KeyChains) : IOR R (oneExternalString (2 ^ a) SgX) Unit extNone :=
  reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent fun (rec : R) v₁ v₂ v₃ =>
    ok && decideKey k (key rec) W.t₁ W.t₂ v₁ v₂ v₃

/-- A proof file at any plain data W and any verdict ok of tests. -/
def proofIORAt {X R : Type} (W : Three.Whole) (ok : Bool) (silent : X × R → TF → TJ → T3 → Bool)
    (key : R → TableKey) (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) :
    IOR (X × R) (oneExternalString (2 ^ a) SgX) Unit extNone :=
  reductionOfWholeFile C (WholeD.of a W) tF tJ t3 silent fun (z : X × R) v₁ v₂ v₃ =>
    ok && decideProof c (key z.2) (block z.1) W.t₁ W.t₂ v₁ v₂ v₃

/-- **A key file as data**: the instance is the record. -/
def keyIOR {R : Type} (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (rec₀ : R) : IOR R (oneExternalString (2 ^ a) SgX) Unit extNone :=
  keyIORAt C a tF tJ t3 (dataAt a (dryKey k (key rec₀))) (okAt a (dryKey k (key rec₀))) silent key k

/-- The annotation of its shape. -/
def keyAnn {R : Type} (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (rec₀ : R) : RoundSplits (keyIOR C a tF tJ t3 silent key k rec₀).shape :=
  (chainsOf C (WholeD.of a (dataAt a (dryKey k (key rec₀)))) tF tJ t3).ann

/-- **A proof file as data**: the instance is what is claimed, and the record. -/
def proofIOR {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (z₀ : X × R) :
    IOR (X × R) (oneExternalString (2 ^ a) SgX) Unit extNone :=
  proofIORAt C a tF tJ t3 (dataAt a (dryProof c (key z₀.2) (block z₀.1)))
    (okAt a (dryProof c (key z₀.2) (block z₀.1))) silent key c block

/-- The annotation of its shape. -/
def proofAnn {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (z₀ : X × R) :
    RoundSplits (proofIOR C a tF tJ t3 silent key c block z₀).shape :=
  (chainsOf C (WholeD.of a (dataAt a (dryProof c (key z₀.2) (block z₀.1)))) tF tJ t3).ann

/-- Where the verifier of a key file says yes, the verdict ok is yes. -/
theorem keyIORAt_guard {R : Type} (W : Three.Whole) (ok : Bool) (silent : R → TF → TJ → T3 → Bool)
    (key : R → TableKey) (k : Params.KeyChains) (x : R) (y : (oneExternalString (2 ^ a) SgX).Str)
    (τ : Tr (keyIORAt C a tF tJ t3 W ok silent key k).shape)
    (h : ((keyIORAt C a tF tJ t3 W ok silent key k).out x y τ).isSome = true) : ok = true := by
  obtain ⟨_, _, _, hr⟩ := wholeIOR_out_run C (WholeD.of a W) tF tJ t3 silent
    (fun (rec : R) v₁ v₂ v₃ => ok && decideKey k (key rec) W.t₁ W.t₂ v₁ v₂ v₃) x y τ h
  exact (Bool.and_eq_true_iff.1 hr).1

/-- The same for a proof file. -/
theorem proofIORAt_guard {X R : Type} (W : Three.Whole) (ok : Bool)
    (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey) (c : Params.ProofChains)
    (block : X → Blk Proof.FirstEnd) (x : X × R) (y : (oneExternalString (2 ^ a) SgX).Str)
    (τ : Tr (proofIORAt C a tF tJ t3 W ok silent key c block).shape)
    (h : ((proofIORAt C a tF tJ t3 W ok silent key c block).out x y τ).isSome = true) :
    ok = true := by
  obtain ⟨_, _, _, hr⟩ := wholeIOR_out_run C (WholeD.of a W) tF tJ t3 silent
    (fun (z : X × R) v₁ v₂ v₃ =>
      ok && decideProof c (key z.2) (block z.1) W.t₁ W.t₂ v₁ v₂ v₃) x y τ h
  exact (Bool.and_eq_true_iff.1 hr).1

/-- **The tests fail closed**: where the verifier of a key file says yes, they have passed. -/
theorem keyIOR_guard {R : Type} (silent : R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (k : Params.KeyChains) (rec₀ x : R) (y : (oneExternalString (2 ^ a) SgX).Str)
    (τ : Tr (keyIOR C a tF tJ t3 silent key k rec₀).shape)
    (h : ((keyIOR C a tF tJ t3 silent key k rec₀).out x y τ).isSome = true) :
    okAt a (dryKey k (key rec₀)) = true :=
  keyIORAt_guard C a tF tJ t3 _ _ silent key k x y τ h

/-- The same for a proof file. -/
theorem proofIOR_guard {X R : Type} (silent : X × R → TF → TJ → T3 → Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) (z₀ x : X × R)
    (y : (oneExternalString (2 ^ a) SgX).Str) (τ : Tr (proofIOR C a tF tJ t3 silent key c block z₀).shape)
    (h : ((proofIOR C a tF tJ t3 silent key c block z₀).out x y τ).isSome = true) :
    okAt a (dryProof c (key z₀.2) (block z₀.1)) = true :=
  proofIORAt_guard C a tF tJ t3 _ _ silent key c block x y τ h

end

end OnBytes.Maker
