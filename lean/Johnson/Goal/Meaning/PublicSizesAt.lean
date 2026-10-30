-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/PublicSizesAt.lean: THE REST OF THE PUBLIC PREMISES AT THE KEY FILE AND THE
PROOF FILE: what follows by arithmetic at all public files; what protocolDataWellFormed gives; and ONE DECIDABLE
TEST ON PUBLIC DATA for what, by inspection, no test beneath verify() says.

Why. The printer's laws ask that the data's and the binding trees' numbers fit one word. Of these
Johnson/Goal/Meaning/PublicFitAt.lean has the trees' depths, the stored table's depth and the
numbers of rounds. Three are left that the makers' tests and the frame's test do not give (by
inspection, not proved): a round's number of items and its trees' widths; the two binding trees'
depth and salt; the leaf salt's length. They hang on the planner's values. They are sentences on
public data, and each can be decided by a run.

Main names.
  sum_trees_le, trees_DK, trees_DP   AT ALL PUBLIC FILES: the number of trees of a file is below
    2^64 (at most two a round, fewer than 2^20 rounds a list).
  lists_full   UNDER protocolDataWellFormed: none of the six lists of rounds is empty.
  sizesB, wordsFitAt   THE TEST: every round has fewer than 2^64 items, every tree a width below
    2^64; both binding trees have logLeaves below 64 and salts of at most 64 bytes; the leaf salt
    has at most 64 bytes.
  SizesSay, wordsFitAt_says   what its yes says, clause by clause.

Limits. The widths (widthsK, widthsP) are not spent by PublicS (Johnson/Prover/Print/FormBack.lean),
which has no width: they are, to the letter, the premise hwid of whole_prints
(OnBytes/Prover/Print/Owed.lean). THAT THE TEST SAYS YES AT ANY PUBLIC FILES IS NOT SHOWN HERE: in
scope it follows from protocolDataWellFormed (wordsFitAt_the, Johnson/Goal/Meaning/WordsFitAtThe.lean), whose
acceptance is proved in Lean, in the side library (outside the main library and with that library's
own limits), at the written copy of the full-size example's files under every acceptance policy in
scope (theLive_zAt, AtFullSide/Top/LiveAtPolicies.lean; owner:
Johnson/Goal/Conditions/HomeLast.lean, limit 4). The scope is wider than these files; elsewhere in
it that protocolDataWellFormed accepts stays a premise. The format's own test on a binding tree (Proof.bindingOk,
OnBytes/Proof/Place.lean: at most 48 levels, a salt of 40 to 64 bytes) says more than the test's two
clauses; where we looked in this library it is drawn from a program's yes to a file, not from the
plan (by inspection, not proved). The copy's file is not spoken of.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.PublicFitAt
import OnBytes.Maker.CarrierTyping

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning
open OnBytes.Maker OnBytes.Slice OnBytes.Prover OnBytes.Flat
open FlashProve FlashProve
open LPFD.Full (XF sBG sTG saltG)
open OnBytes.Maker.Carrier (treesIn)

/-! ## By arithmetic, at all public files -/

theorem sum_trees_le : ∀ ds : List RDT, (∀ d ∈ ds, d.trees.length ≤ 2) →
    (ds.map (·.trees.length)).sum ≤ 2 * ds.length
  | [], _ => by simp
  | d :: ds, h => by
    have h1 := h d (List.mem_cons_self ..)
    have h2 := sum_trees_le ds fun e he => h e (List.mem_cons_of_mem _ he)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- The number of trees, from the two facts. -/
theorem trees_lt {D : WholeD} (h : MadeFit D) (l₁ : D.ds₁.length < 2 ^ 20)
    (l₂ : D.ds₂.length < 2 ^ 20) (l₃ : D.ds₃.length < 2 ^ 20) (a : ℕ) :
    treesIn (D.at a) < 2 ^ 64 := by
  have s₁ := sum_trees_le D.ds₁ fun d hd => h.few d (List.mem_append_left _ hd)
  have s₂ := sum_trees_le D.ds₂ fun d hd =>
    h.few d (List.mem_append_right _ (List.mem_append_left _ hd))
  have s₃ := sum_trees_le D.ds₃ fun d hd =>
    h.few d (List.mem_append_right _ (List.mem_append_right _ hd))
  show (D.ds₁.map (·.trees.length)).sum + (D.ds₂.map (·.trees.length)).sum +
    (D.ds₃.map (·.trees.length)).sum < 2 ^ 64
  omega

theorem trees_DK (Z : VerifierAndGoals.PublicFiles) (a : ℕ) : treesIn ((dataAtFiles flashProveData Z).DK.at a) < 2 ^ 64 :=
  trees_lt (madeFit_DK Z) (rounds_built Z).1.1 (rounds_built Z).1.2.1 (rounds_built Z).1.2.2 a

theorem trees_DP (Z : VerifierAndGoals.PublicFiles) (a : ℕ) : treesIn ((dataAtFiles flashProveData Z).DP.at a) < 2 ^ 64 :=
  trees_lt (madeFit_DP Z) (rounds_built Z).2.1 (rounds_built Z).2.2.1 (rounds_built Z).2.2.2 a

/-! ## Under protocolDataWellFormed -/

/-- **Under protocolDataWellFormed none of the six lists of rounds is empty.** -/
theorem lists_full (Z : VerifierAndGoals.PublicFiles) (hl : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ((dataAtFiles flashProveData Z).DK.ds₁ ≠ [] ∧ (dataAtFiles flashProveData Z).DK.ds₂ ≠ [] ∧
      (dataAtFiles flashProveData Z).DK.ds₃ ≠ []) ∧
    ((dataAtFiles flashProveData Z).DP.ds₁ ≠ [] ∧ (dataAtFiles flashProveData Z).DP.ds₂ ≠ [] ∧
      (dataAtFiles flashProveData Z).DP.ds₃ ≠ []) := by
  have hK : (dataAtFiles flashProveData Z).DK = theKeyDataAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) := by
    show flashProveData.keyRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z) = _
    unfold DescriptionData.keyRoundsOrEmpty
    exact if_pos hl
  have hP : (dataAtFiles flashProveData Z).DP = theProofDataAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) := by
    show flashProveData.proofRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z) = _
    unfold DescriptionData.proofRoundsOrEmpty
    exact if_pos hl
  rw [hK, hP]
  have h := theLiveAt_of OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) hl
  simp only [dataWellFormedAtFullSizeDepth, dataWellFormedApartFromDepth, listsFull, Bool.and_eq_true, Bool.not_eq_true', List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    List.length_eq_zero_iff] at h
  obtain ⟨-, -, a, b, c, d, e, f⟩ := h
  exact ⟨⟨a, b, c⟩, d, e, f⟩

/-! ## The test -/

/-- One file's rounds: fewer than 2^64 items, and widths below 2^64. -/
def roundsB (D : WholeD) : Bool :=
  (D.ds₁ ++ (D.ds₂ ++ D.ds₃)).all fun d =>
    decide (d.items.length < 2 ^ 64) && d.trees.all fun t => decide (t.W < 2 ^ 64)

/-- **The test**, at a plan's values and two files' data. -/
def sizesB (G : FilesParameters XF RecFull) (DK DP : WholeD) : Bool :=
  roundsB DK && roundsB DP &&
    decide ((sTG G).logLeaves < 64) && decide ((sTG G).saltBytes ≤ 64) &&
    decide ((sBG G).logLeaves < 64) && decide ((sBG G).saltBytes ≤ 64) && decide (saltG G ≤ 64)

/-- The test at the plan's values and the two files' data of three public files: what verify()'s
description lays where protocolDataWellFormed says yes. With code: a run can decide it. -/
def wordsFitAt (Zk : OnBytes.K.Pub) : Bool := sizesB (thePlan Zk) (theKeyData Zk) (theProofData Zk)

/-- What the test's yes says, clause by clause. -/
structure SizesSay (G : FilesParameters XF RecFull) (DK DP : WholeD) : Prop where
  itemsK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), d.items.length < 2 ^ 64
  widthsK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64
  itemsP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), d.items.length < 2 ^ 64
  widthsP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), ∀ t ∈ d.trees, t.W < 2 ^ 64
  bindK : (sTG G).logLeaves < 64 ∧ (sTG G).saltBytes ≤ 64
  bindP : (sBG G).logLeaves < 64 ∧ (sBG G).saltBytes ≤ 64
  salt : saltG G ≤ 64

theorem sizesB_says {G : FilesParameters XF RecFull} {DK DP : WholeD} (h : sizesB G DK DP = true) :
    SizesSay G DK DP := by
  simp only [sizesB, roundsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hK, hP⟩, a⟩, b⟩, c⟩, d⟩, e⟩ := h
  exact ⟨fun x hx => (hK x hx).1, fun x hx => (hK x hx).2, fun x hx => (hP x hx).1,
    fun x hx => (hP x hx).2, ⟨a, b⟩, ⟨c, d⟩, e⟩

/-- **What its yes says of what verify()'s description lays at Z, under protocolDataWellFormed.** -/
theorem wordsFitAt_says {Z : VerifierAndGoals.PublicFiles} (hl : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (h : wordsFitAt (VerifierAndGoals.asDescriptionFiles Z) = true) :
    SizesSay (dataAtFiles flashProveData Z).G (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP := by
  have hG : (dataAtFiles flashProveData Z).G = thePlan (VerifierAndGoals.asDescriptionFiles Z) := by
    show flashProveData.filesParametersOrDefault (VerifierAndGoals.asDescriptionFiles Z) = _
    unfold DescriptionData.filesParametersOrDefault
    exact if_pos hl
  have hK : (dataAtFiles flashProveData Z).DK = theKeyData (VerifierAndGoals.asDescriptionFiles Z) := by
    show flashProveData.keyRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z) = _
    unfold DescriptionData.keyRoundsOrEmpty
    exact if_pos hl
  have hP : (dataAtFiles flashProveData Z).DP = theProofData (VerifierAndGoals.asDescriptionFiles Z) := by
    show flashProveData.proofRoundsOrEmpty (VerifierAndGoals.asDescriptionFiles Z) = _
    unfold DescriptionData.proofRoundsOrEmpty
    exact if_pos hl
  rw [hG, hK, hP]
  exact sizesB_says h

end Meaning

#print axioms Meaning.trees_DK
#print axioms Meaning.trees_DP
#print axioms Meaning.lists_full
#print axioms Meaning.sizesB_says
#print axioms Meaning.wordsFitAt_says
