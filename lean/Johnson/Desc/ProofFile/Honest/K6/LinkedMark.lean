-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/LinkedMark.lean: the test `linkedK6T` (Honest/K6/LinkedTest.lean)
on the challenges of the sub-protocol "the output head's own rounds" (K6), turned round, as a mark
at that sub-protocol's member, and what is owed for it (`MarkDebt`, Honest/Law/CoverJoin.lean).
CONDITIONAL. One mark, and lemmas with their proofs. None of the library's goals.

What a mark is, after Honest/Law/Marks.lean: an event of the challenges at which the verifier
rejects nothing, and which is counted all the same, once: a fall behind it (`Fall`,
Honest/Side.lean: a test on the verifier's state in front of a member and on that member's
challenges) can be bounded only where the mark has not spoken. This one speaks where the first
element sampled at one of the rounds that `linkedRounds` names is 0 or 1. Where ls ≤ lPd these are
ls + 3 lt rounds (`linkedRounds_length`).

The test. Behind the segment's batching the verifier asks that no weight on the reads' row and on
the ties' row is 0 (`selfLinked`, Johnson/Desc/First/TailClaims/SelfTests.lean). Honest/K6/Good.lean
says how such a weight on the reads' row hangs on this sub-protocol's challenges, and has a test on
the challenges for it, `linkedK6`: no coordinate of three points, one for each of three committed
matrices, is 0 or 1. `linkedK6T` has that test's first two groups of clauses, for the stream's
matrix and the activations'. In the third group, for the row's matrix, it reads the challenges of
the sumcheck on the products, one element a round, in place of the point on the positions, all of
whose coordinates one round samples. The row's matrix has a table of reads for either: of the twelve
tables (`readsNeed`, Johnson/Stored/HeadSeatAt.lean) the seat's reader in that file lays "hr@P_V"
for `rowAtPV` and "hr@r_tV" for `rowAtProducts`. So each coordinate that `linkedK6T` reads is the
first element of a round of its own, and the debt is met round by round, by the lemma that serves
`goodK6Mark` (Honest/K6/GoodMark.lean).

  `linkedK6TMark`     THE MARK (the test, the numbers of the rounds that it reads and the stated
                      number are Honest/K6/LinkedTest.lean's)
  `linkedK6TMark_speaks`, `linkedK6T_iff`, `linkedK6T_no_iff`, `linkedK6TMark_iff`   where it
                      speaks
  `linkedRounds_good`, `linkedRounds_rise`, `linkedRounds_length`   each named round is one that
                      `goodK6` reads too; they rise; how many there are
  `linkedK6T_markDebt`   **the debt is met at the sum, over the rounds that the test reads, of a
                      bound over THAT ONE ROUND's messages on "its first sampled element is 0 or
                      1"**: a call of `markDebt_of_rounds` (Honest/Small/MarkRounds.lean);
                      `linkedK6T_markDebt_one`: at one bound for all
  `linkedBad_field`   from the words 0 and 1 to the field's 0 and 1
  `linkedT_of_silent`, `linkedT_of_silent_fit`   what the mark's silence gives
  `headSumR_ok`, `headSumR_cut`, `mem_linkedRounds`   small tools

What it is not. NO THEOREM TIES THE TEST `linkedK6T` TO `selfLinked`, NOR TO `linkedK6`: which table
of reads has which point, and that the table's weights are other than 0 where no coordinate of its
point is 0 or 1, are readings of the verifier's text. EVEN BY THESE READINGS THE MARK's SILENCE DOES
NOT GIVE `selfLinked`. It says nothing of the batching element: where the test `linkedK6T` accepts,
a weight on the reads' row is a polynomial in that element that is not the zero polynomial, and can
still come to 0. It says nothing of the ties' row. It does not cover the matrices whose tables are
made of the lookup's challenges alone. And the test `linkedK6T` rejects at more lists of challenges
than those at which a weight is 0 at every batching element. All limits of Honest/K6/Good.lean hold
here too. NO NUMBER IS EVALUATED, AND NONE IS TO BE QUOTED AS HELD: the kit C of verifier's
messages, the rounds' data dsb and the bounds z are letters. The debt has two premises. hlen: the
data have a round at each number that the test reads. hz: the bound over one round's messages: how a
measure over a kit's typed challenges comes from a count of what they show hangs on the kit. MET FOR
NOTHING at z := 1. The mark's stated share (`linkedK6TOdds`) is a stated number, no bound: no lemma
here spends it. The uniform law on the messages: that the messages of any run have it is not said.
The place a is a letter: nothing here lays the mark at a written place. Called: `markDebt_of_rounds`
(Honest/Small/MarkRounds.lean); `headFirstNo_isSome`, `elemOf_at`, `drawsOk_of_fit`
(Honest/K6/GoodMark.lean); `mem_goodRounds`, `headInFront_at`, `headClausesOn_all`
(Honest/K6/GoodRounds.lean); `toE_ofE`, `toE_zeroE`, `toE_oneE` (OnBytes/Slice/Field.lean). Over
files that have not yet landed in the library: Honest/Small/MarkRounds.lean,
Honest/K6/GoodMark.lean, Honest/K6/GoodRounds.lean, Honest/K6/LinkedTest.lean, and what they import.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Small.MarkRounds
import Johnson.Desc.ProofFile.Honest.K6.GoodMark
import Johnson.Desc.ProofFile.Honest.K6.LinkedTest
import OnBytes.Slice.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open scoped ENNReal
open OnBytes (E isZeroE zeroE oneE okE)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Kinds (Point Head.Par)
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

/-- **THE MARK**: at the member a, of that member's own challenges alone: it speaks just where the
test `linkedK6T` rejects, and names the first clause that fails. The share is a stated number, no
bound. -/
def linkedK6TMark (p : Head.Par) (a : Place) : Mark :=
  { place := a, test := fun _ own => linkedK6TSays p own, share := linkedK6TOdds p }

/-! ## 1 Where the mark speaks -/

theorem linkedK6TMark_speaks (p : Head.Par) (a : Place) (fr own : List Fmt.Drawn) :
    ((linkedK6TMark p a).test fr own).isSome = !linkedK6T p own :=
  headFirstNo_isSome (linkedK6TClauses p own)

/-- A test on all challenges of a sumcheck's variables, round by round. -/
theorem headSumR_ok (p : Head.Par) (i n : Nat) (own : List Fmt.Drawn) (ok : E → Bool) :
    (headSumR p i n own).toList.all ok = true ↔
      ∀ j, j < n → ok (elemOf own (headInFront p i + 1 + j)) = true := by
  unfold headSumR
  simp only [List.all_eq_true, List.mem_map, List.mem_range]
  constructor
  · intro h j hj
    exact h _ ⟨j, hj, rfl⟩
  · rintro h x ⟨j, hj, rfl⟩
    exact h j hj

/-- The like on those from number a on. -/
theorem headSumR_cut (p : Head.Par) (i n a : Nat) (own : List Fmt.Drawn) (ok : E → Bool) :
    ((headSumR p i n own).extract a n).toList.all ok = true ↔
      ∀ k, k < n - a → ok (elemOf own (headInFront p i + 1 + a + k)) = true := by
  have e : ((headSumR p i n own).extract a n).toList =
      (List.range (n - a)).map fun k => elemOf own (headInFront p i + 1 + a + k) := by
    unfold headSumR
    rw [Array.toList_extract, List.extract_eq_take_drop]
    apply List.ext_getElem?
    intro t
    show ((((List.range n).map fun j => elemOf own (headInFront p i + 1 + j)).drop a).take
      (n - a))[t]? = _
    rw [List.getElem?_take, List.getElem?_drop, List.getElem?_map, List.getElem?_map]
    by_cases ht : t < n - a
    · rw [if_pos ht, List.getElem?_range (show a + t < n by omega), List.getElem?_range ht]
      show some (elemOf own (headInFront p i + 1 + (a + t))) =
        some (elemOf own (headInFront p i + 1 + a + t))
      rw [Nat.add_assoc (headInFront p i + 1) a t]
    · rw [if_neg ht, List.getElem?_eq_none
        (show (List.range (n - a)).length ≤ t by rw [List.length_range]; omega)]
      rfl
  rw [e]
  simp only [List.all_eq_true, List.mem_map, List.mem_range]
  constructor
  · intro h k hk
    exact h _ ⟨k, hk, rfl⟩
  · rintro h x ⟨k, hk, rfl⟩
    exact h k hk

theorem mem_linkedRounds (p : Head.Par) (r : Nat) : r ∈ linkedRounds p ↔
    (∃ k, k < headLPd p + headLt p - (headLPd p - headLs p) ∧
      r = headInFront p 2 + 1 + (headLPd p - headLs p) + k) ∨
    (∃ j, j < headLt p ∧ r = headInFront p 5 + 1 + j) ∨
    (∃ j, j < headLt p ∧ r = headInFront p 7 + 1 + j) := by
  unfold linkedRounds
  simp only [List.mem_append, List.mem_map, List.mem_range, or_assoc]
  constructor
  · rintro (⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr (Or.inl ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
  · rintro (⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr (Or.inl ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)

/-- **The test `linkedK6T` accepts just if at none of the named rounds the first sampled element is
0 or 1.** No premise. -/
theorem linkedK6T_iff (p : Head.Par) (own : List Fmt.Drawn) :
    linkedK6T p own = true ↔ ∀ r ∈ linkedRounds p, headNotBit (elemOf own r) = true := by
  unfold linkedK6T linkedK6TClauses
  simp only [List.all_append, Bool.and_eq_true, headClausesOn_all, headSumR_ok, headSumR_cut]
  constructor
  · rintro ⟨⟨a2, a7⟩, a5⟩ r hr
    rcases (mem_linkedRounds p r).1 hr with ⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact a2 k hk
    · exact a5 j hj
    · exact a7 j hj
  · intro h
    refine ⟨⟨fun k hk => ?_, fun j hj => ?_⟩, fun j hj => ?_⟩
    · exact h _ ((mem_linkedRounds p _).2 (Or.inl ⟨k, hk, rfl⟩))
    · exact h _ ((mem_linkedRounds p _).2 (Or.inr (Or.inr ⟨j, hj, rfl⟩)))
    · exact h _ ((mem_linkedRounds p _).2 (Or.inr (Or.inl ⟨j, hj, rfl⟩)))

theorem linkedK6T_no_iff (p : Head.Par) (own : List Fmt.Drawn) :
    linkedK6T p own = false ↔ ∃ r ∈ linkedRounds p, headNotBit (elemOf own r) = false := by
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    have hy : linkedK6T p own = true := (linkedK6T_iff p own).2 fun r hr => by
      cases hz : headNotBit (elemOf own r) with
      | true => rfl
      | false => exact absurd ⟨r, hr, hz⟩ hn
    rw [hy] at h
    cases h
  · rintro ⟨r, hr, hz⟩
    cases hg : linkedK6T p own with
    | false => rfl
    | true =>
      rw [(linkedK6T_iff p own).1 hg r hr] at hz
      cases hz

/-- **The mark speaks just if at one of the named rounds the first element of that one round's
challenge is 0 or 1.** No premise: at every front and every list of challenges. -/
theorem linkedK6TMark_iff (p : Head.Par) (a : Place) (fr own : List Fmt.Drawn) :
    ((linkedK6TMark p a).test fr own).isSome = true ↔
      ∃ r ∈ linkedRounds p, (!headNotBit (elemOf ((own.drop r).take 1) 0)) = true := by
  rw [linkedK6TMark_speaks, Bool.not_eq_true', linkedK6T_no_iff]
  simp only [elemOf_at, Bool.not_eq_true']

/-! ## 2 The rounds that it reads -/

/-- Each named round is one that `goodK6` reads too: so it samples just one element, and not by the
rule that never gives 0 (`goodRounds_draw`), and the data have it (`goodRounds_lt_of_fits`). -/
theorem linkedRounds_good (p : Head.Par) : ∀ r ∈ linkedRounds p, r ∈ goodRounds p := by
  intro r hr
  rcases (mem_linkedRounds p r).1 hr with ⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact (mem_goodRounds p _).2 (Or.inl ⟨headLPd p - headLs p + k, by omega, by omega⟩)
  · exact (mem_goodRounds p _).2 (Or.inr (Or.inl ⟨j, hj, rfl⟩))
  · exact (mem_goodRounds p _).2 (Or.inr (Or.inr (Or.inr ⟨j + 1, by omega, by omega⟩)))

theorem linkedRounds_rise (p : Head.Par) : (linkedRounds p).Pairwise (· < ·) := by
  obtain ⟨f2, f5, _, f7⟩ := headInFront_at p
  have up : ∀ (n a : Nat), ((List.range n).map (a + ·)).Pairwise (· < ·) := fun n a => by
    rw [List.pairwise_map]
    exact List.pairwise_lt_range.imp fun h => by omega
  unfold linkedRounds
  simp only [List.pairwise_append, List.mem_append, List.mem_map, List.mem_range]
  refine ⟨⟨up _ _, up _ _, ?_⟩, up _ _, ?_⟩
  · rintro a ⟨i, hi, rfl⟩ b ⟨j, hj, rfl⟩
    omega
  · rintro a (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) b ⟨j, hj, rfl⟩ <;> omega

/-- Conditional: a block has no more features than there are with padding. -/
theorem linkedRounds_length (p : Head.Par) (h : headLs p ≤ headLPd p) :
    (linkedRounds p).length = headLs p + 3 * headLt p := by
  unfold linkedRounds
  simp only [List.length_append, List.length_map, List.length_range]
  omega

/-! ## 3 The debt -/

/-- **WHAT IS OWED FOR THE MARK, FROM BOUNDS OVER ONE ROUND's MESSAGES.** C: the kit, any. dsb: the
data of the member's rounds (hlen: it has each named round). z r: a bound on the measure, OVER THAT
ONE ROUND's MESSAGES, of "the first element that the round samples is 0 or 1". P: any: the test
reads no challenge in front; nor is the list's length spent. -/
theorem linkedK6T_markDebt (C : CK) (dsb : List RDT) (p : Head.Par) (a : Place) (z : Nat → ℝ≥0∞)
    (hlen : ∀ r ∈ linkedRounds p, r < dsb.length)
    (hz : ∀ r ∈ linkedRounds p, ∀ d, dsb[r]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | (!headNotBit (elemOf (drawnT C [d] ρ) 0)) = true} ≤ z r)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt C (linkedK6TMark p a) dsb P ((linkedRounds p).map z).sum :=
  ProofFile.Honest.Small.markDebt_of_rounds C dsb (linkedK6TMark p a) (linkedRounds p)
    (fun _ l => !headNotBit (elemOf l 0)) z P
    (fun fr _ own _ h => (linkedK6TMark_iff p a fr own).1 h) hlen hz

/-- The same at one number for all rounds. -/
theorem linkedK6T_markDebt_one (C : CK) (dsb : List RDT) (p : Head.Par) (a : Place) (z : ℝ≥0∞)
    (hlen : ∀ r ∈ linkedRounds p, r < dsb.length)
    (hz : ∀ r ∈ linkedRounds p, ∀ d, dsb[r]? = some d →
      Iop.prRho {ρ : Iop.Rho (uLT C [d]) | (!headNotBit (elemOf (drawnT C [d] ρ) 0)) = true} ≤ z)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt C (linkedK6TMark p a) dsb P (((linkedRounds p).length : ℝ≥0∞) * z) := by
  have h := linkedK6T_markDebt C dsb p a (fun _ => z) hlen hz P
  rw [List.map_const', List.sum_replicate, nsmul_eq_mul] at h
  exact h

/-- **FROM THE WORDS 0 AND 1 TO THE FIELD's 0 AND 1**: what a payer of hz asks of the test: where
the test on one round's challenge speaks and that challenge shows just one field element x, laid
into words by the library's own `Slice.ofE` (OnBytes/Slice/Field.lean), x is 0 or 1. No premise
beside. -/
theorem linkedBad_field (dr : Fmt.Drawn) (x : Cb.Gl.E)
    (h : (!headNotBit (elemOf [dr] 0)) = true) (he : dr.elems = [OnBytes.Slice.ofE x]) :
    x = 0 ∨ x = 1 := by
  have e : elemOf [dr] 0 = E.ofTriple (OnBytes.Slice.ofE x) := by
    unfold elemOf elemsOf
    simp [he]
  rw [e] at h
  unfold headNotBit at h
  have hx := OnBytes.Slice.toE_ofE x
  cases hz : isZeroE (E.ofTriple (OnBytes.Slice.ofE x)) with
  | true =>
    left
    unfold isZeroE at hz
    simp only [Bool.and_eq_true, beq_iff_eq] at hz
    have t : OnBytes.Slice.ofE x = Fmt.Fld.zeroE := Prod.ext hz.1.1 (Prod.ext hz.1.2 hz.2)
    rw [← hx, t, OnBytes.Slice.toE_zeroE]
  | false =>
    right
    rw [hz] at h
    have h1 : E.ofTriple (OnBytes.Slice.ofE x) = oneE := by simpa using h
    have t : OnBytes.Slice.ofE x = Fmt.Fld.oneE := congrArg E.triple h1
    rw [← hx, t, OnBytes.Slice.toE_oneE]

/-! ## 4 What the mark's silence gives -/

theorem linkedT_of_silent (p : Head.Par) (a : Place) (fr own : List Fmt.Drawn)
    (hs : ((linkedK6TMark p a).test fr own).isSome = false) : linkedK6T p own = true := by
  rw [linkedK6TMark_speaks] at hs
  simpa using hs

/-- At challenges that fit the declared rounds, besides, every word of every sampled element is
below the prime: so "is not the word 0 or 1" means there "is not 0 or 1 in the field". -/
theorem linkedT_of_silent_fit (p : Head.Par) (a : Place) (fr own : List Fmt.Drawn)
    (h : drawsFit p.rounds own = true)
    (hs : ((linkedK6TMark p a).test fr own).isSome = false) :
    (own.all fun d => (elemsOf d).all okE) = true ∧ linkedK6T p own = true :=
  ⟨drawsOk_of_fit p.rounds own h, linkedT_of_silent p a fr own hs⟩

#print axioms linkedK6TMark_speaks
#print axioms headSumR_ok
#print axioms headSumR_cut
#print axioms mem_linkedRounds
#print axioms linkedK6T_iff
#print axioms linkedK6T_no_iff
#print axioms linkedK6TMark_iff
#print axioms linkedRounds_good
#print axioms linkedRounds_rise
#print axioms linkedRounds_length
#print axioms linkedK6T_markDebt
#print axioms linkedK6T_markDebt_one
#print axioms linkedBad_field
#print axioms linkedT_of_silent
#print axioms linkedT_of_silent_fit

end ProofFile.Honest.K6
