-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookCutsLaw.lean: WHERE A DESCRIPTION's TEST ON ITS PLACES ACCEPTS
(F.placesOk) AND A BOOK's CUTS ARE THE MAKER's (B.cuts = cutsOf F, Honest/BookOf.lean), THE TENTH OF
THE BOOK's OWN TESTS (ProverCoinCounts.clauses, Honest/Frame.lean: "a cut stands at no place, stands twice, has
a part without a round or does not add up") ACCEPTS. Written by the authors of the honest side of
the linear claim's shared rounds (K14), in the frame's folder, not by the frame's authors; the
makers are theirs. General in the description and the book; nothing is evaluated. Fourteen
statements with their proofs; no definition.

  foldl_add_shift, lookup_of_nodup   two steps on plain lists: the first by a call of the library's
                  OnBytes.foldl_add (OnBytes/Chain/Lists.lean)
  headRun_le, headOne_le, sumTail_le, unitLen_bounds, unitsOf_fits   the maker's units: each has at
                  least one round and no more than the list; with the list's length for a bound
                  they use the list up
  cutOfNames_fits, partsCut_sum   **the cut adds up to the rounds' number, and no part is without a
                  round**: at every kind (K12's second part is a sum of at least one unit) and every
                  list of names
  partsCutFits_all   **partsCutFits b = true AT EVERY SUB-PROTOCOL b**: that test on the cut cannot
                  reject. NO MAKER AND NO TEST OF THE BOOK READS partsCutFits; NOTHING HERE CALLS
                  partsCutFits_all: the last statement goes by partsCut_sum
  cuts_all_ok     the tenth test's form on plain lists
  cutsIn_mem, cutsIn_places   what a chain's cuts are, for it
  clause10_of_places   **the statement of the first sentence**

How it goes. The sizes' places are the description's order of places, in which no place stands twice
(the frame's orderOf_nodup, Honest/Law/Rule/Tests.lean): so lookup finds a sub-protocol's own size,
which its cut adds up to; the cuts' places are a sublist of these: so none stands twice: the last
clause by one_each (Honest/BookLinear/Tool.lean).
Kin. partsCutFits_written (Honest/BookWritten/Seeds.lean) has partsCutFits at one written
description, by an evaluation in Lean's kernel: a case of partsCutFits_all. cut_send
(Honest/K14/BookAtShared.lean): the cut of a sending's two rounds. lookup_of_nodup: the library has
the same sentence at keys that are numbers (lookup_of_mem, Compile/Batch/PrunedFacts.lean; from
rising keys: Run/PageIsViewProofs.lean): neither serves at a Place. The frame's nodup_of_count
(Honest/Law/Rule/Tests.lean) is one_each's converse. THAT THE LONG TERM OF clause10_of_places IS THE
TENTH MEMBER OF ProverCoinCounts.clauses IS HELD BY LEAN ELSEWHERE: in clause10_at_raw's proof
(Honest/BookRawRows.lean) and in clauses_verdicts (Honest/BookWordOf.lean); in this file it is by
reading.
What is not claimed. That F.placesOk accepts at any named description. That any maker returns a
book: Honest/BookRawRows.lean has that bookRaw's book has the maker's cuts. The ten other tests.
That the cut is the one that the format means: it reads names (Honest/BookOf.lean's own limit).
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests
import Johnson.Desc.ProofFile.Honest.BookLinear.Tool

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place KindName)

/-- A sum by foldl from a is a plus the sum from 0. -/
theorem foldl_add_shift (l : List Nat) : ∀ a : Nat, l.foldl (· + ·) a = a + l.foldl (· + ·) 0 := by
  intro a
  rw [OnBytes.foldl_add l a, OnBytes.foldl_add l 0, Nat.zero_add]

/-- The run at a list's head is no longer than the list. -/
theorem headRun_le (s : String) (ns : List String) : headRun s ns ≤ ns.length := by
  unfold headRun
  exact (List.takeWhile_prefix _).length_le

/-- headOne is no greater than the list's length. -/
theorem headOne_le (s : String) (ns : List String) : headOne s ns ≤ ns.length := by
  unfold headOne
  cases ns with
  | nil => simp
  | cons a l =>
    split
    · simp
    · simp

/-- The rounds of a masked sumcheck behind its first are no more than the list has. -/
theorem sumTail_le (ns : List String) : sumTail ns ≤ ns.length := by
  unfold sumTail
  have h1 := headRun_le "PSC round" ns
  have h2 := headOne_le "PSC Y" (ns.drop (headRun "PSC round" ns))
  have h3 := headOne_le "PSC values"
    (ns.drop (headRun "PSC round" ns + headOne "PSC Y" (ns.drop (headRun "PSC round" ns))))
  simp only [List.length_drop] at h2 h3
  dsimp only
  omega

/-- **The unit at the head of a list that is not empty has at least one round, and no more than the
list has.** -/
theorem unitLen_bounds (n : String) (l : List String) :
    1 ≤ unitLen (n :: l) ∧ unitLen (n :: l) ≤ l.length + 1 := by
  have a1 := sumTail_le l
  have a2 := headRun_le "FOLD round" l
  have a3 : headRun "FOLD round" l.tail ≤ l.length - 1 := by
    simpa [List.length_tail] using headRun_le "FOLD round" l.tail
  have a4 := headOne_le "BASE" l
  simp only [unitLen]
  split_ifs with h1 h2 h3 h4 h5 h6
  · omega
  · have hl : l ≠ [] := by rintro rfl; simp at h3
    have := List.length_pos_iff.2 hl
    omega
  · omega
  · omega
  · have hl : l ≠ [] := by rintro rfl; simp at h5
    have := List.length_pos_iff.2 hl
    omega
  · omega
  · omega

/-- **With a bound of at least the list's length the units use the list up**: they add up to its
length, and none is 0. -/
theorem unitsOf_fits : ∀ (k : Nat) (ns : List String), ns.length ≤ k →
    (unitsOf k ns).foldl (· + ·) 0 = ns.length ∧ ∀ u ∈ unitsOf k ns, u ≠ 0
  | 0, ns, h => by
    have : ns = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 h)
    subst this
    simp [unitsOf]
  | k + 1, [], _ => by simp [unitsOf]
  | k + 1, n :: l, h => by
    obtain ⟨b1, b2⟩ := unitLen_bounds n l
    have hd : ((n :: l).drop (unitLen (n :: l))).length ≤ k := by
      simp only [List.length_drop, List.length_cons] at h ⊢
      omega
    obtain ⟨i1, i2⟩ := unitsOf_fits k _ hd
    unfold unitsOf
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons]
      rw [foldl_add_shift, i1]
      simp only [List.length_drop, List.length_cons]
      omega
    · intro u hu
      rcases List.mem_cons.1 hu with rfl | hu
      · omega
      · exact i2 u hu

/-- **The cut of a place's rounds adds up to their number, and no part is without a round**: at
every kind and every list of names. -/
theorem cutOfNames_fits (kind : KindName) (ns : List String) :
    (cutOfNames kind ns).foldl (· + ·) 0 = ns.length ∧ ∀ u ∈ cutOfNames kind ns, u ≠ 0 := by
  obtain ⟨h1, h2⟩ := unitsOf_fits ns.length ns (Nat.le_refl _)
  unfold cutOfNames
  split
  · rename_i he
    rw [he] at h1
    exact ⟨h1, fun _ h => nomatch h⟩
  · rename_i a rest he
    rw [he] at h1 h2
    split
    · split
      · rename_i hr
        have : rest = [] := List.isEmpty_iff.1 hr
        subst this
        exact ⟨h1, h2⟩
      · rename_i hr
        simp only [List.foldl_cons, List.foldl_nil] at h1 ⊢
        rw [foldl_add_shift] at h1
        refine ⟨by omega, fun u hu => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl
        · exact h2 _ List.mem_cons_self
        · cases rest with
          | nil => simp at hr
          | cons x t =>
            have hx := h2 x (List.mem_cons_of_mem _ List.mem_cons_self)
            simp only [List.foldl_cons]
            rw [foldl_add_shift]
            omega
    · exact ⟨h1, h2⟩

/-- **partsCutFits ACCEPTS EVERY SUB-PROTOCOL.** No maker and no test of the book reads
partsCutFits, and nothing in this file calls this theorem. -/
theorem partsCutFits_all {S Cl : Type} (b : Block S Cl) : partsCutFits b = true := by
  obtain ⟨h1, h2⟩ := cutOfNames_fits b.place.kind (b.rounds.map (·.entry.name))
  unfold partsCutFits partsCut
  rw [Bool.and_eq_true]
  refine ⟨by rw [h1]; simp, List.all_eq_true.2 fun u hu => by simpa using h2 u hu⟩

/-- At a sub-protocol: the maker's cut adds up to the number of its rounds, and no part of it is 0:
cutOfNames_fits at the sub-protocol's kind and its rounds' names. -/
theorem partsCut_sum {S Cl : Type} (b : Block S Cl) :
    (partsCut b).foldl (· + ·) 0 = b.rounds.length ∧ ∀ u ∈ partsCut b, u ≠ 0 := by
  obtain ⟨h1, h2⟩ := cutOfNames_fits b.place.kind (b.rounds.map (·.entry.name))
  exact ⟨by unfold partsCut; rw [h1]; simp, h2⟩

/-- In a list of pairs whose first members are all different, lookup finds a member's second. -/
theorem lookup_of_nodup {α β : Type} [BEq α] [LawfulBEq α] : ∀ (l : List (α × β)),
    (l.map (·.1)).Nodup → ∀ k v, (k, v) ∈ l → l.lookup k = some v
  | [], _, _, _, h => nomatch h
  | (a, b) :: t, hn, k, v, h => by
    have hn' := List.nodup_cons.1 (show (a :: t.map (·.1)).Nodup from hn)
    rw [List.lookup_cons]
    rcases List.mem_cons.1 h with e | h
    · cases e
      simp
    · have hk : k ∈ t.map (·.1) := List.mem_map.2 ⟨(k, v), h, rfl⟩
      have hne : (k == a) = false := by
        rw [beq_eq_false_iff_ne]
        rintro rfl
        exact hn'.1 hk
      rw [hne]
      exact lookup_of_nodup t hn'.2 k v h

/-- **The tenth test's form on plain lists**: sz: sizes by place, no place twice; cs: cuts by place,
no place twice; each cut's sum is its place's size in sz, and no part of it is 0: then at every cut
lookup finds that sum, no part is 0, and its place stands once among the cuts. -/
theorem cuts_all_ok (sz : List (Place × Nat)) (cs : List (Place × List Nat))
    (H1 : (sz.map (·.1)).Nodup)
    (H2 : ∀ c ∈ cs, (c.1, c.2.foldl (· + ·) 0) ∈ sz ∧ ∀ u ∈ c.2, u ≠ 0)
    (H3 : (cs.map (·.1)).Nodup) :
    (cs.all fun c => sz.lookup c.1 == some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
      (cs.filter fun d => d.1 == c.1).length == 1) = true := by
  rw [List.all_eq_true]
  intro c hc
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [lookup_of_nodup sz H1 _ _ (H2 c hc).1]
    simp
  · exact List.all_eq_true.2 fun u hu => by simpa using (H2 c hc).2 u hu
  · exact List.all_eq_true.1 (one_each (fun d : Place × List Nat => d.1) cs H3) c hc

/-- A member of a chain's cuts: its place has its sum for a size among the chain's sizes; no part of
it is 0. -/
theorem cutsIn_mem {S Cl : Type} {bs : List (Block S Cl)} {c : Place × List Nat}
    (h : c ∈ cutsIn bs) :
    (c.1, c.2.foldl (· + ·) 0) ∈ bs.map (fun b => (b.place, b.rounds.length)) ∧
      ∀ u ∈ c.2, u ≠ 0 := by
  unfold cutsIn at h
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
  refine ⟨List.mem_map.2 ⟨b, (List.mem_filter.1 hb).1, ?_⟩, (partsCut_sum b).2⟩
  rw [(partsCut_sum b).1]

/-- The places of a chain's cuts are a sublist of the chain's places. -/
theorem cutsIn_places {S Cl : Type} (bs : List (Block S Cl)) :
    ((cutsIn bs).map (·.1)).Sublist (bs.map (·.place)) := by
  unfold cutsIn
  rw [List.map_map]
  exact (List.filter_sublist).map _

/-- **THE TENTH TEST, AS IT STANDS IN ProverCoinCounts.clauses, AT EVERY BOOK WHOSE CUTS ARE THE MAKER's**,
where the description's test on the places accepts. The long term is that test's, with its "sizes"
written out. -/
theorem clause10_of_places {Xi : Type} {F : FileDescription Xi} (h : F.placesOk = true) {B : ProverCoinCounts}
    (hc : B.cuts = cutsOf F) :
    (B.cuts.all fun c =>
      (F.first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        F.shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        F.second.blocksInOrder.map fun b => (b.place, b.rounds.length)).lookup c.1 ==
          some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
        (B.cuts.filter fun d => d.1 == c.1).length == 1) = true := by
  rw [hc]
  have hn := orderOf_nodup h
  apply cuts_all_ok
  · have e : (F.first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        F.shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
        F.second.blocksInOrder.map fun b => (b.place, b.rounds.length)).map (·.1) = orderOf F := by
      simp [orderOf, List.map_append, List.map_map, Function.comp_def]
    rw [e]
    exact hn
  · intro c hcm
    unfold cutsOf at hcm
    rcases List.mem_append.1 hcm with q | q
    · rcases List.mem_append.1 q with q | q
      · exact ⟨List.mem_append_left _ (List.mem_append_left _ (cutsIn_mem q).1), (cutsIn_mem q).2⟩
      · exact ⟨List.mem_append_left _ (List.mem_append_right _ (cutsIn_mem q).1), (cutsIn_mem q).2⟩
    · exact ⟨List.mem_append_right _ (cutsIn_mem q).1, (cutsIn_mem q).2⟩
  · unfold cutsOf
    rw [List.map_append, List.map_append]
    exact hn.sublist (((cutsIn_places _).append (cutsIn_places _)).append (cutsIn_places _))

end ProofFile.Honest

#print axioms ProofFile.Honest.foldl_add_shift
#print axioms ProofFile.Honest.headRun_le
#print axioms ProofFile.Honest.headOne_le
#print axioms ProofFile.Honest.sumTail_le
#print axioms ProofFile.Honest.unitLen_bounds
#print axioms ProofFile.Honest.unitsOf_fits
#print axioms ProofFile.Honest.cutOfNames_fits
#print axioms ProofFile.Honest.partsCutFits_all
#print axioms ProofFile.Honest.partsCut_sum
#print axioms ProofFile.Honest.lookup_of_nodup
#print axioms ProofFile.Honest.cuts_all_ok
#print axioms ProofFile.Honest.cutsIn_mem
#print axioms ProofFile.Honest.cutsIn_places
#print axioms ProofFile.Honest.clause10_of_places
