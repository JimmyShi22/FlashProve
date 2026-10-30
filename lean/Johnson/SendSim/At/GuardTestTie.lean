-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/GuardTestTie.lean: the two-part test of Johnson/SendSim/At/GuardTest.lean accepts
exactly where the condition on the book (BookClearAny) holds.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. For runs and the
guard: the head of GuardTest.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. P, ride, the book Bk, the order ord, the owner o and the address p are
arbitrary. The first five statements have no premise on P or ride.
  spenderOk_iff      spenderFitsB and guardApartB both accept at o and p if and only if p meets the
                     condition on a spender (SpenderClearAny, Johnson/SendSim/At/FreshWide.lean).
  ownerOkB_iff       ownerOkB accepts at o if and only if the book meets BookClearAny
                     (Johnson/SendSim/At/BookWide.lean) at o.
  guardApartB_iff    guardApartB accepts if and only if GuardClearE holds at the guard sendGuardE.
                     GuardClearE g says, in terms of coins: nothing that p spends is known, and
                     nothing in the guard g of what p spends is known.
  spendersClearAny_of_guard   If ownerFitsB accepts at o, and GuardClearE holds at each address that
                     has a spending entry on o's coins, then SpendersClearAny holds at o
                     (Johnson/SendSim/At/SpendersAlone.lean): the premise under which the field
                     fresh is proved in Johnson/SendSim/At/SpendersAloneProofs.lean.
  spendersClearAny_of_bookClearAny   BookClearAny implies SpendersClearAny.
  spentBy_nil_of_no_spending   If no spending entry of the book has the owner o, no address spends
                     anything of o's coins.
  guardApart_spec, guardApart_of   what guardApartB says of our own guard. It accepts if no coin of
                     the base field is spent, no spent coin is known, and no coin in a run of
                     coinGuard c, for a spent coin c, is known. If it accepts, the last two hold.
  guard_prefix, guard_nil   the guard begins with the spent runs themselves; the guard of no run is
                     no run.
  guardTried_...     Twelve evaluations at three small examples
                     (Johnson/SendSim/At/FilledBooks.lean), in Lean's kernel.
                     At placeThreeFree, one mask row. At the book in which three addresses each
                     spend one free mask entry, ownerOkB accepts. With the pad carried to the last
                     spender, ownerFitsB still accepts and guardApartB rejects. With the mask row's
                     tail carried there, guardApartB rejects. With the main row's tail carried
                     there, guardApartB accepts: a control that checks that the guard does not
                     reject a coin that is tied to no spent coin. With the pad spent in place of a
                     free entry, spenderFitsB rejects.
                     At placeTwoRowsFree, two mask rows, the pad in the second. An address spends an
                     entry of the first row: guardApartB rejects if the first row's tail is carried
                     to it, and if the second row's is. An address spends an entry of the second
                     row: guardApartB accepts with the first row's tail carried to it (a control).
                     At placeRiderFirst, whose first message is a table sent along. An address
                     spends its three coefficient coins: spenderFitsB accepts; guardApartB rejects
                     if the table's tail is carried to it, and accepts if the other message's mask
                     tail is (a control).

How it fits. ownerOkB_iff proves that BookClearAny is equivalent to a further test (ownerFitsB)
together with a guard: the identity on base-field runs, and sendGuardE on extension-field runs. So
the premise on the book can be given to a caller in three parts: which owners it covers, a guard at
each owner, and a further test. Johnson/SendSim/Seat/LotsGuard.lean does that for the senders of the
kind K1 on the first chain. Meant as steps toward index privacy (Johnson/WholeKey/Statement.lean);
nothing in this folder derives index privacy from them. Not one of the release's goal statements.

How it is proved. From the tests to the condition: the guard holds the spent runs, and for each
spent coin the very pads and tails that MaskSpender.clear or FoldSpenderAny.one names. From the
condition to the tests one more fact is needed: a coin is among the mask coins of one message only
(own_apart), so coinGuard adds nothing for a message other than the one that the condition speaks
of.

The other names. InRuns: a number is in one of the runs. ApartRuns: no number is in a run of each of
two lists. meets_coin, apartRunsB_iff: the tests on two runs and on two lists of runs, in terms of
coins. inRuns_runsE, inRuns_guard: which coins are in the runs of a list of entries, and in the
guard. in_tailRun, tail_in_run: a tail's run holds just that tail's coins. guard_free, guard_ride,
guard_cases: which runs coinGuard has. own_end, own_apart, mask_none, mask_some: where a message's
mask coins are. foldShape_spec, foldShape_of: what foldShapeB says. apartF_of_noF: where no coin of
the base field is spent, the base-field runs are apart.

Limits. Every statement here is about the book and the public numbers; none is about a distribution.
The twelve evaluations are at three small examples and made-up books.
-/
import Johnson.SendSim.At.GuardTest
import Johnson.SendSim.At.BookWide
import Johnson.SendSim.At.SpendersAlone
import Johnson.SendSim.At.FilledBooks
import Johnson.Desc.ProofFile.Honest.K1.Fence

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-! ## Runs and coins -/

/-- A number is in one of the runs. -/
def InRuns (l : List (Nat × Nat)) (n : Nat) : Prop := ∃ r ∈ l, r.1 ≤ n ∧ n < r.1 + r.2

/-- Two runs meet exactly if they have a number in common. -/
theorem meets_coin (a n b m : Nat) :
    meets a n b m = true ↔ ∃ k, (a ≤ k ∧ k < a + n) ∧ b ≤ k ∧ k < b + m := by
  unfold meets
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨hn, hm⟩, h1⟩, h2⟩
    by_cases h : a ≤ b
    · exact ⟨b, ⟨h, h2⟩, Nat.le_refl _, by omega⟩
    · exact ⟨a, ⟨Nat.le_refl _, by omega⟩, by omega, h1⟩
  · rintro ⟨k, ⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega

/-- The test on two lists of runs accepts exactly if no number is in both. -/
theorem apartRunsB_iff (a b : List (Nat × Nat)) :
    apartRunsB a b = true ↔ ∀ n, ¬ (InRuns a n ∧ InRuns b n) := by
  unfold apartRunsB
  rw [Bool.not_eq_true']
  constructor
  · rintro h n ⟨⟨x, hx, hx1⟩, ⟨y, hy, hy1⟩⟩
    have h' : (a.any fun x => b.any fun y => meets x.1 x.2 y.1 y.2) = true :=
      List.any_eq_true.2 ⟨x, hx, List.any_eq_true.2 ⟨y, hy, (meets_coin _ _ _ _).2 ⟨n, hx1, hy1⟩⟩⟩
    rw [h] at h'
    cases h'
  · intro h
    cases hq : (a.any fun x => b.any fun y => meets x.1 x.2 y.1 y.2) with
    | false => rfl
    | true =>
      obtain ⟨x, hx, h2⟩ := List.any_eq_true.1 hq
      obtain ⟨y, hy, h3⟩ := List.any_eq_true.1 h2
      obtain ⟨k, h4, h5⟩ := (meets_coin _ _ _ _).1 h3
      exact absurd ⟨⟨x, hx, h4⟩, ⟨y, hy, h5⟩⟩ (h k)

/-- The coins in the extension-field runs of a list of entries are those that the entries cover. -/
theorem inRuns_runsE (l : List Ahead) (n : Nat) : InRuns (runsE l) n ↔ n ∈ eAll l := by
  rw [mem_eAll_iff]
  unfold InRuns runsE inE
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr, h⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
    exact ⟨a, ha, h⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨_, List.mem_map.2 ⟨a, ha, rfl⟩, h⟩

/-- Where no coin of the base field is spent, the base-field runs are apart from any runs. -/
theorem apartF_of_noF {l : List Ahead} (h : noFB l = true) (b : List (Nat × Nat)) :
    apartRunsB (runsF l) b = true := by
  refine (apartRunsB_iff _ _).2 ?_
  rintro n ⟨⟨r, hr, h1, h2⟩, -⟩
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
  have h0 : a.count.f = 0 := beq_iff_eq.1 (List.all_eq_true.1 h a ha)
  have h2' : n < a.start.f + a.count.f := h2
  have h1' : a.start.f ≤ n := h1
  omega

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- The coins in the guard: those in the runs, and those that are tied to one of them. -/
theorem inRuns_guard (e : List (Nat × Nat)) (n : Nat) :
    InRuns (sendGuardE P ride e) n ↔
      InRuns e n ∨ ∃ c, InRuns e c ∧ InRuns (coinGuard P ride c) n := by
  unfold sendGuardE
  constructor
  · rintro ⟨r, hr, h⟩
    rcases List.mem_append.1 hr with h1 | h1
    · exact Or.inl ⟨r, h1, h⟩
    · rw [List.mem_dedup] at h1
      obtain ⟨x, hx, h2⟩ := List.mem_flatMap.1 h1
      obtain ⟨t, ht, h3⟩ := List.mem_flatMap.1 h2
      exact Or.inr ⟨x.1 + t, ⟨x, hx, Nat.le_add_right _ _,
        Nat.add_lt_add_left (List.mem_range.1 ht) _⟩, ⟨r, h3, h⟩⟩
  · rintro (⟨r, hr, h⟩ | ⟨c, ⟨x, hx, h1, h2⟩, ⟨r, hr, h⟩⟩)
    · exact ⟨r, List.mem_append_left _ hr, h⟩
    · refine ⟨r, List.mem_append_right _ (List.mem_dedup.2 (List.mem_flatMap.2 ⟨x, hx,
        List.mem_flatMap.2 ⟨c - x.1, List.mem_range.2 (by omega), ?_⟩⟩)), h⟩
      have e1 : x.1 + (c - x.1) = c := by omega
      rw [e1]
      exact hr

/-- The guard begins with the runs themselves. -/
theorem guard_prefix (e : List (Nat × Nat)) : e <+: sendGuardE P ride e := List.prefix_append _ _

/-- The guard of no run is no run. -/
theorem guard_nil : sendGuardE P ride [] = [] := rfl

/-! ## A tail's run -/

/-- A number in a tail's run is the number of an entry of that tail. -/
theorem in_tailRun {k r n : Nat} (h1 : (tailRun P ride k r).1 ≤ n)
    (h2 : n < (tailRun P ride k r).1 + (tailRun P ride k r).2) :
    ∃ q < (maskCodeAt P k).r, n = maskTailNo P ride k r q := by
  have h1' : maskTailNo P ride k r 0 ≤ n := h1
  have h2' : n < maskTailNo P ride k r 0 + (maskCodeAt P k).r := h2
  refine ⟨n - maskTailNo P ride k r 0, by omega, ?_⟩
  unfold maskTailNo at h1' h2' ⊢
  omega

/-- The number of an entry of a tail is in that tail's run. -/
theorem tail_in_run {k r q : Nat} (hq : q < (maskCodeAt P k).r) :
    (tailRun P ride k r).1 ≤ maskTailNo P ride k r q ∧
      maskTailNo P ride k r q < (tailRun P ride k r).1 + (tailRun P ride k r).2 := by
  show maskTailNo P ride k r 0 ≤ maskTailNo P ride k r q ∧
    maskTailNo P ride k r q < maskTailNo P ride k r 0 + (maskCodeAt P k).r
  unfold maskTailNo
  omega

/-! ## Which runs are tied to a coin -/

/-- At a free mask entry of a sampled message that is not sent along: the pads and two tails. -/
theorem guard_free {k j : Nat} (hk : k < P.sent.size) (hr : ride k = none)
    (ha : (shapeAt P k).answers ≠ 0)
    (hj : j < OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows (maskCodeAt P k).ell
      (shapeAt P k).answers) {r : Nat × Nat}
    (h : r ∈ padRuns P ride k ++ [tailRun P ride k (j % (shapeAt P k).maskRows),
      tailRun P ride k ((shapeAt P k).maskRows - 1)]) :
    r ∈ coinGuard P ride (maskStart P ride k + j) := by
  unfold coinGuard
  refine List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩
  simp only [hr]
  rw [if_pos (by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨⟨ha, Nat.le_add_right _ _⟩, Nat.add_lt_add_left hj _⟩), Nat.add_sub_cancel_left]
  exact h

/-- At a coin of a table sent along: the tails of all its rows. -/
theorem guard_ride {k c : Nat} {R : Ride} (hk : k < P.sent.size) (hr : ride k = some R)
    (h1 : maskStart P ride k ≤ c) (h2 : c < maskStart P ride k + R.count) {r : Nat}
    (h : r < (shapeAt P k).maskRows) : tailRun P ride k r ∈ coinGuard P ride c := by
  unfold coinGuard
  refine List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ?_⟩
  simp only [hr]
  rw [if_pos (by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h1, h2⟩)]
  exact List.mem_map.2 ⟨r, List.mem_range.2 h, rfl⟩

/-- Every run of coinGuard c is one of those in guard_free or guard_ride. -/
theorem guard_cases {c : Nat} {r : Nat × Nat} (h : r ∈ coinGuard P ride c) :
    ∃ k < P.sent.size,
      (ride k = none ∧ (shapeAt P k).answers ≠ 0 ∧ maskStart P ride k ≤ c ∧
        c < maskStart P ride k + OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows
          (maskCodeAt P k).ell (shapeAt P k).answers ∧
        r ∈ padRuns P ride k ++
          [tailRun P ride k ((c - maskStart P ride k) % (shapeAt P k).maskRows),
            tailRun P ride k ((shapeAt P k).maskRows - 1)]) ∨
      ∃ R, ride k = some R ∧ maskStart P ride k ≤ c ∧ c < maskStart P ride k + R.count ∧
        ∃ ρ < (shapeAt P k).maskRows, r = tailRun P ride k ρ := by
  unfold coinGuard at h
  obtain ⟨k, hk, h⟩ := List.mem_flatMap.1 h
  refine ⟨k, List.mem_range.1 hk, ?_⟩
  cases hR : ride k with
  | none =>
    simp only [hR] at h
    split_ifs at h with hc
    · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
      exact Or.inl ⟨rfl, hc.1.1, hc.1.2, hc.2, h⟩
    · cases h
  | some R =>
    simp only [hR] at h
    split_ifs at h with hc
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨ρ, hρ, e⟩ := List.mem_map.1 h
      exact Or.inr ⟨R, rfl, hc.1, hc.2, ρ, List.mem_range.1 hρ, e.symm⟩
    · cases h

/-! ## A coin is among the mask coins of one message only -/

/-- A message's mask coins end before the next message's coins begin. -/
theorem own_end (k : Nat) :
    maskStart P ride k + (stepsOf P.codes (shapeAt P k) (ride k)).mask ≤
      (startR P ride (k + 1)).e := by
  rw [startR_succ]
  show _ ≤ (startR P ride k).e + (dueMsg P.codes (shapeAt P k) (ride k)).e
  unfold maskStart dueMsg
  by_cases h3 : ((shapeAt P k).mainDeg == 3) = true
  · simp only [h3, if_true]
    omega
  · simp only [h3, if_false, Bool.false_eq_true]
    omega

/-- A coin is among the mask coins of one message only. -/
theorem own_apart {k k' c : Nat} (h1 : maskStart P ride k ≤ c)
    (h2 : c < maskStart P ride k + (stepsOf P.codes (shapeAt P k) (ride k)).mask)
    (h3 : maskStart P ride k' ≤ c)
    (h4 : c < maskStart P ride k' + (stepsOf P.codes (shapeAt P k') (ride k')).mask) : k = k' := by
  have hs : ∀ i, (startR P ride i).e ≤ maskStart P ride i := fun i => Nat.le_add_right _ _
  rcases Nat.lt_trichotomy k k' with h | h | h
  · have a1 := own_end P ride k
    have a2 := startR_mono P ride (k + 1) k' h
    have a3 := hs k'
    omega
  · exact h
  · have a1 := own_end P ride k'
    have a2 := startR_mono P ride (k' + 1) k h
    have a3 := hs k
    omega

/-- The number of mask coins of a message that is not sent along. -/
theorem mask_none {k : Nat} (hr : ride k = none) :
    (stepsOf P.codes (shapeAt P k) (ride k)).mask =
      (shapeAt P k).maskRows * (maskCodeAt P k).ell := by
  simp only [stepsOf, hr, Option.map_none, Option.getD_none]

/-- The number of mask coins of a table sent along. -/
theorem mask_some {k : Nat} {R : Ride} (hr : ride k = some R) :
    (stepsOf P.codes (shapeAt P k) (ride k)).mask = R.count := by
  simp only [stepsOf, hr, Option.map_some, Option.getD_some]

/-! ## The two parts at one address -/

/-- If foldShapeB accepts, the list is one entry that is exactly the coefficient coins of one table
sent along. -/
theorem foldShape_spec {sp : List Ahead} (h : foldShapeB P ride sp = true) :
    ∃ k R e, k < P.sent.size ∧ ride k = some R ∧ sp = [e] ∧ e.count = ⟨0, R.count⟩ ∧
      e.start.e = maskStart P ride k := by
  match sp, h with
  | [e], h =>
    obtain ⟨k, hk, hb⟩ := List.any_eq_true.1 h
    match hr : ride k, hb with
    | some R, hb =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      exact ⟨k, R, e, List.mem_range.1 hk, hr, rfl, hb.1, hb.2⟩

/-- The converse of foldShape_spec. -/
theorem foldShape_of {k : Nat} {R : Ride} {e : Ahead} (hk : k < P.sent.size)
    (hr : ride k = some R) (hc : e.count = ⟨0, R.count⟩) (hst : e.start.e = maskStart P ride k) :
    foldShapeB P ride [e] = true := by
  refine List.any_eq_true.2 ⟨k, List.mem_range.2 hk, ?_⟩
  rw [hr]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨hc, hst⟩

variable {P ride}

/-- If guardApartB accepts: no spent coin is known, and no coin that is tied to a spent coin. -/
theorem guardApart_spec {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}
    (h : guardApartB P ride Bk ord o p = true) :
    Disjoint (eAll (Bk.spentBy o p)) (eAll (Bk.knownBy ord o p)) ∧
      ∀ c ∈ eAll (Bk.spentBy o p), ∀ r ∈ coinGuard P ride c, ∀ n, r.1 ≤ n → n < r.1 + r.2 →
        n ∉ eAll (Bk.knownBy ord o p) := by
  simp only [guardApartB, Bool.and_eq_true] at h
  have hE := (apartRunsB_iff _ _).1 h.2.2
  refine ⟨Finset.disjoint_left.2 fun n h1 h2 => hE n
    ⟨(inRuns_guard P ride _ _).2 (Or.inl ((inRuns_runsE _ _).2 h1)), (inRuns_runsE _ _).2 h2⟩,
    fun c hc r hr n h1 h2 h3 => hE n
      ⟨(inRuns_guard P ride _ _).2 (Or.inr ⟨c, (inRuns_runsE _ _).2 hc, r, hr, h1, h2⟩),
        (inRuns_runsE _ _).2 h3⟩⟩

/-- guardApartB accepts if no coin of the base field is spent, no spent coin is known, and no coin
that is tied to a spent coin is known. -/
theorem guardApart_of {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}
    (hF : noFB (Bk.spentBy o p) = true)
    (hU : Disjoint (eAll (Bk.spentBy o p)) (eAll (Bk.knownBy ord o p)))
    (hT : ∀ c ∈ eAll (Bk.spentBy o p), ∀ r ∈ coinGuard P ride c, ∀ n, r.1 ≤ n → n < r.1 + r.2 →
      n ∉ eAll (Bk.knownBy ord o p)) : guardApartB P ride Bk ord o p = true := by
  simp only [guardApartB, spentApartB, Bool.and_eq_true]
  refine ⟨⟨apartF_of_noF hF _, (apartRunsB_iff _ _).2 ?_⟩, apartF_of_noF hF _,
    (apartRunsB_iff _ _).2 ?_⟩
  · rintro n ⟨h1, h2⟩
    exact Finset.disjoint_left.1 hU ((inRuns_runsE _ _).1 h1) ((inRuns_runsE _ _).1 h2)
  · rintro n ⟨h1, h2⟩
    have h2' := (inRuns_runsE _ _).1 h2
    rcases (inRuns_guard P ride _ _).1 h1 with h | ⟨c, hc, r, hr, h3, h4⟩
    · exact Finset.disjoint_left.1 hU ((inRuns_runsE _ _).1 h) h2'
    · exact hT c ((inRuns_runsE _ _).1 hc) r hr n h3 h4 h2'

/-- **The two parts accept at an address exactly if the address meets the condition on a
spender.** -/
theorem spenderOk_iff {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr} :
    (spenderFitsB P ride Bk o p = true ∧ guardApartB P ride Bk ord o p = true) ↔
      SpenderClearAny P ride Bk ord o p := by
  constructor
  · rintro ⟨hf, hg⟩
    obtain ⟨hU, hT⟩ := guardApart_spec hg
    unfold spenderFitsB at hf
    simp only [Bool.or_eq_true, Bool.and_eq_true, List.isEmpty_iff] at hf
    rcases hf with (h0 | ⟨⟨h1, h2⟩, h3⟩) | h4
    · exact Or.inl h0
    · refine Or.inr (Or.inl ⟨fAll_of_test h1, fun n hn => ?_, apart_of_test h3, hU,
        fun k j hk hr ha hj hs => ?_⟩)
      · obtain ⟨k, hk, hb⟩ := List.any_eq_true.1 (allE_spec h2 hn)
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
          Option.isNone_iff_eq_none] at hb
        exact ⟨k, List.mem_range.1 hk, hb.1.1.1, hb.1.1.2, mem_freeNo P ride hb.1.2 hb.2⟩
      · have hj' := lt_of_mem_freeNo P ride hj
        refine ⟨fun i hi => hT _ hs (padNo P ride k i, 1)
          (guard_free P ride hk hr ha hj' (List.mem_append_left _
            (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩))) _ (Nat.le_refl _)
            (Nat.lt_succ_self _), fun q hq => ⟨?_, ?_⟩⟩
        · exact hT _ hs _ (guard_free P ride hk hr ha hj' (List.mem_append_right _
            (List.mem_cons_self ..))) _ (tail_in_run P ride hq).1 (tail_in_run P ride hq).2
        · exact hT _ hs _ (guard_free P ride hk hr ha hj' (List.mem_append_right _
            (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) _ (tail_in_run P ride hq).1
            (tail_in_run P ride hq).2
    · obtain ⟨k, R, e, hk, hr, hs, hc, hst⟩ := foldShape_spec P ride h4
      refine Or.inr (Or.inr ⟨⟨k, R, e, hk, hr, hs, hc, hst, fun r hr' q hq => ?_⟩, hU⟩)
      have hce : e.count.e = R.count := congrArg Due.e hc
      have hpos : 0 < R.count := Nat.succ_pos _
      have hm : maskStart P ride k ∈ eAll (Bk.spentBy o p) := by
        rw [hs, eAll_one]
        exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
      exact hT _ hm _ (guard_ride P ride hk hr (Nat.le_refl _) (by omega) hr') _
        (tail_in_run P ride hq).1 (tail_in_run P ride hq).2
  · rintro (h0 | hM | hF)
    · refine ⟨by unfold spenderFitsB; rw [h0]; rfl, guardApart_of (by rw [h0]; rfl) ?_ ?_⟩
      · rw [h0]
        exact Finset.disjoint_empty_left _
      · intro c hc
        rw [h0] at hc
        exact absurd hc (Finset.notMem_empty c)
    · have ht := test_of_mask P ride hM
      simp only [maskB, Bool.and_eq_true] at ht
      obtain ⟨⟨⟨⟨t1, t2⟩, t3⟩, -⟩, -⟩ := ht
      refine ⟨by
        unfold spenderFitsB
        rw [t1, t2, t3]
        simp, guardApart_of t1 hM.unknown fun c hc r hr n h1 h2 => ?_⟩
      obtain ⟨k, hk, hcase⟩ := guard_cases P ride hr
      rcases hcase with ⟨hrk, ha, g1, g2, hmem⟩ | ⟨R, hrk, g1, g2, -⟩
      · have ec : maskStart P ride k + (c - maskStart P ride k) = c := by omega
        have hcl := hM.clear k (c - maskStart P ride k) hk hrk ha
          (by rw [ec]; exact mem_freeNo P ride g1 g2) (by rw [ec]; exact hc)
        rcases List.mem_append.1 hmem with hp | ht'
        · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
          have hn : n = padNo P ride k i := by
            have a1 : padNo P ride k i ≤ n := h1
            have a2 : n < padNo P ride k i + 1 := h2
            omega
          rw [hn]
          exact hcl.1 i (List.mem_range.1 hi)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht'
          rcases ht' with rfl | rfl
          · obtain ⟨q, hq, rfl⟩ := in_tailRun P ride h1 h2
            exact (hcl.2 q hq).1
          · obtain ⟨q, hq, rfl⟩ := in_tailRun P ride h1 h2
            exact (hcl.2 q hq).2
      · exfalso
        obtain ⟨k', -, hr', ha', hfree⟩ := hM.free c hc
        unfold freeNo at hfree
        obtain ⟨t, ht', rfl⟩ := Finset.mem_image.1 hfree
        have hlt := free_lt _ _ _ t (Nat.pos_of_ne_zero ha') (Finset.mem_range.1 ht')
        have e := own_apart P ride (k := k) (k' := k') g1 (by rw [mask_some P ride hrk]; exact g2)
          (Nat.le_add_right _ _) (by rw [mask_none P ride hr']; exact Nat.add_lt_add_left hlt _)
        rw [e, hr'] at hrk
        cases hrk
    · obtain ⟨k, R, e, hk, hr, hs, hc, hst, htl⟩ := hF.one
      have hce : e.count.e = R.count := congrArg Due.e hc
      have hcf : e.count.f = 0 := congrArg Due.f hc
      refine ⟨by
        unfold spenderFitsB
        rw [hs, foldShape_of P ride hk hr hc hst]
        simp, guardApart_of (by rw [hs]; simp [noFB, hcf]) hF.unknown
          fun c hc' r hr' n h1 h2 => ?_⟩
      rw [hs, eAll_one] at hc'
      have hc2 := Finset.mem_Ico.1 hc'
      have c1 : maskStart P ride k ≤ c := by omega
      have c2 : c < maskStart P ride k + (stepsOf P.codes (shapeAt P k) (ride k)).mask := by
        rw [mask_some P ride hr]
        omega
      obtain ⟨k', -, hcase⟩ := guard_cases P ride hr'
      rcases hcase with ⟨hrk, ha, g1, g2, -⟩ | ⟨R', hrk, g1, g2, ρ, hρ, rfl⟩
      · exfalso
        have hlt := free_lt (shapeAt P k').maskRows (maskCodeAt P k').ell (shapeAt P k').answers
          (c - maskStart P ride k') (Nat.pos_of_ne_zero ha) (by omega)
        have e' := own_apart P ride (k := k) (k' := k') c1 c2 g1
          (by rw [mask_none P ride hrk]; omega)
        rw [← e', hr] at hrk
        cases hrk
      · have e' := own_apart P ride (k := k) (k' := k') c1 c2 g1
          (by rw [mask_some P ride hrk]; exact g2)
        subst e'
        obtain ⟨q, hq, rfl⟩ := in_tailRun P ride h1 h2
        exact htl ρ hρ q hq

/-- **The two-part test accepts at an owner exactly if the book meets BookClearAny there.** -/
theorem ownerOkB_iff {Bk : ProverCoinCounts} {ord : List Place} {o : Addr} :
    ownerOkB P ride Bk ord o = true ↔ BookClearAny P ride Bk ord o := by
  rw [← bookClearAnyB_iff]
  unfold ownerOkB ownerFitsB bookClearAnyB
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, List.isEmpty_iff]
  constructor
  · rintro ⟨⟨hw, hf⟩, hg⟩
    refine ⟨hw, fun p hp => (spenderClearAnyB_iff P ride).2 ?_⟩
    rcases hg p hp with h0 | h1
    · exact Or.inl h0
    · exact spenderOk_iff.1 ⟨hf p hp, h1⟩
  · rintro ⟨hw, h⟩
    have h' := fun p hp => spenderOk_iff.2 ((spenderClearAnyB_iff P ride).1 (h p hp))
    exact ⟨⟨hw, fun p hp => (h' p hp).1⟩, fun p hp => Or.inr (h' p hp).2⟩

/-! ## The same in terms of coins, and what it gives at the addresses that spend -/

/-- No number is in a run of a and in a run of b. -/
def ApartRuns (a b : List (Nat × Nat)) : Prop := ∀ n, ¬ (InRuns a n ∧ InRuns b n)

/-- At an owner and an address, for a guard g on runs of the extension field: nothing that the
address spends is known there, and nothing in the guard of what it spends. The clause on the base
field appears in both halves, because the guard is the identity on base-field runs. -/
def GuardClearE (g : List (Nat × Nat) → List (Nat × Nat)) (Bk : ProverCoinCounts) (ord : List Place)
    (o p : Addr) : Prop :=
  (ApartRuns (runsF (Bk.spentBy o p)) (runsF (Bk.knownBy ord o p)) ∧
      ApartRuns (runsE (Bk.spentBy o p)) (runsE (Bk.knownBy ord o p))) ∧
    ApartRuns (runsF (Bk.spentBy o p)) (runsF (Bk.knownBy ord o p)) ∧
      ApartRuns (g (runsE (Bk.spentBy o p))) (runsE (Bk.knownBy ord o p))

/-- guardApartB accepts exactly where GuardClearE holds at the guard sendGuardE. -/
theorem guardApartB_iff {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr} :
    guardApartB P ride Bk ord o p = true ↔ GuardClearE (sendGuardE P ride) Bk ord o p := by
  simp only [guardApartB, spentApartB, Bool.and_eq_true, apartRunsB_iff]
  exact Iff.rfl

/-- BookClearAny implies the premises on the book at each address that spends. -/
theorem spendersClearAny_of_bookClearAny {Bk : ProverCoinCounts} {ord : List Place} {o : Addr}
    (h : BookClearAny P ride Bk ord o) : SpendersClearAny P ride Bk ord o :=
  fun p _ => ⟨withinAt_of_takes h.1 ord p, h.2 p⟩

/-- If no spending entry of the book has the owner o, no address spends anything of o's coins. -/
theorem spentBy_nil_of_no_spending {Bk : ProverCoinCounts} {o : Addr}
    (h : ∀ e ∈ Bk.ahead, e.once = true → e.owner ≠ o) (p : Addr) : Bk.spentBy o p = [] := by
  refine List.filter_eq_nil_iff.2 fun e he hc => ?_
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  exact h e he hc.2 hc.1.1

/-- **If ownerFitsB accepts, and GuardClearE holds at each address that has a spending entry on the
owner's coins, then the premises on the book hold at each such address (SpendersClearAny).** -/
theorem spendersClearAny_of_guard {Bk : ProverCoinCounts} {ord : List Place} {o : Addr}
    (hf : ownerFitsB P ride Bk o = true)
    (hg : ∀ p, Bk.spentBy o p ≠ [] → GuardClearE (sendGuardE P ride) Bk ord o p) :
    SpendersClearAny P ride Bk ord o := by
  unfold ownerFitsB at hf
  rw [Bool.and_eq_true, List.all_eq_true] at hf
  intro p hp
  have hmem : p ∈ Bk.ahead.map (·.spender) := by
    by_contra hn
    exact hp (spentBy_nil_of_not hn)
  exact ⟨withinAt_of_takes (within_of_test P ride hf.1) ord p,
    spenderOk_iff.1 ⟨hf.2 p hmem, guardApartB_iff.2 (hg p hp)⟩⟩

/-! ## The two parts at three small examples -/

namespace Small

/-- At the book in which three addresses each spend one free mask entry, the test accepts. -/
theorem guardTried_filled :
    ownerOkB placeThreeFree noRide (bookWith (filledAt 1 2 3)) [] smallAddr = true := by
  decide +kernel

/-- With the pad carried to the last spender: what is spent still fits. -/
theorem guardTried_padKnown_fits :
    ownerFitsB placeThreeFree noRide
      (bookWith (filledAt 1 2 3 ++ [carryE "pad" 4 1 spenderThree])) smallAddr = true := by
  decide +kernel

/-- A negative test: with the pad carried to the last spender, guardApartB rejects there. -/
theorem guardTried_padKnown_guard :
    guardApartB placeThreeFree noRide
      (bookWith (filledAt 1 2 3 ++ [carryE "pad" 4 1 spenderThree])) [] smallAddr spenderThree =
        false := by
  decide +kernel

/-- A negative test: with the mask row's tail carried to the last spender the guard rejects. -/
theorem guardTried_tailKnown_guard :
    guardApartB placeThreeFree noRide
      (bookWith (filledAt 1 2 3 ++ [carryE "tail" 5 1 spenderThree])) [] smallAddr spenderThree =
        false := by
  decide +kernel

/-- A control: it checks that the guard does not reject a coin that is tied to no spent coin. With
the main row's tail carried to the last spender, guardApartB accepts. -/
theorem guardTried_mainTailKnown_guard :
    guardApartB placeThreeFree noRide
      (bookWith (filledAt 1 2 3 ++ [carryE "main tail" 0 1 spenderThree])) [] smallAddr
        spenderThree = true := by
  decide +kernel

/-- A negative test: with the pad spent in place of a free entry, what is spent does not fit. -/
theorem guardTried_padSpent_fits :
    spenderFitsB placeThreeFree noRide
      (bookWith (filledAt 1 2 4 ++ [carryE "free" 3 1 spenderThree])) smallAddr spenderThree =
        false := by
  decide +kernel

/-- A negative test at two mask rows: an entry of the first row is spent and that row's tail is
carried to the spender. -/
theorem guardTried_ownRow :
    guardApartB placeTwoRowsFree noRide
      (bookWith [spendE "entry" 3 1 spenderThree, carryE "tail" 5 1 spenderThree]) [] smallAddr
        spenderThree = false := by
  decide +kernel

/-- A negative test at two mask rows: an entry of the first row is spent and the tail of the second
row, which holds the pad, is carried to the spender. -/
theorem guardTried_padRow :
    guardApartB placeTwoRowsFree noRide
      (bookWith [spendE "entry" 3 1 spenderThree, carryE "tail" 6 1 spenderThree]) [] smallAddr
        spenderThree = false := by
  decide +kernel

/-- A control at two mask rows: it checks that the first row's tail is not tied to an entry of the
second row. An entry of the second row is spent and the first row's tail is carried to the
spender. -/
theorem guardTried_otherRow :
    guardApartB placeTwoRowsFree noRide
      (bookWith [spendE "entry" 2 1 spenderThree, carryE "tail" 5 1 spenderThree]) [] smallAddr
        spenderThree = true := by
  decide +kernel

/-- At a table sent along: its three coefficient coins in one spending entry fit. -/
theorem guardTried_ride_fits :
    spenderFitsB placeRiderFirst riderFirst
      (bookWith [spendE "table" 0 3 spenderThree, carryE "tail" 3 1 spenderThree]) smallAddr
        spenderThree = true := by
  decide +kernel

/-- A negative test at a table sent along: its coefficient coins are spent and its tail is carried
to the spender. -/
theorem guardTried_ride_tail :
    guardApartB placeRiderFirst riderFirst
      (bookWith [spendE "table" 0 3 spenderThree, carryE "tail" 3 1 spenderThree]) [] smallAddr
        spenderThree = false := by
  decide +kernel

/-- A control at a table sent along: it checks that another message's tail is not tied to the
table's coins. The other message's mask tail is carried to the spender. -/
theorem guardTried_ride_other :
    guardApartB placeRiderFirst riderFirst
      (bookWith [spendE "table" 0 3 spenderThree, carryE "tail" 9 1 spenderThree]) [] smallAddr
        spenderThree = true := by
  decide +kernel

end Small

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.meets_coin
#print axioms OnBytes.SendSim.At.apartRunsB_iff
#print axioms OnBytes.SendSim.At.inRuns_runsE
#print axioms OnBytes.SendSim.At.apartF_of_noF
#print axioms OnBytes.SendSim.At.inRuns_guard
#print axioms OnBytes.SendSim.At.guard_prefix
#print axioms OnBytes.SendSim.At.guard_nil
#print axioms OnBytes.SendSim.At.in_tailRun
#print axioms OnBytes.SendSim.At.tail_in_run
#print axioms OnBytes.SendSim.At.guard_free
#print axioms OnBytes.SendSim.At.guard_ride
#print axioms OnBytes.SendSim.At.guard_cases
#print axioms OnBytes.SendSim.At.own_end
#print axioms OnBytes.SendSim.At.own_apart
#print axioms OnBytes.SendSim.At.mask_none
#print axioms OnBytes.SendSim.At.mask_some
#print axioms OnBytes.SendSim.At.foldShape_spec
#print axioms OnBytes.SendSim.At.foldShape_of
#print axioms OnBytes.SendSim.At.guardApart_spec
#print axioms OnBytes.SendSim.At.guardApart_of
#print axioms OnBytes.SendSim.At.spenderOk_iff
#print axioms OnBytes.SendSim.At.ownerOkB_iff
#print axioms OnBytes.SendSim.At.guardApartB_iff
#print axioms OnBytes.SendSim.At.spendersClearAny_of_guard
#print axioms OnBytes.SendSim.At.Small.guardTried_filled
#print axioms OnBytes.SendSim.At.Small.guardTried_padKnown_fits
#print axioms OnBytes.SendSim.At.Small.guardTried_padKnown_guard
#print axioms OnBytes.SendSim.At.Small.guardTried_tailKnown_guard
#print axioms OnBytes.SendSim.At.Small.guardTried_mainTailKnown_guard
#print axioms OnBytes.SendSim.At.Small.guardTried_padSpent_fits
#print axioms OnBytes.SendSim.At.Small.guardTried_ownRow
#print axioms OnBytes.SendSim.At.Small.guardTried_padRow
#print axioms OnBytes.SendSim.At.Small.guardTried_otherRow
#print axioms OnBytes.SendSim.At.Small.guardTried_ride_fits
#print axioms OnBytes.SendSim.At.Small.guardTried_ride_tail
#print axioms OnBytes.SendSim.At.Small.guardTried_ride_other
#print axioms OnBytes.SendSim.At.spendersClearAny_of_bookClearAny
#print axioms OnBytes.SendSim.At.spentBy_nil_of_no_spending
