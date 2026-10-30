-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MaskWhole.lean: kind K14: **WHERE THE SHORT PUBLIC TEST maskWholeB
(Honest/K14/MaskWholeTest.lean) ON A BOOK's ENTRIES AT THE PART AT "send o_u", THE PUBLIC TEST ON
THE ORDER OF PLACES behindSpenderB (Honest/K14/OwnerOrder.lean) AT THE FIRST MASK's WHOLE RUN, AND
THREE TESTS ON THE PLAN ACCEPT: THE OWNER's TEST maskOwner (Honest/K14/MaskOwner.lean) ACCEPTS, AT
EVERY ORDER OF PLACES**; and where the book fails none of its own tests (ProverCoinCounts.clauses,
Honest/Frame.lean) the test on the order accepts at the order of places of the IOP as written in
Lean (below: the description). Statements with their proofs; no definition. No maker of a book is
opened. On lists of entries, numbers and an order of places alone: no distribution occurs.

  maskRun_holds   the first mask's whole run begins with its 2 k + 1 coefficients
  mask_runsFit    o_u's whole run is apart from the guard's run; the first mask's holds a spent coin
  maskFits_of_whole   the owner's further test (maskOwnerFits): runIs is the short test's first
                  half; the count: the spent run and both stretches lie within the part's count
                  (mask_room, Honest/K14/MaskOfRows.lean; mask_count, Honest/K14/MaskLaw.lean)
  maskOwner_ok_of_order   **the owner's test accepts, at every order of places at which the test on
                  the order accepts**: by guardClear_of_order; none of the book's own tests is used
  mask_known_at_fold   **in the frame's own term**: what else of the owner's coins is handed to a
                  part that spends of them, or to a part in front of it (ProverCoinCounts.knownBy,
                  Honest/Frame.lean), has o_u's whole run: by known_of_order
  mask_knownBelow, maskGuard_by_bridge   so the test knownBelow accepts (Honest/K14/FreshDefs.lean),
                  and the guard's clause follows a second way: by maskBridge
                  (Honest/K14/MaskLaw.lean)
  maskOwner_ok_of_whole   **where the book fails none of its own tests**, maskWholeB accepts and the
                  three tests on the plan accept: the owner's test accepts, AT THE DESCRIPTION's OWN
                  ORDER OF PLACES (orderOf F): a corollary, by behindSpender_of_word
                  (Honest/K14/OwnerWhole.lean)

What is not claimed. THAT ANY MAKER's BOOK PASSES maskWholeB OR behindSpenderB:
Honest/K14/BookAtU.lean, under premises. These statements are called here at no book. Nothing on
what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.MaskWholeTest
import Johnson.Desc.ProofFile.Honest.K14.OwnerWhole
import Johnson.Desc.ProofFile.Honest.K14.MaskOfRows
import Johnson.Desc.ProofFile.Honest.K14.MaskLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (FileDescription Place)
open Johnson.Prover.Send (shapeAt)

/-- The first mask's whole run begins with its 2 k + 1 coefficients. -/
theorem maskRun_holds (A : SendPub) (s : OnBytes.Params.IoppStage)
    (hs : A.P.S.testU.head? = some s) : 2 * s.k + 1 ≤ (maskRun A).2 := by
  show _ ≤ dueOf (jobU A).Q.codes (shapeAt (jobU A).Q 1) ((jobU A).sort 1)
  rw [u_sort1 A s hs 0]
  exact Nat.le_add_right _ _

/-- o_u's whole run is apart from the guard's run; the first mask's holds a spent coin. -/
theorem mask_runsFit (A : SendPub) (k : Nat) (hk : 2 * k + 1 ≤ (maskRun A).2) :
    runsFit (maskRun A).1 (maskRun A).2 (maskFirstCoin A) (2 * k + 1) (maskStretches A) = true := by
  have e : (maskRun A).1 = maskFirstCoin A := rfl
  simp only [runsFit, maskStretches, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_self_eq_true, true_and, Bool.or_eq_true, Bool.not_eq_true', e]
  refine ⟨Or.inl ?_, Or.inr ?_⟩
  · simp [meets]
  · simp only [meets, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    omega

/-- The owner's further test, from the short test and the three tests on the plan. -/
theorem maskFits_of_whole {B : ProverCoinCounts} (A : SendPub) (s : OnBytes.Params.IoppStage)
    (hW : wholeOrSpent ⟨0, maskFirstCoin A⟩ ⟨0, 2 * s.k + 1⟩ (maskStretches A) B
      { place := sendPlace 2, part := 0 } = true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head? = some s) :
    maskOwnerFits A s.k B { place := sendPlace 2, part := 0 } = true := by
  have hroom := mask_room A s hfit hm hs
  obtain ⟨-, hcount⟩ := mask_count A hfit hm
  have e1 : (maskRun A).1 = maskFirstCoin A := rfl
  unfold wholeOrSpent at hW
  rw [Bool.and_eq_true] at hW
  obtain ⟨hS, hA⟩ := hW
  have h1 : runIs B { place := sendPlace 2, part := 0 } (maskFirstCoin A) (2 * s.k + 1) = true := by
    unfold runIs
    cases hsp : spendersOf B { place := sendPlace 2, part := 0 } with
    | nil => rfl
    | cons e l =>
      cases l with
      | cons _ _ => rw [hsp] at hS; cases hS
      | nil =>
        rw [hsp] at hS
        exact hS
  have h2 : withinCount (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort) B
      { place := sendPlace 2, part := 0 } = true := by
    have hT : (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort).e =
        (maskRun A).1 + (maskRun A).2 := hcount
    have hT0 : (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort).f = 0 := rfl
    have hR : maskFirstCoin A + (2 * s.k + 1) ≤
        (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort).e := hroom
    unfold withinCount
    rw [List.all_eq_true]
    intro e he
    by_cases ho : (e.owner == ({ place := sendPlace 2, part := 0 } : Addr)) = true
    · rw [ho]
      have hin := List.all_eq_true.1 hA e (List.mem_filter.2 ⟨he, ho⟩)
      cases hc : e.once with
      | true =>
        have hmem : e ∈ spendersOf B { place := sendPlace 2, part := 0 } :=
          List.mem_filter.2 ⟨he, by rw [hc, ho]; rfl⟩
        cases hsp : spendersOf B { place := sendPlace 2, part := 0 } with
        | nil => rw [hsp] at hmem; cases hmem
        | cons x l =>
          cases l with
          | cons _ _ => rw [hsp] at hS; cases hS
          | nil =>
            rw [hsp] at hS hmem
            obtain rfl := List.mem_singleton.1 hmem
            simp only [Bool.and_eq_true, beq_iff_eq] at hS
            simp only [hS.1, hS.2, hT0, Bool.not_true, Bool.false_or, Bool.and_eq_true,
              decide_eq_true_eq]
            exact ⟨Nat.le_refl _, hR⟩
      | false =>
        rw [hc, Bool.false_or] at hin
        have hmem := List.contains_iff_mem.1 hin
        simp only [maskStretches, List.mem_cons, List.not_mem_nil, or_false,
          Prod.mk.injEq] at hmem
        rcases hmem with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · simp only [q1, q2, hT0, Bool.not_true, Bool.false_or, Bool.and_eq_true,
            decide_eq_true_eq]
          refine ⟨Nat.le_refl _, ?_⟩
          omega
        · simp only [q1, q2, hT0, Bool.not_true, Bool.false_or, Bool.and_eq_true,
            decide_eq_true_eq]
          refine ⟨Nat.le_refl _, ?_⟩
          rw [hT, e1]
    · simp [ho]
  unfold maskOwnerFits
  rw [h1, hfit, hm, h2, hs]
  simp

/-- **The test for the part at "send o_u" accepts**, at every order of places at which the test on
the order accepts. No test of the book's own is asked. -/
theorem maskOwner_ok_of_order {B : ProverCoinCounts} {ord : List Place} (A : SendPub)
    (hW : maskWholeB A B = true)
    (hO : behindSpenderB (maskRun A).1 (maskRun A).2 B ord { place := sendPlace 2, part := 0 } =
      true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true) :
    (maskOwner A).ok B ord { place := sendPlace 2, part := 0 } = true := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hs
  have hk : maskRounds A = s.k := by
    unfold maskRounds
    rw [hs]
    rfl
  have hlen := maskRun_holds A s hs
  have e1 : (maskRun A).1 = maskFirstCoin A := rfl
  unfold maskWholeB at hW
  rw [hk] at hW
  have hG := guardClear_of_order (first := (maskRun A).1) (len := (maskRun A).2) hW
    (Nat.le_refl _) (by rw [e1]; omega) (fun m hm => by
      simp only [maskStretches, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl <;> rfl) hO
  unfold maskOwner
  rw [hk]
  unfold OwnerTest.ok
  rw [Bool.and_eq_true]
  refine ⟨maskFits_of_whole A s hW hfit hm hs, List.all_eq_true.2 fun p _ => ?_⟩
  by_cases hp : B.spentBy { place := sendPlace 2, part := 0 } p = []
  · rw [hp]
    rfl
  · rw [Bool.or_eq_true]
    exact Or.inr ((guardClearB_iff _ _ _ _ _).2 (hG p hp))

/-- **What is known at a part that spends, in the frame's own term**: every other entry that hands
coins of the owner to a part that spends of them, or to a part in front of that part, has o_u's
whole run. -/
theorem mask_known_at_fold {B : ProverCoinCounts} {ord : List Place} (A : SendPub)
    (hW : maskWholeB A B = true)
    (hO : behindSpenderB (maskRun A).1 (maskRun A).2 B ord { place := sendPlace 2, part := 0 } =
      true)
    (hs : A.P.S.testU.head?.isSome = true) :
    ∀ e ∈ spendersOf B { place := sendPlace 2, part := 0 },
      ∀ x ∈ B.knownBy ord { place := sendPlace 2, part := 0 } e.spender,
        x.start = ⟨0, 0⟩ ∧ x.count = ⟨0, maskFirstCoin A⟩ := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hs
  have hlen := maskRun_holds A s hs
  have e1 : (maskRun A).1 = maskFirstCoin A := rfl
  intro e he x hx
  obtain ⟨-, hmem, hno⟩ := known_of_order hW hO e he x hx
  simp only [maskStretches, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨q1, q2⟩ | ⟨q1, q2⟩
  · exact ⟨q1, q2⟩
  · exfalso
    have hmeet : meets x.start.e x.count.e (maskRun A).1 (maskRun A).2 = true := by
      rw [q1, q2, e1]
      simp only [meets, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
      omega
    rw [hmeet] at hno
    cases hno

/-- **So the test knownBelow accepts**: what is known at a spender ends at the first mask's first
coin. -/
theorem mask_knownBelow {B : ProverCoinCounts} {ord : List Place} (A : SendPub) (hW : maskWholeB A B = true)
    (hO : behindSpenderB (maskRun A).1 (maskRun A).2 B ord { place := sendPlace 2, part := 0 } =
      true)
    (hs : A.P.S.testU.head?.isSome = true) :
    knownBelow B ord { place := sendPlace 2, part := 0 } (maskFirstCoin A) = true := by
  unfold knownBelow
  refine List.all_eq_true.2 fun e he => List.all_eq_true.2 fun x hx => ?_
  obtain ⟨q1, q2⟩ := mask_known_at_fold A hW hO hs e he x hx
  rw [q1, q2]
  simp

/-- **The guard's clause a second way**: by knownBelow and maskBridge. -/
theorem maskGuard_by_bridge {B : ProverCoinCounts} {ord : List Place} (A : SendPub)
    (hW : maskWholeB A B = true)
    (hO : behindSpenderB (maskRun A).1 (maskRun A).2 B ord { place := sendPlace 2, part := 0 } =
      true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true) :
    ∀ p, B.spentBy { place := sendPlace 2, part := 0 } p ≠ [] →
      GuardClear (maskGuard A) B ord { place := sendPlace 2, part := 0 } p := by
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 hs
  have hk : maskRounds A = s.k := by
    unfold maskRounds
    rw [hs']
    rfl
  have hW' := hW
  unfold maskWholeB at hW'
  rw [hk] at hW'
  exact maskBridge A s.k B ord _ (maskOwnerFits_gives (maskFits_of_whole A s hW' hfit hm hs')).1
    (mask_knownBelow A hW hO hs)

/-- **Where the book fails none of its own tests, the short test accepts and the three tests on the
plan accept: the owner's test accepts**, at the description's own order of places. -/
theorem maskOwner_ok_of_whole {Xi : Type} {F : FileDescription Xi} {B : ProverCoinCounts} (A : SendPub)
    (h : B.word F = none) (hW : maskWholeB A B = true)
    (hfit : sendingsFit A.P = true) (hm : A.P.S.masksAhead = true)
    (hs : A.P.S.testU.head?.isSome = true) :
    (maskOwner A).ok B (orderOf F) { place := sendPlace 2, part := 0 } = true := by
  obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 hs
  have hk : maskRounds A = s.k := by
    unfold maskRounds
    rw [hs']
    rfl
  have hW' := hW
  unfold maskWholeB at hW'
  rw [hk] at hW'
  exact maskOwner_ok_of_order A hW
    (behindSpender_of_word h hW' (mask_runsFit A s.k (maskRun_holds A s hs'))) hfit hm hs

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.maskRun_holds
#print axioms ProofFile.Honest.K14.mask_runsFit
#print axioms ProofFile.Honest.K14.maskFits_of_whole
#print axioms ProofFile.Honest.K14.maskOwner_ok_of_order
#print axioms ProofFile.Honest.K14.mask_known_at_fold
#print axioms ProofFile.Honest.K14.mask_knownBelow
#print axioms ProofFile.Honest.K14.maskGuard_by_bridge
#print axioms ProofFile.Honest.K14.maskOwner_ok_of_whole
