-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Rows14.lean: kind K14: THE KIND's FOUR OWN ROWS AS ROWS WITHOUT
LETTERS (Unlettered, Honest/Thread/Rows.lean): at each of the places 1, 4, 7, 8 the place, the part
WITH ITS SIMULATOR, the kind's On and bud (which ask nothing). They are made where sixOf
(Honest/K14/Six.lean) makes the halves, by a call of the same tests (rejection); and the rows'
halves ARE the kind's four own halves among what sixOf makes. Definitions with code, and eight
statements with their proofs. Nothing here is noncomputable.

  ownRows         the rows, of the public data: three quiet rows, and the row of "SPLIT" where the
                  shape splits
  ownRows_half    **their halves are the kind's own halves** (proverSidesOfSharedRounds, Honest/K14/Parts.lean)
  k14Rows         the rows, or the message of the test that rejects
  k14Rows_own, k14Rows_six   **where k14Rows returns rows, they are ownRows at the numbers that
                  dataOf makes, and sixOf returns their halves with the two sendings' halves behind
                  them**
  k14Rows_error   the two return an error together, with one message
  sixOf_text      where sixOf returns, what it returns, written out: the two numbers are what
                  roundsInFront says of the list at the places 1 and 7
  k14RowsAt, k14WordAt   the rows as a function of the public part and the ground, general in the
                  two readers that make the plan's parameters and the chain's list of the public
                  part; and why it lays no row, where it lays none
  k14Rows_returns, k14WordAt_none   k14Rows returns just where no test rejects and dataOf returns;
                  k14WordAt says nothing just where the two readers and k14Rows return
  k14RowsAt_eq    **where the readers and k14Rows return: these rows, and sixOf's list is their
                  halves with the two sendings' behind them**

THE TWO SENDINGS HAVE NO ROW HERE: their parts have no simulator in this kind's own text: it comes
with the shared sending's part, once the two sendings are calls of it. So this is FOUR ROWS FOR SIX
HALVES. THE EQUATION ON HALVES IS MET IN THIS KIND's OWN SHARE ALONE: what the frame's own law on
the rows' prover takes at the shared chain (prover_lay_self, Honest/Thread/Rows.lean) is that the
WHOLE chain's halves are the rows' halves: at these four rows alone that is false: it wants the two
sendings' rows behind them (in sixOf's order: 1, 4, 7, 8, then 2, 5) and the rows of the members
behind "SPLIT".

ON sixOf_text. The frame's own filling lays the shared chain's halves by a text of its own
(nowShared, in a file that is not imported here): the two numbers by roundsInFront at the places 1
and 7, then proverSidesOfSharedRounds and proverSidesOfSharedSendings. sixOf_text says that sixOf's list has that form. THE TWO LISTS
ARE ONE ONLY where sixOf returns, at the plan and the list that that filling's own readers make, at
the identity for weights and at its own reader of the index committer's coins; that filling
evaluates none of rejection's three tests. No statement here names it.

What is not claimed. That the two readers return at any public part: no term is typed for them. The
structure Good at any of the rows: Honest/K14/GoodSeated.lean. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.PartsCalls
import Johnson.Desc.ProofFile.Honest.K14.Six
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block)

variable {W₀ Rc Ky X Pb S Cl : Type}

/-- **The kind's own rows**, of the public data. -/
def ownRows (A : Data) (weights : W₀ → Weights) :
    List (Unlettered Empty (Common W₀ Rc Ky) X Pb) :=
  [{ place := place 1, row := quietRow A weights 1, On := k14On, bud := k14Bud },
   { place := place 4, row := quietRow A weights 4, On := k14On, bud := k14Bud },
   { place := place 7, row := quietRow A weights 7, On := k14On, bud := k14Bud }] ++
    if A.S.sharedSplitNeeded then
      [{ place := place 8, row := splitRow A weights, On := k14On, bud := k14Bud }]
    else []

/-- **Their halves are the kind's own halves.** -/
theorem ownRows_half (A : Data) (weights : W₀ → Weights) :
    ((ownRows A weights : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)).map (·.half)) =
      proverSidesOfSharedRounds A weights := by
  rw [halves_eq]
  unfold ownRows
  by_cases h : A.S.sharedSplitNeeded = true
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- **The rows, or the message of the public test that rejects**: sixOf's own tests (rejection,
Honest/K14/Six.lean), called. -/
def k14Rows (P : Desc.K14.P14) (bs : List (Block S Cl)) (weights : W₀ → Weights) :
    Except String (List (Unlettered Empty (Common W₀ Rc Ky) X Pb)) :=
  match rejection P bs with
  | some e => .error e
  | none =>
    match dataOf P.S bs with
    | none => .error "K14: \"LIN point\" or \"LIN zeta\" is not in the list"
    | some d => .ok (ownRows d weights)

/-- Where k14Rows returns rows, they are ownRows at the numbers that dataOf makes. -/
theorem k14Rows_own (P : Desc.K14.P14) (bs : List (Block S Cl)) (weights : W₀ → Weights)
    (rs : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)) (h : k14Rows P bs weights = .ok rs) :
    ∃ d, dataOf P.S bs = some d ∧ rs = ownRows d weights := by
  unfold k14Rows at h
  cases hr : rejection P bs with
  | some e => rw [hr] at h; cases h
  | none =>
    rw [hr] at h
    cases hd : dataOf P.S bs with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      exact ⟨d, rfl, (Except.ok.inj h).symm⟩

/-- **Where k14Rows returns rows, sixOf returns their halves, with the two sendings' halves behind
them.** -/
theorem k14Rows_six (P : Desc.K14.P14) (bs : List (Block S Cl)) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (rs : List (Unlettered Empty (Common W₀ Rc Ky) X Pb))
    (h : k14Rows P bs weights = .ok rs) :
    ∃ d, dataOf P.S bs = some d ∧ rs = ownRows d weights ∧
      sixOf P bs weights rand =
        .ok (rs.map (·.half) ++ proverSidesOfSharedSendings { P := P, atPoint := d.atPoint } weights rand) := by
  unfold k14Rows at h
  unfold sixOf
  cases hr : rejection P bs with
  | some e => rw [hr] at h; cases h
  | none =>
    rw [hr] at h
    cases hd : dataOf P.S bs with
    | none => rw [hd] at h; cases h
    | some d =>
      rw [hd] at h
      obtain rfl := Except.ok.inj h
      exact ⟨d, rfl, rfl, by rw [ownRows_half]⟩

/-- The two return an error together, with one message. -/
theorem k14Rows_error (P : Desc.K14.P14) (bs : List (Block S Cl)) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (e : String) :
    (k14Rows P bs weights : Except String (List (Unlettered Empty (Common W₀ Rc Ky) X Pb))) =
        .error e ↔
      (sixOf P bs weights rand : Except String (List (Placed Empty (Common W₀ Rc Ky) X))) =
        .error e := by
  unfold k14Rows sixOf
  cases rejection P bs with
  | some e' => exact ⟨fun h => (by cases h; rfl), fun h => (by cases h; rfl)⟩
  | none =>
    cases dataOf P.S bs with
    | none => exact ⟨fun h => (by cases h; rfl), fun h => (by cases h; rfl)⟩
    | some d => exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- **Where sixOf returns, what it returns, written out.** -/
theorem sixOf_text (P : Desc.K14.P14) (bs : List (Block S Cl)) (weights : W₀ → Weights)
    (rand : Rc → TableRand) (hs : List (Placed Empty (Common W₀ Rc Ky) X))
    (h : sixOf P bs weights rand = .ok hs) :
    ∃ a z, roundsInFront bs (place 1) = some a ∧ roundsInFront bs (place 7) = some z ∧
      hs = proverSidesOfSharedRounds { S := P.S, atPoint := a, atZeta := z } weights ++
        proverSidesOfSharedSendings { P := P, atPoint := a } weights rand := by
  unfold sixOf at h
  cases hr : rejection P bs with
  | some e => rw [hr] at h; cases h
  | none =>
    rw [hr] at h
    unfold dataOf at h
    cases ha : roundsInFront bs (place 1) with
    | none => rw [ha] at h; cases h
    | some a =>
      cases hz : roundsInFront bs (place 7) with
      | none => rw [ha, hz] at h; cases h
      | some z =>
        rw [ha, hz] at h
        exact ⟨a, z, rfl, rfl, (Except.ok.inj h).symm⟩

/-- **The rows as a function of the public part and the ground.** planAt, listAt: the readers that
make the plan's parameters and the shared chain's list of sub-protocols of the public part. The
ground is not read. NO ROW, IN SILENCE, where a reader returns nothing or k14Rows returns an error:
k14WordAt says why. -/
def k14RowsAt (planAt : Pub → Option Desc.K14.P14) (listAt : Pub → Option (List (Block S Cl)))
    (weights : W₀ → Weights) (Z : Pub) (_ : Ground) :
    List (Unlettered Empty (Common W₀ Rc Ky) X Pb) :=
  match planAt Z, listAt Z with
  | some P, some bs => ((k14Rows P bs weights).toOption).getD []
  | _, _ => []

/-- **Why k14RowsAt lays no row at a public part**; none where it lays the rows. -/
def k14WordAt (planAt : Pub → Option Desc.K14.P14) (listAt : Pub → Option (List (Block S Cl)))
    (Z : Pub) : Option String :=
  match planAt Z, listAt Z with
  | some P, some bs =>
    (rejection P bs).or
      (if (dataOf P.S bs).isNone then some "K14: \"LIN point\" or \"LIN zeta\" is not in the list"
       else none)
  | none, _ => some "K14: the shared chain's own parameters could not be made"
  | _, none => some "K14: the shared chain's list of sub-protocols could not be made"

/-- **k14RowsAt, where the two readers and k14Rows return: these rows; and sixOf at what the readers
made returns their halves with the two sendings' halves behind them.** -/
theorem k14RowsAt_eq (planAt : Pub → Option Desc.K14.P14)
    (listAt : Pub → Option (List (Block S Cl))) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (Z : Pub) (G : Ground) (P : Desc.K14.P14) (bs : List (Block S Cl))
    (rs : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)) (hP : planAt Z = some P)
    (hl : listAt Z = some bs) (h : k14Rows P bs weights = .ok rs) :
    k14RowsAt planAt listAt weights Z G = rs ∧
      ∃ d, dataOf P.S bs = some d ∧
        sixOf P bs weights rand =
          .ok ((k14RowsAt planAt listAt weights Z G :
              List (Unlettered Empty (Common W₀ Rc Ky) X Pb)).map (·.half) ++
            proverSidesOfSharedSendings { P := P, atPoint := d.atPoint } weights rand) := by
  have e : (k14RowsAt planAt listAt weights Z G :
      List (Unlettered Empty (Common W₀ Rc Ky) X Pb)) = rs := by
    unfold k14RowsAt
    rw [hP, hl]
    show ((k14Rows P bs weights).toOption).getD [] = rs
    rw [h]
    rfl
  obtain ⟨d, hd, -, h6⟩ := k14Rows_six P bs weights rand rs h
  exact ⟨e, d, hd, by rw [e]; exact h6⟩

/-- k14Rows returns just where none of the tests rejects and dataOf returns. -/
theorem k14Rows_returns (P : Desc.K14.P14) (bs : List (Block S Cl)) (weights : W₀ → Weights) :
    (∃ rs : List (Unlettered Empty (Common W₀ Rc Ky) X Pb), k14Rows P bs weights = .ok rs) ↔
      rejection P bs = none ∧ (dataOf P.S bs).isNone = false := by
  unfold k14Rows
  cases rejection P bs with
  | some e => simp
  | none =>
    cases dataOf P.S bs with
    | none => simp
    | some d => simp

/-- **k14WordAt says nothing just where the two readers and k14Rows return.** -/
theorem k14WordAt_none (planAt : Pub → Option Desc.K14.P14)
    (listAt : Pub → Option (List (Block S Cl))) (weights : W₀ → Weights) (Z : Pub) :
    k14WordAt planAt listAt Z = none ↔
      ∃ P bs, planAt Z = some P ∧ listAt Z = some bs ∧
        ∃ rs : List (Unlettered Empty (Common W₀ Rc Ky) X Pb), k14Rows P bs weights = .ok rs := by
  unfold k14WordAt
  cases hP : planAt Z with
  | none => exact ⟨fun h => (by cases h), fun ⟨_, _, h, _⟩ => (by cases h)⟩
  | some P =>
    cases hl : listAt Z with
    | none => exact ⟨fun h => (by cases h), fun ⟨_, _, _, h, _⟩ => (by cases h)⟩
    | some bs =>
      show ((rejection P bs).or
        (if (dataOf P.S bs).isNone then some "K14: \"LIN point\" or \"LIN zeta\" is not in the list"
         else none)) = none ↔ _
      constructor
      · intro h
        refine ⟨P, bs, rfl, rfl, (k14Rows_returns P bs weights).2 ?_⟩
        revert h
        cases rejection P bs <;> cases dataOf P.S bs <;> simp
      · rintro ⟨P', bs', h1, h2, h3⟩
        obtain rfl := Option.some.inj h1
        obtain rfl := Option.some.inj h2
        obtain ⟨a, b⟩ := (k14Rows_returns P bs weights).1 h3
        rw [a, b]
        rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.k14Rows_own
#print axioms ProofFile.Honest.K14.k14Rows_returns
#print axioms ProofFile.Honest.K14.k14WordAt_none
#print axioms ProofFile.Honest.K14.sixOf_text
#print axioms ProofFile.Honest.K14.k14Rows_error
#print axioms ProofFile.Honest.K14.k14RowsAt_eq
#print axioms ProofFile.Honest.K14.ownRows_half
#print axioms ProofFile.Honest.K14.k14Rows_six
