-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/GoodSeated.lean: kind K14: CONDITIONAL. THE FIELDS fits, exact AND
fresh OF THE STRUCTURE Good (Honest/Side.lean) AT THE SIDE THAT Side.seated MAKES OF ONE OF THE
KIND's FOUR OWN ROWS AND A LIST OF SUB-PROTOCOLS THAT BEGINS WITH THE SHARED CHAIN's FRONT
SUB-PROTOCOL AND EIGHT MORE (FlatOf, Johnson/Desc/K14/Honest/FlatForm.lean), WHERE THE EIGHT ARE
THOSE THAT blocks P RETURNS AT A PLAN P (hb) AND THE BOOK PASSES noneSpent AT THE ROW's PLACE (hB):
so the side's sub-protocol is THE MEMBER AS THE LIST HOLDS IT, not the library's bare one; what is
stated of that member is that it is like the library's own (Like). What
Honest/K14/GoodCalls.lean and PartsCalls.lean ask of a side's sub-protocol (its place; one declared
round; one empty list of oracle messages; what the round cuts) IS SHOWN HERE, from what the
library's eight declare (declares3, declares_split: Honest/K14/Debts.lean). No argument over a
distribution is made here.

ON exact. good_quiet and good_split show ExactMember (Honest/Small/Field.lean): the condition asked
at EVERY value of the state's field opened. Good's own field exact has one premise more, on that
field and on the letter pre; it is had from ExactMember by exactAt_of_exact (the same file), at
every pre: one premise is thrown away. pre is tied to no description; at each pre good_rows says no
more than the law on ExactMember beneath.

hb IS A PREMISE OF EVERY STATEMENT HERE BUT place_of_row AND ownRows_four: FlatOf by itself holds of
any eight sub-protocols; that the eight are the plan's is blocks P = some [b1, …, b8]. In the list
below «such a list» means: FlatOf with hb.

  seated_own      the side that Side.seated makes at the places 1, 4, 7, 8 of such a list has the
                  row that it was handed, and its sub-protocol is like the library's own (Like)
  seated_some     Side.seated returns there: so the laws' premise on it can be met
  good_quiet      **fits, exact, fresh at the places 1, 4, 7**
  good_split      **fits, exact, fresh at the place 8**, where the shape splits
  good_rows       **the structure Good as one term, at each row of ownRows (Honest/K14/Rows14.lean),
                  at the row's own place, On and bud, AT EVERY pre**: WITH THE LETTERS A AND B
                  «False»: ITS FIELDS plays AND acc HOLD FROM A FALSE PREMISE AND SHOW NOTHING
  place_of_row, ownRows_four   a row's place is one of the four; where the shape splits the rows'
                  places are the four, in order
  good_rows_some  good_rows with the side that Side.seated returns
  k14Rows_flat    at such a list k14Rows returns where its two tests on the shapes accept

THE LIMITS OF Honest/K14/GoodCalls.lean ON WHAT exact AND fresh SAY HOLD HERE: its head is to be
read with this file: at a quiet row two constants are compared; at "SPLIT" the spender's half alone;
fresh is true and empty; whatever that head lists as not shown there is not shown here either, but
for what it asks of a side's sub-protocol. WHAT IS NEW HERE IS ON PUBLIC DATA ALONE: from declares3
and declares_split (Honest/K14/Debts.lean), places4 (PaidAt.lean), places2 (DataMade.lean),
send_declares (SendingsPlay.lean), fits_quiet and fits_split (PartsCalls.lean). The falls fs (the
frame's tests at which a member's own step may reject at a state that a coin has made) are free: the
three fields read none. The premise on the book (noneSpent at the part 0 of the place) stays a
premise.

What is not claimed. Good's fields plays and acc at letters that say something. That a book passes
noneSpent. good_rows speaks of ownRows at ANY public data A with A.S = P.S: the two rounds' numbers
are free; the rows as k14Rows returns them are ownRows at dataOf's numbers (k14Rows_own,
Honest/K14/Rows14.lean; 0 and 6 at such a list: k14Rows_flat). At a bare list of the form FlatOf the
member is only like the library's own (Like); it is that one, carried to the file's type of claims,
at the carried chain's flat list. Where these laws are called in this tree: at any letters whose
list is the carried shared chain's flat list at the IOP as written in Lean
(Honest/K14/GoodSeatedShared.lean), and in Honest/K14/AtFilling.lean and AtFillingMore.lean. Calls
at a small shape and at what onlineDescription returns are in files that are not part of this tree. What
stands in the list behind its ninth member is free: a second member at one of the four places is
never seen. The two sendings' rows. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.GoodCalls
import Johnson.Desc.ProofFile.Honest.K14.DataMade
import Johnson.Desc.ProofFile.Honest.K14.Rows14

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open Desc.K14 (P14 St blocks)
open Desc.K14.Honest (FlatOf Like)
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent exactAt_of_exact)

variable {Cl X Pb W₀ Rc Ky V W : Type}

/-- **What Side.seated makes at the kind's four own places** of a list that begins with the shared
chain's front sub-protocol and the eight (FlatOf), where the eight are those that blocks P returns
(hb): the row as handed; the sub-protocol like the library's own (Like). -/
theorem seated_own {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {P : P14}
    {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (row : List (Part V W X × Sim Pb)) (fs : List (Fall St)) (σ : Side St Cl V W X Pb) :
    (Side.seated xs (place 1) row fs = some σ → σ.row = row ∧ Like σ.block b1) ∧
      (Side.seated xs (place 4) row fs = some σ → σ.row = row ∧ Like σ.block b4) ∧
      (Side.seated xs (place 7) row fs = some σ → σ.row = row ∧ Like σ.block b7) ∧
      (Side.seated xs (place 8) row fs = some σ → σ.row = row ∧ Like σ.block b8) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  obtain ⟨p1, p4, p7, p8⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p3, p6⟩ := places2 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, pU, -, pO⟩ := send_declares P 0 b1 b2 b3 b4 b5 b6 b7 b8 hb
  have q0 : x0.place = ⟨2, none, 0, .frame⟩ := l0.place
  have q1 := l1.place.trans p1
  have q2 := l2.place.trans pU
  have q3 := l3.place.trans p3
  have q4 := l4.place.trans p4
  have q5 := l5.place.trans pO
  have q6 := l6.place.trans p6
  have q7 := l7.place.trans p7
  have q8 := l8.place.trans p8
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · unfold Side.seated at h
    rw [List.find?_cons_of_neg (by rw [q0]; decide),
      List.find?_cons_of_pos (by rw [q1]; decide)] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, l1⟩
  · unfold Side.seated at h
    rw [List.find?_cons_of_neg (by rw [q0]; decide), List.find?_cons_of_neg (by rw [q1]; decide),
      List.find?_cons_of_neg (by rw [q2]; decide), List.find?_cons_of_neg (by rw [q3]; decide),
      List.find?_cons_of_pos (by rw [q4]; decide)] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, l4⟩
  · unfold Side.seated at h
    rw [List.find?_cons_of_neg (by rw [q0]; decide), List.find?_cons_of_neg (by rw [q1]; decide),
      List.find?_cons_of_neg (by rw [q2]; decide), List.find?_cons_of_neg (by rw [q3]; decide),
      List.find?_cons_of_neg (by rw [q4]; decide), List.find?_cons_of_neg (by rw [q5]; decide),
      List.find?_cons_of_neg (by rw [q6]; decide),
      List.find?_cons_of_pos (by rw [q7]; decide)] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, l7⟩
  · unfold Side.seated at h
    rw [List.find?_cons_of_neg (by rw [q0]; decide), List.find?_cons_of_neg (by rw [q1]; decide),
      List.find?_cons_of_neg (by rw [q2]; decide), List.find?_cons_of_neg (by rw [q3]; decide),
      List.find?_cons_of_neg (by rw [q4]; decide), List.find?_cons_of_neg (by rw [q5]; decide),
      List.find?_cons_of_neg (by rw [q6]; decide), List.find?_cons_of_neg (by rw [q7]; decide),
      List.find?_cons_of_pos (by rw [q8]; decide)] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, l8⟩

variable {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains} {P : P14}
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}

/-- CONDITIONAL. **fits, exact and fresh at the side that Side.seated makes of a quiet row**, at the
places 1, 4, 7: under FlatOf, hb (the eight are those that blocks P returns) and hB (the book passes
noneSpent at the part 0 of the place). For exact what is shown is ExactMember (the head: ON exact).
-/
theorem good_quiet (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (A : Data) (weights : W₀ → Weights)
    (i : Nat) (hi : i = 1 ∨ i = 4 ∨ i = 7) (fs : List (Fall St))
    (σ : Side St Cl Empty (Common W₀ Rc Ky) X Pb)
    (hσ : Side.seated xs (place i) (quietRow A weights i) fs = some σ)
    (φ : Face Empty (Common W₀ Rc Ky) Pb) (Bk : ProverCoinCounts) (ord : List Place) (chain firstTree : Nat)
    (hB : noneSpent Bk { place := place i, part := 0 } = true) :
    σ.fits = true ∧ (∀ u ∈ σ.members, ExactMember φ σ chain firstTree k14On k14Bud u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord k14Bud u := by
  obtain ⟨c1, c4, c7, r1, o1, r4, o4, r7, o7⟩ := declares3 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨p1, p4, p7, -⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨s1, s4, s7, -⟩ := seated_own F hb (quietRow A weights i) fs σ
  have key : ∃ d : Fmt.DeclaredRound, σ.row = quietRow A weights i ∧ σ.block.place = place i ∧
      σ.block.rounds = [d] ∧ σ.block.oracles = [[]] ∧ d.items = [] := by
    rcases hi with rfl | rfl | rfl
    · obtain ⟨e, l⟩ := s1 hσ
      exact ⟨_, e, l.place.trans p1, l.rounds.trans r1, l.oracles.trans o1, c1⟩
    · obtain ⟨e, l⟩ := s4 hσ
      exact ⟨_, e, l.place.trans p4, l.rounds.trans r4, l.oracles.trans o4, c4⟩
    · obtain ⟨e, l⟩ := s7 hσ
      exact ⟨_, e, l.place.trans p7, l.rounds.trans r7, l.oracles.trans o7, c7⟩
  obtain ⟨d, hrow, hp, hr, ho, hd⟩ := key
  exact ⟨fits_quiet A weights i σ hrow hp (by rw [hr]; rfl) (by rw [ho]; rfl),
    exact_quiet A weights i φ σ chain firstTree hrow d hr ho hd,
    fresh_quiet A weights i φ σ Bk ord hrow d hr ho (by rw [hp]; exact hB)⟩

/-- CONDITIONAL. **fits, exact and fresh at the side that Side.seated makes of the row of "SPLIT"**,
where the shape splits: under FlatOf, hb (the eight are those that blocks P returns) and hB (the
book passes noneSpent at the part 0 of the place 8). For exact what is shown is ExactMember (the
head: ON exact). -/
theorem good_split (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (A : Data) (weights : W₀ → Weights) (fs : List (Fall St))
    (σ : Side St Cl Empty (Common W₀ Rc Ky) X Pb)
    (hσ : Side.seated xs (place 8) (splitRow A weights) fs = some σ)
    (φ : Face Empty (Common W₀ Rc Ky) Pb) (Bk : ProverCoinCounts) (ord : List Place) (chain firstTree : Nat)
    (hB : noneSpent Bk { place := place 8, part := 0 } = true) :
    σ.fits = true ∧ (∀ u ∈ σ.members, ExactMember φ σ chain firstTree k14On k14Bud u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord k14Bud u := by
  obtain ⟨c8, r8, o8⟩ := declares_split P b1 b2 b3 b4 b5 b6 b7 b8 hb hS
  obtain ⟨-, -, -, p8⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  obtain ⟨-, -, -, s8⟩ := seated_own F hb (splitRow A weights) fs σ
  obtain ⟨hrow, l⟩ := s8 hσ
  have hp := l.place.trans p8
  have hr := l.rounds.trans r8
  have ho := l.oracles.trans o8
  exact ⟨fits_split A weights σ hrow hp (by rw [hr]; rfl) (by rw [ho]; rfl),
    exact_split A weights φ σ chain firstTree hrow _ hr ho c8,
    fresh_split A weights φ σ Bk ord hrow _ hr ho (by rw [hp]; exact hB)⟩

/-- **Side.seated returns at such a list** (FlatOf with hb), at each of the kind's four own places,
whatever the row and the falls: so the premise hσ of this file's laws can be met. -/
theorem seated_some (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (i : Nat)
    (hi : i = 1 ∨ i = 4 ∨ i = 7 ∨ i = 8) (row : List (Part V W X × Sim Pb))
    (fs : List (Fall St)) : ∃ σ, Side.seated xs (place i) row fs = some σ := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, -, l1, -, -, l4, -, -, l7, l8⟩ := F
  obtain ⟨p1, p4, p7, p8⟩ := places4 P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have hx : ∃ x ∈ x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl,
      (x.place == place i) = true := by
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨x1, by simp, by rw [l1.place, p1]; exact beq_self_eq_true _⟩
    · exact ⟨x4, by simp, by rw [l4.place, p4]; exact beq_self_eq_true _⟩
    · exact ⟨x7, by simp, by rw [l7.place, p7]; exact beq_self_eq_true _⟩
    · exact ⟨x8, by simp, by rw [l8.place, p8]; exact beq_self_eq_true _⟩
  obtain ⟨x, hm, hp⟩ := hx
  unfold Side.seated
  cases hf : List.find? (fun b => b.place == place i)
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl) with
  | none => exact absurd hp (by simpa using List.find?_eq_none.1 hf x hm)
  | some y => exact ⟨_, rfl⟩

/-- CONDITIONAL. **The structure Good AS ONE TERM, at each row of ownRows (Honest/K14/Rows14.lean),
at any public data A with A.S = P.S**, at the row's own place, On and bud, at the side that
Side.seated makes, at whatever falls, AT EVERY pre: under FlatOf, hb and hB (the book passes
noneSpent at the part 0 of the row's place). THE LETTERS A AND B ARE «False»: SO THE FIELDS plays
AND acc HOLD FROM A FALSE PREMISE AND SHOW NOTHING: they are laid so that the term has the frame's
form; what is shown is fits, exact and fresh. pre is tied to no description; at each pre this says
no more than the law on ExactMember beneath (good_quiet, good_split): the field exact is had from it
by exactAt_of_exact. -/
theorem good_rows (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (A : Data) (hA : A.S = P.S)
    (weights : W₀ → Weights) (r : Unlettered Empty (Common W₀ Rc Ky) X Pb)
    (hr : r ∈ (ownRows A weights : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)))
    (fs : List (Fall St)) (σ : Side St Cl Empty (Common W₀ Rc Ky) X Pb)
    (hσ : Side.seated xs r.place r.row fs = some σ) (φ : Face Empty (Common W₀ Rc Ky) Pb)
    (Bk : ProverCoinCounts) (ord : List Place) (chain firstTree : Nat)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (hB : noneSpent Bk { place := r.place, part := 0 } = true) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On
      r.bud := by
  have three : σ.fits = true ∧ (∀ u ∈ σ.members, ExactMember φ σ chain firstTree r.On r.bud u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord r.bud u := by
    unfold ownRows at hr
    rcases List.mem_append.1 hr with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl
      · exact good_quiet F hb A weights 1 (Or.inl rfl) fs σ hσ φ Bk ord chain firstTree hB
      · exact good_quiet F hb A weights 4 (Or.inr (Or.inl rfl)) fs σ hσ φ Bk ord chain firstTree
          hB
      · exact good_quiet F hb A weights 7 (Or.inr (Or.inr rfl)) fs σ hσ φ Bk ord chain firstTree
          hB
    · by_cases hS : A.S.sharedSplitNeeded = true
      · rw [if_pos hS] at h
        obtain rfl := List.mem_singleton.1 h
        exact good_split F hb (hA ▸ hS) A weights fs σ hσ φ Bk ord chain firstTree hB
      · rw [if_neg hS] at h
        cases h
  exact { fits := three.1, plays := fun _ _ _ _ _ h => h.elim, acc := fun _ _ _ _ _ h => h.elim
          exact := fun u hu => exactAt_of_exact pre (three.2.1 u hu), fresh := three.2.2 }

/-- A row of ownRows stands at one of the kind's four own places. -/
theorem place_of_row (A : Data) (weights : W₀ → Weights)
    (r : Unlettered Empty (Common W₀ Rc Ky) X Pb)
    (hr : r ∈ (ownRows A weights : List (Unlettered Empty (Common W₀ Rc Ky) X Pb))) :
    ∃ i, (i = 1 ∨ i = 4 ∨ i = 7 ∨ i = 8) ∧ r.place = place i := by
  unfold ownRows at hr
  rcases List.mem_append.1 hr with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨1, Or.inl rfl, rfl⟩
    · exact ⟨4, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨7, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
  · split at h
    · obtain rfl := List.mem_singleton.1 h
      exact ⟨8, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
    · cases h

/-- Where the shape splits the rows' places are the four, in order: the places 1, 4, 7 and 8. An
equation on the places alone. -/
theorem ownRows_four (A : Data) (weights : W₀ → Weights) (hS : A.S.sharedSplitNeeded = true) :
    (ownRows A weights : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)).map (·.place) =
      [place 1, place 4, place 7, place 8] := by
  unfold ownRows
  rw [if_pos hS]
  rfl

/-- CONDITIONAL. **good_rows with the side that Side.seated returns, AT THE LETTERS False**, under
good_rows's premises (FlatOf, hb, A.S = P.S, hB): at each row of ownRows and every pre: there is
such a side, and Good holds of it as one term whose fields plays and acc hold from a false premise
and show nothing. pre is tied to no description; at each pre this says no more than the law on
ExactMember beneath (good_quiet, good_split). -/
theorem good_rows_some (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (A : Data) (hA : A.S = P.S)
    (weights : W₀ → Weights) (r : Unlettered Empty (Common W₀ Rc Ky) X Pb)
    (hr : r ∈ (ownRows A weights : List (Unlettered Empty (Common W₀ Rc Ky) X Pb)))
    (fs : List (Fall St)) (φ : Face Empty (Common W₀ Rc Ky) Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (hB : noneSpent Bk { place := r.place, part := 0 } = true) :
    ∃ σ, Side.seated xs r.place r.row fs = some σ ∧
      Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On
        r.bud := by
  obtain ⟨i, hi, e⟩ := place_of_row A weights r hr
  obtain ⟨σ, hσ⟩ := seated_some F hb i hi r.row fs
  rw [← e] at hσ
  exact ⟨σ, hσ, good_rows F hb A hA weights r hr fs σ hσ φ Bk ord chain firstTree pre hB⟩

/-- At such a list (FlatOf with hb) k14Rows returns, with the numbers 0 and 6, where its two tests
on the shapes (linOk, sendingsFit) accept: the third test and dataOf follow from the list's form. -/
theorem k14Rows_flat (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hok : OnBytes.linOk P.codes P.S = true) (hfit : sendingsFit P = true)
    (weights : W₀ → Weights) :
    (k14Rows P xs weights : Except String (List (Unlettered Empty (Common W₀ Rc Ky) X Pb))) =
      .ok (ownRows { S := P.S, atPoint := 0, atZeta := 6 } weights) := by
  unfold k14Rows rejection
  rw [hok, hfit, tiedTo_flat F hb, dataOf_flat F hb]
  rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.place_of_row
#print axioms ProofFile.Honest.K14.ownRows_four
#print axioms ProofFile.Honest.K14.good_rows_some
#print axioms ProofFile.Honest.K14.k14Rows_flat
#print axioms ProofFile.Honest.K14.seated_some
#print axioms ProofFile.Honest.K14.good_rows
#print axioms ProofFile.Honest.K14.seated_own
#print axioms ProofFile.Honest.K14.good_quiet
#print axioms ProofFile.Honest.K14.good_split
