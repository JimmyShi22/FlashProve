-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AtFilling.lean: kind K14: THE SHARED CHAIN's HALVES AS THE FRAME's
FILLING LAYS THEM (nowShared, Honest/SharedChainProverSides.lean) AGAINST WHAT THIS KIND's OWN MAKER RETURNS
(sixOf, Honest/K14/Six.lean), AT THE FILLING's OWN READERS: the plan's parameters by p14At, the
chain's list by the library's onlineSharedChain. Definitions with code, and statements with their
proofs.

  randNow         the filling's reader of the index committer's coins: those of the plan's item
  readers_at      where the library makes the places' numbers N of the public part: p14At returns
                  qAt Z N, and onlineSharedChain the library's own value for the shared chain there
                  (seatN Z N, of the structure SharedSeat)
  flatOf_plain    where the library makes its eight sub-protocols of P: at every chains, tests and
                  closing, the flat list of chainOf, not carried to another type of claims (as seatN
                  Z N holds it), has the form FlatOf
  MadeAt Z N      the library makes its eight sub-protocols of qAt Z N, and the shape splits
  made_plain, made_carried   MadeAt FROM EITHER OF TWO LISTS' TESTS ON THE PLAN: the plain flat list
                  of seatN Z N; or the list carried to another type of claims, which is the list of
                  a thread's letters
  now_of_numbers, numbers_of_data   what nowShared returns where the readers return and the two
                  places are found; the two numbers of dataOf are these places' numbers
  now_of_six      **where sixOf returns a list at these readers, nowShared returns that very list**
  now_made        **where the library makes N of Z, under MadeAt: nowShared returns proverSidesOfSharedRounds at the
                  numbers 0 and 6, then the two sendings' halves at 0**: no test on the shapes is
                  asked: it evaluates none
  six_now         **under MadeAt and the two tests on the shapes: sixOf, at qAt Z N and the plain
                  flat list of seatN Z N, returns that same term**; it names nowShared nowhere;
                  these two arguments are the filling's own readers' values where the library makes
                  N of Z
  rowsNow         the kind's four rows as a function of the public part and the ground, AT THE
                  FILLING's OWN READERS: a term, with code
  rowsNowWord     why rowsNow lays no row at a public part; none where it lays the rows
  rowsNow_eq      **under now_made's and six_now's premises rowsNow's value is ownRows at 0 and 6**:
                  the rows with their simulators, On and bud, of which Honest/K14/GoodSeated.lean
                  speaks
  rowsNow_half    so they stand at the places 1, 4, 7, 8, and nowShared's list is their halves with
                  the two sendings' halves behind them
  rowsNow_none    WHERE THE LIBRARY MAKES N OF Z AND A TEST ON THE SHAPES REJECTS: rowsNow lays NO
                  row and rowsNowWord returns a message. (Under MadeAt nowShared lays its six halves
                  there all the same, by now_made: no statement joins the two.)
  halves_now      **where the library makes N of Z: at letters whose halves are nowShared's list,
                  under MadeAt: K14Asks' fields halves and sends** (Honest/K14/Asks.lean), at the
                  identity for weights and at randNow, at the public data planData (whose two
                  numbers are 0 and 6 by its own text)
  halves_shared   the same (where the library makes N of Z) where the letters' list of sub-protocols
                  is the carried chain's and every member of it passes its test on the plan

WHY rowsNow IS NOT A CALL OF k14RowsAt (Honest/K14/Rows14.lean). That function's second reader
returns a list of sub-protocols at ONE type of states; the library's structure SharedSeat has its
type of states as a field, so a reader off onlineSharedChain does not type there. rowsNow matches on the
two readers and calls k14Rows, which is general in that type.

LIMITS. (1) nowShared is, by its own file's head, the halves that are written there:
now_of_numbers, now_of_six, now_made and rowsNow_half say that its list IS this kind's six halves
and nothing else. IF A HALF FOR A LATER MEMBER OF THE CHAIN IS ADDED THERE, THESE STATEMENTS BECOME
FALSE AND THIS FILE NO LONGER COMPILES; six_now, which names sixOf alone, would stand; halves_now's
two ends (membership; no place twice) could still hold, by another proof. (2) THE OTHER WAY DOES NOT
HOLD: nowShared evaluates none of sixOf's three tests: it CAN return where sixOf returns an error;
that rows and halves then part is now_made beside rowsNow_none, joined by no statement; where one of
the two places is not in the list both return an error. (3) FOUR ROWS FOR SIX HALVES: rowsNow has no
row for the two sendings, and none for the members behind "SPLIT". (4) halves_now's premise on the
letters' halves is a premise: L is any letters; nothing here ties a thread's own halves to
nowShared's list. (5) rowsNow returns a list: where it lays no row its type has no room for a
message; the message is rowsNowWord's, and no type makes a caller ask it. rowsNow_none says that
there is a message, not which; by the text it is one of two written strings. That rowsNowWord
returns nothing JUST where rowsNow lays the rows is typed at rowsNow_eq's case alone. (6) MadeAt's
second half (the shape splits) is not spent in now_made, six_now and rowsNow_eq.

What is not claimed. That the premises hold at any public file. That a filling's field for the
shared chain is nowShared's list: the filling itself is not imported (its file imports the other
kinds' files). K14Asks' other fields. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SharedChainProverSides
import Johnson.Desc.ProofFile.Honest.K14.GoodSeatedShared
import Johnson.Desc.ProofFile.Honest.K14.Asks
import Johnson.Desc.ProofFile.Honest.K14.Thread2Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open Desc.K14 (P14 St blocks chainOf frontBlock)
open Desc.K14.Honest (FlatOf Like)
open Desc.K14.Law (seatN blocks_said split_at_the_chain eight_of_pass own_pass_carried
  split_given)

/-- The filling's reader of the index committer's coins: those of the plan's item. -/
def randNow (P : P14) (rc : IndexCommitterCoins) : TableRand := ⟨(rc P.item).pad, (rc P.item).tail⟩

/-- Where the library makes the places' numbers: what the filling's two readers return. -/
theorem readers_at (Z : Pub) (N : H2U.Places4) (hN : H2U.placesOfMade Z.made = .ok N) :
    p14At Z = some (qAt Z N) ∧ onlineSharedChain Z = some (seatN Z N) := by
  constructor
  · unfold p14At
    rw [hN]
  · show Desc.K14.sharedSeatAt Z = _
    unfold Desc.K14.sharedSeatAt
    rw [hN]
    rfl

/-- Where the library makes its eight sub-protocols of P (hb): at every chains, tests and closing,
the shared chain's flat list, not carried to another type of claims, has the form FlatOf. -/
theorem flatOf_plain (c : OnBytes.Model.Verify.Chains) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (ts : List (Block St Unit))
    (lst : List (Block St Unit) → Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    FlatOf (chainOf c P ts lst).blocksInOrder c b1 b2 b3 b4 b5 b6 b7 b8 := by
  have hc : chainOf c P ts lst =
      { first := frontBlock c, front := [], links := []
        back := [b1, b2, b3, b4, b5, b6, b7, b8] ++ ts
        last := lst ([b1, b2, b3, b4, b5, b6, b7, b8] ++ ts) } := by
    simp [chainOf, Desc.K14.blocksOr, hb]
  rw [hc]
  exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩

/-- **The library makes its eight sub-protocols of the plan's parameters at Z and N, and the shape
splits.** -/
def MadeAt (Z : Pub) (N : H2U.Places4) : Prop :=
  (∃ b1 b2 b3 b4 b5 b6 b7 b8, blocks (qAt Z N) = some [b1, b2, b3, b4, b5, b6, b7, b8]) ∧
    (qAt Z N).S.sharedSplitNeeded = true

variable (Z : Pub) (N : H2U.Places4)

/-- MadeAt, where every member of the PLAIN flat list of seatN Z N passes its test on the plan. -/
theorem made_plain (hp : ∀ b ∈ (seatN Z N).chain.blocksInOrder, b.planOk = true) : MadeAt Z N := by
  have hp' : ∀ b ∈ (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder, b.planOk = true := hp
  obtain ⟨l, hb⟩ := blocks_said Z.p.chains (qAt Z N) (tests N) last hp'
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := Desc.K14.Law.eight (qAt Z N) l hb
  exact ⟨⟨_, _, _, _, _, _, _, _, hb⟩,
    split_at_the_chain Z.p.chains (qAt Z N) (tests N) last hp'⟩

/-- MadeAt, where every member of the list CARRIED to another type of claims passes its test on the
plan: the list of a thread's letters. -/
theorem made_carried {Cl' : Type}
    (hp : ∀ b ∈ ((chainOf Z.p.chains (qAt Z N) (tests N) last).retype (Cl' := Cl')).blocksInOrder,
      b.planOk = true) : MadeAt Z N := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ :=
    eight_of_pass Z.p.chains (qAt Z N) (tests N) last hp
  have h8 : b8.planOk = true := by
    have key := own_pass_carried Z.p.chains (qAt Z N) (tests N) last hp
    unfold Desc.K14.blocksOr at key
    rw [hb] at key
    exact key b8 (by simp)
  exact ⟨⟨_, _, _, _, _, _, _, _, hb⟩, split_given _ b1 b2 b3 b4 b5 b6 b7 b8 hb h8⟩

/-- What nowShared returns, where the two readers return and the two places are found in the
list. -/
theorem now_of_numbers (P : P14) (s : SharedSeat) (hP : p14At Z = some P)
    (hs : onlineSharedChain Z = some s) (a z : Nat)
    (ha : roundsInFront s.chain.blocksInOrder (place 1) = some a)
    (hz : roundsInFront s.chain.blocksInOrder (place 7) = some z) :
    nowShared Z = .ok (proverSidesOfSharedRounds { S := P.S, atPoint := a, atZeta := z } id ++
      proverSidesOfSharedSendings { P := P, atPoint := a } id (randNow P)) := by
  unfold nowShared sharedInFront
  rw [hP, hs]
  show (due? _ (roundsInFront s.chain.blocksInOrder (place 1))).bind _ = _
  rw [ha]
  show (due? _ (roundsInFront s.chain.blocksInOrder (place 7))).bind _ = _
  rw [hz]
  rfl

/-- **Where sixOf returns a list at the filling's own readers, nowShared returns that very
list.** -/
theorem now_of_six (P : P14) (s : SharedSeat) (hP : p14At Z = some P)
    (hs : onlineSharedChain Z = some s)
    (l : List (Placed Empty (Common Weights IndexCommitterCoins TableKey) Unit))
    (h : sixOf P s.chain.blocksInOrder id (randNow P) = .ok l) : nowShared Z = .ok l := by
  obtain ⟨a, z, ha, hz, rfl⟩ := sixOf_text P s.chain.blocksInOrder id (randNow P) l h
  exact now_of_numbers Z P s hP hs a z ha hz

/-- The two numbers that dataOf lays are the two places' numbers of rounds in front. -/
theorem numbers_of_data {S Cl : Type} (shape : OnBytes.Params.LinShape) (bs : List (Block S Cl))
    (a z : Nat) (h : dataOf shape bs = some { S := shape, atPoint := a, atZeta := z }) :
    roundsInFront bs (place 1) = some a ∧ roundsInFront bs (place 7) = some z := by
  unfold dataOf at h
  cases ha : roundsInFront bs (place 1) with
  | none => rw [ha] at h; cases h
  | some a' =>
    rw [ha] at h
    cases hz : roundsInFront bs (place 7) with
    | none => rw [hz] at h; cases h
    | some z' =>
      rw [hz] at h
      have e : ({ S := shape, atPoint := a', atZeta := z' } : Data) =
          { S := shape, atPoint := a, atZeta := z } := Option.some.inj h
      exact ⟨congrArg some (congrArg Data.atPoint e), congrArg some (congrArg Data.atZeta e)⟩

/-- **Where the library makes N of Z, under MadeAt: what nowShared returns.** No test on the shapes
is asked: nowShared evaluates none. -/
theorem now_made (hN : H2U.placesOfMade Z.made = .ok N) (hM : MadeAt Z N) :
    nowShared Z = .ok (proverSidesOfSharedRounds (planData (qAt Z N)) id ++
      proverSidesOfSharedSendings { P := qAt Z N, atPoint := 0 } id (randNow (qAt Z N))) := by
  obtain ⟨hP, hs⟩ := readers_at Z N hN
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩, -⟩ := hM
  obtain ⟨ha, hz⟩ := numbers_of_data (qAt Z N).S
    (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder 0 6
    (dataOf_flat (flatOf_plain Z.p.chains (qAt Z N) b1 b2 b3 b4 b5 b6 b7 b8 (tests N) last hb)
      hb (qAt Z N).S)
  exact now_of_numbers Z (qAt Z N) (seatN Z N) hP hs 0 6 ha hz

/-- **Under MadeAt and the two tests on the shapes: what sixOf returns at qAt Z N and the plain flat
list of seatN Z N**: the term that stands in now_made. N is any here: the two arguments are the
filling's own readers' values where the library makes N of Z (readers_at). -/
theorem six_now (hM : MadeAt Z N)
    (hok : OnBytes.linOk (qAt Z N).codes (qAt Z N).S = true)
    (hfit : sendingsFit (qAt Z N) = true) :
    sixOf (qAt Z N) (seatN Z N).chain.blocksInOrder id (randNow (qAt Z N)) =
      .ok (proverSidesOfSharedRounds (planData (qAt Z N)) id ++
        proverSidesOfSharedSendings { P := qAt Z N, atPoint := 0 } id (randNow (qAt Z N)) :
          List (Placed Empty (Common Weights IndexCommitterCoins TableKey) Unit)) := by
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩, -⟩ := hM
  exact sixOf_flat (flatOf_plain Z.p.chains (qAt Z N) b1 b2 b3 b4 b5 b6 b7 b8 (tests N) last hb)
    hb hok hfit id (randNow (qAt Z N))

/-- **The kind's four rows as a function of the public part and the ground, at the filling's own
readers.** The ground is not read. NO ROW where a reader returns nothing or k14Rows returns an
error: rowsNowWord says why. -/
def rowsNow {Pb : Type} (Z : Pub) (_ : Ground) :
    List (Unlettered Empty (Common Weights IndexCommitterCoins TableKey) Unit Pb) :=
  match p14At Z, onlineSharedChain Z with
  | some P, some s => ((k14Rows P s.chain.blocksInOrder id).toOption).getD []
  | _, _ => []

/-- **Why rowsNow lays no row at a public part**; none where it lays the rows. The text of
k14WordAt (Honest/K14/Rows14.lean), at these two readers. -/
def rowsNowWord (Z : Pub) : Option String :=
  match p14At Z, onlineSharedChain Z with
  | some P, some s =>
    (rejection P s.chain.blocksInOrder).or
      (if (dataOf P.S s.chain.blocksInOrder).isNone then
        some "K14: \"LIN point\" or \"LIN zeta\" is not in the list"
       else none)
  | none, _ => some "K14: the shared chain's own parameters could not be made"
  | _, none => some "K14: the shared chain's list of sub-protocols could not be made"

/-- **Under now_made's and six_now's premises rowsNow's value is ownRows at the numbers 0 and 6, and
rowsNowWord returns nothing.** -/
theorem rowsNow_eq {Pb : Type} (G : Ground) (hN : H2U.placesOfMade Z.made = .ok N)
    (hM : MadeAt Z N) (hok : OnBytes.linOk (qAt Z N).codes (qAt Z N).S = true)
    (hfit : sendingsFit (qAt Z N) = true) :
    (rowsNow Z G : List (Unlettered Empty (Common Weights IndexCommitterCoins TableKey) Unit Pb)) =
        ownRows (planData (qAt Z N)) id ∧ rowsNowWord Z = none := by
  obtain ⟨hP, hs⟩ := readers_at Z N hN
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩, -⟩ := hM
  have Fl := flatOf_plain Z.p.chains (qAt Z N) b1 b2 b3 b4 b5 b6 b7 b8 (tests N) last hb
  constructor
  · unfold rowsNow
    rw [hP, hs]
    have hk : (k14Rows (qAt Z N) (seatN Z N).chain.blocksInOrder id :
        Except String (List (Unlettered Empty (Common Weights IndexCommitterCoins TableKey) Unit Pb))) =
        .ok (ownRows { S := (qAt Z N).S, atPoint := 0, atZeta := 6 } id) :=
      k14Rows_flat Fl hb hok hfit id
    exact congrArg (fun x => (x.toOption).getD []) hk
  · unfold rowsNowWord
    rw [hP, hs]
    show ((rejection (qAt Z N) (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder).or
      (if (dataOf (qAt Z N).S (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder).isNone then _
       else none)) = none
    have hr : rejection (qAt Z N) (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder = none := by
      unfold rejection
      rw [hok, hfit, tiedTo_flat Fl hb]
      rfl
    rw [hr, dataOf_flat Fl hb]
    rfl

/-- **So they stand at the places 1, 4, 7, 8, and nowShared's list is their halves with the two
sendings' halves behind them.** -/
theorem rowsNow_half {Pb : Type} (G : Ground) (hN : H2U.placesOfMade Z.made = .ok N)
    (hM : MadeAt Z N) (hok : OnBytes.linOk (qAt Z N).codes (qAt Z N).S = true)
    (hfit : sendingsFit (qAt Z N) = true) :
    ((rowsNow Z G : List (Unlettered Empty (Common Weights IndexCommitterCoins TableKey) Unit Pb)).map
        (·.place) = [place 1, place 4, place 7, place 8]) ∧
      nowShared Z = .ok ((rowsNow Z G :
          List (Unlettered Empty (Common Weights IndexCommitterCoins TableKey) Unit Pb)).map (·.half) ++
        proverSidesOfSharedSendings { P := qAt Z N, atPoint := 0 } id (randNow (qAt Z N))) := by
  rw [(rowsNow_eq Z N G hN hM hok hfit).1, ownRows_half]
  exact ⟨ownRows_four _ id hM.2, now_made Z N hN hM⟩

/-- **Where the library makes N of Z and a test on the shapes rejects: rowsNow lays no row, and
rowsNowWord returns a message.** Of nowShared and of sixOf nothing is said here. -/
theorem rowsNow_none {Pb : Type} (G : Ground) (hN : H2U.placesOfMade Z.made = .ok N)
    (h : OnBytes.linOk (qAt Z N).codes (qAt Z N).S = false ∨ sendingsFit (qAt Z N) = false) :
    (rowsNow Z G : List (Unlettered Empty (Common Weights IndexCommitterCoins TableKey) Unit Pb)) = [] ∧
      (rowsNowWord Z).isSome = true := by
  obtain ⟨hP, hs⟩ := readers_at Z N hN
  have hr : ∃ e, rejection (qAt Z N) (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder =
      some e := by
    unfold rejection
    rcases h with h | h
    · rw [h]
      exact ⟨_, rfl⟩
    · cases hk : OnBytes.linOk (qAt Z N).codes (qAt Z N).S
      · exact ⟨_, rfl⟩
      · rw [h]
        exact ⟨_, rfl⟩
  obtain ⟨e, he⟩ := hr
  constructor
  · unfold rowsNow
    rw [hP, hs]
    show ((k14Rows (qAt Z N) (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder id).toOption).getD
      [] = []
    unfold k14Rows
    rw [he]
    rfl
  · unfold rowsNowWord
    rw [hP, hs]
    show ((rejection (qAt Z N) (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder).or _).isSome =
      true
    rw [he]
    rfl

/-- **Where the library makes N of Z (hN): at letters whose halves are nowShared's list, under
MadeAt: K14Asks' fields halves and sends.** hH: the letters' halves are what nowShared returns: A
PREMISE: L is any letters. -/
theorem halves_now {Bk : ProverCoinCounts} {P₁ Cl Wt : Type} (ℓ : WitLens Wt)
    (L : SharedThread.Letters Bk St Cl Weights IndexCommitterCoins TableKey Unit P₁ Wt)
    (c : OnBytes.Model.Verify.Chains) (ts : List (Block St Unit))
    (lst : List (Block St Unit) → Block St Unit)
    (hN : H2U.placesOfMade Z.made = .ok N) (hM : MadeAt Z N) (hH : nowShared Z = .ok L.hs) :
    HalvesIn (qAt Z N)
        (othersOf ℓ L c ts lst (holds2 (qAt Z N) id (randNow (qAt Z N)))) (planData (qAt Z N))
        id ∧
      SendsIn (qAt Z N)
        (othersOf ℓ L c ts lst (holds2 (qAt Z N) id (randNow (qAt Z N)))) (planData (qAt Z N))
        id (randNow (qAt Z N)) := by
  have e : L.hs = proverSidesOfSharedRounds (planData (qAt Z N)) id ++
      proverSidesOfSharedSendings { P := qAt Z N, atPoint := 0 } id (randNow (qAt Z N)) :=
    (Except.ok.inj (hH.symm.trans (now_made Z N hN hM)))
  refine ⟨⟨rfl, ?_, fun h hh => ?_⟩, fun g hg => ?_⟩
  · show (L.hs.map (·.place)).Nodup
    rw [e, halves_eq, sendHalves_eq]
    have e2 : (planData (qAt Z N)).S.sharedSplitNeeded = true := hM.2
    rw [e2, if_pos rfl]
    show ([place 1, place 4, place 7, place 8, sendPlace 2, sendPlace 5] : List Place).Nodup
    decide
  · show h ∈ L.hs
    rw [e]
    exact List.mem_append_left _ hh
  · show g ∈ L.hs
    rw [e]
    exact List.mem_append_right _ hg

/-- **The same, where the library makes N of Z (hN), where the letters' list of sub-protocols is the
carried chain's and every member of it passes its test on the plan**: hp: A PREMISE. -/
theorem halves_shared {Bk : ProverCoinCounts} {P₁ Cl Wt : Type} (ℓ : WitLens Wt)
    (L : SharedThread.Letters Bk St Cl Weights IndexCommitterCoins TableKey Unit P₁ Wt)
    (c : OnBytes.Model.Verify.Chains) (ts : List (Block St Unit))
    (lst : List (Block St Unit) → Block St Unit)
    (hN : H2U.placesOfMade Z.made = .ok N)
    (hL : L.bs = ((chainOf Z.p.chains (qAt Z N) (tests N) last).retype (Cl' := Cl)).blocksInOrder)
    (hp : ∀ b ∈ L.bs, b.planOk = true) (hH : nowShared Z = .ok L.hs) :
    HalvesIn (qAt Z N)
        (othersOf ℓ L c ts lst (holds2 (qAt Z N) id (randNow (qAt Z N)))) (planData (qAt Z N))
        id ∧
      SendsIn (qAt Z N)
        (othersOf ℓ L c ts lst (holds2 (qAt Z N) id (randNow (qAt Z N)))) (planData (qAt Z N))
        id (randNow (qAt Z N)) :=
  halves_now Z N ℓ L c ts lst hN (made_carried Z N (hL ▸ hp)) hH

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.readers_at
#print axioms ProofFile.Honest.K14.flatOf_plain
#print axioms ProofFile.Honest.K14.made_plain
#print axioms ProofFile.Honest.K14.made_carried
#print axioms ProofFile.Honest.K14.now_of_numbers
#print axioms ProofFile.Honest.K14.now_of_six
#print axioms ProofFile.Honest.K14.numbers_of_data
#print axioms ProofFile.Honest.K14.now_made
#print axioms ProofFile.Honest.K14.six_now
#print axioms ProofFile.Honest.K14.rowsNow_eq
#print axioms ProofFile.Honest.K14.rowsNow_half
#print axioms ProofFile.Honest.K14.rowsNow_none
#print axioms ProofFile.Honest.K14.halves_now
#print axioms ProofFile.Honest.K14.halves_shared
