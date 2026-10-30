-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AtFillingMore.lean: kind K14: WHERE EVERY MEMBER OF THE SHARED
CHAIN's FLAT LIST, PLAIN OR CARRIED TO ANOTHER TYPE OF CLAIMS, PASSES ITS TEST ON THE PLAN, THE
LIBRARY's TEST linOk ACCEPTS AT THE PLAN's PARAMETERS qAt Z N (linOk_plain, linOk_carried). Beside
these two, five smaller statements on the names of Honest/K14/AtFilling.lean. Seven statements with
their proofs; no definition.

  linOk_of_point  where the library makes its eight and "LIN point"'s own test on the plan accepts:
                  linOk accepts: by the library's point_given
                  (Johnson/Desc/K14/Law/SharesGiven.lean) and linFits_eq
                  (Johnson/Desc/Own/LinAgree.lean)
  pass_plain      each of the kind's sub-protocols passes its test on the plan where every member of
                  the plain flat list does (the library has this law as a private one:
                  Johnson/Desc/K14/Law/SplitGiven.lean; its public twin at the carried list is
                  own_pass_carried)
  linOk_plain, linOk_carried   **linOk FOLLOWS FROM EITHER LIST's TESTS ON THE PLAN**: so whoever
                  has the tests on the plan at either list need not ask linOk beside them; and the
                  first of the two cases of rowsNow_none's premise (AtFilling.lean: linOk rejects,
                  or sendingsFit rejects) holds at no public part at which either list passes
  made_of_plan    **Plan2 at qAt Z N, which is the type of K14Asks' field plan
                  (Honest/K14/Asks.lean), gives MadeAt**: a way to it beside made_plain and
                  made_carried (AtFilling.lean) and made_of_laid (Honest/K14/BudAtRow.lean)
  rowsNowWord_none   **rowsNowWord returns nothing JUST WHERE the two readers and k14Rows return**:
                  the twin of k14WordAt_none (Honest/K14/Rows14.lean)
  good_rowsNow    CONDITIONAL, on four premises: the library makes the places' numbers N of the
                  public part Z; MadeAt Z N; linOk accepts at qAt Z N; sendingsFit accepts at
                  qAt Z N. **Under these: Good, AS ONE TERM AT THE LETTERS False, at each row that
                  rowsNow lays**, at the side that Side.seated returns off the list carried to any
                  type of claims, at whatever falls, at a book that passes noneSpent at the row's
                  place, at every pre

Who calls them. made_of_plan: Honest/K14/SendingsAtFilling.lean. linOk_of_point: linOk_plain and
linOk_carried here; pass_plain: linOk_plain here. linOk_plain, linOk_carried, rowsNowWord_none and
good_rowsNow are called by no other file: they are offered, and spent nowhere.

IN good_rowsNow THE LETTERS A AND B ARE «False»: Good's FIELDS plays AND acc HOLD FROM A FALSE
PREMISE AND SHOW NOTHING; what is shown is fits, exact and fresh, with all the limits of
Honest/K14/GoodCalls.lean.

What is not claimed. That a premise holds at any public file. sendingsFit follows from nothing here.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.AtFilling
import Johnson.Desc.K14.Law.SharesGiven
import Johnson.Desc.Own.LinAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (TableKey OracleNotice TreeLay)
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc.K12.Seat (tests last)
open VerifiableInference.Desc.Own (linFits_eq)
open VerifiableInference.OnPublicFiles
open Desc.K14 (P14 St blocks chainOf frontBlock blocksOr)
open Desc.K14.Honest (FlatOf flatOf_carried)
open Desc.K14.Law (seatN blocks_said eight_of_pass own_pass_carried point_given)
open ProofFile.Honest.Small (noneSpent)

/-- Where the library makes its eight and "LIN point"'s own test on the plan accepts, linOk
accepts. -/
theorem linOk_of_point (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (h1 : b1.planOk = true) :
    OnBytes.linOk P.codes P.S = true := by
  have h := (point_given P b1 b2 b3 b4 b5 b6 b7 b8 hb h1).1
  unfold OkD.At.linPoint at h
  simp only [Bool.and_eq_true] at h
  rw [← linFits_eq]
  exact h.1.1.2

/-- Each of the kind's sub-protocols passes its test on the plan where every member of the plain
flat list does. The statement and the proof are those of the library's private law own_pass
(Johnson/Desc/K14/Law/SplitGiven.lean), which cannot be called from another file. -/
theorem pass_plain (c : OnBytes.Model.Verify.Chains) (P : P14) (ts : List (Block St Unit))
    (lst : List (Block St Unit) → Block St Unit)
    (h : ∀ b ∈ (chainOf c P ts lst).blocksInOrder, b.planOk = true) :
    ∀ x ∈ blocksOr P, x.planOk = true := by
  intro x hx
  let B : Block St Unit → Block St Unit := fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }
  have hflat : (chainOf c P ts lst).blocksInOrder = B (frontBlock c) ::
      (blocksOr P ++ ts ++ [lst (blocksOr P ++ ts)]).map B := by
    simp [chainOf, Chain.blocksInOrder, B]
  have hm : B x ∈ (chainOf c P ts lst).blocksInOrder := by
    rw [hflat]
    exact List.mem_cons_of_mem _
      (List.mem_map.2 ⟨x, List.mem_append_left _ (List.mem_append_left _ hx), rfl⟩)
  have k : (x.planOk && x.hasNoClaimsAndNothingAfter) = true := h (B x) hm
  rw [Bool.and_eq_true] at k
  exact k.1

variable (Z : Pub) (N : H2U.Places4)

/-- **Where every member of the plain flat list of seatN Z N passes its test on the plan, linOk
accepts at qAt Z N.** -/
theorem linOk_plain (hp : ∀ b ∈ (seatN Z N).chain.blocksInOrder, b.planOk = true) :
    OnBytes.linOk (qAt Z N).codes (qAt Z N).S = true := by
  have hp' : ∀ b ∈ (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder, b.planOk = true := hp
  obtain ⟨l, hb⟩ := blocks_said Z.p.chains (qAt Z N) (tests N) last hp'
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := Desc.K14.Law.eight (qAt Z N) l hb
  refine linOk_of_point _ b1 b2 b3 b4 b5 b6 b7 b8 hb ?_
  have key := pass_plain Z.p.chains (qAt Z N) (tests N) last hp'
  unfold blocksOr at key
  rw [hb] at key
  exact key b1 (by simp)

/-- **Where every member of the list carried to another type of claims passes its test on the plan,
linOk accepts at qAt Z N.** -/
theorem linOk_carried {Cl' : Type}
    (hp : ∀ b ∈ ((chainOf Z.p.chains (qAt Z N) (tests N) last).retype (Cl' := Cl')).blocksInOrder,
      b.planOk = true) : OnBytes.linOk (qAt Z N).codes (qAt Z N).S = true := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩ :=
    eight_of_pass Z.p.chains (qAt Z N) (tests N) last hp
  refine linOk_of_point _ b1 b2 b3 b4 b5 b6 b7 b8 hb ?_
  have key := own_pass_carried Z.p.chains (qAt Z N) (tests N) last hp
  unfold blocksOr at key
  rw [hb] at key
  exact key b1 (by simp)

/-- **Plan2 at qAt Z N, the type of K14Asks' field plan, gives MadeAt Z N.** -/
theorem made_of_plan {sentU : Array OracleNotice} {layO : TreeLay}
    (h : Plan2 (qAt Z N) sentU layO) : MadeAt Z N := by
  obtain ⟨B⟩ := h.eight
  exact ⟨⟨B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8, B.made⟩, h.facts.two⟩

/-- **rowsNowWord returns nothing just where the two readers and k14Rows return.** -/
theorem rowsNowWord_none {Pb : Type} :
    rowsNowWord Z = none ↔
      ∃ (P : P14) (s : SharedSeat), p14At Z = some P ∧ onlineSharedChain Z = some s ∧
        ∃ rs : List (Unlettered Empty (Common Weights IndexCommitterCoins TableKey) Unit Pb),
          k14Rows P s.chain.blocksInOrder id = .ok rs := by
  unfold rowsNowWord
  cases hP : p14At Z with
  | none => exact ⟨fun h => (by cases h), fun ⟨_, _, h, _⟩ => (by cases h)⟩
  | some P =>
    cases hs : onlineSharedChain Z with
    | none => exact ⟨fun h => (by cases h), fun ⟨_, _, _, h, _⟩ => (by cases h)⟩
    | some s =>
      show ((rejection P s.chain.blocksInOrder).or
        (if (dataOf P.S s.chain.blocksInOrder).isNone then
          some "K14: \"LIN point\" or \"LIN zeta\" is not in the list"
         else none)) = none ↔ _
      constructor
      · intro h
        refine ⟨P, s, rfl, rfl, (k14Rows_returns P s.chain.blocksInOrder id).2 ?_⟩
        revert h
        cases rejection P s.chain.blocksInOrder <;> cases dataOf P.S s.chain.blocksInOrder <;> simp
      · rintro ⟨P', s', h1, h2, h3⟩
        obtain rfl := Option.some.inj h1
        obtain rfl := Option.some.inj h2
        obtain ⟨a, b⟩ := (k14Rows_returns P s.chain.blocksInOrder id).1 h3
        rw [a, b]
        rfl

/-- CONDITIONAL, on four premises: the library makes the places' numbers N of Z (hN); MadeAt Z N
(hM); linOk accepts at qAt Z N (hok); sendingsFit accepts at qAt Z N (hfit); and, row by row, the
book passes noneSpent at the row's place. **Under these: Good, as one term AT THE LETTERS False, at
each row that rowsNow lays**: its fields plays and acc hold from a false premise and show nothing.
The side is the one that Side.seated returns off the list carried to the type Cl' of claims. It
holds at every pre: pre is tied to no description; at each pre this says no more than the law on
ExactMember beneath (Honest/K14/GoodSeated.lean). -/
theorem good_rowsNow {Pb Cl' : Type} (G : Ground) (hN : H2U.placesOfMade Z.made = .ok N)
    (hM : MadeAt Z N) (hok : OnBytes.linOk (qAt Z N).codes (qAt Z N).S = true)
    (hfit : sendingsFit (qAt Z N) = true) :
    ∀ r ∈ (rowsNow Z G : List (Unlettered Empty (Common Weights IndexCommitterCoins TableKey) Unit Pb)),
      ∀ (fs : List (Fall St)) (φ : Face Empty (Common Weights IndexCommitterCoins TableKey) Pb) (Bk : ProverCoinCounts)
        (ord : List Place) (chain firstTree : Nat) (pre : List (Nat × Nat × List Fmt.DeclaredRound)),
        noneSpent Bk { place := r.place, part := 0 } = true →
        ∃ σ, Side.seated ((chainOf Z.p.chains (qAt Z N) (tests N) last).retype (Cl' := Cl')).blocksInOrder
            r.place r.row fs = some σ ∧
          Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) r.On
            r.bud := by
  intro r hr fs φ Bk ord chain firstTree pre hB
  rw [(rowsNow_eq Z N G hN hM hok hfit).1] at hr
  obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7, b8, hb⟩, -⟩ := hM
  exact good_rows_some
    (flatOf_carried (Cl := Cl') Z.p.chains (qAt Z N) b1 b2 b3 b4 b5 b6 b7 b8 (tests N) last hb)
    hb _ rfl id r hr fs φ Bk ord chain firstTree pre hB

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.linOk_of_point
#print axioms ProofFile.Honest.K14.pass_plain
#print axioms ProofFile.Honest.K14.linOk_plain
#print axioms ProofFile.Honest.K14.linOk_carried
#print axioms ProofFile.Honest.K14.made_of_plan
#print axioms ProofFile.Honest.K14.rowsNowWord_none
#print axioms ProofFile.Honest.K14.good_rowsNow
