-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Whole.lean: CONDITIONAL: the debts of the member of the first
chain that stands at an attention segment's own rounds (kind K5), in one statement, with the named
premises on values of Honest/K5/Law/Exchange.lean given way to the ties from which they are shown. A
joining: calls alone.

  `k5_seated_keys`  CONDITIONAL: `K5Seated` at the public data written out (`seatOf`,
                    Honest/K5/Law/SeatReturns.lean), from the third test's yes, `KeySizes` and
                    `LotLaid`
  `k5_owes_join`    CONDITIONAL: **`Plays`, `Behind`, `Exchange`, and `Accepted` for every fall**,
                    with `JoinOwed` given way to `K5Script` (Honest/K5/Law/Script.lean;
                    `joinOwed_script`, Honest/K5/Law/JoinClosed.lean)

  `k5_owes_whole`   CONDITIONAL: **the same with `SayOwed` given way too**: to `K5Script` and
                    `IdnOwed` (`sayOwed_of`, Honest/K5/Law/SayOwed.lean; Honest/K5/Law/IdnAt.lean)

THE PREMISES OF `k5_owes_whole`: those of `k5_owes_keys` (Honest/K5/Law/SeatReturns.lean: its head
lists them with who is meant to pay each) but `SayOwed` and `JoinOwed`; and in their stead TWO
PREMISES THAT BEAR ON VALUES:
  Sc: `K5Script` at the member: three ties between the witness, the book's coins, the trace's cells
      and the state's key points. IT IS NOT SHOWN.
  hI: `IdnOwed`: a sentence on the letter `valid`: every valid input's cells meet the library's
      three families of identities. SHOWN OF NO `valid`.
`k5_owes_join` keeps `SayOwed`, which holds the clause on values of the item "own".
No premise of `k5_owes_whole` says that a form is worth 0: the clause "each form is worth 0" of the
three owed items on forms is a conclusion there. It hangs on the two premises above.

Limits. Every theorem is conditional; none of the premises is shown to be met. The riders' debt
(`RidesPast`) is not among the conclusions.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatReturns
import Johnson.Desc.ProofFile.Honest.K5.Law.JoinClosed
import Johnson.Desc.ProofFile.Honest.K5.Law.SayOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Strs Chain)
open VerifiableInference.Desc.Sound (seatTab)
open H2K5.Honest (K5Keeps)
open ProofFile.Honest.FirstThread (Script WtF)
open P5J (AtMgA TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **`K5Seated` at the public data written out.** CONDITIONAL: under the hypothesis h; g is below
12; hG: G is the ground that the description's maker makes; hKey: the third test's yes; hK:
`KeySizes`; hL: `LotLaid` at the maker with three tests. -/
theorem k5_seated_keys {g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hK : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid hs (seatAtK keyOf Zp G) cells G) :
    ∃ blk a, (P5J.At.X Zp).A[g]? = some a ∧
      K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
        cells (seatOf keyOf Zp G cF g a) (parAt Zp g a) blk := by
  obtain ⟨-, a, -, hP, -⟩ := k5_member h hg
  have hYs := seatAt_returns_at_head h hg hG hP.plan (hKey a hP.plan)
  rcases half_laid h hs hg (fun l nm j Y e => seatAt_link l nm j Y (seatAtK_spec e).1) hG hL with
    ⟨Z5', hY', hh⟩ | ⟨hY', -⟩
  · obtain rfl : Z5' = seatOf keyOf Zp G cF g a := Option.some.inj (hY'.symm.trans hYs.2)
    obtain ⟨blk, a', ha', Hs⟩ :=
      k5_seated_head h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hG hYs.1
        (hK a hP.plan) hh
    obtain rfl : a' = a := Option.some.inj (ha'.symm.trans hP.plan)
    exact ⟨blk, a', ha', Hs⟩
  · rw [hYs.2] at hY'
    cases hY'

/-- **THE MEMBER's DEBTS, WITH `JoinOwed` GIVEN WAY TO THE TIES**: it plays; behind its yes; the
exchange; it is accepted, for every fall. CONDITIONAL: the premises stand in the file's head. Sc is
shown by nobody. `SayOwed` HOLDS THE CLAUSE ON VALUES of the item "own". -/
theorem k5_owes_join {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hK : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid hs (seatAtK keyOf Zp G) cells G)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → keeps (borderOf g) s s')
    (Rd : ∀ w s s', rides (borderOf g) w s → K5Keeps s s' → rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hSay : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      SayOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a)
    (Sc : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      K5Script (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
        cells (seatOf keyOf Zp G cF g a) a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms)) :
    Plays (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Behind (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Exchange (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      ∀ fall, Accepted (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) fall
        (borderOf g) := by
  obtain ⟨blk, a, ha, Hs⟩ :=
    k5_seated_keys h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hG hKey hK hL
  exact k5_owes h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hfit hb Kp Rd
    hans (hSay a ha)
    (joinOwed_script h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hfit hb
      (Sc a blk ha Hs.member) rfl)

/-- **THE MEMBER's DEBTS, WITH BOTH NAMED PREMISES ON VALUES GIVEN WAY TO THE TIES**: it plays;
behind its yes; the exchange; it is accepted, for every fall. CONDITIONAL: the premises stand in the
file's head. Sc and hI are shown by nobody. -/
theorem k5_owes_whole {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hKey : ∀ a, (P5J.At.X Zp).A[g]? = some a → (seatOf keyOf Zp G cF g a).keysFit
      (blankDraws (Zp.D.1.take (roundsTo cF.blocksInOrder (borderOf g)))) = true)
    (hK : ∀ a, (P5J.At.X Zp).A[g]? = some a → KeySizes (seatOf keyOf Zp G cF g a))
    {cells : Tr → Cells} (hL : LotLaid hs (seatAtK keyOf Zp G) cells G)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → keeps (borderOf g) s s')
    (Rd : ∀ w s s', rides (borderOf g) w s → K5Keeps s s' → rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (Sc : ∀ a blk, (P5J.At.X Zp).A[g]? = some a → cF.blocksInOrder[borderOf g]? = some blk →
      K5Script (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
        cells (seatOf keyOf Zp G cF g a) a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms))
    (hI : ∀ a, (P5J.At.X Zp).A[g]? = some a → IdnOwed valid cells (seatOf keyOf Zp G cF g a)) :
    Plays (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Behind (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Exchange (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      ∀ fall, Accepted (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) fall
        (borderOf g) := by
  obtain ⟨blk, a, ha, Hs⟩ :=
    k5_seated_keys h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hG hKey hK hL
  exact k5_owes h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hfit hb Kp Rd
    hans
    (sayOwed_of h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs
      (Sc a blk ha Hs.member) rfl (hI a ha))
    (joinOwed_script h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hfit hb
      (Sc a blk ha Hs.member) rfl)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_seated_keys
#print axioms ProofFile.Honest.K5.k5_owes_join
#print axioms ProofFile.Honest.K5.k5_owes_whole
