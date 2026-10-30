-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/OwesAtHead.lean: CONDITIONAL: the debts of the member of the
first chain that stands at an attention segment's own rounds (kind K5), in one statement, WITHOUT
the premise `K5Seated`: from the hypothesis `P5J.AtMgA`, "the maker of the place's public data has
yielded Z5 at the description's maker's own ground", and "the list of halves holds the kind's half
at that place". A joining: calls alone.

  `k5_seated_head`  CONDITIONAL: `K5Seated` at that member, with the number of rounds in front paid
                    (`hbase_at`, Honest/K5/Law/BaseAt.lean) and the ground's public parameters paid
                    (the description's maker's own ground; Johnson/Desc/First/Att/Door/Law/
                    K5AtConstant.lean)
  `k5_owes_head`    CONDITIONAL: **`Plays`, `Behind`, `Exchange`, and `Accepted` for every fall** at
                    that member (`k5_owes`, Honest/K5/Law/Exchange.lean)

THE PREMISES OF `k5_owes_head`, and who is meant to pay each.
  h : `P5J.AtMgA`: not shown here.
  hG: G is the ground that the description's maker makes of the public part: an equation.
  hY: `seatAt` yields Z5 at that ground, at the segment 2 g + 1 of the name "A‹g›": that it yields
      at the real public files (its two tests with code say yes there) is an evaluation; not shown.
  hK: `KeySizes` Z5: whoever lays the reader of the key points.
  hh: the list of halves holds the kind's half at the place, and it is the first there: whoever lays
      that list.
  hfit, hb: the test `Thread.fits` on the letters: an evaluation.
  Kp, Rd, hans: whoever lays the letters `keeps`, `rides`, `ans`.
  `SayOwed`, `JoinOwed`: THEY HOLD THE CLAUSES ON VALUES of two of the six items that the kind's
      row owes: the laws on the values that the honest side sends, with the lookup's law on its
      half of the join. They are asked at the plan of the group: there is just one.

Limits. For these two items a frame, not a result on values. None of the premises is shown to be
met. The riders' debt (`RidesPast`) is not among the conclusions.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Exchange
import Johnson.Desc.ProofFile.Honest.K5.Law.BaseAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Strs Chain)
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

/-- **`K5Seated` at the kind's member of group g**, with the number of rounds in front and the
ground's public parameters paid. CONDITIONAL: under the hypothesis h; g is below 12; hG: G is the
ground that the description's maker makes; hY: the maker of the place's public data has yielded Z5
there; hK: `KeySizes`; hh: the list of halves holds the kind's half at the place. -/
theorem k5_seated_head {g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Z5 : Seat5}
    (hY : seatAt keyOf Zp G (2 * g + 1) ("A" ++ toString g) g = some Z5)
    (hK : KeySizes Z5) {cells : Tr → Cells}
    (hh : hs.find? (fun q => q.place == Z5.place) = some (k5Half cells Z5)) :
    ∃ blk a, (P5J.At.X Zp).A[g]? = some a ∧
      K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
        cells Z5 (parAt Zp g a) blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : G.W = P5J.At.X Zp := by
    obtain rfl : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
    exact O.W
  exact k5Seated_head h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hY hW
    (hbase_at h hg hY) hK hh

/-- **THE MEMBER's DEBTS IN ONE STATEMENT, WITHOUT `K5Seated` AS A PREMISE**: it plays; behind its
yes; the exchange; it is accepted, for every fall. CONDITIONAL: every premise stands in the file's
head with who is meant to pay it. `SayOwed`, `JoinOwed` HOLD THE CLAUSES ON VALUES of two of the six
items owed: for these a frame, not a result on values. -/
theorem k5_owes_head {n g : Nat} (hg : g < 12)
    {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array OnBytes.E)} {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {Z5 : Seat5}
    (hY : seatAt keyOf Zp G (2 * g + 1) ("A" ++ toString g) g = some Z5)
    (hK : KeySizes Z5) {cells : Tr → Cells}
    (hh : hs.find? (fun q => q.place == Z5.place) = some (k5Half cells Z5))
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (Kp : ∀ s s', K5Keeps s s' → keeps (borderOf g) s s')
    (Rd : ∀ w s s', rides (borderOf g) w s → K5Keeps s s' → rides (borderOf g + 1) w s')
    (hans : AnsReadsRest ans ((P5J.At.N Zp cF).sent (2 * g + 1) 0))
    (hSay : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      SayOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a)
    (hJ : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a) :
    Plays (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Behind (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      Exchange (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) ∧
      ∀ fall, Accepted (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) fall
        (borderOf g) := by
  obtain ⟨blk, a, ha, Hs⟩ :=
    k5_seated_head h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hG hY hK hh
  exact k5_owes h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hfit hb Kp Rd
    hans (hSay a ha) (hJ a ha)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_seated_head
#print axioms ProofFile.Honest.K5.k5_owes_head
