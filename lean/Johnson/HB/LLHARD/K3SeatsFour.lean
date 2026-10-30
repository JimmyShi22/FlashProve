-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/K3SeatsFour.lean: four of the six tests that make up `At.k3SeatsB` of the head's
law (Johnson/P5J/Rad3Seat3Tests.lean): `linkThereB`, `alignedB`, `callsSentB` and `digSentB`, at all
25 segments. They accept wherever the value is laid in scope and the test that holds the made plan
to the written one accepts. And the join: with them the whole test follows from the other two.

Row or tool. General laws, closed facts on written values, and two laws in scope by rewriting
through named ties. Payers for a premise of another law.

What the four read, the written terms and the ties.
  of `sentAt Zp` the request's shape alone: `proofSizedFull.request`
    (Johnson/Desc/Ok/PlanWritten/SizedLit.lean). Tie: the third equation of `first_written_in_scope`
    (Johnson/Goal/Numbers/MadeInScope.lean). The list of built segments, the layout and the codes
    are not read.
  `At.pseats Zp`: `P5T.psFull`. `At.N Zp cF`, through its field `sent`: `P5T.N0Full`. Tie:
    `seats_in_scope` (Johnson/P5T/PlanSeatsTie.lean).
  the radii `rad3At Zp lay` and the layout file: not read: the two tests on what stands sent read
    the lists' lengths, and a radius is laid beside each shape without changing the length.

The premise beyond scope, the files read, and the value laid. One: `madePinnedAt … = true`.

What is here.
  `sentOf S`: a value of the structure `Sent` with the shape S and nothing else. `fourAt S ps N
    l`: the four tests' texts at it.
  `calls_len`, `dig_len`: the lists' lengths are those at the radius 0.
  `four_is`: the four tests at the closed letters are `fourAt` at the letters' shape, seats and
    numbers. `fourAt_same`: it reads the numbers through `sent` alone.
  `four_written`: it accepts at all 25 segments at the written values. `four_rejects`: the negative
    test of the seats' own file: with the tenant of the first segment's first own oracle message
    moved by 1000, it rejects there.
  `four_walks`: at every segment the digits' list has a member; so has the calls' list.
  `k3Four_at_name`, `k3SeatsB_of_two`.
By evaluations in Lean's kernel (`decide +kernel`): `four_written`, `four_rejects`, `four_walks`.

Limits. The other two tests, `callsSomeB` and `digSomeB`, read the members and the radii off the
rows' maker: no test that compares a written value at a run holds these; they stay one named premise
of `k3SeatsB_of_two`. Nothing here says `madePinnedAt` accepts at any files. Nothing on soundness.


-/
import Johnson.P5J.Rad3Seat3Tests
import Johnson.P5J.LaidOpens
import Johnson.P5T.PlanSeatsTie
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigList sigListCalls lastMoment)
open VerifiableInference.PlanWritten (madePinnedAt proofSizedFull)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope)
open P5T (PSeat psFull N0Full seats_in_scope sentB)

/-- A value of the structure `Sent` with the shape S and nothing else. -/
def sentOf (S : ReqShape) : Sent := ⟨{}, S, ⟨[]⟩, #[]⟩

/-- **The four tests' texts**, at a shape, a list of seats and numbers. -/
def fourAt (S : ReqShape) (ps : List PSeat) (N : Numbers) (l : ℕ) : Bool :=
  ((S.link[l]?).isSome && ((reqGroups S)[l]?).isSome) &&
    (P6T.zeroFirst (sentOf S) l && P6T.bornFits (sentOf S) l) &&
    sentB N l [0] (P6T.listCallsAt (sentOf S) l).length (P6T.seatCallsT ps (sentOf S) l) &&
    sentB N l [2, 0, 1] (P6T.listAt (sentOf S) l).length (P6T.seatT ps l)

/-- The calls' list is as long as at the radius 0. -/
theorem calls_len (D : Sent) (rad : OracleShape → ℕ) (l : ℕ) :
    (sigListCalls D rad l).length = (P6T.listCallsAt D l).length := by
  unfold P6T.listCallsAt sigListCalls sigList
  simp only [List.length_append, List.length_map]

/-- So is the digits' list. -/
theorem dig_len (D : Sent) (rad : OracleShape → ℕ) (l : ℕ) :
    (sigList D rad l (lastMoment D l)).length = (P6T.listAt D l).length := by
  unfold P6T.listAt sigList
  simp only [List.length_map]

/-- **The four tests at the closed letters.** -/
theorem four_is (Zp : ProofFile.Pub) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) (lay : ByteArray)
    (l : ℕ) :
    (At.linkThereB Zp l && At.alignedB Zp l && At.callsSentB Zp cF lay l l &&
      At.digSentB Zp cF lay l l) = fourAt (At.shape Zp) (At.pseats Zp) (At.N Zp cF) l := by
  unfold At.callsSentB At.digSentB At.callsListAt At.digListAt
  rw [calls_len, dig_len]
  rfl

/-- It reads the numbers through `sent` alone. -/
theorem fourAt_same (S : ReqShape) (ps : List PSeat) {N N' : Numbers} (h : N.sent = N'.sent)
    (l : ℕ) : fourAt S ps N l = fourAt S ps N' l := by
  unfold fourAt sentB
  rw [h]

set_option maxRecDepth 1000000 in
/-- **They accept at all 25 segments, at the written values.** -/
theorem four_written :
    ((List.range 25).all fun l => fourAt proofSizedFull.request psFull N0Full l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The negative test.** -/
theorem four_rejects :
    fourAt proofSizedFull.request (P6T.bumped psFull 0) N0Full 0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At every segment each of the two lists has a member. -/
theorem four_walks :
    ((List.range 25).all fun l =>
      !(P6T.listAt (sentOf proofSizedFull.request) l).isEmpty &&
        !(P6T.listCallsAt (sentOf proofSizedFull.request) l).isEmpty) = true := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}

/-- **The four, at the closed letters of the head's law.** -/
theorem k3Four_at_name (hZ : VerifierAndGoals.InScope Z = true) (_ : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    ((List.range At.links.length).all fun l =>
      At.linkThereB Zp l && At.alignedB Zp l && At.callsSentB Zp cF Z.lay l l &&
        At.digSentB Zp cF Z.lay l l) = true := by
  have hl := LPFD.Full.laidPOf_of L.value L.planOk L.data L.asks
  obtain ⟨hps, -, hN0⟩ := seats_in_scope hZ L.pub hy hl
  have hs : (At.N Zp cF).sent = N0Full.sent := by
    rw [← hN0]
    rfl
  have hS : At.shape Zp = proofSizedFull.request := (first_written_in_scope hZ L.pub hy).2.2.1
  have hp : At.pseats Zp = psFull := hps
  refine List.all_eq_true.2 fun l hl' => ?_
  rw [four_is, fourAt_same _ _ hs, hS, hp]
  exact List.all_eq_true.1 four_written l hl'

/-- **The join**: the whole test from the other two. -/
theorem k3SeatsB_of_two (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (h2 : ((List.range At.links.length).all fun l =>
      At.callsSomeB Zp Z.lay l && At.digSomeB Zp Z.lay l) = true) :
    At.k3SeatsB Zp cF Z.lay = true := by
  unfold At.k3SeatsB
  refine List.all_eq_true.2 fun l hl => ?_
  have a := List.all_eq_true.1 (k3Four_at_name hZ hR L hy) l hl
  have b := List.all_eq_true.1 h2 l hl
  simp only [Bool.and_eq_true] at a b ⊢
  exact ⟨⟨⟨⟨⟨a.1.1.1, a.1.1.2⟩, b.1⟩, a.1.2⟩, b.2⟩, a.2⟩

end

end P5J

#print axioms P5J.calls_len
#print axioms P5J.dig_len
#print axioms P5J.four_is
#print axioms P5J.fourAt_same
#print axioms P5J.four_written
#print axioms P5J.four_rejects
#print axioms P5J.four_walks
#print axioms P5J.k3Four_at_name
#print axioms P5J.k3SeatsB_of_two
