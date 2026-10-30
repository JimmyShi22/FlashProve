-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/WrittenAtZ.lean: the bridge from the numbers at which the proof file's
description seats the kinds K13 and K14 to the closed sentences on written and typed numbers.

The description's maker lays K13's batching at K13.whereOf Z (ProofFile/Lot/K13.lean) and the shared
chain at p14Of Z.p.chains (beforePointOf N) (ProofFile/Lot/K14SeatAtZ.lean: sharedSeatAt), Z the
public part (ProofFile/Pub.lean). The conditions K13Cond, K13Rounds, K14Cond and K14Rounds
are shown, in this folder, at typed numbers: 13 rows, the shape that the planner's sizing of the
linear claim returns behind the proof file's first six codes, the written lists. Here: ONE structure
of equations on Z, each with its test with code, under which these sentences hold AT THE SEAT's OWN
PARAMETERS.
  Written Z x: twelve equations: the pile has 13 rows; the first chain's shape of the linear claim,
      and the sized proof's, are x.shape; no work at the batching's first three rounds; the setting,
      the codes; the scope is the batch's; the batching starts at round 48270; the plan's own
      entries there, and the shared chain's first eight, are the written lists'; a message is fixed
      before the shared point; the request tree has at most 64 leaves (Z.first.binding.logLeaves:
      the number that the frame takes as its depthReq: Johnson/Goal/Tie/DescriptionOnDecodedProof.lean; FastFull.lean:
      sBG)
  work_of_entries: one of the twelve, the equation on the work, follows from two others (start,
      entries₁) and a fact on the written list
  writtenB Z, writtenB_sound: the test with code, FOR A RUN AT A LIVE Z; its yes gives Written Z x
      at the x that realSized returns
  k13_at_Z: under Written: K13Cond, K13Called and K13AtCap at K13.whereOf Z
  k14_at_Z: under Written: K14Cond, K14Rounds (28 bits of work at LOC), PointPaid, Point64 and
      PointCap (LIN point's two lists beneath the cap for every N ≤ 64) at p14Of Z.p.chains bp, for
      every bp that is not empty
  k14_at_seat: where sharedSeatAt Z returns: there is N with placesOfMade Z.made = .ok N, and the
      same at p14Of Z.p.chains (beforePointOf N): the parameters of the seat's own chain

What is not claimed. THAT Written HOLDS AT ANY Z: `written_in_scope`
(Johnson/Goal/Numbers/WrittenInScope.lean) has it, under that file's premises, at the public part
that the proof file's IOP computes; that these have a member is not shown here: Lean's kernel does
not evaluate the planner's parsing here. That the description's list of blocks holds the kinds'
blocks at these parameters (K13_sits, K14_sits). The full size alone. What the heads of the files
named do not claim. Nothing on soundness of a verifier, on an honest prover or on hiding.
-/
import Johnson.Goal.Numbers.K13CalledAt
import Johnson.Goal.Numbers.K13CapAt
import Johnson.Goal.Numbers.K14PointCap
import Johnson.Desc.ProofFile.Lot.K13
import Johnson.Desc.ProofFile.Lot.K14SeatAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices Johnson.G
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K13.Law (K13Cond K13Called K13AtCap stretch k13_real k13_called_real
  k13_at_cap_real)

/-- **The equations on the public part.** -/
structure Written (Z : ProofFile.Pub) (x : LinSized) : Prop where
  rows : Z.first.pendingRows = 13
  lin : Z.first.lin = x.shape
  work : (VerifiableInference.Desc.K13.whereOf Z).work = (0, 0, 0)
  set : Z.p.chains.made.sized.proof.set = recordSet
  codes : Z.p.chains.made.sized.proof.codes = codesFull2
  shape : Z.p.chains.made.sized.proof.batch.shape = x.shape
  batch : Z.p.chains.made.sized.proof.batch.lines.oneTime = false
  start : VerifiableInference.Desc.K13.fromOf Z = 48270
  entries₁ : (Z.plans.1.drop 48270).take (2 + x.shape.kCol) =
    (stretch dryProofFull.1 48270 (2 + x.shape.kCol)).map (·.1)
  entries₂ : Z.plans.2.1.take 8 = (dryProofFull.2.1.take 8).map (·.1.entry)
  before : ∀ N, H2U.placesOfMade Z.made = .ok N → Desc.K14.beforePointOf N ≠ []
  slots : 2 ^ Z.first.binding.logLeaves ≤ 64

/-- The typed shape has 18 column variables. -/
theorem kCol_real {x : LinSized} (hx : realSized = some (x, codesFull2)) : x.shape.kCol = 18 := by
  have h : (realSized.any fun p => decide (p.1.shape.kCol = 18)) = true := by decide +kernel
  rw [hx, Option.any_some] at h
  exact of_decide_eq_true h

/-- The written list's three first entries of the batching bear no work. -/
theorem written_work : ∀ i < 3,
    (((stretch dryProofFull.1 48270 20).map (·.1))[i]?).map (·.work) = some 0 := by
  decide +kernel

/-- **The equation on the work follows from two others**: where the batching starts at round 48270
and the plan's own entries there are the written list's, the batching's first three rounds bear no
work. -/
theorem work_of_entries {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (hs : VerifiableInference.Desc.K13.fromOf Z = 48270)
    (he : (Z.plans.1.drop 48270).take (2 + x.shape.kCol) =
      (stretch dryProofFull.1 48270 (2 + x.shape.kCol)).map (·.1)) :
    (VerifiableInference.Desc.K13.whereOf Z).work = (0, 0, 0) := by
  rw [kCol_real hx] at he
  have key : ∀ i < 3, ((Z.plans.1[48270 + i]?).map (·.work)).getD 0 = 0 := by
    intro i hi
    have e : Z.plans.1[48270 + i]? = ((stretch dryProofFull.1 48270 20).map (·.1))[i]? := by
      rw [← he, List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    rw [e, written_work i hi]
    rfl
  show ((((Z.plans.1[VerifiableInference.Desc.K13.fromOf Z + 0]?).map (·.work)).getD 0,
    ((Z.plans.1[VerifiableInference.Desc.K13.fromOf Z + 1]?).map (·.work)).getD 0,
    ((Z.plans.1[VerifiableInference.Desc.K13.fromOf Z + 2]?).map (·.work)).getD 0) : ℕ × ℕ × ℕ) =
      (0, 0, 0)
  rw [hs, key 0 (by decide), key 1 (by decide), key 2 (by decide)]

/-- The test with code. -/
def writtenB (Z : ProofFile.Pub) : Bool :=
  realSized.any fun p =>
    decide (Z.first.pendingRows = 13) && decide (Z.first.lin = p.1.shape) &&
    decide ((VerifiableInference.Desc.K13.whereOf Z).work = (0, 0, 0)) &&
    decide (Z.p.chains.made.sized.proof.set = recordSet) &&
    decide (Z.p.chains.made.sized.proof.codes = p.2) &&
    decide (Z.p.chains.made.sized.proof.batch.shape = p.1.shape) &&
    decide (Z.p.chains.made.sized.proof.batch.lines.oneTime = false) &&
    decide (VerifiableInference.Desc.K13.fromOf Z = 48270) &&
    decide ((Z.plans.1.drop 48270).take (2 + p.1.shape.kCol) =
      (stretch dryProofFull.1 48270 (2 + p.1.shape.kCol)).map (·.1)) &&
    decide (Z.plans.2.1.take 8 = (dryProofFull.2.1.take 8).map (·.1.entry)) &&
    (match H2U.placesOfMade Z.made with
      | .ok N => !(Desc.K14.beforePointOf N).isEmpty
      | .error _ => true) &&
    decide (2 ^ Z.first.binding.logLeaves ≤ 64)

theorem writtenB_sound {Z : ProofFile.Pub} (h : writtenB Z = true) :
    ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧ Written Z x := by
  obtain ⟨x, a1, a2, -⟩ := k14_real
  unfold writtenB at h
  rw [a1, Option.any_some] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h13⟩ := h
  refine ⟨x, a1, a2, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun N hN hb => ?_, h13⟩
  rw [hN] at h11
  have h12 : (!(Desc.K14.beforePointOf N).isEmpty) = true := h11
  rw [hb] at h12
  cases h12

/-- realSized returns one thing. -/
theorem sized_one {x y : LinSized} (hx : realSized = some (x, codesFull2))
    (hy : realSized = some (y, codesFull2)) : x = y :=
  congrArg Prod.fst (Option.some.inj (hx.symm.trans hy))

/-- **K13 at the lot's own numbers.** -/
theorem k13_at_Z {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : Written Z x) :
    K13Cond (VerifiableInference.Desc.K13.whereOf Z) codesFull2 dryProofFull.1 48270
        (VerifiableInference.Desc.K1.sentOf 2 0)[81]? ∧
      K13Called (VerifiableInference.Desc.K13.whereOf Z) dryProofFull.1 48270 ∧
      K13AtCap (VerifiableInference.Desc.K13.whereOf Z) dryProofFull.1 48270 := by
  obtain ⟨x1, a1, -, a3⟩ := k13_real
  obtain ⟨x2, b1, -, b3⟩ := k13_called_real
  obtain ⟨x3, c1, -, c3⟩ := k13_at_cap_real
  obtain rfl := sized_one hx a1
  obtain rfl := sized_one hx b1
  obtain rfl := sized_one hx c1
  exact ⟨(a3 _ h.rows h.lin h.work).1, b3 _ h.rows h.lin h.work, c3 _ h.rows h.lin h.work⟩

/-- What is had at the shared chain's parameters. -/
def K14At (P : P14) : Prop :=
  K14Cond 2 P dryProofFull.2.1 ∧ K14Rounds P.S dryProofFull.2.1 recordRadius cMax 28 ∧
    PointPaid P.S dryProofFull.2.1 ∧ Point64 P.S dryProofFull.2.1 ∧
    PointCap P.S dryProofFull.2.1

/-- **K14 at the parameters that the shared chain's maker takes off the planner's chains.** -/
theorem k14_at_Z {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : Written Z x) (bp : List (Nat × Nat)) (hbp : bp ≠ []) : K14At (p14Of Z.p.chains bp) := by
  obtain ⟨x1, a1, -, a3⟩ := k14_real_seat
  obtain ⟨x2, b1, -, -, b4⟩ := k14_rounds_real
  obtain ⟨x3, c1, -, c3⟩ := k14_point_real
  obtain ⟨x4, d1, -, d3⟩ := k14_point64_real
  obtain ⟨x5, f1, -, f3⟩ := point_cap_real
  obtain rfl := sized_one hx a1
  obtain rfl := sized_one hx b1
  obtain rfl := sized_one hx c1
  obtain rfl := sized_one hx d1
  obtain rfl := sized_one hx f1
  have e : (p14Of Z.p.chains bp).S = x.shape := h.shape
  refine ⟨a3 Z.p.chains bp hbp h.set h.codes h.shape h.batch, ?_, ?_, ?_, ?_⟩
  · rw [e]; exact b4
  · rw [e]; exact c3.2
  · rw [e]; exact d3
  · rw [e]; exact f3

/-- **At the seat's own chain.** -/
theorem k14_at_seat {Z : ProofFile.Pub} {x : LinSized} (hx : realSized = some (x, codesFull2))
    (h : Written Z x) {s : ProofFile.SharedSeat} (hs : Desc.K14.sharedSeatAt Z = some s) :
    ∃ N, H2U.placesOfMade Z.made = .ok N ∧
      K14At (p14Of Z.p.chains (Desc.K14.beforePointOf N)) := by
  unfold Desc.K14.sharedSeatAt at hs
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    rw [hN] at hs
    cases hs
  | ok N => exact ⟨N, rfl, k14_at_Z hx h _ (h.before N hN)⟩

end Desc.K14.Law
