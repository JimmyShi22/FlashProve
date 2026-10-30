-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.WrittenAtSeats
import Johnson.Loose.H2K12.AtFullPlain
import Johnson.Desc.K12.Law.SitsBats
import Johnson.Desc.K12.Law.StretchLast
import Johnson.Desc.K12.Law.RoundsOfG
import Johnson.Desc.K12.Law.FirstTreeOfMade
import Johnson.Desc.K12.Law.CondAtFull
/-
Johnson/Loose/H2K12/CondAtLast.lean: the condition of the law of a proximity test (the kind K12),
and the two forms "every written round is below", AT THE SEAT OF THE FIRST CHAIN's LAST TEST in the
proof file's description, at the full size.

Why. H2K12/CondAtSeats.lean has the three later seats. At the first chain's seat
Johnson/Desc/K12/Law/CondAtFull.lean left two premises on the made place unpaid: its written rounds
are the closed place's; its rows are the closed place's. This file pays both, off the written
list of the first chain.
How. The description's first chain declares pre's rounds, then the test's, then l's
(H2K12/DeclAtSeats.lean); written out they are that written list. The test's 33 names hang on its
stages and bits of work alone, and they begin in that list at one place (`at_one_place`,
Law/StretchLast.lean): so pre has 48,237 rounds. Readers take of the closed place's declared rounds
just that stretch, and a declared round is told by what a reader takes of it (Law/RoundsOfG.lean):
so the two places declare the same rounds; the first of them bears the rows. No round of the written
list behind that place is named "BAT": that pays the rule on the first free own number
(`free_seat_L`, Law/StartOfMade.lean) its premise; the rounds in front send 77 roots.
Main names:
  `plan_at_seat_L`: the test on the plan of the kind's block at the seat, from the description's.
  `names_of_nums`: two places with the same stages and bits of work declare rounds of the same
    names.
  `stretch_at_L`: what the seat hands to a general step: the list as cut; the place's declared
    rounds; pre's length; the first free own number.
  `rounds_at_seat_L`, `rows_at_seat_L`, `written_at_seat_L`.
  `k12Condition_at_seat_L`, `roundsHold_at_seat_L`, `roundsBelow_at_seat_L`.
The premises, all: those of CondAtSeats.lean (hZ, hN, hp, A, hW; for the condition hpub); the cut's
letters same, pre, l, J with hb and hJ (`k12_sits`, H2K12/SitsAtDescPure.lean, hands them from
`onlineDescription`'s yes); and hL: THE RECORD's STAGES OF THE LAST TEST ARE THE TYPED LIST. hL is shown in
the goals' scope only under a premise on the layout file's lines on groups (`last_of_plain`,
H2K12/AtFullPlain.lean): that premise is nobody's.
Limits: those of CondAtSeats.lean. The payers are named, not called. The full size only. One round's
share each, no sum; 20 of the 128 bits are work at "CS" and "BASE"; "BAT": its number is priced; its
list's law is not shown. `RoundsBelowAt` holds no clause on the radii: the weight lies in
`RoundsHoldAt`. Nothing on soundness of a verifier. Nothing on hiding.

-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open OnBytes.Slice
open H2K.Made (batsR bats)
open H2K.Member (piLFull dsOf xsFirst namesL)
open Johnson.G (dryProofFull)
open scoped ENNReal

/-- Two places with the same stages and bits of work declare rounds of the same names. -/
theorem names_of_nums {M M0 : H2U.TestNums} {ds ds0 : List Fmt.DeclaredRound}
    (hM : H2U.roundsOfNums M = some ds) (h0 : H2U.roundsOfNums M0 = some ds0)
    (h2 : M.work = M0.work) (h3 : M.stages = M0.stages) :
    ds.map (·.entry.name) = ds0.map (·.entry.name) := by
  obtain ⟨s, nx, rest, R, e1, hR, rfl⟩ := H2K.Made.rounds_top M ds hM
  obtain ⟨s', nx', rest', R', e1', hR', rfl⟩ := H2K.Made.rounds_top M0 ds0 h0
  obtain ⟨a1, et⟩ := List.cons.inj (e1.symm.trans (h3.trans e1'))
  obtain ⟨a2, a3⟩ := List.cons.inj et
  subst a1 a2 a3
  rw [List.map_cons, List.map_cons, lay_names _ _ _ _ _ hR, lay_names _ _ _ _ _ hR', h2]

/-- The rows stand in the first declared round. -/
theorem rows_of_rounds {M M0 : H2U.TestNums} (h : H2U.roundsOfNums M = H2U.roundsOfNums M0)
    {ds0 : List Fmt.DeclaredRound} (h0 : H2U.roundsOfNums M0 = some ds0) : M.rows = M0.rows := by
  obtain ⟨_, _, _, R, _, _, e⟩ := H2K.Made.rounds_top M ds0 (h.trans h0)
  obtain ⟨_, _, _, R', _, _, e'⟩ := H2K.Made.rounds_top M0 ds0 h0
  have hh := (List.cons.inj (e.symm.trans e')).1
  exact congrArg (fun d : Fmt.DeclaredRound => d.entry.rows) hh

section
variable (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
  (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) (mk : ProofFile.LinksBy) (N : H2U.Places4)
  (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
  (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
  (A : H2K.Sizes.AtFull Z.made.p.chains.made)
  (hL : Z.made.p.chains.made.sized.proof.last.stages = H2K.Member.szLFull)
  (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
    .ok dryProofFull)
  (same : First.S → First.S → Bool) (pre l : List (Block First.S ProofFile.Cl))
  (J : Block First.S ProofFile.Cl)
  (hb : c.blocksInOrder = pre ++ firstEntry same J :: l) (hJ : FirstJ (pL N) J)

include hp hb hJ in
/-- The test on the plan of the kind's block at the first chain's seat. -/
theorem plan_at_seat_L : (proximityTestKind guardedProximityTestParts (pL N) : Blk').planOk = true := by
  obtain ⟨b1, _, _⟩ := Keeps.planOk_blocks _ hp
  obtain ⟨leave, _, hs⟩ := firstJ_sits same (pL N) J hJ
  have mL : firstEntry same J ∈ (descN o mk guardedProximityTestParts Z N c).first.blocksInOrder := by
    show firstEntry same J ∈ c.blocksInOrder
    rw [hb]
    exact List.mem_append_right _ List.mem_cons_self
  exact hs.plan (b1 _ mL)

include hZ hN hp A hL hW hb hJ in
/-- What the first chain's seat hands to a general step. -/
theorem stretch_at_L :
    (pre.flatMap (·.rounds) ++ ((proximityTestKind guardedProximityTestParts (pL N) : Blk').rounds ++
        l.flatMap (·.rounds))).mapM (·.round []) = some xsFirst ∧
      H2U.roundsOfNums N.L.nums = some (proximityTestKind guardedProximityTestParts (pL N) : Blk').rounds ∧
      (pre.flatMap (·.rounds)).length = 48237 ∧ N.L.nums.free = 77 := by
  have pLk := plan_at_seat_L o Z mk N c hp same pre l J hb hJ
  obtain ⟨hr0, r, R', er, hr⟩ := seat_rounds a12 N.L pLk
  obtain ⟨e1, e2, _⟩ := H2K.Sizes.place_L_of_full A hN hL
  have hd := decl_atL o mk Z N c same pre l J hb hJ
  have hx : (pre.flatMap (·.rounds) ++ ((proximityTestKind guardedProximityTestParts (pL N) : Blk').rounds ++
      l.flatMap (·.rounds))).mapM (·.round []) = some xsFirst := by
    rw [← hd]
    exact (H2K.Pub.chains_of_written hW).1
  have hl : (pre.flatMap (·.rounds)).length = 48237 :=
    H2K.Member.at_one_place hx (names_of_nums hr0 H2K.Member.rounds_LFull e2 e1)
  refine ⟨hx, hr0, hl, ?_⟩
  -- none behind, off the closed list
  have hE := entries_of_rounds hx
  have hk : batsR (R' ++ l.flatMap (·.rounds)) = 0 := by
    have h1 := congrArg (List.drop 48238) hE
    rw [show (proximityTestKind guardedProximityTestParts (pL N) : Blk').rounds = r :: R' from er, List.map_append,
      List.cons_append, List.map_cons] at h1
    have hl' : ((pre.flatMap (·.rounds)).map (·.entry)).length = 48237 := by
      rw [List.length_map, hl]
    have h3 : ((pre.flatMap (·.rounds)).map (·.entry) ++
        r.entry :: (R' ++ l.flatMap (·.rounds)).map (·.entry)).drop
          (((pre.flatMap (·.rounds)).map (·.entry)).length + 1) =
        (R' ++ l.flatMap (·.rounds)).map (·.entry) := by
      rw [List.drop_append, List.drop_of_length_le (by omega), Nat.add_sub_cancel_left,
        List.nil_append]
      rfl
    rw [hl'] at h3
    have h2 : ((pre.flatMap (·.rounds)).map (·.entry) ++
        r.entry :: (R' ++ l.flatMap (·.rounds)).map (·.entry)).drop 48238 =
        (R' ++ l.flatMap (·.rounds)).map (·.entry) := h3
    rw [h2] at h1
    unfold batsR bats
    rw [← h1, H2K.Member.none_behind_LFull]
    rfl
  have eD : (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks.1 = Z.D.1 := ((FileDescription.planOk_ok _).1 hp).decl₁
  have hD1 : Z.D.1 = pre.flatMap (·.rounds) ++ r :: (R' ++ l.flatMap (·.rounds)) := by
    rw [← eD, hd, show (proximityTestKind guardedProximityTestParts (pL N) : Blk').rounds = r :: R' from er, List.cons_append]
  have hf := (H2K.Made.free_seat_L Z.made N Z.D (pub_planLike o pol lay KL Z hZ) hN
    (pub_D o pol lay KL Z hZ) _ r _ hD1 hr hk).2
  rw [hf, roots_closed hx, hl]
  exact H2K.Member.roots_front_LFull

include hZ hN hp A hL hW hb hJ in
/-- **The made place declares the closed place's rounds.** -/
theorem rounds_at_seat_L : H2U.roundsOfNums N.L.nums = H2U.roundsOfNums piLFull.nums := by
  obtain ⟨hx, hr0, hl, _⟩ :=
    stretch_at_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  obtain ⟨e1, e2, _⟩ := H2K.Sizes.place_L_of_full A hN hL
  exact H2K.Pub.roundsOfNums_at_stretch H2K.Pub.srcInj_nil hx hr0 H2K.Member.rounds_LFull
    (by rw [hl]; exact H2K.Member.stretch_LFull) e2 e1

include hZ hN hp A hL hW hb hJ in
/-- **Its rows are the closed place's.** -/
theorem rows_at_seat_L : N.L.nums.rows = piLFull.nums.rows :=
  rows_of_rounds (rounds_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ)
    H2K.Member.rounds_LFull

include hZ hN hp A hL hW hb hJ in
/-- **Its written rounds are the closed place's.** -/
theorem written_at_seat_L : H2K.Pub.writtenOf N.L.nums = H2K.Pub.writtenOf piLFull.nums := by
  obtain ⟨_, _, _, hf⟩ :=
    stretch_at_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ
  obtain ⟨e1, _, _⟩ := H2K.Sizes.place_L_of_full A hN hL
  refine H2K.Pub.writtenOf_of_rounds
    (rounds_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ) e1
    (H2K.Member.places_ownL Z.made N hN) ?_
  rw [(H2K.Made.places_firstTree Z.made N hN).1, hf]
  rfl

include hZ hN hp A hL hW hb hJ in
/-- The condition at the seat of the first chain's last test. -/
theorem k12Condition_at_seat_L (K : OnBytes.Codes) (hpub : H2K.Pub.pubOk (pL N) K = true) :
    H2K.Pub.K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.last.stages)
      (pL N) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  H2K.Pub.k12Condition_at_full_L A hN _ K hL
    (written_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ) hpub

include hZ hN hp A hL hW hb hJ in
/-- Every written round is below, with the radii pinned, at that seat: on public data alone. -/
theorem roundsHold_at_seat_L :
    H2K.Pub.RoundsHoldAt (pL N)
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.last.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  H2K.Pub.roundsHold_at_full_L A hN _ hL
    (rows_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ)
    (written_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ)
    (plan_at_seat_L o Z mk N c hp same pre l J hb hJ)

include hZ hN hp A hL hW hb hJ in
/-- So the form `RoundsBelowAt`. -/
theorem roundsBelow_at_seat_L :
    H2K.Pub.RoundsBelowAt (pL N)
      (H2K.Pub.radBy Z.made.p.chains.made.sized.proof.set
        Z.made.p.chains.made.sized.proof.last.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (roundsHold_at_seat_L o pol lay KL Z hZ mk N c hN hp A hL hW same pre l J hb hJ).below

end

end H2K.JointK

#print axioms H2K.JointK.plan_at_seat_L
#print axioms H2K.JointK.stretch_at_L
#print axioms H2K.JointK.rounds_at_seat_L
#print axioms H2K.JointK.rows_at_seat_L
#print axioms H2K.JointK.written_at_seat_L
#print axioms H2K.JointK.k12Condition_at_seat_L
#print axioms H2K.JointK.roundsHold_at_seat_L
#print axioms H2K.JointK.roundsBelow_at_seat_L
