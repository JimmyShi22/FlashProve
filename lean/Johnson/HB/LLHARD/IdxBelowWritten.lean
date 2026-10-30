-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/IdxBelowWritten.lean: four named premises of other files' laws AT THE WRITTEN
VALUES OF THE FULL SIZE: hI and hV (what the general theorem `hbelow_of` leaves), the premise of
`smpOld_named` ("seats.idxOf N.index < N.msgsAt p"), and K01's eighth ("every sampled tenant whose
pin is open in front of the place has its number in seats below the place's count of oracle
messages"). Definitions and statements with their proofs.

THE ARGUMENTS, EACH WITH ITS WRITTEN TERM AND ITS TIE:
  N's fields sent, keptOf, index, w · `N0Full` (Johnson/P5T/PlanSeatsFull.lean) · `seats_in_scope`
    (Johnson/P5T/PlanSeatsTie.lean): green.
  seats · `seatsFull`, the (tree, tenant) of `psFull`: the text of "seats" at `P5T.planSeats` ·
    the same: green.
  N.msgsAt · `countsFull` (Johnson/HB/LLHARD/ToldCounts.lean) · `told_at` UNDER `CountsAre told`: at
    the written cut of the IOP as written in Lean: `countsAre_cut`; that the sub-protocols at Z tell
    that cut is the second test's: typed by its owners, not called here.
  the segments and places · `linksFull`, `flatPlacesOf linksFull true`: closed constants.
  t₁ (hI | hV) · 83 · NO TIE HERE: that the first chain of the seated IOP tells 83 trees is the
    second test's too (`cut_tells`: the written cut tells 83).

  `hI_written`, `hV_written`, `hV_rejects`.
  `seatsFull`; `sampledIn_core`; `idxBelowB`: the test along ONE walk of the open sets.
  `idxBelow_written`: (W): it accepts at all 359 borders: so at K01's fifty places, whichever
    numbers these have. `idxBelow_rejects`: (N): with the counts one border earlier it rejects.
  `idx_index`: the index masks' message is the fifth that is sent; 359 open sets are walked.
  `idx_at`, `idx_of_counts`: at each border; at numbers laid off a told with the written counts.
  `counts_from_three`, `idxIndex_of_counts`: the premise of `smpOld_named` at every place from the
    fourth on (at the first three nothing has been sent: there it is false).
  `hI_hV_in_scope`, `idx_in_scope`: (Z): in the goals' scope, at the numbers and seats of
    `P5T.planSeats`.
By evaluations in Lean's kernel (`decide +kernel`): `idxBelow_written`, `idxBelow_rejects`,
`idx_index`, `counts_from_three`. The counts that make these say something: `psFull_whole`,
`psFull_roles`; that a seat which is not in the list gets the list's length (199), above every count
but the last.

Limits. How many comparisons the walk makes is not stated here. Nothing on soundness.
-/
import Johnson.HB.LLHARD.ToldCounts
import Johnson.P5T.PlanSeatsTie
import Johnson.Desc.K13.Law.AtTable
import Johnson.Desc.First.RowsAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item Numbers flatPlacesOf openSets start sampledIn)
open VerifiableInference.Desc.Sound (linksFull)
open P5T (psFull N0Full)

/-! ## 1 The two seats sit in trees of the first chain -/

/-- **hI** at the written values: the index masks' message sits below the first chain's 83 trees. -/
theorem hI_written : N0Full.index.1 < 83 := by
  rw [show N0Full.index = (1, 0) from congrArg Prod.fst P5T.N0Full_seats]
  decide

/-- **hV** at the written values: so does W. -/
theorem hV_written : N0Full.w.1 < 83 := by
  rw [show N0Full.w = (82, 0) from congrArg Prod.snd P5T.N0Full_seats]
  decide

/-- The negative test: one lower, W does not. -/
theorem hV_rejects : ¬ N0Full.w.1 < 82 := by
  rw [show N0Full.w = (82, 0) from congrArg Prod.snd P5T.N0Full_seats]
  decide

/-! ## 2 A sampled tenant whose pin is open has been sent -/

/-- The first chain's seats as (tree, tenant), in the order of sending. -/
def seatsFull : List (ℕ × ℕ) := psFull.map fun p => (p.j, p.t)

/-- The reader of the open pins' tenants reads four fields of the numbers alone. -/
theorem sampledIn_core {N N' : Numbers} (h1 : N.sent = N'.sent) (h2 : N.keptOf = N'.keptOf)
    (h3 : N.index = N'.index) (h4 : N.w = N'.w) (O : List Item) :
    sampledIn N O = sampledIn N' O := by
  unfold sampledIn
  rw [h1, h2, h3, h4]

/-- A test: along the borders, every sampled tenant whose pin is open at a border has a number in
seats below that border's count of oracle messages. cnt: for each border the oracle messages and the
trees in front. ONE walk of the open sets. -/
def idxBelowB (N : Numbers) (seats : List (ℕ × ℕ)) (cnt : List (ℕ × ℕ)) : Bool :=
  ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull)).zip cnt).all fun x =>
    (sampledIn N x.1).all fun u => decide (seats.idxOf u < x.2.1)

set_option maxRecDepth 1000000 in
/-- **(W)** At the written values it accepts, at all 359 borders. -/
theorem idxBelow_written : idxBelowB N0Full seatsFull countsFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** With each border's counts taken one border earlier it rejects. -/
theorem idxBelow_rejects : idxBelowB N0Full seatsFull ((0, 0) :: countsFull) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The index masks' message is the fifth that is sent; and 359 open sets are walked. -/
theorem idx_index :
    (seatsFull.idxOf N0Full.index,
      (openSets linksFull (flatPlacesOf linksFull true) (start linksFull)).length) = (4, 359) := by
  decide +kernel

/-- So at each border. -/
theorem idx_at {k : ℕ} {c : ℕ × ℕ} (hc : countsFull[k]? = some c) :
    ∀ u ∈ sampledIn N0Full (openAt linksFull (flatPlacesOf linksFull true) k),
      seatsFull.idxOf u < c.1 := by
  intro u hu
  unfold openAt at hu
  cases hO : (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]? with
  | none =>
    rw [hO] at hu
    exact (List.not_mem_nil (show u ∈ ([] : List (ℕ × ℕ)) from hu)).elim
  | some O =>
    rw [hO] at hu
    have hz : ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull)).zip
        countsFull)[k]? = some (O, c) := List.getElem?_zip_eq_some.2 ⟨hO, hc⟩
    have a := List.all_eq_true.1 idxBelow_written _ (List.mem_of_getElem? hz)
    exact of_decide_eq_true (List.all_eq_true.1 a u hu)

/-- **K01's 8, at every place**: at numbers whose four fields are the core's, laid off a told with
the written counts. -/
theorem idx_of_counts {N : Numbers} (h1 : N.sent = N0Full.sent) (h2 : N.keptOf = N0Full.keptOf)
    (h3 : N.index = N0Full.index) (h4 : N.w = N0Full.w) {told : List (List Oracle)}
    (h : CountsAre told) {k : ℕ} (hk : k ≤ 358) :
    ∀ u ∈ sampledIn (N.withTold (flatPlacesOf linksFull true) told)
        (openAt linksFull (flatPlacesOf linksFull true) k),
      seatsFull.idxOf u <
        (N.withTold (flatPlacesOf linksFull true) told).msgsAt
          (flatPlacesOf linksFull true)[k]? := by
  intro u hu
  rw [sampledIn_core (N := N.withTold (flatPlacesOf linksFull true) told) (N' := N0Full) h1 h2 h3
    h4] at hu
  exact idx_at (told_at N h hk) u hu

set_option maxRecDepth 1000000 in
/-- From the fourth border on more than four oracle messages stand in front. -/
theorem counts_from_three : ((countsFull.drop 3).all fun x => decide (4 < x.1)) = true := by
  decide +kernel

/-- **The premise of `smpOld_named`** ("seats.idxOf N.index < N.msgsAt p"), at every place from the
fourth on. -/
theorem idxIndex_of_counts {N : Numbers} (h3 : N.index = N0Full.index)
    {told : List (List Oracle)} (h : CountsAre told) {k : ℕ} (h0 : 3 ≤ k) (hk : k ≤ 358) :
    seatsFull.idxOf (N.withTold (flatPlacesOf linksFull true) told).index <
      (N.withTold (flatPlacesOf linksFull true) told).msgsAt (flatPlacesOf linksFull true)[k]? := by
  have e := told_at N h hk
  have hd : (countsFull.drop 3)[k - 3]? = some
      ((N.withTold (flatPlacesOf linksFull true) told).msgsAt (flatPlacesOf linksFull true)[k]?,
        (N.withTold (flatPlacesOf linksFull true) told).treesAt
          (flatPlacesOf linksFull true)[k]?) := by
    rw [List.getElem?_drop, show 3 + (k - 3) = k by omega]
    exact e
  have a := of_decide_eq_true (List.all_eq_true.1 counts_from_three _ (List.mem_of_getElem? hd))
  show seatsFull.idxOf N.index < _
  rw [h3, show seatsFull.idxOf N0Full.index = 4 from congrArg Prod.fst idx_index]
  exact a

/-! ## 3 In the goals' scope -/

section
variable {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub} {D : OnBytes.Maker.WholeD}
  {r : LPFD.Full.RunPF}

/-- hI and hV at the public part's own numbers. -/
theorem hI_hV_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) :
    (P5T.numbersOf (P5T.planSeats Z Z.D.1)).index.1 < 83 ∧
      (P5T.numbersOf (P5T.planSeats Z Z.D.1)).w.1 < 83 := by
  rw [(P5T.seats_in_scope hW h hy hl).2.2]
  exact ⟨hI_written, hV_written⟩

/-- K01's 8 at the numbers and seats of `P5T.planSeats`, at every place; told: a parameter, under
the written counts; s, t, n: the parameters of the rows' numbers, which the test does not read. -/
theorem idx_in_scope (hW : VerifierAndGoals.InScope W = true)
    (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o W.pol W.lay W.KL = .ok (D, r)) {told : List (List Oracle)}
    (hc : CountsAre told) (s : OnBytes.Params.ReqShape) (t : ℕ → ℕ) (n : ℕ) {k : ℕ}
    (hk : k ≤ 358) :
    ∀ u ∈ sampledIn
        (((P5T.numbersOf (P5T.planSeats Z Z.D.1)).withRows s t n).withTold
          (flatPlacesOf linksFull true) told)
        (openAt linksFull (flatPlacesOf linksFull true) k),
      ((P5T.planSeats Z Z.D.1).map fun p => (p.j, p.t)).idxOf u <
        (((P5T.numbersOf (P5T.planSeats Z Z.D.1)).withRows s t n).withTold
          (flatPlacesOf linksFull true) told).msgsAt (flatPlacesOf linksFull true)[k]? := by
  obtain ⟨e1, _, e3⟩ := P5T.seats_in_scope hW h hy hl
  rw [e3, e1]
  exact idx_of_counts (N := N0Full.withRows s t n) rfl rfl rfl rfl hc hk

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.hI_written
#print axioms VerifiableInference.Desc.K13.Law.hV_written
#print axioms VerifiableInference.Desc.K13.Law.hV_rejects
#print axioms VerifiableInference.Desc.K13.Law.sampledIn_core
#print axioms VerifiableInference.Desc.K13.Law.idxBelow_written
#print axioms VerifiableInference.Desc.K13.Law.idxBelow_rejects
#print axioms VerifiableInference.Desc.K13.Law.idx_index
#print axioms VerifiableInference.Desc.K13.Law.idx_at
#print axioms VerifiableInference.Desc.K13.Law.idx_of_counts
#print axioms VerifiableInference.Desc.K13.Law.counts_from_three
#print axioms VerifiableInference.Desc.K13.Law.idxIndex_of_counts
#print axioms VerifiableInference.Desc.K13.Law.hI_hV_in_scope
#print axioms VerifiableInference.Desc.K13.Law.idx_in_scope
