-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/LendsAtHeadW.lean: THE REQUEST's OWN PROXIMITY TEST (the place W, the last chain),
THE FULL SIZE: AT THE MAKER's BOOK THE FRAME LENDS THE PAIR ITS COINS, AT EVERY RUN's COINS, AT A
JOB WITH THESE PUBLIC FIELDS; AND THE RUNS BEGIN WHERE THE SENDERS' OWN RECKONING SAYS. PUBLIC DATA
ALONE.

Why. The twin at W of LendsAtHeadL.lean. `lendRow` compares names and counts and cuts the runs at
the entries' starts. StatedAtHeadW.lean in this folder held the names and the counts that the pair
carries. Here: what it takes and spends; so that the frame lends; and the starts, against K1's
`startR`.

  `dueW_W`, `dueRest_WFull`   the written table's counts for the test's two parts; the text's count
  `spent_W_written`, `spent_named_W`   the first part spends one run, by owner, start, count, and by
                 name; the second none
  `starts_W`, `starts_W_bite`   THE FOUR ENTRIES TO THE SECOND PART, AND THE SPENT ONE, START WHERE
                 `K1.startR` SAYS at the written plans and the senders' own rides; two controls
  `fit_W`       each of the pair's parts states just what the book has for it
  `placeW_in_WP`   the place is the written description's last chain's
  `lendRow_W`   at the written description: `lendRow` returns at every run's coins
  `lendRow_W_at_head`   UNDER THE HEAD: the same at whatever book the maker returns at the head's
                 own sendings

Limits.
- THE JOB IS ASKED ONLY ITS PUBLIC FIELDS (hp, hm, hf, hs): at `bareW` under the head these are
  `membersW_head`'s and `freshW_head`'s; at `jobW` they are not shown here.
- WHAT IS HANDED IS NOT DESCRIBED: only that something is.
- THE STARTS ARE NUMBERS AGAINST NUMBERS: that a sender lays its message's run there is `K1.rowsR`'s
  text (`rowsR_congr`, `csAt`); no law here says that a row read at the test is the row sent. OF THE
  FOUR, TWO CAN SAY NO: the index-mask message's and W's second. W's first is `startR` at 0, Omega's
  a literal 0 against the written 0: both hold by make. The three entries to the first part are in
  no clause; they bear the same starts in the written list.
- The laws stand at `(proverSideOfProximityTest J).parts`. `halfW` lays the pair behind the guard: that the guard
  keeps a part's takes, spends and carries is its head's word; the bridge for `lendRow` is not here.
- At `jobW` the clause hm wants `msgK1 senderW JW.P JW.ride 0 = rowWF`: equal where the ride is none
  at message 0 (JobW.lean's limits).
- It is not "`ready` returns" nor "`chainSteps` returns": `laysLastB` (StepsReturnLast.lean) has the
  frame's tests.
- No filling is named. The written facts' own limits bind: evaluations in Lean's kernel beneath.
- What may be said of this pair on hiding stands in the head of
  Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfW.lean.
- The full size alone. It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.StatedAtHeadW
import AtFullSide.K14.FoldsWritten
import AtFullSide.K14.RawBookRowsWritten
import AtFullSide.K14.RawMineAtK13
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.Small.LendsRowOf
import Johnson.Desc.ProofFile.Honest.K14.BookForAtPure
import Johnson.Desc.ProofFile.Honest.K1.Law.RideAtPlans
import Johnson.AtFull.ProofPlan.At.PlacesOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open H2K.Member (piWFull)
open P2Law.ProofPlan (WP wp_placesOk)
open Johnson.G (proofSendsFull)
open AtFullSide.K14 (rawAheadW rawSegW rawRowsSecondW foldsFirstW rawCarriesWW
  bookWhole_returns_written_ahead rawBookRows_written rawWhole_is_raw)
open P5J (TS)

/-! ## 1 The closed facts -/

set_option maxRecDepth 1000000 in
/-- The written table's counts for the test's two parts. -/
theorem dueW_W : dueAt rawRowsSecondW ⟨placeW, 0⟩ = ⟨0, 0⟩ ∧
    dueAt rawRowsSecondW ⟨placeW, 1⟩ = ⟨0, 12778⟩ := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The text's count for the second part is that number. -/
theorem dueRest_WFull : dueRest piWFull.nums.stages = 12778 := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At the written list of the book's entries the first part spends one entry**: its owner is W's
sending; it starts at (0, 3882) and counts (0, 11). The second part spends none. Evaluations in
Lean's kernel over the whole written list. -/
theorem spent_W_written :
    ((rawAheadW.filter fun e => e.spender == ⟨placeW, 0⟩).filter (·.once)).map (fun e =>
        (e.owner, e.start, e.count)) =
        [(senderW, ⟨0, 3882⟩, ⟨0, 11⟩)] ∧
      (rawAheadW.filter fun e => e.spender == ⟨placeW, 1⟩).filter (·.once) = [] := by
  unfold rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **THE RUNS BEGIN WHERE THE SENDERS' OWN RECKONING SAYS.** The four written entries to the second
part, and where `K1.startR` lays the messages: the index-mask message, W's two; Omega's message 0
is a literal (the head says which can say no). The spent entry stands where W's second message
begins. -/
theorem starts_W :
    (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 1⟩).map (·.start) =
      [K1.startR VerifiableInference.Desc.K1.parGF
          (ProofFile.Honest.K1.firstRide VerifiableInference.Desc.K1.qFull)
          (VerifiableInference.Desc.K1.parGF.sent.size - 1),
       K1.startR VerifiableInference.Desc.K1.parWF
          (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold VerifiableInference.Desc.K1.qFull.lin)) 0,
       ⟨0, 0⟩,
       K1.startR VerifiableInference.Desc.K1.parWF
          (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold VerifiableInference.Desc.K1.qFull.lin)) 1] ∧
    K1.startR VerifiableInference.Desc.K1.parWF
        (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold VerifiableInference.Desc.K1.qFull.lin)) 1 =
      ⟨0, 3882⟩ := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluation can fail: at the first sending's message 3 in the place of its last it says no;
and with W's message 0 in the place of its message 1. -/
theorem starts_W_bite :
    decide ((rawCarriesWW.filter fun e => e.spender == ⟨placeW, 1⟩).map (·.start) =
      [K1.startR VerifiableInference.Desc.K1.parGF
          (ProofFile.Honest.K1.firstRide VerifiableInference.Desc.K1.qFull) 3,
       K1.startR VerifiableInference.Desc.K1.parWF
          (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold VerifiableInference.Desc.K1.qFull.lin)) 0,
       ⟨0, 0⟩,
       K1.startR VerifiableInference.Desc.K1.parWF
          (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold VerifiableInference.Desc.K1.qFull.lin)) 1]) =
      false ∧
    decide (K1.startR VerifiableInference.Desc.K1.parWF
        (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold VerifiableInference.Desc.K1.qFull.lin)) 0 =
      ⟨0, 3882⟩) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test's place is a place of the written description's last chain. -/
theorem placeW_in_WP : placeW ∈ placesAt WP 2 := by decide +kernel

/-! ## 2 On the book -/

/-- **At the written entries the first part spends one run, by name and count; the second none.** -/
theorem spent_named_W {B : ProverCoinCounts} (he : B.ahead = rawAheadW) :
    (spentE B ⟨placeW, 0⟩).map Ahead.named =
        [(runName foldMaskRun ⟨placeW, 0⟩ "fold", ⟨0, 11⟩)] ∧
      spentE B ⟨placeW, 1⟩ = [] := by
  obtain ⟨s0, s1⟩ := spent_W_written
  have e0 : spentE B ⟨placeW, 0⟩ =
      (rawAheadW.filter fun e => e.spender == ⟨placeW, 0⟩).filter (·.once) := by
    unfold spentE
    rw [he]
  have e1 : spentE B ⟨placeW, 1⟩ =
      (rawAheadW.filter fun e => e.spender == ⟨placeW, 1⟩).filter (·.once) := by
    unfold spentE
    rw [he]
  refine ⟨?_, e1.trans s1⟩
  have hlen : (spentE B ⟨placeW, 0⟩).length = 1 := by
    rw [e0, ← List.length_map (f := fun e : Ahead => (e.owner, e.start, e.count)), s0]
    rfl
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.1 hlen
  have hf : (⟨"the fold's fresh mask to 3.-.2.0: fold", senderW, ⟨0, 3882⟩, ⟨0, 11⟩,
      ⟨placeW, 0⟩, true⟩ : Ahead) ∈ foldsFirstW :=
    List.mem_of_getElem? (i := 26) rfl
  have hm : (⟨"the fold's fresh mask to 3.-.2.0: fold", senderW, ⟨0, 3882⟩, ⟨0, 11⟩,
      ⟨placeW, 0⟩, true⟩ : Ahead) ∈ spentE B ⟨placeW, 0⟩ := by
    rw [e0]
    refine List.mem_filter.2 ⟨List.mem_filter.2 ⟨?_, by decide⟩, rfl⟩
    unfold rawAheadW
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hf))))))))
  rw [hy] at hm ⊢
  obtain rfl := List.mem_singleton.1 hm
  decide +kernel

variable {V W X : Type}

/-- hB is a premise. **EACH OF THE PAIR's PARTS STATES JUST WHAT THE BOOK HAS FOR IT.** At any job
with these public fields. -/
theorem fit_W {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) (J : TestJob W X) (hp : J.p.place = placeW)
    (hm : J.members = membersWF) (hf : J.fresh = some (senderW, 1))
    (hs : J.p.nums.stages = piWFull.nums.stages) :
    ∀ i p, (proverSideOfProximityTest (V := V) J).parts[i]? = some p →
      p.takes = dueAt (B.rowsOf 2) ⟨placeW, i⟩ ∧
        (spentE B ⟨placeW, i⟩).map Ahead.named = p.spends ∧
        (carryE B ⟨placeW, i⟩).map Ahead.named = p.carries := by
  obtain ⟨B₀, h₀, he⟩ := bookWhole_returns_written_ahead
  obtain rfl : B = B₀ := Except.ok.inj (hB.symm.trans h₀)
  obtain ⟨s0, s1⟩ := spent_named_W he
  obtain ⟨t0, t1⟩ := statedW_W
  have hr : B.rowsOf 2 = rawRowsSecondW :=
    (rawBookRows_written _ B (rawWhole_is_raw hB)).2.2
  have m0 : memberRuns J ⟨placeW, 0⟩ =
      membersWF.map fun m => (carriedName m.1 m.2.1 ⟨placeW, 0⟩, m.2.2) := by
    unfold memberRuns
    rw [hm]
  have m1 : memberRuns J ⟨placeW, 1⟩ =
      membersWF.map fun m => (carriedName m.1 m.2.1 ⟨placeW, 1⟩, m.2.2) := by
    unfold memberRuns
    rw [hm]
  have es : spentRun J = (runName foldMaskRun ⟨placeW, 0⟩ "fold", ⟨0, 11⟩) := by
    show (runName foldMaskRun ⟨J.p.place, 0⟩ "fold",
      (⟨0, 2 * (J.p.nums.stages.headD default).k + 1⟩ : Due)) = _
    rw [hp, hs]
    rfl
  have ef : freshRun J = (carriedName senderW 1 ⟨placeW, 1⟩,
      ⟨0, dueFresh (piWFull.nums.stages.headD default)⟩) := by
    show (carriedName (J.fresh.getD (⟨J.p.place, 0⟩, 0)).1 (J.fresh.getD (⟨J.p.place, 0⟩, 0)).2
      ⟨J.p.place, 1⟩, (⟨0, dueFresh (J.p.nums.stages.headD default)⟩ : Due)) = _
    rw [hf, hp, hs]
    rfl
  have c0 := carryE_at_W hB (a := ⟨placeW, 0⟩) (Or.inl rfl)
  have c1 := carryE_at_W hB (a := ⟨placeW, 1⟩) (Or.inr rfl)
  intro i p hq
  match i, hq with
  | 0, hq =>
    obtain rfl := Option.some.inj hq
    have f0 : ((firstPart J : Part V W X).takes, (firstPart J : Part V W X).spends,
        (firstPart J : Part V W X).carries) =
        (⟨0, 0⟩, [spentRun J], memberRuns J ⟨J.p.place, 0⟩) := by
      simp only [firstPart, hf]
    obtain ⟨g1, g2, g3⟩ : (firstPart J : Part V W X).takes = ⟨0, 0⟩ ∧
        (firstPart J : Part V W X).spends = [spentRun J] ∧
        (firstPart J : Part V W X).carries = memberRuns J ⟨J.p.place, 0⟩ := by
      simpa using f0
    refine ⟨?_, ?_, ?_⟩
    · rw [g1, hr]
      exact dueW_W.1.symm
    · rw [g2, es]
      exact s0
    · rw [g3, hp, m0, c0]
      exact t0.symm
  | 1, hq =>
    obtain rfl := Option.some.inj hq
    refine ⟨?_, ?_, ?_⟩
    · show (⟨0, dueRest J.p.nums.stages⟩ : Due) = _
      rw [hs, dueRest_WFull, hr]
      exact dueW_W.2.symm
    · rw [s1]
      rfl
    · show _ = memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J]
      rw [hp, m1, ef, c1]
      exact t1.symm
  | _ + 2, hq => cases hq

/-- hB is a premise. **AT THE WRITTEN DESCRIPTION THE FRAME LENDS THE PAIR, AT EVERY RUN's
COINS.** -/
theorem lendRow_W {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) (J : TestJob W X) (hp : J.p.place = placeW)
    (hm : J.members = membersWF) (hf : J.fresh = some (senderW, 1))
    (hs : J.p.nums.stages = piWFull.nums.stages) (k : Coins B) :
    ∃ c, lendRow B (B.rowsOf 2) (k.look 2) placeW (proverSideOfProximityTest (V := V) J).parts 0 = .ok c :=
  lendRow_of_fit (F := WP) (bookWhole_word hB) wp_placesOk (ch := 2) (Or.inr (Or.inr rfl))
    placeW_in_WP k _ 0 fun i p hq => by
      rw [Nat.zero_add]
      exact fit_W hB J hp hm hf hs i p hq

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- hW IS A PREMISE. **UNDER THE HEAD, AT THAT BOOK, THE FRAME LENDS THE PAIR.** CONDITIONAL on
h. -/
theorem lendRow_W_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x₀) {Bk : ProverCoinCounts}
    (hW : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 Zp.made.proof.2.1
      Zp.made.proof.2.2 (mergesByName cF.blocksInOrder) = .ok Bk) (J : TestJob W X)
    (hp : J.p.place = placeW) (hm : J.members = membersWF) (hf : J.fresh = some (senderW, 1))
    (hs : J.p.nums.stages = piWFull.nums.stages) (k : Coins Bk) :
    ∃ c, lendRow Bk (Bk.rowsOf 2) (k.look 2) placeW (proverSideOfProximityTest (V := V) J).parts 0 = .ok c := by
  obtain ⟨B₀, h₀, -⟩ := bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_made h₀ h).symm.trans hW)
  exact lendRow_W h₀ J hp hm hf hs k

end AtFullSide.K12

#print axioms AtFullSide.K12.dueW_W
#print axioms AtFullSide.K12.dueRest_WFull
#print axioms AtFullSide.K12.spent_W_written
#print axioms AtFullSide.K12.starts_W
#print axioms AtFullSide.K12.starts_W_bite
#print axioms AtFullSide.K12.placeW_in_WP
#print axioms AtFullSide.K12.spent_named_W
#print axioms AtFullSide.K12.fit_W
#print axioms AtFullSide.K12.lendRow_W
#print axioms AtFullSide.K12.lendRow_W_at_head
