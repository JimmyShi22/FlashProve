-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/BookAtK8.lean: the smallness test and the book of coins: at whatever book the maker
returns at the protocol's public files no entry names a part of kind K8, as spender or as owner, and
the first chain's table has no count for such a part. So the part is lent its coins, which are none,
at every run's coins, and no other part spends a coin of it. Statements with their proofs.

  `noK8`, `noK8_wants`, `noK8_seg`, `noK8_short`, `noK8_all`   the test on an entry, at the written
                  description's entries, piece by piece: evaluations in Lean's kernel
  `noK13_bent`     the like test at K13 says no: the test can fail
  `noK8_rows`      no row of the first chain's written table is at a part of the kind
  `k8_noneSpent`, `k8_mine`, `k8_due`   the three facts at the book that the maker returns at the
                  written description and lists
  `k8_ahead_any`, `k8_rows_any`, `k8_cuts_written`, `k8_cuts`   the book's other tests at the kind's
                  places: the cut there is one part of one round
  `book_at_maker`  where the maker returns A under the head, A's book is that book
  `k8_lendRow`     **the frame's lendRow returns at the kind's row, at every run's coins**

What is assumed. The head, and that the maker returns. The sendings' labels and the merges' guess are
as in AtFullSide/K14/RawMineAtK13.lean's head: that file's limits hold here.
Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K14.RawMineAtK13
import Johnson.Desc.ProofFile.Honest.K14.BookAtPure
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.BookWholeAlikeGuess
import Johnson.Desc.ProofFile.Honest.BookLends
import Johnson.Desc.ProofFile.Honest.Small.Field
import Johnson.Desc.ProofFile.Honest.K8.Side
import Johnson.Desc.ProofFile.Honest.BookRawRows
import Johnson.Desc.ProofFile.Honest.BookWritten.Cuts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8
open ProofFile.Honest ProofFile.Honest.K8 ProofFile.Honest.K14
open AtFullSide.K14
open VerifiableInference.Desc (Place Chain KindName)
open VerifiableInference.Desc.First.K8 (Par)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.Small (noneSpent)
open P5J (AtMgA TS)

/-- The test on an entry: neither its spender nor its owner is a part of kind K8. -/
def noK8 (e : Ahead) : Bool := e.spender.place.kind != .K8 && e.owner.place.kind != .K8

set_option maxRecDepth 1000000 in
/-- The test accepts the stretches' entries. -/
theorem noK8_wants : (rawWantsW.map (·.entry)).all noK8 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: K13's part spends by a stretch. -/
theorem noK13_bent :
    (rawWantsW.map (·.entry)).all (fun e => e.spender.place.kind != .K13) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test accepts the carrying entries of the chain of segments. -/
theorem noK8_seg : rawSegW.all noK8 = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test accepts the written pieces' entries. -/
theorem noK8_short : rawShortW.all noK8 = true := by
  decide +kernel

/-- **The test accepts all the written entries.** -/
theorem noK8_all : rawAheadW.all noK8 = true :=
  rawAll_whole _ noK8_wants noK8_seg noK8_short

set_option maxRecDepth 1000000 in
/-- No row of the first chain's written table is at a part of the kind. -/
theorem noK8_rows : rawRowsFirstW.all (fun r => r.1.place.kind != .K8) = true := by
  decide +kernel

section Book
variable {B : ProverCoinCounts}

/-- What the test says of an entry of the book. -/
theorem noK8_entry (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {e : Ahead} (he : e ∈ B.ahead) :
    e.spender.place.kind ≠ .K8 ∧ e.owner.place.kind ≠ .K8 := by
  rw [rawAhead_written B (rawWhole_is_raw hB)] at he
  have h := List.all_eq_true.1 noK8_all e he
  simpa [noK8] using h

/-- **No entry spends a coin of a part of the kind.** -/
theorem k8_noneSpent (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {a : Addr} (ha : a.place.kind = .K8) :
    noneSpent B a = true := by
  unfold noneSpent
  refine List.all_eq_true.2 fun e he => ?_
  have hne : e.owner ≠ a := fun h => (noK8_entry hB he).2 (h ▸ ha)
  simp [hne]

/-- **No entry names a part of the kind as its spender.** -/
theorem k8_mine (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {a : Addr} (ha : a.place.kind = .K8) :
    (B.ahead.filter fun e => e.spender == a) = [] := by
  refine List.filter_eq_nil_iff.2 fun e he hs => ?_
  exact (noK8_entry hB he).1 ((beq_iff_eq.1 hs) ▸ ha)

/-- **The first chain's table has no count for a part of the kind.** -/
theorem k8_due (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {a : Addr} (ha : a.place.kind = .K8) :
    dueAt (B.rowsOf 0) a = ⟨0, 0⟩ := by
  have h : B.rowsOf 0 = rawRowsFirstW := (rawBookRows_written _ B (rawWhole_is_raw hB)).1
  rw [h]
  unfold dueAt
  have hl : rawRowsFirstW.lookup a = none := by
    refine List.lookup_eq_none_iff.2 fun r hr => ?_
    have hk := List.all_eq_true.1 noK8_rows r hr
    have hne : a ≠ r.1 := fun e => by
      rw [← e, ha] at hk
      simp at hk
    simpa using hne
  rw [hl]
  rfl

/-- No entry's spender stands at a place of the kind. -/
theorem k8_ahead_any (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {a : Place} (ha : a.kind = .K8) (n : Nat) :
    B.ahead.any (fun e => e.spender.place == a && decide (n ≤ e.spender.part)) = false := by
  refine List.any_eq_false.2 fun e he hc => ?_
  obtain ⟨h1, -⟩ := Bool.and_eq_true_iff.1 hc
  exact (noK8_entry hB he).1 ((beq_iff_eq.1 h1) ▸ ha)

/-- No row of the first chain's table stands at a place of the kind. -/
theorem k8_rows_any (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {a : Place} (ha : a.kind = .K8) (n : Nat) :
    (B.rowsOf 0).any (fun r => r.1.place == a && decide (n ≤ r.1.part)) = false := by
  have h : B.rowsOf 0 = rawRowsFirstW := (rawBookRows_written _ B (rawWhole_is_raw hB)).1
  rw [h]
  refine List.any_eq_false.2 fun r hr hc => ?_
  obtain ⟨h1, -⟩ := Bool.and_eq_true_iff.1 hc
  have hk := List.all_eq_true.1 noK8_rows r hr
  rw [beq_iff_eq.1 h1, ha] at hk
  simp at hk

set_option maxRecDepth 1000000 in
/-- At each place of the kind in the written list the book's cut is one part of one round. -/
theorem k8_cuts_written : (P5J.At.ps.filter (·.kind == .K8)).all
    (fun p => (cutsFirstW ++ cutsSharedW ++ cutsSecondW).lookup p == some [1]) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- That list has the kind's 25 places: the test above is not idle. -/
theorem k8_ps_count : (P5J.At.ps.filter (·.kind == .K8)).length = 25 := by
  decide +kernel

/-- **The book's cut at a place of the kind.** -/
theorem k8_cuts (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {a : Place} (ha : a ∈ P5J.At.ps) (hk : a.kind = .K8) :
    B.cuts.lookup a = some [1] := by
  obtain ⟨r0, r1, r2, s0, s1, s2, tail, -, -, -, -, -, -, -, -, -, -, hc⟩ :=
    bookRaw_rows (rawWhole_is_raw hB)
  rw [hc, cutsOf_written]
  have h := List.all_eq_true.1 k8_cuts_written a (List.mem_filter.2 ⟨ha, by simp [hk]⟩)
  exact beq_iff_eq.1 h

end Book

section Maker
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **Where the maker returns A under the head, A's book is the book at the written description.** -/
theorem book_at_maker (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok A.B := by
  obtain ⟨-, -, hF, -⟩ := atPure_ok hA
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (hF.symm.trans h.laid.value)
  obtain ⟨k0, k1, k2, e, p0, p1, p2, hs, hB⟩ := atPure_book hA
  obtain ⟨En, hl⟩ := sends_written_at_files h.scope h.laid hs
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨-, -, -, -, rfl, rfl, rfl⟩ := hl
  rw [eF] at hB
  exact (bookWhole_planAlike_guess (planAlike_at_head h) _ _ _).trans hB

/-- **The frame's lendRow returns at the kind's row, at every run's coins.** p: a place of the
first chain's. -/
theorem k8_lendRow (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {W₁ R₁ Xi T₁ X₁ : Type}
    (cells : T₁ → Cells) (Q : Par × List (Nat × String × Nat))
    (hpl : smallPlace Q.1 ∈ placesAt (P5J.F0T OnBytes.secondHashFunction Zp Np cF) 0) (k : Coins A.B) :
    ∃ c, lendRow A.B (A.B.rowsOf 0) (k.look 0) (smallPlace Q.1)
      (smallHalf (W₀ := W₁) (Rc := R₁) (Xi := Xi) (X := X₁) cells Q).parts 0 = .ok c := by
  have hB := book_at_maker h hA
  have ha : (⟨smallPlace Q.1, 0⟩ : Addr).place.kind = .K8 := rfl
  have hm := k8_mine hB ha
  have hw : A.B.word (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = none :=
    bookWhole_word ((bookWhole_planAlike_guess (planAlike_at_head h) _ _ _).symm.trans hB)
  obtain ⟨c0, e0⟩ := lendPart_of_fit (V := Local W₁ R₁ Xi T₁) (W := Local W₁ R₁ Xi T₁) (Y := X₁)
    (p := (smallPart Q.1).lift (askOfInput cells Q.2) (askOfInput cells Q.2) (fun _ => ())
      fun x _ => x) hw (Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk) (Or.inl rfl)
    (a := ⟨smallPlace Q.1, 0⟩) hpl (k8_due hB ha).symm
    (by simp [spentE, hm]; rfl) (by simp [carryE, hm]; rfl) k
  refine ⟨(c0, ()), ?_⟩
  show ((lendPart A.B (A.B.rowsOf 0) (k.look 0) ⟨smallPlace Q.1, 0⟩ _).mapError _).bind _ = _
  rw [e0]
  rfl

end Maker

end AtFullSide.K8

#print axioms AtFullSide.K8.noK8_all
#print axioms AtFullSide.K8.noK13_bent
#print axioms AtFullSide.K8.noK8_rows
#print axioms AtFullSide.K8.k8_noneSpent
#print axioms AtFullSide.K8.k8_mine
#print axioms AtFullSide.K8.k8_due
#print axioms AtFullSide.K8.k8_ahead_any
#print axioms AtFullSide.K8.k8_rows_any
#print axioms AtFullSide.K8.k8_cuts_written
#print axioms AtFullSide.K8.k8_ps_count
#print axioms AtFullSide.K8.k8_cuts
#print axioms AtFullSide.K8.book_at_maker
#print axioms AtFullSide.K8.k8_lendRow
