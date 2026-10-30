-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/KeepAtMerge.lean: the eight public tests of `keep24` (K11PubClosed.lean)
pass the accepting step of the merge of the claims on the committed table, at the composed meaning
`mgAll D Mg`: the premise hkeep of `merge_pubHeld_full`, to the letter. Two definitions, and
theorems with their proofs.

How. By cases on the eight. At the composed meaning a public test is `pubAll D.pubD Mg.pub`
(`mgAll_pub`). The two tests "lookOut 24 3" and "lookOut 24 8" are the lookup arguments' `lookOutC`
(`pubAll_lookOut`), which passes any step that leaves what it reads (`k3OnOut_step`,
Johnson/Desc/First/Look/K3OnOutStep.lean): the merge's step leaves what the two lookups' verifiers
have heard (`isLocal`, Law.lean); its ledger behind is later (`decide_later`, Keeps.lean); and it
turns no slot below the ledger's next free number in front (`merge_below_next`, LedgerBehind.lean).
The six tests "formsIn 24 k r" stand for ten runs of claims (`pubAll_formsIn`; the table's `runsOf`
at the output head's sort of segment): nine go by `formsIn_merge` (FormsAcross.lean), the
approximate range proof's own run by `formsInA_merge` (FormsAheadAcross.lean). Their premises on the
ledger's sizes and on the free slot come from the table's own two tests `ledgerB` and `freeAboveB`
in front. Which runs the six stand for is read off the table's own `runsOf` at `linksFull` by
evaluation; the lemma six_are_ten (FormsBackAtMerge.lean) is not called, and neither are
`merge_ledger` (LedgerBehind.lean) and `merge_sameOn` (KeepsAt.lean).

Main names:
  `segAt_of_fork`, `sized_of_ledgerB`, `free_of_above`, `getD_in`: where a ledger is open the open
    segment's part is there; what the table's two tests on the ledger give.
  `merge_forks`, `merge_reads`: the merge's accepting step, read at what the eight tests read: the
    two ledgers; what has been heard; the parameters of the approximate range proof and the tables
    with their weights.
  `sorts_at_head`: where the output head's segment has the number 24 (`headLink X = 24`), the lookup
    arguments' part answers at the pieces 3 and 8 of that segment.
  `lookOut_keeps`: `lookOutC` passes the step.
  `NotLate Rd P piece run s`: the slot of the merge's end value is none of the run's late slots.
  `RunsPass Rd P a b`: WHAT STAYS A PREMISE: for each of NINE of the ten runs, a field `fwd_‹run›`
    (the run's reader answers behind what it answers in front: `Fwd`,
    Johnson/Desc/Reads/FormsPass.lean) and a field `late_‹run›` (`NotLate`). The number in a field's
    name is the run's sub-protocol's number in front of the batching, from 0.
  `small_late`, `equations_forms`, `equations_pass`: at the tenth, the approximate range proof's own
    run, both facts hold outright: its reader has no late slot, and reads of the state what
    `merge_reads` says is left (`smallReader_same`, Johnson/Desc/First/Batch/ReadersAt.lean).
  `run_keeps`, `formsItem_keeps`: one run; one test "formsIn 24 k r".
  `keep_at_merge`: THE EIGHT. `keep_at_merge_head`: the same under the one equation `headLink X =
    24` in the place of h3 and h8.
  `ledger_at_front`: out of the table's condition at border 346, at an unmarked state: `ledgerB`
    accepts, and `freeAboveB` at some number.
  `keep_at_merge_on`: the eight, with that condition in front in the place of the two tests.

Limits. NO EXAMPLE: six of the eight cases stand under eighteen premises on the runs (`RunsPass`)
that are neither shown nor evaluated at any state. IDLE CASES: each of the eight cases is an
implication from the test in front: where a test of the eight rejects in front, its case asks
nothing; every field of `RunsPass` asks nothing where the run's reader answers nothing, and where
D.lk 24 is none all eighteen are free, and there the six tests reject in front. Other premises that
are shown at no value here: `headLink X = 24` (in `keep_at_merge`: h3 and h8, two tests with code on
the public parameters, which hold together just where that equation holds; without them `pubAll`
hands the two tests to Mg.pub, of which nothing is known); D.links = `linksFull`; Mg.more = {}; in
the forms without the table's condition, `ledgerB` and `freeAboveB` in front. No accepting step of
the merge is exhibited. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.K11PubClosed
import Johnson.Top.H0.MergeLaw.FormsAheadAcross
import Johnson.Desc.First.Look.K3OnOutStep
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.K9 (segAt? lateAt formsIn formsInA Readers)
open VerifiableInference.Desc.K3 (sizedB freeB heardAt k3OnOut)
open VerifiableInference.Desc.First.Look (K3Data k3SortAt lookOutC placeAt)
open VerifiableInference.Desc.Sound (MgData mgAll mgAll_pub keep24 linksFull runsAt CellsQ MsgT
  k11_hIn)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-! ## The ledger in front -/

/-- Where a ledger is open, the open segment's part is there, with that ledger. -/
theorem segAt_of_fork {s : S} {F : Fork} (h : s.fork? = some F) :
    ∃ pa, segAt? s = some pa ∧ pa.F = F := by
  have hL : ∃ L, s.link? = some L := by
    cases e : s.here with
    | between => simp [S.fork?, e] at h
    | lay a => exact ⟨a.L, by simp [S.link?, e]⟩
    | att a => exact ⟨a.L, by simp [S.link?, e]⟩
    | head a =>
      cases ho : a.opened with
      | false => simp [S.fork?, e, ho] at h
      | true => exact ⟨a.L, by simp [S.link?, e, ho]⟩
    | fin a => simp [S.fork?, e] at h
    | mem a => simp [S.fork?, e] at h
  have hT : ∃ tl, s.tl? = some tl := by
    cases e : s.here with
    | between => simp [S.fork?, e] at h
    | lay a => exact ⟨a.tl, by simp [S.tl?, e]⟩
    | att a => exact ⟨a.tl, by simp [S.tl?, e]⟩
    | head a =>
      cases ho : a.opened with
      | false => simp [S.fork?, e, ho] at h
      | true => exact ⟨a.tl, by simp [S.tl?, e, ho]⟩
    | fin a => simp [S.fork?, e] at h
    | mem a => simp [S.fork?, e] at h
  obtain ⟨L, hL⟩ := hL
  obtain ⟨tl, hT⟩ := hT
  simp only [segAt?, hL, h, hT, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  exact ⟨_, rfl, rfl⟩

/-- The table's test on the ledger: a ledger is open, of the right sizes. -/
theorem sized_of_ledgerB {s : S} (h : ledgerB s = true) : ∃ F, s.fork? = some F ∧ Sized F := by
  unfold ledgerB at h
  cases e : s.fork? with
  | none =>
    rw [e] at h
    simp at h
  | some F =>
    rw [e] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨F, rfl, h.1.1, h.1.2, h.2⟩

/-- Inside an array the value that stands for "not there" is not read. -/
theorem getD_in {xs : Array Bool} {i : ℕ} (h : i < xs.size) (d d' : Bool) :
    xs.getD i d = xs.getD i d' := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h]
  rfl

/-- The table's test "free above": no slot from the ledger's next free number on is filled. -/
theorem free_of_above {s : S} {F : Fork} {n : ℕ} (hF : s.fork? = some F) (hS : Sized F)
    (h : freeAboveB n s = true) (j : ℕ) : F.gotF.getD (F.next + j) false = false := by
  unfold freeAboveB at h
  rw [hF] at h
  simp only [Option.any_some, Bool.and_eq_true] at h
  by_cases hj : j < F.ns - F.next
  · have e := List.all_eq_true.1 h.1 j (List.mem_range.2 hj)
    have hin : F.next + j < F.gotF.size := by
      rw [hS.2.2]
      omega
    rw [getD_in hin false true]
    simpa using e
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [hS.2.2]; omega)]
    rfl

/-! ## The merge's accepting step -/

/-- **The merge's accepting step, read at what the eight tests read.** -/
theorem merge_forks (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') {F : Fork} (hF : s.fork? = some F) :
    ∃ x x' : HeadOwn, s.here = .head x ∧ s'.here = .head x' ∧ x.F = F ∧
      s'.fork? = some x'.F ∧ Later F x'.F ∧ s'.tl? = s.tl? ∧ s'.lookHeard? = s.lookHeard? := by
  obtain ⟨x, x', hx, hx', -, ex, -⟩ := isLocal P s rs s' h
  obtain ⟨y, y', hy, hy', hl⟩ := decide_later h
  obtain rfl : y = x := by
    rw [hx] at hy
    exact (Here.head.inj hy).symm
  obtain rfl : y' = x' := by
    rw [hx'] at hy'
    exact (Here.head.inj hy').symm
  have ho : y.opened = true := by
    cases e : y.opened with
    | true => rfl
    | false => simp [S.fork?, hx, e] at hF
  have eF : y.F = F := by simpa [S.fork?, hx, ho] using hF
  have ho' : y'.opened = true := by
    rw [ex]
    exact ho
  have et : y'.tl = y.tl := by rw [ex]
  have eh : y'.lookHeard = y.lookHeard := by rw [ex]
  refine ⟨y, y', hx, hx', eF, by simp [S.fork?, hx', ho'], eF ▸ hl, ?_, ?_⟩
  · simp [S.tl?, hx, hx', ho, ho', et]
  · simp [S.lookHeard?, hx, hx', ho, ho', eh]

/-- The merge's accepting step leaves the parameters of the approximate range proof, and the tables
with their weights. -/
theorem merge_reads (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') : s'.tl? = s.tl? ∧ s'.funs? = s.funs? := by
  obtain ⟨x, x', hx, hx', -, ex, -⟩ := isLocal P s rs s' h
  have eo : x'.opened = x.opened := by rw [ex]
  have et : x'.tl = x.tl := by rw [ex]
  have ef : x'.t = x.t := by rw [ex]
  constructor
  · simp [S.tl?, hx, hx', eo, et]
  · simp [S.funs?, hx, hx', eo, ef]

/-! ## The two tests of the lookup arguments -/

/-- Where the output head's segment has the full size's number, the lookup arguments' part answers
at the pieces 3 and 8 of segment 24. -/
theorem sorts_at_head {X : OnBytes.Model.Verify.Public}
    (hH : VerifiableInference.OnPublicFiles.headLink X = 24) :
    k3SortAt X 24 3 = some false ∧ k3SortAt X 24 8 = some true := by
  have hh : K3.isHead X 24 = true := by
    unfold K3.isHead
    unfold VerifiableInference.OnPublicFiles.headLink at hH
    rw [hH]
    rfl
  have p8 : K3.pieceAt X 24 true = 8 := by
    unfold K3.pieceAt
    rw [hh]
    rfl
  have p3 : K3.pieceAt X 24 false = 3 := by
    unfold K3.pieceAt
    rw [hh]
    rfl
  constructor
  · unfold k3SortAt
    rw [p8, p3]
    rfl
  · have h := First.Look.sort_digits X 24
    rw [p8] at h
    exact h

/-- **The lookup arguments' test behind a lookup passes the merge's accepting step.** -/
theorem lookOut_keeps (d : K3Data) (m : ℕ) (dg : Bool) (P : HeadMergeP) {a b : S}
    {rs : List Fmt.RoundView} (hy : headMergeDecide P a rs = .ok b) (hled : ledgerB a = true)
    (h : lookOutC d m dg a = true) : lookOutC d m dg b = true := by
  unfold lookOutC at h ⊢
  cases e : placeAt d.X m dg with
  | none =>
    rw [e] at h
    simp at h
  | some p =>
    rw [e] at h
    simp only [Option.any_some] at h ⊢
    obtain ⟨F, hF, hS⟩ := sized_of_ledgerB hled
    obtain ⟨x, x', hx, hx', rfl, hG, hl, htl, hlh⟩ := merge_forks P hy hF
    have hS' : Sized x'.F := hl.sized hS
    have hh : heardAt p.digits b = heardAt p.digits a := by
      unfold heardAt
      rw [htl, hlh]
    have hsz : sizedB x'.F = true := by
      simp [sizedB, hS'.1, hS'.2.1, hS'.2.2]
    refine VerifiableInference.OnPublicFiles.k3OnOut_step p a b x.F x'.F hF hG hh hl.next hsz ?_ h
    intro first n hn hf
    unfold freeB at hf ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
    refine ⟨by rw [hl.ns]; exact hf.1, ?_⟩
    rw [List.all_eq_true]
    intro j hj
    have hj' : j < n := List.mem_range.1 hj
    have e0 := List.all_eq_true.1 hf.2 j hj
    have hin : first + j < x.F.gotF.size := by
      rw [hS.2.2]
      omega
    have hin' : first + j < x'.F.gotF.size := by
      rw [hS'.2.2, hl.ns]
      omega
    have e1 : x.F.gotF.getD (first + j) false = false := by
      rw [getD_in hin false true]
      simpa using e0
    have e2 : ¬ Filled x'.F (first + j) := fun hfil => by
      have := (merge_below_next P hy hx hx' hS (first + j) (by omega)).1 hfil
      unfold Filled at this
      rw [e1] at this
      cases this
    have e3 : x'.F.gotF.getD (first + j) false = false := by
      unfold Filled at e2
      simpa using e2
    rw [getD_in hin' true false, e3]
    rfl

/-! ## The six tests on the runs' forms -/

/-- The slot of the merge's end value is none of the run's late slots. -/
def NotLate (Rd : Readers) (P : HeadMergeP) (piece : ℕ) (run : String) (s : S) : Prop :=
  ∀ F R, s.fork? = some F → Rd.forms piece run s = some R →
    lateAt R.late (F.next + 2 * P.lay.lk + 2) = none

/-- **What stays a premise, a run a line**: the run's reader answers behind the merge what it
answers in front; the slot of the merge's end value is none of the run's late slots. -/
structure RunsPass (Rd : Readers) (P : HeadMergeP) (a b : S) : Prop where
  fwd_objects2 : Fwd Rd 2 "objects" a b
  late_objects2 : NotLate Rd P 2 "objects" a
  fwd_guests2 : Fwd Rd 2 "guests" a b
  late_guests2 : NotLate Rd P 2 "guests" a
  fwd_planes2 : Fwd Rd 2 "planes" a b
  late_planes2 : NotLate Rd P 2 "planes" a
  fwd_join3 : Fwd Rd 3 "join" a b
  late_join3 : NotLate Rd P 3 "join" a
  fwd_norm3 : Fwd Rd 3 "norm" a b
  late_norm3 : NotLate Rd P 3 "norm" a
  fwd_policy3 : Fwd Rd 3 "policy" a b
  late_policy3 : NotLate Rd P 3 "policy" a
  fwd_logits3 : Fwd Rd 3 "logits" a b
  late_logits3 : NotLate Rd P 3 "logits" a
  fwd_objects7 : Fwd Rd 7 "objects" a b
  late_objects7 : NotLate Rd P 7 "objects" a
  fwd_guests7 : Fwd Rd 7 "guests" a b
  late_guests7 : NotLate Rd P 7 "guests" a

/-- One run: its test, in either form, passes the merge's accepting step. -/
theorem run_keeps (Rd : Readers) (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (P : HeadMergeP)
    {a b : S} {rs : List Fmt.RoundView} (hy : headMergeDecide P a rs = .ok b) (hled : ledgerB a = true)
    {n : ℕ} (hfa : freeAboveB n a = true) (ah : Bool) (piece : ℕ) (run : String)
    (hf : Fwd Rd piece run a b) (hn : NotLate Rd P piece run a)
    (hin : (if ah then formsInA Rd sent own piece run a else formsIn Rd own piece run a) = true) :
    (if ah then formsInA Rd sent own piece run b else formsIn Rd own piece run b) = true := by
  obtain ⟨F, hF, hS⟩ := sized_of_ledgerB hled
  obtain ⟨pa, hpa, rfl⟩ := segAt_of_fork hF
  have hfree : pa.F.gotF.getD (pa.F.next + 2 * P.lay.lk + 2) false = false := by
    rw [Nat.add_assoc]
    exact free_of_above hF hS hfa (2 * P.lay.lk + 2)
  have hlate : ∀ R, Rd.forms piece run a = some R →
      lateAt R.late (pa.F.next + 2 * P.lay.lk + 2) = none := fun R hR => hn pa.F R hF hR
  cases ah with
  | true => exact formsInA_merge Rd sent own piece run P hy pa hpa hS hfree hf hlate hin
  | false => exact formsIn_merge Rd own piece run P hy pa hpa hS hfree hf hlate hin

/-! ### The approximate range proof's own run: both facts hold outright -/

/-- What the reader of that run answers has no late slot. -/
theorem small_late {s : S} {R : K9.Read} (h : K9.smallReader s = some R) : R.late = [] := by
  unfold K9.smallReader at h
  cases e1 : s.tl? with
  | none => simp [e1] at h
  | some tl =>
    cases e2 : s.funs? with
    | none => simp [e1, e2] at h
    | some f =>
      simp only [e1, e2, Option.some.injEq] at h
      rw [← h]

/-- At that run's name a segment's readers are that one reader, or answer nothing. -/
theorem equations_forms (lk : ℕ → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public)
    (mH m k : ℕ) :
    (∀ s, (K9.readersAt lk X mH m).forms k "K8.equations" s = K9.smallReader s) ∨
      ∀ s, (K9.readersAt lk X mH m).forms k "K8.equations" s = none := by
  cases h : lk m with
  | none =>
    right
    intro s
    rw [K9.readersAt_none lk X mH m h]
  | some l =>
    left
    intro s
    rw [K9.readersAt_some lk X mH m l h]
    unfold K9.readersOfLink K9.holesAt
    simp

/-- **The two facts at the approximate range proof's own run.** -/
theorem equations_pass (lk : ℕ → Option (Link S Claim)) (X : OnBytes.Model.Verify.Public)
    (mH m k : ℕ) (P : HeadMergeP) {a b : S} {rs : List Fmt.RoundView}
    (hy : headMergeDecide P a rs = .ok b) :
    Fwd (K9.readersAt lk X mH m) k "K8.equations" a b ∧
      NotLate (K9.readersAt lk X mH m) P k "K8.equations" a := by
  obtain ⟨et, ef⟩ := merge_reads P hy
  rcases equations_forms lk X mH m k with h | h
  · refine ⟨fun R hR => ?_, fun F R _ hR => ?_⟩
    · rw [h, K9.smallReader_same a b et ef, ← h]
      exact hR
    · rw [h] at hR
      rw [small_late hR]
      rfl
  · refine ⟨fun R hR => ?_, fun F R _ hR => ?_⟩
    · rw [h] at hR
      cases hR
    · rw [h] at hR
      cases hR

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- One test "formsIn 24 k r": l is the list of runs for which it stands at the full size. -/
theorem formsItem_keeps (hl : D.links = linksFull) (Pm : HeadMergeP) (z : P) {a b : S}
    {rs : List Fmt.RoundView} (hy : headMergeDecide Pm a rs = .ok b) (hled : ledgerB a = true) {n : ℕ}
    (hfa : freeAboveB n a = true) (k : ℕ) (r : String) (l : List (ℕ × String))
    (hruns : runsAt linksFull 24 k r = l)
    (hall : ∀ p ∈ l, Fwd (D.Rd 24) p.1 p.2 a b ∧ NotLate (D.Rd 24) Pm p.1 p.2 a) :
    (mgAll D Mg).pub (.formsIn 24 k r) (z, a) = true →
      (mgAll D Mg).pub (.formsIn 24 k r) (z, b) = true := by
  have e : D.pubD.runs 24 k r = l := by
    show runsAt D.links 24 k r = l
    rw [hl]
    exact hruns
  rw [mgAll_pub, pubAll_formsIn, pubAll_formsIn, e, List.all_eq_true, List.all_eq_true]
  intro h p hp
  exact run_keeps (D.pubD.Rd 24) (D.pubD.N.sent 24) (D.pubD.N.group 24) Pm hy hled hfa
    (D.pubD.ah p.1 p.2) p.1 p.2 (hall p hp).1 (hall p hp).2 (h p hp)

/-- **THE EIGHT PUBLIC TESTS OF `keep24` PASS THE MERGE's ACCEPTING STEP**: the premise hkeep of
`merge_pubHeld_full`. -/
theorem keep_at_merge (hl : D.links = linksFull) (Pm : HeadMergeP) (z : P) {a b : S}
    {rs : List Fmt.RoundView} (hy : headMergeDecide Pm a rs = .ok b) {dg3 dg8 : Bool}
    (h3 : k3SortAt D.pubD.d3.X 24 3 = some dg3) (h8 : k3SortAt D.pubD.d3.X 24 8 = some dg8)
    (hled : ledgerB a = true) {n : ℕ} (hfa : freeAboveB n a = true)
    (H : RunsPass (D.Rd 24) Pm a b) :
    ∀ q ∈ keep24, (mgAll D Mg).pub q (z, a) = true → (mgAll D Mg).pub q (z, b) = true := by
  intro q hq
  simp only [keep24, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [mgAll_pub, pubAll_lookOut D.pubD Mg.pub 24 3 dg3 h3,
      pubAll_lookOut D.pubD Mg.pub 24 3 dg3 h3]
    exact lookOut_keeps D.pubD.d3 24 dg3 Pm hy hled
  · rw [mgAll_pub, pubAll_lookOut D.pubD Mg.pub 24 8 dg8 h8,
      pubAll_lookOut D.pubD Mg.pub 24 8 dg8 h8]
    exact lookOut_keeps D.pubD.d3 24 dg8 Pm hy hled
  · refine formsItem_keeps D Mg hl Pm z hy hled hfa 3 "objects"
      [(2, "objects"), (2, "guests")] (by decide) ?_
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨H.fwd_objects2, H.late_objects2⟩
    · exact ⟨H.fwd_guests2, H.late_guests2⟩
  · refine formsItem_keeps D Mg hl Pm z hy hled hfa 3 "planes"
      [(2, "planes")] (by decide) ?_
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    · exact ⟨H.fwd_planes2, H.late_planes2⟩
  · refine formsItem_keeps D Mg hl Pm z hy hled hfa 4 "join"
      [(3, "join")] (by decide) ?_
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    · exact ⟨H.fwd_join3, H.late_join3⟩
  · refine formsItem_keeps D Mg hl Pm z hy hled hfa 4 "own"
      [(3, "norm"), (3, "policy"), (3, "logits")] (by decide) ?_
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨H.fwd_norm3, H.late_norm3⟩
    · exact ⟨H.fwd_policy3, H.late_policy3⟩
    · exact ⟨H.fwd_logits3, H.late_logits3⟩
  · refine formsItem_keeps D Mg hl Pm z hy hled hfa 6 "small"
      [(5, "K8.equations")] (by decide) ?_
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl
    · exact equations_pass D.lk X (VerifiableInference.OnPublicFiles.headLink X) 24 5 Pm hy
  · refine formsItem_keeps D Mg hl Pm z hy hled hfa 8 "objects"
      [(7, "objects"), (7, "guests")] (by decide) ?_
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨H.fwd_objects7, H.late_objects7⟩
    · exact ⟨H.fwd_guests7, H.late_guests7⟩

/-- **The same under one equation on the public parameters**: the output head's segment has the full
size's number. -/
theorem keep_at_merge_head (hl : D.links = linksFull)
    (hH : VerifiableInference.OnPublicFiles.headLink X = 24) (Pm : HeadMergeP) (z : P) {a b : S}
    {rs : List Fmt.RoundView} (hy : headMergeDecide Pm a rs = .ok b) (hled : ledgerB a = true) {n : ℕ}
    (hfa : freeAboveB n a = true) (H : RunsPass (D.Rd 24) Pm a b) :
    ∀ q ∈ keep24, (mgAll D Mg).pub q (z, a) = true → (mgAll D Mg).pub q (z, b) = true :=
  keep_at_merge D Mg hl Pm z hy (sorts_at_head hH).1 (sorts_at_head hH).2 hled hfa H

/-- **Out of the table's condition at border 346**, at an unmarked state: the table's own two tests
on the ledger accept. -/
theorem ledger_at_front (hM : Mg.more = {}) (Nn : Numbers) {Fr : Sound.Frame} (z : P)
    (a : S × Fr.E.Str)
    (hon : Sound.onQ Nn (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346
      a) (hf : a.1.failed = none) : ledgerB a.1 = true ∧ ∃ n, freeAboveB n a.1 = true := by
  unfold Sound.onQ onAt at hon
  obtain ⟨-, hmk | ⟨hb, -⟩⟩ := hon
  · exact absurd hf hmk
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨-, hpub⟩, -⟩ := hb
    unfold pubHeld at hpub
    have hq : ∀ q ∈ [Pub.ledger 24, .freeAbove 24, .indexIs, .indexThere] ++ keep24,
        (mgAll D Mg).pub q (z, a.1) = true :=
      fun q hq => List.all_eq_true.1 hpub q (k11_hIn D Mg hM q hq)
    have h1 := hq (.ledger 24) (List.mem_append_left _ (by simp))
    have h2 := hq (.freeAbove 24) (List.mem_append_left _ (by simp))
    rw [mgAll_pub, pubAll_ledger] at h1
    rw [mgAll_pub, pubAll_freeAbove] at h2
    refine ⟨h1, ?_⟩
    cases e : D.pubD.nsOf 24 with
    | none =>
      rw [e] at h2
      simp at h2
    | some n =>
      rw [e] at h2
      exact ⟨n, by simpa using h2⟩

/-- **The eight, with the table's condition in front in the place of the two tests on the ledger.**
-/
theorem keep_at_merge_on (hl : D.links = linksFull) (hM : Mg.more = {})
    (hH : VerifiableInference.OnPublicFiles.headLink X = 24) (Pm : HeadMergeP) (Nn : Numbers)
    {Fr : Sound.Frame} (z : P) (a b : S × Fr.E.Str) {rs : List Fmt.RoundView}
    (hon : Sound.onQ Nn (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346
      a) (hf : a.1.failed = none) (hy : headMergeDecide Pm a.1 rs = .ok b.1)
    (H : RunsPass (D.Rd 24) Pm a.1 b.1) :
    ∀ q ∈ keep24, (mgAll D Mg).pub q (z, a.1) = true → (mgAll D Mg).pub q (z, b.1) = true := by
  obtain ⟨hled, n, hfa⟩ := ledger_at_front D Mg hM Nn z a hon hf
  exact keep_at_merge_head D Mg hl hH Pm z hy hled hfa H

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.segAt_of_fork
#print axioms VerifiableInference.Desc.First.MergeLaw.sized_of_ledgerB
#print axioms VerifiableInference.Desc.First.MergeLaw.getD_in
#print axioms VerifiableInference.Desc.First.MergeLaw.free_of_above
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_forks
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_reads
#print axioms VerifiableInference.Desc.First.MergeLaw.sorts_at_head
#print axioms VerifiableInference.Desc.First.MergeLaw.lookOut_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.run_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.small_late
#print axioms VerifiableInference.Desc.First.MergeLaw.equations_forms
#print axioms VerifiableInference.Desc.First.MergeLaw.equations_pass
#print axioms VerifiableInference.Desc.First.MergeLaw.formsItem_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.keep_at_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.keep_at_merge_head
#print axioms VerifiableInference.Desc.First.MergeLaw.ledger_at_front
#print axioms VerifiableInference.Desc.First.MergeLaw.keep_at_merge_on
