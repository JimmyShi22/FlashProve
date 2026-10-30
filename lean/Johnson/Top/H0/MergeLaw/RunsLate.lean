-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunsLate.lean: nine of the eighteen fields of `RunsPass` (KeepAtMerge.lean):
at each of the nine runs, the slot of the merge's end value is none of the run's late slots
(`NotLate`). Beside them two small lemmas that the other nine fields want. Definitions, and
theorems with their proofs.

How. A reader's late slots are the slots that are free in the state's ledger and filled in the
ledger behind the run (`lateOf`, Johnson/Desc/First/Batch/ReaderOf.lean). Eight of the nine runs
turn no mark "filled": "objects" and "join" lay a mark on a debt, "guests" and the output head's
three own runs return the state. So their list is empty. The ninth, "planes", fills the slots of
the hiding polynomial of the sumcheck over the leaves: a stretch that begins where that sumcheck
began. The lookup arguments' public test behind the lookup on the calls puts the stretch's
1 + 2 d + 5 slots at or below the ledger's next free number; the merge's slot lies above that
number.

Main names:
  `merge_owed`: where the ledger in front has its sizes, the merge's accepting step leaves the
    ledger's list of debts (the proof of `merge_trees`, LedgerBehind.lean, at another field).
  `lateG_is`: `lateG` (Johnson/Top/H/Keep/K3Late.lean) is `lateOf`.
  `forms_opens`: what a segment's reader answers at a name other than "K8.equations" is the stated
    run's own reader's answer at the state, or, where that reader is silent, its answer at the state
    with the reads' tables laid. `withTables_reads`: the second state has the first one's ledger,
    and what the two lookups have heard.
  `Quiet own`: the run's accept turns no mark "filled" of the open ledger. `quiet_objects`,
    `quiet_guests`, `quiet_join`, `quiet_own`.
  `reader_late_nil`, `notLate_of_quiet`: at a quiet run.
  `leavesLenB s`: A TEST WITH CODE, WHICH STAYS A PREMISE: the walk of the sumcheck over the leaves
    that the lookup on the calls has heard has 1 + 2 d + 5 members, d its own shape's.
  `same_d`, `placeAt_digits`, `leaves_below`: out of the public test and `leavesLenB`: the stretch
    ends at or below the next free number; the ledger has its sizes.
  `reader_late_planes`, `lateAt_stretch`, `notLate_planes`: the ninth.
  `NineLate Rd P a`: the nine fields, under the names that they have in `RunsPass`.
  `nine_late`: THE NINE, from: the segment is there; `RunsAre` (RunsAre.lean); the public test
    behind the lookup on the calls, in front of the merge; `leavesLenB` there.
  `leavesLenB_rejects`, `leavesLenB_rejects_len`: negative tests: the test rejects where nothing is
    heard, and where the walk that was heard has another length.
  `lateAt_hits`: a negative test: at a slot inside such a stretch `lateAt` answers.
  `notLate_fails`: `NotLate` can fail: at every state with an open ledger it is false of readers
    that answer a list which holds the merge's slot.

Limits. NO EXAMPLE IN LEAN: the premises are shown together at no segment and no state. AN
EVALUATION, NO THEOREM: over another state of the library, at the state in front of the merge of one
honest full-size run over synthetic weights, the term of `leavesLenB`, typed out, has been seen to
accept, and the same term against one member more to reject; the own reader of "planes" named 44
late slots there. `RunsAre` and `lookOutC` have not been evaluated there. `leavesLenB`
follows from no public test in front of the merge: the lookup arguments' test names the number
1 + 2 d + 5 and never the walk, and the run's own accept says only that its stretch is in room and
free, as the merge's slot is. Who can show it: the walk's length is a fact on the lookup's accepting
step: `Fo.Tp.PadExact.len` at the heard shape, which `decide_exact` has of `K3.block`'s decision
from a ledger with its sizes (both Johnson/Top/H/Keep/PadExact.lean); the made chain holds
`Law.blockVia`, whose accept is `K3.block`'s under two tests on the entries (`decideVia_decide`,
Johnson/Top/H/K3Via/Blocks.lean); and what the lookup has heard is laid once. None of these is
called here. IDLE CASES: a field asks nothing where no ledger is open or the reader answers nothing.
The merge's accepting step is a premise of `merge_owed` alone: `NotLate` speaks of the state in
front. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.KeepAtMerge
import Johnson.Top.H0.MergeLaw.RunsAre
import Johnson.Top.H.Keep.K3Late
import Johnson.Top.H.K3SeatFits
import Johnson.Desc.Kinds.Law.HeadRunsCarry

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.K9 (statesOfLink readerOf lateOf lateAt readersAt phAt)
open VerifiableInference.Desc.First.Look (K3Data lookOutC placeAt)
open VerifiableInference.Desc.Kinds.Head (asClaim)
open VerifiableInference.Desc.Kinds.Head.Law (withTables k6Silent k6_same)
open VerifiableInference.OnPublicFiles (lateG late_same planes_late lvLen objectsRun guestsRun objects_cut
        guests_same joinRun_cut join_heard fork_putFork)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-! ## Two small lemmas -/

/-- **The merge's accepting step leaves the ledger's list of debts**, where the ledger in front has
its sizes. -/
theorem merge_owed (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') {a a' : HeadOwn} (ha : s.here = .head a)
    (ha' : s'.here = .head a') (hz : Sized a.F) : a'.F.owed = a.F.owed := by
  obtain ⟨a₁, a₁', tp, G, claim, x, wo, e1, e1', _, _, _, _, hm, hF, _⟩ := decide_inv h
  obtain ⟨_, _, _, _, _, v, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsF, hhide, _⟩ :=
    mergeHear_inv hm
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  have hz1 : Sized ({ a₁.F with next := a₁.F.next + 1 + 2 * P.lay.lk + 2 } : Fork) := hz
  have hs := (OnBytes.PscRun.hideRun_ok _ G _ _ _ hz1 hhide).1
  rw [hF]
  show G.owed = _
  unfold OnBytes.PscRun.Same at hs
  rw [hs]

/-- The lookup arguments' list of late slots is the readers'. -/
theorem lateG_is (F G : Fork) : lateG F G = lateOf F G := rfl

/-! ## What a segment's reader answers -/

/-- The state with the reads' tables laid has the ledger of the state, and what the two lookups have
heard. -/
theorem withTables_reads {Q : K8.ReadsQuiet.PH} {s t : S} (h : withTables Q s = some t) :
    t.fork? = s.fork? ∧ t.lookHeard? = s.lookHeard? ∧ t.tl? = s.tl? := by
  unfold withTables at h
  split at h
  · rename_i a ha
    obtain ⟨tt, -, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [S.fork?, S.lookHeard?, S.tl?, ha]
  · cases h

/-- **What a segment's reader answers**, at a name other than the approximate range proof's own
run's: the stated run's own reader's answer, at the state or at the state with the tables laid. -/
theorem forms_opens {lk : ℕ → Option (Link S Claim)} {X : OnBytes.Model.Verify.Public} {mH m : ℕ}
    {l : Link S Claim} (hlk : lk m = some l) {k : ℕ} {name : String}
    (hn : (name == "K8.equations") = false) {s : S} {R : K9.Read}
    (h : (readersAt lk X mH m).forms k name s = some R) :
    readerOf (statesOfLink l) k name s = some R ∨
      (readerOf (statesOfLink l) k name s = none ∧
        ∃ t, withTables (phAt X m) s = some t ∧ readerOf (statesOfLink l) k name t = some R) := by
  rw [K9.readersAt_some lk X mH m l hlk] at h
  have h' : (if name == "K8.equations" then K9.smallReader s else
      match readerOf (statesOfLink l) k name s with
      | some R => some R
      | none => (if m == mH then k6Silent (phAt X m) (statesOfLink l) else fun _ _ _ => none)
          k name s) = some R := h
  rw [hn] at h'
  simp only [Bool.false_eq_true, if_false] at h'
  cases e : readerOf (statesOfLink l) k name s with
  | some R' =>
    rw [e] at h'
    exact Or.inl h'
  | none =>
    rw [e] at h'
    refine Or.inr ⟨rfl, ?_⟩
    by_cases hm : (m == mH) = true
    · simp only [hm, if_true] at h'
      exact Option.bind_eq_some_iff.1 h'
    · simp only [hm] at h'
      cases h'

/-! ## The eight runs that fill no slot -/

/-- The run's accept turns no mark "filled" of the open ledger. -/
def Quiet (own : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∀ n t y F G, own n t = .ok y → t.fork? = some F → y.2.fork? = some G →
    ∀ j, G.gotF.getD j false = F.gotF.getD j false

theorem quiet_objects (seat : K3.Seat S Claim) (hfk : ∀ s, seat.fork s = s.fork?)
    (hmk : ∀ s G, seat.mark s G = s.putFork G) : Quiet (objectsRun seat) := by
  rintro n t ⟨c, t'⟩ F G h hF hG j
  obtain ⟨F1, g, e1, -, rfl⟩ := objects_cut seat h
  rw [hfk] at e1
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  have hG' : (t.putFork (F.paid g.owedObjects)).fork? = some G := by
    rw [← hmk]
    exact hG
  rw [← Option.some.inj ((fork_putFork t F _ hF).symm.trans hG')]
  rfl

theorem quiet_guests (gs : List (Look.Guest S Claim)) : Quiet (guestsRun gs) := by
  rintro n t ⟨c, t'⟩ F G h hF hG j
  obtain rfl : t' = t := guests_same gs t t' ⟨n, c, h⟩
  rw [Option.some.inj (hF.symm.trans hG)]

theorem quiet_join (seat : K3.Seat S Claim) (hfk : ∀ s, seat.fork s = s.fork?)
    (hmk : ∀ s G, seat.mark s G = s.putFork G) (keys : S → Option (Array Aff)) :
    Quiet (K3.joinRun seat keys) := by
  rintro n t ⟨c, t'⟩ F G h hF hG j
  obtain ⟨F1, g, e1, e2⟩ := join_heard seat keys h
  obtain ⟨-, -, -, -, rfl⟩ := joinRun_cut seat keys e1 e2 h
  rw [hfk] at e1
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  have hG' : (t.putFork (F.paid g.owedJoin)).fork? = some G := by
    rw [← hmk]
    exact hG
  rw [← Option.some.inj ((fork_putFork t F _ hF).symm.trans hG')]
  rfl

theorem quiet_own {hS : OnBytes.Model.Head.Shape} {iU3 lnk piece : ℕ} {p : Kinds.Head.Par}
    {name : String} {own : ℕ → S → Except String (List Claim × S)}
    (h : (Kinds.Head.kind asClaim (Kinds.Head.seatAt hS iU3) lnk piece p).claims.lookup name =
      some own) : Quiet own := by
  intro n t y F G hy hF hG j
  have e : y.2 = t := k6_same hS iU3 lnk piece p (name, own)
    (VerifiableInference.Desc.Kinds.Head.Law.lookup_mem _ _ _ h) n t y hy
  rw [e] at hG
  rw [Option.some.inj (hF.symm.trans hG)]

/-- At a quiet run the stated run's own reader names no late slot. -/
theorem reader_late_nil {l : Link S Claim} {k : ℕ} {name : String}
    {own : ℕ → S → Except String (List Claim × S)} (hr : RunIs l k name own) (hq : Quiet own)
    {s : S} {R : K9.Read} (h : readerOf (statesOfLink l) k name s = some R) : R.late = [] := by
  obtain ⟨run, hf, fwd, -⟩ := hr
  unfold readerOf at h
  rw [hf] at h
  simp only [Option.bind_some] at h
  cases hrun : run 0 s with
  | error e =>
    rw [hrun] at h
    cases h
  | ok z =>
    cases hF : s.fork? with
    | none =>
      rw [hrun, hF] at h
      cases h
    | some F =>
      rw [hrun, hF] at h
      simp only at h
      obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · rw [← Option.some.inj h]
        show lateOf F G = []
        rw [← lateG_is]
        exact late_same (hq 0 s z F G (fwd 0 s z hrun) hF hG)
      · cases h

/-- **`NotLate` at a quiet run.** -/
theorem notLate_of_quiet {lk : ℕ → Option (Link S Claim)} {X : OnBytes.Model.Verify.Public}
    {mH m : ℕ} {l : Link S Claim} (hlk : lk m = some l) {k : ℕ} {name : String}
    (hn : (name == "K8.equations") = false) {own : ℕ → S → Except String (List Claim × S)}
    (hr : RunIs l k name own) (hq : Quiet own) (P : HeadMergeP) (a : S) :
    NotLate (readersAt lk X mH m) P k name a := by
  intro F R _ hR
  rcases forms_opens hlk hn hR with h | ⟨-, t, -, h⟩
  · rw [reader_late_nil hr hq h]
    rfl
  · rw [reader_late_nil hr hq h]
    rfl

/-! ## "planes" -/

/-- **A test with code, which stays a premise**: the walk of the sumcheck over the leaves that the
lookup on the calls has heard has 1 + 2 d + 5 members, d its own shape's. -/
def leavesLenB (s : S) : Bool :=
  s.lookHeard?.any fun g => lvLen g == 1 + 2 * g.shape.d + 5

/-- A negative test: where nothing is heard the test rejects. -/
theorem leavesLenB_rejects {s : S} (h : s.lookHeard? = none) : leavesLenB s = false := by
  unfold leavesLenB
  rw [h]
  rfl

/-- A negative test at the test's one comparison: where the walk that was heard has another length
the test rejects. -/
theorem leavesLenB_rejects_len {s : S} {g : Forest.Heard} (hg : s.lookHeard? = some g)
    (h : lvLen g ≠ 1 + 2 * g.shape.d + 5) : leavesLenB s = false := by
  unfold leavesLenB
  rw [hg]
  exact beq_eq_false_iff_ne.2 h

/-- Two shapes that pass the public test's comparison have one number of bits of a row's index. -/
theorem same_d {a b : Forest.Shape} (h : K3.sameShapeAll a b = true) : a.d = b.d := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := b
  simp only [K3.sameShapeAll, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h3⟩, -⟩, -⟩, -⟩, h7⟩, -⟩, -⟩, -⟩, -⟩ := h
  show a3 + a7 = b3 + b7
  rw [beq_iff_eq.1 h3, beq_iff_eq.1 h7]

/-- The parameters of a lookup say which of the segment's two it is. -/
theorem placeAt_digits {X : OnBytes.Model.Verify.Public} {i : ℕ} {dg : Bool} {p : Look.P}
    (h : placeAt X i dg = some p) : p.digits = dg := by
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **Out of the public test behind the lookup on the calls, and `leavesLenB`**: the stretch that
"planes" fills ends at or below the ledger's next free number; the ledger has its sizes. -/
theorem leaves_below (d : K3Data) (m : ℕ) {s : S} {F : Fork} {g : Forest.Heard}
    (hF : s.fork? = some F) (hg : s.lookHeard? = some g) (hout : lookOutC d m false s = true)
    (hlen : leavesLenB s = true) : g.leaves.first + lvLen g ≤ F.next ∧ Sized F := by
  unfold leavesLenB at hlen
  rw [hg] at hlen
  simp only [Option.any_some, beq_iff_eq] at hlen
  unfold lookOutC at hout
  cases e : placeAt d.X m false with
  | none =>
    rw [e] at hout
    cases hout
  | some p =>
    rw [e] at hout
    simp only [Option.any_some] at hout
    unfold K3.k3OnOut K3.heardAt at hout
    rw [placeAt_digits e] at hout
    simp only [Bool.false_eq_true, if_false] at hout
    rw [hF, hg] at hout
    cases hs : p.shape with
    | none =>
      rw [hs] at hout
      cases hout
    | some h =>
      rw [hs] at hout
      simp only [Bool.and_eq_true] at hout
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, -⟩, -⟩, -⟩, -⟩, -⟩, c7⟩, c8⟩, -⟩, -⟩, c11⟩, -⟩, -⟩ := hout
      have k7 := of_decide_eq_true c7
      have k11 := of_decide_eq_true c11
      have kd := same_d c1
      unfold K3.sizedB at c8
      simp only [Bool.and_eq_true, beq_iff_eq] at c8
      refine ⟨?_, c8.1.1, c8.1.2, c8.2⟩
      rw [hlen, kd]
      omega

/-- **The late slots that the reader of "planes" names**: a function of what was heard alone. -/
theorem reader_late_planes {l : Link S Claim} {lm : ℕ} {readers : K3.Readers S}
    (hr : RunIs l 2 "planes" (K3.planesRun (K3.seatCalls asClaim) lm readers)) {s : S} {F : Fork}
    {g : Forest.Heard} {R : K9.Read} (hS : Sized F) (hF : s.fork? = some F)
    (hg : s.lookHeard? = some g) (h : readerOf (statesOfLink l) 2 "planes" s = some R) :
    R.late = (List.range (lvLen g)).map fun t => (g.leaves.first + t, zeroE, subE zeroE oneE) := by
  obtain ⟨run, hf, fwd, -⟩ := hr
  unfold readerOf at h
  rw [hf] at h
  simp only [Option.bind_some] at h
  cases hrun : run 0 s with
  | error e =>
    rw [hrun] at h
    cases h
  | ok z =>
    rw [hrun, hF] at h
    simp only at h
    obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨G', e1, e2⟩ := planes_late (K3.seatCalls asClaim) lm readers (i := 0) (s' := z.2)
      (l := z.1) hF hS hg (fwd 0 s z hrun)
    have eG : G' = G := by
      rw [e1] at hG
      exact Option.some.inj ((fork_putFork s F G' hF).symm.trans hG)
    split at h
    · rw [← Option.some.inj h]
      show lateOf F G = _
      rw [← eG, ← lateG_is]
      exact e2
    · cases h

/-- Outside a stretch of slots the list of that stretch answers nothing. -/
theorem lateAt_stretch (a n j : ℕ) (v f : E) (h : j < a ∨ a + n ≤ j) :
    lateAt ((List.range n).map fun t => (a + t, v, f)) j = none := by
  unfold lateAt
  rw [List.find?_eq_none.2]
  · rfl
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    have := List.mem_range.1 ht
    simp only [beq_iff_eq]
    omega

/-- A negative test: inside the stretch it answers. -/
theorem lateAt_hits : lateAt ((List.range 2).map fun t => (3 + t, zeroE, subE zeroE oneE)) 4 =
    some (zeroE, subE zeroE oneE) := rfl

/-- **`NotLate` can fail**: at a state with an open ledger, of readers that answer a list which
holds the merge's slot. -/
theorem notLate_fails (P : HeadMergeP) (k : ℕ) (name : String) {s : S} {F : Fork}
    (hF : s.fork? = some F) :
    ¬ NotLate ⟨fun _ _ _ => some
      { forms := [], late := [(F.next + 2 * P.lay.lk + 2, zeroE, zeroE)] }⟩ P k name s := by
  intro H
  have h := H F { forms := [], late := [(F.next + 2 * P.lay.lk + 2, zeroE, zeroE)] } hF rfl
  have e : lateAt [(F.next + 2 * P.lay.lk + 2, zeroE, zeroE)] (F.next + 2 * P.lay.lk + 2) =
      some (zeroE, zeroE) := by
    unfold lateAt
    simp
  rw [e] at h
  cases h

/-- **`NotLate` at "planes".** -/
theorem notLate_planes {lk : ℕ → Option (Link S Claim)} {X : OnBytes.Model.Verify.Public}
    {mH m : ℕ} {l : Link S Claim} (hlk : lk m = some l) {lm : ℕ} {readers : K3.Readers S}
    (hr : RunIs l 2 "planes" (K3.planesRun (K3.seatCalls asClaim) lm readers)) (d : K3Data)
    (P : HeadMergeP) {a : S} (hout : lookOutC d m false a = true) (hlen : leavesLenB a = true) :
    NotLate (readersAt lk X mH m) P 2 "planes" a := by
  intro F R hF hR
  obtain ⟨g, hg⟩ : ∃ g, a.lookHeard? = some g := by
    cases e : a.lookHeard? with
    | none => rw [leavesLenB_rejects e] at hlen; cases hlen
    | some g => exact ⟨g, rfl⟩
  obtain ⟨hb, hS⟩ := leaves_below d m hF hg hout hlen
  have key : ∀ t : S, t.fork? = some F → t.lookHeard? = some g →
      readerOf (statesOfLink l) 2 "planes" t = some R →
      lateAt R.late (F.next + 2 * P.lay.lk + 2) = none := fun t h1 h2 h3 => by
    rw [reader_late_planes hr hS h1 h2 h3]
    exact lateAt_stretch _ _ _ _ _ (Or.inr (by omega))
  rcases forms_opens hlk (by decide) hR with h | ⟨-, t, ht, h⟩
  · exact key a hF hg h
  · obtain ⟨e1, e2, -⟩ := withTables_reads ht
    exact key t (e1.trans hF) (e2.trans hg) h

/-! ## The nine -/

/-- The nine fields, under the names that they have in `RunsPass`. -/
structure NineLate (Rd : K9.Readers) (P : HeadMergeP) (a : S) : Prop where
  late_objects2 : NotLate Rd P 2 "objects" a
  late_guests2 : NotLate Rd P 2 "guests" a
  late_planes2 : NotLate Rd P 2 "planes" a
  late_join3 : NotLate Rd P 3 "join" a
  late_norm3 : NotLate Rd P 3 "norm" a
  late_policy3 : NotLate Rd P 3 "policy" a
  late_logits3 : NotLate Rd P 3 "logits" a
  late_objects7 : NotLate Rd P 7 "objects" a
  late_guests7 : NotLate Rd P 7 "guests" a

/-- **THE SLOT OF THE MERGE's END VALUE IS NONE OF THE NINE RUNS' LATE SLOTS.** -/
theorem nine_late {lk : ℕ → Option (Link S Claim)} {X : OnBytes.Model.Verify.Public} {mH m : ℕ}
    {l : Link S Claim} (hlk : lk m = some l) {iU3 lm : ℕ} (H : RunsAre l X iU3 lm) (d : K3Data)
    (P : HeadMergeP) {a : S} (hout : lookOutC d m false a = true) (hlen : leavesLenB a = true) :
    NineLate (readersAt lk X mH m) P a where
  late_objects2 := notLate_of_quiet hlk (by decide) H.objects2
    (quiet_objects _ (fun _ => rfl) fun _ _ => rfl) P a
  late_guests2 := notLate_of_quiet hlk (by decide) H.guests2 (quiet_guests _) P a
  late_planes2 := notLate_planes hlk H.planes2 d P hout hlen
  late_join3 := notLate_of_quiet hlk (by decide) H.join3
    (quiet_join _ (fun _ => rfl) (fun _ _ => rfl) _) P a
  late_norm3 := by
    obtain ⟨own, h, hr⟩ := H.norm3
    exact notLate_of_quiet hlk (by decide) hr (quiet_own h) P a
  late_policy3 := by
    obtain ⟨own, h, hr⟩ := H.policy3
    exact notLate_of_quiet hlk (by decide) hr (quiet_own h) P a
  late_logits3 := by
    obtain ⟨own, h, hr⟩ := H.logits3
    exact notLate_of_quiet hlk (by decide) hr (quiet_own h) P a
  late_objects7 := notLate_of_quiet hlk (by decide) H.objects7
    (quiet_objects _ (fun _ => rfl) fun _ _ => rfl) P a
  late_guests7 := notLate_of_quiet hlk (by decide) H.guests7 (quiet_guests _) P a

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_owed
#print axioms VerifiableInference.Desc.First.MergeLaw.lateG_is
#print axioms VerifiableInference.Desc.First.MergeLaw.withTables_reads
#print axioms VerifiableInference.Desc.First.MergeLaw.forms_opens
#print axioms VerifiableInference.Desc.First.MergeLaw.quiet_objects
#print axioms VerifiableInference.Desc.First.MergeLaw.quiet_guests
#print axioms VerifiableInference.Desc.First.MergeLaw.quiet_join
#print axioms VerifiableInference.Desc.First.MergeLaw.quiet_own
#print axioms VerifiableInference.Desc.First.MergeLaw.reader_late_nil
#print axioms VerifiableInference.Desc.First.MergeLaw.notLate_of_quiet
#print axioms VerifiableInference.Desc.First.MergeLaw.leavesLenB_rejects
#print axioms VerifiableInference.Desc.First.MergeLaw.leavesLenB_rejects_len
#print axioms VerifiableInference.Desc.First.MergeLaw.same_d
#print axioms VerifiableInference.Desc.First.MergeLaw.placeAt_digits
#print axioms VerifiableInference.Desc.First.MergeLaw.leaves_below
#print axioms VerifiableInference.Desc.First.MergeLaw.reader_late_planes
#print axioms VerifiableInference.Desc.First.MergeLaw.lateAt_stretch
#print axioms VerifiableInference.Desc.First.MergeLaw.lateAt_hits
#print axioms VerifiableInference.Desc.First.MergeLaw.notLate_fails
#print axioms VerifiableInference.Desc.First.MergeLaw.notLate_planes
#print axioms VerifiableInference.Desc.First.MergeLaw.nine_late
