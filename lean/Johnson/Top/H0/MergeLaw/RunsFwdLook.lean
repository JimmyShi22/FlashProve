-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunsFwdLook.lean: five of the eighteen fields of `RunsPass`
(KeepAtMerge.lean): at the runs "objects" and "guests" of the two lookups and at "join", what the
run's reader answers in front of the merge's accepting step it answers behind it (`Fwd`,
Johnson/Desc/Reads/FormsPass.lean). Definitions, and theorems with their proofs.

How. The reader of a run is the run itself, called at the state (`readerOf`,
Johnson/Desc/First/Batch/ReaderOf.lean): its claims' forms; the slots that it fills; a test on the
entries that reads the ledger's arrays' numbers of rows. So the reader's answer passes from a state
s to a state s' where the run, called at s', states the same claims, fills the same slots with the
same values, leaves the reply, and the arrays have the same numbers of rows: `Moves`. The merge's
accepting step TURNS the open ledger: its next free number, and what lies under one slot. Of the
ledger the five runs read that it is open, its arrays and ("join") its list of debts; beside it,
what a lookup has heard: these stay (`LookStays`). "join" reads the calling kind's key vectors too:
they pass one way: where they are made in front, the same are made behind (`keys_alike`).

The readers' second arm (the reader at the state with the reads' tables laid, where the stated
run's own reader is silent) CANNOT OCCUR at "objects" and "guests": these runs do not read the
tables, so `Moves` holds from the state with the tables back to the state, and the own reader
answers wherever the second arm would. That is shown, not assumed. At "join" it can occur: there the
test `speaksAt` (RunsAre.lean) in front shuts it out.

Main names:
  `reader_cut`, `reader_made`: what an answer of the stated run's own reader is made of; and back.
  `Moves own s s'`, `reader_moves`: see above. `forms_closes`: the own reader's answer is the
    segment's reader's.
  `fwd_plain`, `fwd_speaking`: `Fwd` from `Moves`, with the second arm shown empty, or shut out.
  `LookStays s s'`: where s has an open ledger, s' has one with the same arrays and the same list of
    debts; what the two lookups have heard is the same. `stays_tables`, `stays_merge`.
  `objects_moves`, `guests_moves`, `join_moves`: the three runs. `keys_alike`: the output head's key
    vectors, by `letters_alike` (Johnson/Desc/Kinds/Law/RunsFixed.lean).
  `FiveFwd Rd a b`: the five fields, under the names that they have in `RunsPass`.
  `five_fwd`: THE FIVE, from: the segment is there; `RunsAre`; the merge's accepting step; the
    table's test `ledgerB` in front; `speaksAt` at "join" in front.

Limits. NO EXAMPLE IN LEAN: the premises are shown together at no segment and no state; no accepting
step of the merge is exhibited. AN EVALUATION, NO THEOREM: over another state of the library, at one
honest full-size run over synthetic weights, the term of `speaksAt` at "join", typed out, has been
seen to accept at the state in front of the merge, and the own reader's answers at "join" in front
of the merge and behind it were one. The four other runs of this file, `RunsAre` and `ledgerB` have
not been evaluated there. IDLE CASES: a field asks nothing where the reader answers nothing in
front. "planes" is not here. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.RunsLate
import Johnson.Top.H0.MergeLaw.AlikeAtMerge
import Johnson.Desc.Kinds.Law.ReaderRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Reads.Pass (Fwd)
open VerifiableInference.Desc.K9 (statesOfLink readerOf lateOf ownRow readersAt phAt)
open VerifiableInference.Desc.Kinds.Head (asClaim callerKeys seatAt lettersAt)
open VerifiableInference.Desc.Kinds.Head.Law (withTables k6Silent ownRow_same Alike letters_alike)
open VerifiableInference.OnPublicFiles (lateG late_same late_paid objectsRun guestsRun objects_cut
        objects_answer fork_putFork named_bind)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-! ## The stated run's own reader -/

section
variable {l : Link S Claim} {k : ℕ} {name : String}
  {own : ℕ → S → Except String (List Claim × S)}

/-- What an answer of the stated run's own reader is made of. -/
theorem reader_cut (hr : RunIs l k name own) {s : S} {R : K9.Read}
    (h : readerOf (statesOfLink l) k name s = some R) :
    ∃ z F G, own 0 s = .ok z ∧ s.fork? = some F ∧ z.2.fork? = some G ∧
      (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) = true ∧
      R = { forms := z.1.map (·.form), late := lateOf F G } := by
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
      · rename_i hall
        exact ⟨z, F, G, fwd 0 s z hrun, rfl, hG, hall, (Option.some.inj h).symm⟩
      · cases h

/-- And back: where `own` accepts and leaves the reply, a ledger is open in front and behind, and
the claims pass the reader's test. -/
theorem reader_made (hr : RunIs l k name own) {s : S} {z : List Claim × S} {F G : Fork}
    (h0 : own 0 s = .ok z) (hrep : z.2.out.reply = s.out.reply) (hF : s.fork? = some F)
    (hG : z.2.fork? = some G)
    (hall : (z.1.all fun c =>
      c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F)) = true) :
    readerOf (statesOfLink l) k name s =
      some { forms := z.1.map (·.form), late := lateOf F G } := by
  obtain ⟨run, hf, -, bwd⟩ := hr
  unfold readerOf
  rw [hf]
  simp only [Option.bind_some]
  rw [bwd 0 s z h0 hrep, hF]
  simp only
  rw [hG]
  simp only [Option.bind_some]
  rw [if_pos hall]

/-- Where the run, handed 0 claims, accepts at s, with a ledger open in front of it and behind it:
called at s' it accepts, states the same claims, fills the same slots with the same values and
leaves the reply, a ledger is open in front of it and behind it, and the two ledgers' arrays have
the same numbers of rows. -/
def Moves (own : ℕ → S → Except String (List Claim × S)) (s s' : S) : Prop :=
  ∀ z F G, own 0 s = .ok z → s.fork? = some F → z.2.fork? = some G →
    ∃ z' F' G', own 0 s' = .ok z' ∧ z'.2.out.reply = s'.out.reply ∧ s'.fork? = some F' ∧
      z'.2.fork? = some G' ∧ z'.1 = z.1 ∧ F'.trees.map (·.R) = F.trees.map (·.R) ∧
      lateOf F' G' = lateOf F G

/-- **The own reader's answer passes.** -/
theorem reader_moves (hr : RunIs l k name own) {s s' : S} (mv : Moves own s s') {R : K9.Read}
    (h : readerOf (statesOfLink l) k name s = some R) :
    readerOf (statesOfLink l) k name s' = some R := by
  obtain ⟨z, F, G, h0, hF, hG, hall, rfl⟩ := reader_cut hr h
  obtain ⟨z', F', G', h0', hrep, hF', hG', ez, et, el⟩ := mv z F G h0 hF hG
  have eo : ownRow F' = ownRow F := funext (ownRow_same et)
  have hall' : (z'.1.all fun c =>
      c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow F')) = true := by
    rw [ez, eo]
    exact hall
  rw [reader_made hr h0' hrep hF' hG' hall', ez, el]

variable {lk : ℕ → Option (Link S Claim)} {X : OnBytes.Model.Verify.Public} {mH m : ℕ}

/-- The own reader's answer is the segment's reader's. -/
theorem forms_closes (hlk : lk m = some l) (hn : (name == "K8.equations") = false) {s : S}
    {R : K9.Read} (h : readerOf (statesOfLink l) k name s = some R) :
    (readersAt lk X mH m).forms k name s = some R := by
  rw [K9.readersAt_some lk X mH m l hlk]
  show (if name == "K8.equations" then K9.smallReader s else
      match readerOf (statesOfLink l) k name s with
      | some R => some R
      | none => (if m == mH then k6Silent (phAt X m) (statesOfLink l) else fun _ _ _ => none)
          k name s) = some R
  rw [hn, h]
  rfl

/-- **`Fwd`, the readers' second arm shown empty.** -/
theorem fwd_plain (hlk : lk m = some l) (hn : (name == "K8.equations") = false)
    (hr : RunIs l k name own) {a b : S} (mv : Moves own a b)
    (off : ∀ t, withTables (phAt X m) a = some t → Moves own t a) :
    Fwd (readersAt lk X mH m) k name a b := by
  intro R hR
  rcases forms_opens hlk hn hR with h | ⟨h0, t, ht, h⟩
  · exact forms_closes hlk hn (reader_moves hr mv h)
  · rw [reader_moves hr (off t ht) h] at h0
    cases h0

/-- **`Fwd`, the readers' second arm shut out by the test in front.** -/
theorem fwd_speaking (hlk : lk m = some l) (hn : (name == "K8.equations") = false)
    (hr : RunIs l k name own) {a b : S} (mv : Moves own a b)
    (hs : speaksAt l k name a = true) : Fwd (readersAt lk X mH m) k name a b := by
  intro R hR
  rcases forms_opens hlk hn hR with h | ⟨h0, -⟩
  · exact forms_closes hlk hn (reader_moves hr mv h)
  · unfold speaksAt at hs
    rw [h0] at hs
    cases hs

end

/-! ## What the lookups' runs read -/

/-- Where s has an open ledger, s' has one with the same arrays and the same list of debts; what the
two lookups have heard is the same. -/
structure LookStays (s s' : S) : Prop where
  fork : ∀ F, s.fork? = some F → ∃ F', s'.fork? = some F' ∧ F'.trees = F.trees ∧ F'.owed = F.owed
  calls : s'.lookHeard? = s.lookHeard?
  digits : s'.tl? = s.tl?

/-- From the state with the reads' tables laid back to the state. -/
theorem stays_tables {Q : K8.ReadsQuiet.PH} {s t : S} (h : withTables Q s = some t) :
    LookStays t s := by
  obtain ⟨e1, e2, e3⟩ := withTables_reads h
  exact ⟨fun F hF => ⟨F, e1.symm.trans hF, rfl, rfl⟩, e2.symm, e3.symm⟩

/-- Across the merge's accepting step. -/
theorem stays_merge (P : HeadMergeP) {a b : S} {rs : List Fmt.RoundView}
    (hy : headMergeDecide P a rs = .ok b) (hled : ledgerB a = true) : LookStays a b := by
  obtain ⟨F0, hF0, hS⟩ := sized_of_ledgerB hled
  obtain ⟨x, x', hx, hx', rfl, hG, -, htl, hlh⟩ := merge_forks P hy hF0
  refine ⟨fun F hF => ?_, hlh, htl⟩
  obtain rfl : x.F = F := Option.some.inj (hF0.symm.trans hF)
  exact ⟨x'.F, hG, merge_trees P hy hx hx' hS, merge_owed P hy hx hx' hS⟩

/-- Laying a ledger leaves what the chain hands on. -/
theorem out_putFork (s : S) (G : Fork) : (s.putFork G).out = s.out := by
  unfold S.putFork
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

/-! ## The three runs -/

theorem objects_moves (seat : K3.Seat S Claim) (hfk : ∀ s, seat.fork s = s.fork?)
    (hmk : ∀ s G, seat.mark s G = s.putFork G) {s s' : S} (st : LookStays s s')
    (hh : seat.heard s' = seat.heard s) : Moves (objectsRun seat) s s' := by
  intro z F G h0 hF hG
  obtain ⟨F1, g, e1, e2, -⟩ := objects_cut seat (i := 0) (l := z.1) (s' := z.2) h0
  have ez : z = (g.rows.toList.map seat.claim, seat.mark s (F1.paid g.owedObjects)) :=
    Except.ok.inj (h0.symm.trans (objects_answer seat 0 e1 e2))
  rw [hfk] at e1
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  obtain ⟨F', hF', ht, -⟩ := st.fork F hF
  have eG : G = F.paid g.owedObjects := by
    rw [ez, hmk] at hG
    exact (Option.some.inj ((fork_putFork s F _ hF).symm.trans hG)).symm
  refine ⟨(g.rows.toList.map seat.claim, seat.mark s' (F'.paid g.owedObjects)), F',
    F'.paid g.owedObjects, objects_answer seat 0 ((hfk s').trans hF') (hh.trans e2), ?_, hF', ?_,
    ?_, by rw [ht], ?_⟩
  · show (seat.mark s' _).out.reply = _
    rw [hmk, out_putFork]
  · show (seat.mark s' _).fork? = _
    rw [hmk]
    exact fork_putFork s' F' _ hF'
  · rw [ez]
  · rw [eG, ← lateG_is, ← lateG_is, late_paid, late_paid]

/-- With no guest the run "guests" states no claim and returns the state. -/
theorem guests_answer (n : ℕ) (s : S) :
    guestsRun ([] : List (Look.Guest S Claim)) n s = .ok ([], s) := rfl

theorem guests_moves {s s' : S} (st : LookStays s s') :
    Moves (guestsRun ([] : List (Look.Guest S Claim))) s s' := by
  intro z F G h0 hF hG
  have ez : z = ([], s) := Except.ok.inj (h0.symm.trans (guests_answer 0 s))
  obtain ⟨F', hF', ht, -⟩ := st.fork F hF
  have eG : G = F := by
    rw [ez] at hG
    exact Option.some.inj (hG.symm.trans hF)
  refine ⟨([], s'), F', F', guests_answer 0 s', rfl, hF', hF', by rw [ez], by rw [ht], ?_⟩
  rw [eG, ← lateG_is, ← lateG_is, late_same fun _ => rfl, late_same fun _ => rfl]

theorem join_moves (seat : K3.Seat S Claim) (hfk : ∀ s, seat.fork s = s.fork?)
    (hmk : ∀ s G, seat.mark s G = s.putFork G) (keys : S → Option (Array Aff)) {s s' : S}
    (st : LookStays s s') (hh : seat.heard s' = seat.heard s)
    (hk : ∀ KF, keys s = some KF → keys s' = some KF) : Moves (K3.joinRun seat keys) s s' := by
  intro z F G h0 hF hG
  unfold K3.joinRun at h0
  rw [named_bind] at h0
  obtain ⟨F1, e1, h0⟩ := h0
  rw [named_bind] at h0
  obtain ⟨g, e2, h0⟩ := h0
  rw [VerifiableInference.OnPublicFiles.need_bind] at h0
  obtain ⟨hu, h0⟩ := h0
  rw [named_bind] at h0
  obtain ⟨KF, e3, h0⟩ := h0
  rw [named_bind] at h0
  obtain ⟨⟨x, G1, u⟩, e4, h0⟩ := h0
  rw [hfk] at e1
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans e1)
  obtain ⟨hb, rfl, rfl, rfl⟩ := (Kinds.Head.Law.Came.joinF_spec g KF F G1 [] u x).1 e4
  have ez : z = ([seat.claim (Kinds.Head.Law.Came.joinForm g KF)],
      seat.mark s (F.paid g.owedJoin)) := (Except.ok.inj h0).symm
  obtain ⟨F', hF', ht, ho⟩ := st.fork F hF
  have eG : G = F.paid g.owedJoin := by
    rw [ez, hmk] at hG
    exact (Option.some.inj ((fork_putFork s F _ hF).symm.trans hG)).symm
  have run' : K3.joinRun seat keys 0 s' = .ok ([seat.claim (Kinds.Head.Law.Came.joinForm g KF)],
      seat.mark s' (F'.paid g.owedJoin)) := by
    unfold K3.joinRun
    rw [named_bind]
    refine ⟨F', (hfk s').trans hF', ?_⟩
    rw [named_bind]
    refine ⟨g, hh.trans e2, ?_⟩
    rw [VerifiableInference.OnPublicFiles.need_bind]
    refine ⟨?_, ?_⟩
    · unfold K3.unpaid at hu ⊢
      rw [ho]
      exact hu
    · rw [named_bind]
      refine ⟨KF, hk KF e3, ?_⟩
      rw [named_bind]
      exact ⟨(Kinds.Head.Law.Came.joinForm g KF, F'.paid g.owedJoin, []),
        (Kinds.Head.Law.Came.joinF_spec g KF F' _ [] [] _).2 ⟨hb, rfl, rfl, rfl⟩, rfl⟩
  refine ⟨_, F', F'.paid g.owedJoin, run', ?_, hF', ?_, by rw [ez], by rw [ht], ?_⟩
  · show (seat.mark s' _).out.reply = _
    rw [hmk, out_putFork]
  · show (seat.mark s' _).fork? = _
    rw [hmk]
    exact fork_putFork s' F' _ hF'
  · rw [eG, ← lateG_is, ← lateG_is, late_paid, late_paid]

/-- The output head's key vectors: where they are made at s they are made at a state that goes on
from s, the same. -/
theorem keys_alike (hS : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Kinds.Head.Par) {s s' : S}
    (al : Alike s s') (KF : Array Aff) (h : callerKeys p (seatAt hS iU3) s = some KF) :
    callerKeys p (seatAt hS iU3) s' = some KF := by
  cases e : lettersAt p (seatAt hS iU3) s with
  | error msg =>
    have e0 : callerKeys p (seatAt hS iU3) s = none := by
      unfold callerKeys
      rw [e]
      rfl
    rw [e0] at h
    cases h
  | ok v =>
    have e' := letters_alike hS iU3 p al v e
    have e1 : callerKeys p (seatAt hS iU3) s' = callerKeys p (seatAt hS iU3) s := by
      unfold callerKeys
      rw [e, e']
    rw [e1]
    exact h

/-! ## The five -/

/-- The five fields, under the names that they have in `RunsPass`. -/
structure FiveFwd (Rd : K9.Readers) (a b : S) : Prop where
  fwd_objects2 : Fwd Rd 2 "objects" a b
  fwd_guests2 : Fwd Rd 2 "guests" a b
  fwd_join3 : Fwd Rd 3 "join" a b
  fwd_objects7 : Fwd Rd 7 "objects" a b
  fwd_guests7 : Fwd Rd 7 "guests" a b

/-- **WHAT THE READERS OF THESE FIVE RUNS ANSWER IN FRONT OF THE MERGE's ACCEPTING STEP THEY ANSWER
BEHIND IT.** -/
theorem five_fwd {lk : ℕ → Option (Link S Claim)} {X : OnBytes.Model.Verify.Public} {mH m : ℕ}
    {l : Link S Claim} (hlk : lk m = some l) {iU3 lm : ℕ} (H : RunsAre l X iU3 lm)
    (P : HeadMergeP) {a b : S} {rs : List Fmt.RoundView} (hy : headMergeDecide P a rs = .ok b)
    (hled : ledgerB a = true) (hs : speaksAt l 3 "join" a = true) :
    FiveFwd (readersAt lk X mH m) a b := by
  have st := stays_merge P hy hled
  have al : Alike a b := by
    obtain ⟨F0, hF0, hS⟩ := sized_of_ledgerB hled
    obtain ⟨x, x', hx, -, rfl, -⟩ := merge_forks P hy hF0
    refine merge_alike P hy fun y hy' => ?_
    rw [hx] at hy'
    obtain rfl := Here.head.inj hy'
    exact hS
  have dg : ∀ {s s' : S}, LookStays s s' →
      (K3.seatDigits asClaim).heard s' = (K3.seatDigits asClaim).heard s := fun q => by
    show _ = (_ : Option _)
    exact congrArg (fun x : Option HTailF2 => x.bind (·.heard)) q.digits
  exact
    { fwd_objects2 := fwd_plain hlk (by decide) H.objects2
        (objects_moves _ (fun _ => rfl) (fun _ _ => rfl) st st.calls)
        fun t ht => objects_moves _ (fun _ => rfl) (fun _ _ => rfl) (stays_tables ht)
          (stays_tables ht).calls
      fwd_guests2 := fwd_plain hlk (by decide) H.guests2 (guests_moves st)
        fun t ht => guests_moves (stays_tables ht)
      fwd_join3 := fwd_speaking hlk (by decide) H.join3
        (join_moves _ (fun _ => rfl) (fun _ _ => rfl) _ st st.calls (keys_alike _ _ _ al)) hs
      fwd_objects7 := fwd_plain hlk (by decide) H.objects7
        (objects_moves _ (fun _ => rfl) (fun _ _ => rfl) st (dg st))
        fun t ht => objects_moves _ (fun _ => rfl) (fun _ _ => rfl) (stays_tables ht)
          (dg (stays_tables ht))
      fwd_guests7 := fwd_plain hlk (by decide) H.guests7 (guests_moves st)
        fun t ht => guests_moves (stays_tables ht) }

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.reader_cut
#print axioms VerifiableInference.Desc.First.MergeLaw.reader_made
#print axioms VerifiableInference.Desc.First.MergeLaw.reader_moves
#print axioms VerifiableInference.Desc.First.MergeLaw.forms_closes
#print axioms VerifiableInference.Desc.First.MergeLaw.fwd_plain
#print axioms VerifiableInference.Desc.First.MergeLaw.fwd_speaking
#print axioms VerifiableInference.Desc.First.MergeLaw.stays_tables
#print axioms VerifiableInference.Desc.First.MergeLaw.stays_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.out_putFork
#print axioms VerifiableInference.Desc.First.MergeLaw.objects_moves
#print axioms VerifiableInference.Desc.First.MergeLaw.guests_answer
#print axioms VerifiableInference.Desc.First.MergeLaw.guests_moves
#print axioms VerifiableInference.Desc.First.MergeLaw.join_moves
#print axioms VerifiableInference.Desc.First.MergeLaw.keys_alike
#print axioms VerifiableInference.Desc.First.MergeLaw.five_fwd
