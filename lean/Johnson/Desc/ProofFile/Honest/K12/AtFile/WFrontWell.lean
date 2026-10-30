-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontWell.lean: along the shared chain's fold every sampled
message has as many sample rows as its shape counts answers, and the public pad.

  WellSampled, WellStays   the sentence; the relation "if in front, then behind"
  SameSample, well_later, fit_pad   what a step must leave; a sending's test on the pad
  groundQuiet_well         the ground's functions that ask nothing of their caller keep it
  decideSend_newWell, decideSend_well, sendKeeps_well   a sending
  admit_well, call_well, calls_well, seat_well   a call of a proximity test, and the test in its seat
  carried_well, carried_fold_well   every block of the chain as a file holds it; the fold
  wellSampled_first        the chain's first record

The sentence is no sentence on all of the ground: the copying from another statement takes its pad
from there. It is not called on this chain.

Limits.
- The blocks' tests on the plan are a premise of carried_fold_well.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontShared
import Johnson.Desc.K13.Law.K1Ids

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Params _root_.Desc.Plain
open VerifiableInference.Desc (Block OpenedColumn foldBlocks noDigest roundsFit)
open VerifiableInference.Desc.Ground (GroundQuiet)
open VerifiableInference.Desc.Keeps (Steps steps_of_decides step_fit)
open Desc.K14 (St P14 RelAt sendAt blocks blocksOr frontBlock chainOf)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts P12)
open OnBytes.Slice

/-- **Every sampled message has its count of sample rows and the public pad.** -/
def WellSampled (T : Statement) : Prop :=
  ∀ (o : ℕ) (x : OnBytes.Oracle), T.oracles[o]? = some x → x.sampled = true →
    x.sampleRows.size = x.shape.answers ∧
      ∃ l, VerifiableInference.Desc.Own.padMade T.codes x.shape = some l ∧
        x.pad = l.map fun p => (p.part, p.index)

/-- If it holds in front, it holds behind. -/
def WellStays (A B : Statement) : Prop := WellSampled A → WellSampled B

/-- What a message holds for the sentence. -/
def SameSample (x y : OnBytes.Oracle) : Prop :=
  x.sampled = y.sampled ∧ x.shape = y.shape ∧ x.pad = y.pad ∧
    x.sampleRows.size = y.sampleRows.size

/-- A step that leaves the codes, and lays no sampled message but those that were there. -/
theorem well_later {A B : Statement} (hc : B.codes = A.codes)
    (h : ∀ (o : ℕ) (y : OnBytes.Oracle), B.oracles[o]? = some y → y.sampled = true →
      ∃ x : OnBytes.Oracle, A.oracles[o]? = some x ∧ SameSample x y) : WellStays A B := by
  intro hA o y hy hs
  obtain ⟨x, hx, e1, e2, e3, e4⟩ := h o y hy hs
  obtain ⟨a, l, hl, e⟩ := hA o x hx (by rw [e1]; exact hs)
  exact ⟨by rw [← e4, ← e2]; exact a, l, by rw [hc, ← e2]; exact hl, by rw [← e3]; exact e⟩

/-- One message is turned, and keeps what the sentence reads. -/
theorem same_modify (S : Statement) (o : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, SameSample x (f x)) (j : ℕ) (y : OnBytes.Oracle)
    (hy : (S.oracles.modify o f)[j]? = some y) :
    ∃ x : OnBytes.Oracle, S.oracles[j]? = some x ∧ SameSample x y := by
  rw [Array.getElem?_modify] at hy
  by_cases c : o = j
  · subst c
    rw [if_pos rfl] at hy
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hy
    exact ⟨x, hx, hf x⟩
  · rw [if_neg c] at hy
    exact ⟨y, hy, rfl, rfl, rfl, rfl⟩

theorem well_modify (S : Statement) (o : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, SameSample x (f x)) : WellStays S { S with oracles := S.oracles.modify o f } :=
  well_later rfl fun j y hy _ => same_modify S o f hf j y hy

theorem well_sent (S : Statement) (sent : Array OracleNotice) : WellStays S (stSent S sent) := by
  refine well_later rfl fun o y hy hs => ?_
  have hy' : (S.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[o]? =
      some y := hy
  by_cases c : o < S.oracles.size
  · rw [Array.getElem?_append_left c] at hy'
    exact ⟨y, hy', rfl, rfl, rfl, rfl⟩
  · rw [Array.getElem?_append_right (by omega), Array.getElem?_map] at hy'
    obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.1 hy'
    cases hs

/-- Closing ledgers leaves what the sentence reads. -/
theorem well_closeLedgers : ∀ (l : List ℕ) (S : Statement), WellStays S (closeLedgers S l)
  | [], _ => fun h => h
  | a :: l, S => fun h => by
    have e : closeLedgers S (a :: l) = closeLedgers { S with oracles := S.oracles.modify a fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } l := rfl
    rw [e]
    exact well_closeLedgers l _ (well_modify S a
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      (fun _ => ⟨rfl, rfl, rfl, rfl⟩) h)

/-- **The ground's quiet functions keep it.** -/
theorem groundQuiet_well : GroundQuiet WellStays where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := by
    intro L d d' code maskCode n h
    unfold VerifiableInference.Desc.Ground.newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact fun hA => hA
    · cases h
  recv := by
    intro L ft d d' sent ids h
    unfold VerifiableInference.Desc.Ground.recvP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact well_sent _ _
    · cases h
  join := by
    intro L d d' g o kept h
    unfold VerifiableInference.Desc.Ground.joinP at h
    split at h
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact well_later rfl fun j y hy _ => same_modify d.st o
        (fun x => { x with groups := x.groups ++ [g] }) (fun _ => ⟨rfl, rfl, rfl, rfl⟩) j y hy
    · cases h
  addRow := by
    intro L d d' g row h
    unfold VerifiableInference.Desc.Ground.addRowP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact fun hA => hA
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold VerifiableInference.Desc.Ground.takeMaskP at h
    split at h
    · obtain ⟨l, -, e⟩ := Option.map_eq_some_iff.1 h
      obtain rfl : _ = d' := congrArg Prod.snd e
      exact well_modify d.st o _ fun _ => ⟨rfl, rfl, rfl, rfl⟩
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold VerifiableInference.Desc.Ground.closeLedgerP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact well_closeLedgers [o] d.st
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold VerifiableInference.Desc.Ground.spendAsMaskP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact well_modify d.st o _ fun _ => ⟨rfl, rfl, rfl, rfl⟩
    · cases h
  adopt := by
    intro L d d' sent given ids h
    unfold VerifiableInference.Desc.Ground.adoptP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact well_sent _ _
    · cases h

/-- What a list of shapes that fits says of each message with an answer: its pad can be made. -/
theorem fit_pad (codes : Codes) (n : ℕ) : ∀ (l : List OracleShape) (ys : List E),
    VerifiableInference.Desc.K1.fitB codes n l ys = true → ∀ s ∈ l, s.answers ≠ 0 →
      (Send.pad codes s).isSome = true
  | [], _, _, _, hs, _ => by cases hs
  | a :: l, ys, h, s, hs, h0 => by
    by_cases ha : a.answers = 0
    · simp only [VerifiableInference.Desc.K1.fitB, ha, if_true] at h
      rcases List.mem_cons.1 hs with rfl | hs'
      · exact absurd ha h0
      · exact fit_pad codes n l ys h s hs' h0
    · simp only [VerifiableInference.Desc.K1.fitB, ha, if_false, Bool.and_eq_true] at h
      rcases List.mem_cons.1 hs with rfl | hs'
      · exact h.1.2
      · exact fit_pad codes n l _ h.2 s hs' h0

section Sending
open VerifiableInference.Desc.K1
open VerifiableInference.Desc.First.K2 (oldRows_of_old)

/-- **A new message with an answer, behind a sending**: it is sampled, with its count and the public
pad. -/
theorem decideSend_newWell {L : Type} (P : VerifiableInference.Desc.K1.Par) (owed : Option ℕ)
    (d d' : DState L) (rs : List Fmt.RoundView) (ids : Array ℕ)
    (h : decideSend P owed d rs = .ok (ids, d')) (k : ℕ) (hk : k < (shapesOf P).length)
    (hans : (shapesOf P)[k].answers ≠ 0) :
    ∃ x : OnBytes.Oracle, d'.st.oracles[d.st.oracles.size + k]? = some x ∧
      x.shape = (shapesOf P)[k] ∧ x.sampled = true ∧ x.spentAsMask = false ∧
      x.sampleRows.size = x.shape.answers ∧
      ∃ l, VerifiableInference.Desc.Own.padMade d'.st.codes x.shape = some l ∧
        x.pad = l.map fun p => (p.part, p.index) := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
    have hcod : (behind P d (seedsOf P r₁) (answersIn r₂)).st.codes = P.codes :=
      (kept_behind P d _ _).1.trans hc
    obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
      d.st.oracles.size (answersIn r₂) hf k hk
    have hkS : sampledAt P ⟨k, hk⟩ := hans
    have hlenS : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
    have hle : (shapesOf P)[k].answers ≤ (seedsOf P r₁).length := by
      rw [hlenS]
      exact msgAt_answers_le P ⟨k, hk⟩
    have hpad := fit_pad P.codes P.seeds _ _ hf (shapesOf P)[k] (List.getElem_mem hk) hans
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 hpad
    have hw : (wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys').shape =
        (shapesOf P)[k] := by
      unfold wr
      split <;> rfl
    refine ⟨wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys', ?_, hw, ?_, ?_, ?_,
      l, ?_, ?_⟩
    · show (_ ++ outs _ _ _ _ _).toArray[_]? = _
      rw [List.getElem?_toArray, List.getElem?_append_right (by simp)]
      simpa using hget
    · simp [wr, hans]
    · simp [wr, hans]
    · rw [hw]
      simp only [wr, hans, if_false]
      exact rowsOf_size _ _ _ _ _ hle hy
    · rw [hcod, hw]
      exact hl
    · simp only [wr, hans, if_false, hl, Option.getD_some]

/-- **A sending keeps it.** -/
theorem decideSend_well {L : Type} (P : VerifiableInference.Desc.K1.Par)
    (hB : planOkOwn P = true) (owed : Option ℕ) (d d' : DState L) (rs : List Fmt.RoundView)
    (ids : Array ℕ) (h : decideSend P owed d rs = .ok (ids, d')) : WellStays d.st d'.st := by
  match rs, h with
  | [r₁, r₂], h =>
    obtain ⟨⟨_, hc, _, _, hf⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
    intro hA o x hx hs
    have hcod : (behind P d (seedsOf P r₁) (answersIn r₂)).st.codes = d.st.codes :=
      (kept_behind P d _ _).1
    have hx' : (d.st.oracles.toList ++ outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P)
        (answersIn r₂)).toArray[o]? = some x := hx
    by_cases ho : o < d.st.oracles.size
    · rw [List.getElem?_toArray, List.getElem?_append_left (by simpa using ho)] at hx'
      have hx₂ : d.st.oracles[o]? = some x := by simpa using hx'
      obtain ⟨a, l, hl, e⟩ := hA o x hx₂ hs
      exact ⟨a, l, by rw [hcod]; exact hl, e⟩
    · obtain ⟨k, rfl⟩ : ∃ k, o = d.st.oracles.size + k := ⟨o - d.st.oracles.size, by omega⟩
      rw [List.getElem?_toArray, List.getElem?_append_right (by simp)] at hx'
      have hx2 : (outs P.codes (seedsOf P r₁) d.st.oracles.size (shapesOf P) (answersIn r₂))[k]? =
          some x := by simpa using hx'
      have hk : k < (shapesOf P).length := by
        have := (List.getElem?_eq_some_iff.1 hx2).1
        rwa [VerifiableInference.Desc.K13.Law.outs_length] at this
      obtain ⟨ys', hy, hget⟩ := outs_spec P.codes (seedsOf P r₁) P.seeds (shapesOf P)
        d.st.oracles.size (answersIn r₂) hf k hk
      obtain rfl : wr P.codes (seedsOf P r₁) (d.st.oracles.size + k) (shapesOf P)[k] ys' = x :=
        Option.some.inj (hget.symm.trans hx2)
      have hk' : (shapesOf P)[k].answers ≠ 0 := by
        intro h0
        simp [wr, h0, fresh] at hs
      obtain ⟨x', hx₁, -, -, -, a, l, hl, e⟩ := decideSend_newWell P owed d _ [r₁, r₂] ids h k hk hk'
      obtain rfl := Option.some.inj (hx.symm.trans hx₁)
      exact ⟨a, l, hl, e⟩

/-- **A sending, at its own record.** -/
theorem sendKeeps_well : SendKeeps WellStays := by
  intro Q hB s s' rs gs hfit h
  obtain ⟨r₁, r₂, rfl⟩ := fit_two _ _ rs hfit
  have h' : (decideSend Q s.owed s.held [noDigest r₁, noDigest r₂]).map
      (fun x => ({ owed := none, held := { x.2 with loc := x.1 } } :
        Owing (DState (Array ℕ)))) = .ok s' := h
  obtain ⟨x, h1, h2⟩ := VerifiableInference.Desc.Keeps.emap_ok h'
  subst h2
  exact decideSend_well Q hB _ _ x.2 _ x.1 h1

end Sending

/-- The admitting of rows that are made for the message. -/
theorem admit_well {d d' : Desc.Plain.DState Unit} {o : ℕ} {rows : Array OnBytes.Row}
    {s : OracleShape} (hs : (d.st.oracles[o]?).map (·.shape) = some s)
    (hr : rows.size = s.answers) (h : VerifiableInference.Desc.Ground.admitP d o rows = some d') :
    WellStays d.st d'.st := by
  unfold VerifiableInference.Desc.Ground.admitP at h
  by_cases c : VerifiableInference.Desc.Ground.ok (VerifiableInference.Desc.Ground.admitL d.st o rows) = true
  · rw [if_pos c] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, places, hp, rfl⟩ := h
    rw [hx] at hs
    obtain rfl := Option.some.inj hs
    intro hA j y hy hsy
    have hy' : (d.st.oracles.modify o fun y => { y with
        sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
        ledger := freshLedger d.st.codes x.shape })[j]? = some y := hy
    rw [Array.getElem?_modify] at hy'
    by_cases e : o = j
    · subst e
      rw [if_pos rfl, hx] at hy'
      obtain rfl := Option.some.inj hy'
      exact ⟨hr, places, hp, rfl⟩
    · rw [if_neg e] at hy'
      exact hA j y hy' hsy
  · rw [if_neg c] at h
    cases h

/-- **One call of a proximity test keeps it.** -/
theorem call_well {ft : ℕ} (d d' : Desc.Plain.DState Unit) (h : H2K.Out.Call ft d d') :
    WellStays d.st d'.st := by
  cases h with
  | newGroup h => exact groundQuiet_well.newGroup _ _ _ _ _ h
  | recv h => exact groundQuiet_well.recv _ _ _ _ _ h
  | admit hs hok hz hr h =>
    exact admit_well hs (VerifiableInference.Desc.First.K2.rowsFor_are hr).1 h
  | join h => exact groundQuiet_well.join _ _ _ _ _ h
  | addRow h => exact groundQuiet_well.addRow _ _ _ _ h
  | closeLedger h => exact groundQuiet_well.closeLedger _ _ _ h
  | spend h => exact groundQuiet_well.spendAsMask _ _ _ h
  | begin h =>
    unfold VerifiableInference.Desc.Ground.beginRunP at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨G, -, -, rfl⟩ := h
      exact fun hA o x hx hs => well_closeLedgers G.members.toList _ hA o x hx hs
    · cases h
  | count t => exact fun hA => hA
  | cols l => exact fun hA => hA

theorem calls_well {ft : ℕ} {d d' : Desc.Plain.DState Unit} (h : H2K.Out.Calls ft d d') :
    WellStays d.st d'.st := by
  induction h with
  | nil d => exact fun hA => hA
  | cons s _ ih => exact fun hA => ih (call_well _ _ s hA)

/-- **A proximity test in its seat.** -/
theorem seat_well (g : Desc.K14.Lin → ℕ) (mask : Desc.K14.Lin → Option ℕ) (p : P12) :
    Steps (RelAt WellStays) (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave) := by
  intro _ ft s rs cols s' k hs
  obtain ⟨-, gs, h⟩ := step_fit ft _ s s' rs cols k hs
  have h' : ((VerifiableInference.Desc.K12.Seat.enter g mask s).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide t (rs.map noDigest) gs).bind
        (VerifiableInference.Desc.K12.Seat.leave s)) = .ok s' := h
  obtain ⟨t, ht, h'⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl'⟩ := (VerifiableInference.Desc.K12.Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl'
  exact calls_well (H2K.Out.k12_calls p _ t' _ gs ht' [] [])

/-- **Every block of the chain as a file holds it keeps it.** -/
theorem carried_well {Cl : Type} (c : OnBytes.Model.Verify.Chains) (P : P14) (N : H2U.Places4) :
    ∀ b ∈ ((chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder,
      Steps (RelAt WellStays) b :=
  carried_steps groundQuiet_well sendKeeps_well seat_well c P N

/-- **Along the fold.** -/
theorem carried_fold_well {Cl : Type} (c : OnBytes.Model.Verify.Chains) (P : P14)
    (N : H2U.Places4)
    (hp : ∀ b ∈ ((chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder, b.planOk = true) (ft : ℕ)
    (s : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft ((chainOf c P (VerifiableInference.Desc.K12.Seat.tests N)
      VerifiableInference.Desc.K12.Seat.last).retype (Cl' := Cl)).blocksInOrder s rs cols = .ok r)
    (hs : WellSampled s.st) : WellSampled r.1.st :=
  VerifiableInference.Desc.Keeps.foldBlocks_steps (RelAt WellStays) (fun _ h => h)
    (fun _ _ _ h k x => k (h x)) ft _ (carried_well c P N) hp s rs cols r h hs

/-- The chain's first record has no message. -/
theorem wellSampled_first (codes : Codes) (key : OnBytes.TableKey) :
    WellSampled (Desc.K14.first codes key).st := fun o x hx => by
  have hx' : (#[] : Array OnBytes.Oracle)[o]? = some x := hx
  simp at hx'

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.groundQuiet_well
#print axioms ProofFile.Honest.K12.AtFile.decideSend_newWell
#print axioms ProofFile.Honest.K12.AtFile.decideSend_well
#print axioms ProofFile.Honest.K12.AtFile.call_well
#print axioms ProofFile.Honest.K12.AtFile.seat_well
#print axioms ProofFile.Honest.K12.AtFile.carried_fold_well
