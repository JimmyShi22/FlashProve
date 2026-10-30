-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RidesBehind.lean: WHAT OF THE CARRIED RECORD RIDES PAST A YES OF K10's
BLOCK: in one statement, field by field. Statements and proofs.

Why. A table's promise behind K10's block, and every item that rides past it, read the record
through a handful of fields: the statement's table of codes, its messages' number, shapes and sample
rows, whether it is tidy; the book; the request's words; the walk's own copy of the calls' state
(its frame's shape, its rows' layout). Whoever lays a meaning's letters against K10's block wants
each of these once.
  `tidy_spent`, `behind_tidy`: the four invariants on a statement (`Tidy`,
    Johnson/Desc/Means/Walk.lean) hold of `spent (begun S g G) id` (StBehind.lean, beside this file)
    if they hold of S.
  `closeFrame_shape`: the frame that the closing returns has the shape of the frame that it took.
  `putLive_check`: writing the live copy of the calls' state with another frame of the same shape
    leaves the shape of the frame, and the rows' layout, OF THE WALK's OWN COPY (`S.check`): inside
    a segment that copy is not written at all; outside it is the live one.
  `k10_rides`: at a yes of `closeFrame` at what K10 reads of s, with s' K10's writing: the same
    codes; as many messages; each with its shape and its sample rows; tidy if s's statement is; the
    same book, roots, mark, words of the request; nothing owed; the walk's copy's frame's shape and
    rows' layout as they were.
Limits. On the record alone: no meaning, no table, no letter is named. Nothing on the strings.
Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.StBehind
import Johnson.Desc.First.Close.Law.Leaves
import Johnson.Desc.Means.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (recOf putRec)

/-- Marking a message as spent leaves the four invariants. -/
theorem tidy_spent {T : Statement} (h : Tidy T) (id : Nat) : Tidy (spent T id) :=
  ⟨h.inOrder.onOracle id _ (fun _ => rfl) fun _ => rfl, h.kinds.sameGroups rfl,
    h.noneYet.onOracle id (fun x : OnBytes.Oracle => { x with spentAsMask := true }) rfl
      (fun _ => rfl) fun _ => rfl,
    h.members.onOracle id (fun x : OnBytes.Oracle => { x with spentAsMask := true }) rfl rfl
      fun _ hs => hs⟩

theorem behind_tidy {T : Statement} (h : Tidy T) (g : Nat) (G : Group)
    (hG : T.groups[g]? = some G) (id : Nat) : Tidy (spent (begun T g G) id) :=
  tidy_spent (h.begun g G hG) id

/-- The frame that the closing returns has the shape of the frame that it took. -/
theorem closeFrame_shape {owed : Option Nat} {f : ReqFrame} {T : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f T es rs = .ok x) :
    x.1.shape = f.shape := by
  unfold closeFrame at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨L, -, h⟩ := ok_bind h
  obtain ⟨Gf, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨y, -, h⟩ := ok_bind h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rfl

/-- Writing the live copy with another frame of the same shape: the walk's own copy. -/
theorem putLive_check (s : S) (f : ReqFrame) (hf : f.shape = s.live.frame.shape) :
    (s.putLive { s.live with frame := f }).check.frame.shape = s.check.frame.shape ∧
      (s.putLive { s.live with frame := f }).check.rows.layout = s.check.rows.layout := by
  unfold S.putLive
  cases h : s.link? with
  | none =>
    have e : s.live = s.check := by unfold S.live; rw [h]
    rw [e] at hf ⊢
    exact ⟨hf, rfl⟩
  | some L =>
    unfold S.putLink
    cases hh : s.here with
    | lay a => exact ⟨rfl, rfl⟩
    | att a => exact ⟨rfl, rfl⟩
    | head a => by_cases ho : a.opened = true <;> simp only [ho] <;> exact ⟨rfl, rfl⟩
    | between => exact ⟨rfl, rfl⟩
    | fin a => exact ⟨rfl, rfl⟩
    | mem a => exact ⟨rfl, rfl⟩

/-- **WHAT RIDES PAST A YES OF K10's BLOCK.** -/
theorem k10_rides (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView) (x : ReqFrame × Statement)
    (hx : closeFrame (recOf s).owed (recOf s).frame (recOf s).st es rs = .ok x) :
    (putRec s ⟨none, x.1, x.2⟩).st.codes = s.st.codes ∧
      (putRec s ⟨none, x.1, x.2⟩).st.oracles.size = s.st.oracles.size ∧
      (∀ o : Nat, ((putRec s ⟨none, x.1, x.2⟩).st.oracles[o]?).map (fun y : OnBytes.Oracle =>
          y.shape) =
        (s.st.oracles[o]?).map fun y : OnBytes.Oracle => y.shape) ∧
      (∀ o : Nat, ((putRec s ⟨none, x.1, x.2⟩).st.oracles[o]?).map (fun y : OnBytes.Oracle =>
          y.sampleRows) =
        (s.st.oracles[o]?).map fun y : OnBytes.Oracle => y.sampleRows) ∧
      (Tidy s.st → Tidy (putRec s ⟨none, x.1, x.2⟩).st) ∧
      (putRec s ⟨none, x.1, x.2⟩).book = s.book ∧ (putRec s ⟨none, x.1, x.2⟩).roots = s.roots ∧
      (putRec s ⟨none, x.1, x.2⟩).failed = s.failed ∧ (putRec s ⟨none, x.1, x.2⟩).req = s.req ∧
      (putRec s ⟨none, x.1, x.2⟩).rowsOwed = none ∧
      (putRec s ⟨none, x.1, x.2⟩).check.frame.shape = s.check.frame.shape ∧
      (putRec s ⟨none, x.1, x.2⟩).check.rows.layout = s.check.rows.layout := by
  obtain ⟨G, id, -, hG, e3⟩ := closeFrame_st hx
  obtain ⟨k1, k2, k3, -, k5, k6⟩ := putRec_keeps s ⟨none, x.1, x.2⟩
  have es' : (putRec s ⟨none, x.1, x.2⟩).st = spent (begun s.st (recOf s).frame.group G) id := e3
  have hc := putLive_check s x.1 (closeFrame_shape hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, k1, k2, k3, k5, k6, hc.1, hc.2⟩
  · rw [es']; exact behind_codes _ _ _ _
  · rw [es']; exact behind_size _ _ _ _
  · intro o; rw [es']; exact behind_shape _ _ _ _ o
  · intro o; rw [es']; exact behind_samples _ _ _ _ o
  · intro hT; rw [es']; exact behind_tidy hT _ G hG id

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.behind_tidy
#print axioms VerifiableInference.Desc.First.Close.closeFrame_shape
#print axioms VerifiableInference.Desc.First.Close.putLive_check
#print axioms VerifiableInference.Desc.First.Close.k10_rides
