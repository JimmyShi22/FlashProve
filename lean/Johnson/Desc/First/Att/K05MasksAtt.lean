-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05MasksAtt.lean: a test on public data that guards how the mask row is read
at the closed caller of the lookup on an attention link's calls, up to the last slot of the own
rounds of the kind K5.

Why. `attLin0`.maskOf m j (Johnson/Desc/First/Att/K05AtCaller.lean) is (valAt … m (.mask j)).getD 0:
where the reading fails it is 0, and nothing says so. The guards in
Johnson/Desc/First/Look/K3CallerAtt.lean (`AttReadsOK`.seated over `ReadsAtt`, and `AttOK`.masksIn)
speak of the mask entries of the lookup's own scalars alone. The slots of the own rounds of K5 lie
behind these.

Definitions, statements and proofs.
Main names:
  `maskMsg D i`: the number, in the signature's list, of the message that holds the link's mask row.
  `masksUpTo D x hi`: a Bool. It says yes if hi ≤ x.ns, the link has a message with a mask row, that
    message is a member of the signature's list (the messages that stand sent when the lookup's
    shift is drawn), it has a mask row there, and hi is at most the message length of its mask code.
  `attMasksK5 D x own`: `masksUpTo` at hi := x.F.next + Forest.elems x.fs + slotsOf (script own).
  `masks_seated`: a yes gives `Seated` at every address .mask j with j < hi.
  `maskOf_at`: a yes gives valAt … m (.mask j) = some (attLin0.maskOf m j): no default is taken.
  `maskOf_entry`: a yes gives that attLin0.maskOf m j is entry (row 0, place j) of the mask rows'
    table of message number k of the tuple m, where maskMsg D x.link = some k: one message for all
    j.
Limits: the test is evaluated in no file of this library. That D holds the carried record's own
codes, shape, layout and names of arrays is not said here. The number x.ns is tied to the letter ns
of the statements on the kind only where ns := x.ns is laid. Nothing is claimed on soundness,
completeness or hiding.

-/
import Johnson.Desc.First.Att.K05AtCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open OnBytes.Road.Rows (Addr)
open Johnson.Pack (sigOf pMask)
open VerifiableInference.Desc.First.Look (Sent sigListCalls sigList seatCalls keptAt messagesAt valAt readAt
  readAt_some Seated finOf_some jMask attSg)

/-- The shapes of the oracle messages that stand sent when the lookup's shift is drawn. -/
def shapesCalls (D : Sent) (i : ℕ) : List OracleShape := (sigListCalls D (fun _ => 0) i).map (·.1)

/-- They do not hang on the radii. -/
theorem shapes_any (D : Sent) (rad : OracleShape → ℕ) (i : ℕ) : (sigListCalls D rad i).map (·.1) = shapesCalls D i := by
  unfold shapesCalls sigListCalls sigList
  simp only [List.map_append, List.map_map]
  rfl

/-- The number, in the signature's list, of the message that holds the link's mask row. -/
def maskMsg (D : Sent) (i : ℕ) : Option ℕ :=
  ((messagesAt D i).findIdx? fun y => y.shape.maskRows != 0).map fun mi => (keptAt D i).length + mi

/-- **THE TEST, on public data alone**: every mask entry below hi has a seat in a message that stands
sent when the lookup's shift is drawn; and hi is at most the place's number of slots. -/
def masksUpTo (D : Sent) (x : VerifiableInference.Desc.First.Look.Place) (hi : ℕ) : Bool :=
  Decidable.decide (hi ≤ x.ns) &&
    match maskMsg D x.link with
    | some k =>
      match (shapesCalls D x.link)[k]? with
      | some o => Decidable.decide (0 < o.maskRows) && Decidable.decide (hi ≤ (pMask D.codes o).ell)
      | none => false
    | none => false

/-- The test up to the last slot of the own rounds of the kind K5. -/
def attMasksK5 (D : Sent) (x : VerifiableInference.Desc.First.Look.Place) (own : Params.AttentionRounds) : Bool :=
  masksUpTo D x (x.F.next + Forest.elems x.fs + slotsOf (script own))

section Guard
variable {D : Sent} {x : VerifiableInference.Desc.First.Look.Place} {hi : ℕ}

/-- What a yes says. -/
theorem masksUpTo_yes (h : masksUpTo D x hi = true) (rad : OracleShape → ℕ) :
    hi ≤ x.ns ∧
      ∃ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length), maskMsg D x.link = some k ∧
        0 < ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows ∧
        hi ≤
          (pMask D.codes ((sigListCalls D rad x.link).get ⟨k, hk⟩).1).ell := by
  unfold masksUpTo at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1⟩ := h
  refine ⟨h0, ?_⟩
  cases hm : maskMsg D x.link with
  | none =>
    rw [hm] at h1
    cases h1
  | some k =>
    rw [hm] at h1
    cases ho : (shapesCalls D x.link)[k]? with
    | none =>
      simp only [ho] at h1
      cases h1
    | some o =>
      simp only [ho, Bool.and_eq_true, decide_eq_true_eq] at h1
      have e : ((sigListCalls D rad x.link)[k]?).map (·.1) = some o := by
        rw [← List.getElem?_map, shapes_any]
        exact ho
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 e
      obtain ⟨hk, hget⟩ := List.getElem?_eq_some_iff.1 hp
      have eg : (sigListCalls D rad x.link).get ⟨k, hk⟩ = p := hget
      exact ⟨k, hk, rfl, by rw [eg]; exact h1.1, by rw [eg]; exact h1.2⟩

/-- The seat of a mask entry. -/
theorem seat_mask {k : ℕ} (hm : maskMsg D x.link = some k) (j : ℕ) :
    seatCalls D x.link (.mask j) = some ⟨k, true, 0, j⟩ := by
  unfold maskMsg at hm
  obtain ⟨mi, h1, rfl⟩ := Option.map_eq_some_iff.1 hm
  show (((messagesAt D x.link).findIdx? fun y => y.shape.maskRows != 0).map fun m =>
    (⟨(keptAt D x.link).length + m, true, 0, j⟩ : VerifiableInference.Desc.First.Look.Seat)) = _
  rw [h1]
  rfl

/-- **Every mask entry below hi has a seat, and the seat lies in its table.** -/
theorem masks_seated (h : masksUpTo D x hi = true) (rad : OracleShape → ℕ) :
    Seated D.codes (sigListCalls D rad x.link) (seatCalls D x.link)
      (fun a => ∃ j, j < hi ∧ a = .mask j) := by
  rintro _ ⟨j, hj, rfl⟩
  obtain ⟨_, k, hk, hm, h1, h2⟩ := masksUpTo_yes h rad
  refine ⟨_, seat_mask hm j, ?_⟩
  unfold VerifiableInference.Desc.First.Look.Seat.Fits
  refine ⟨hk, ?_⟩
  rw [if_pos rfl]
  exact ⟨h1, Nat.lt_of_lt_of_le hj h2⟩

variable (S : Attention.Shape) (tl : HTailF2) (rad : OracleShape → ℕ)

/-- **No default is taken.** -/
theorem maskOf_at (h : masksUpTo D x hi = true) (m : (attSg x D rad).Msg) {j : ℕ}
    (hj : j < hi) :
    valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) m (.mask j) =
      some ((attLin0 x S tl D rad).maskOf m j) := by
  obtain ⟨s, hs, hf⟩ := masks_seated h rad _ ⟨j, hj, rfl⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (readAt_some _ _ s hf m)
  have e : valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) m (.mask j) = some v := by
    unfold valAt
    rw [hs]
    exact hv
  show _ = some ((valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) m (.mask j)).getD 0)
  rw [e]
  rfl

/-- **The reading is the committed row's entry**: row 0, place j, of the mask rows' table of one
message of the tuple, the same for all j. -/
theorem maskOf_entry (h : masksUpTo D x hi = true) (m : (attSg x D rad).Msg) {j : ℕ}
    (hj : j < hi) :
    ∃ (k : ℕ) (hk : k < (sigListCalls D rad x.link).length)
      (h0 : 0 < ((sigListCalls D rad x.link).get ⟨k, hk⟩).1.maskRows)
      (hc : j < (pMask D.codes ((sigListCalls D rad x.link).get ⟨k, hk⟩).1).ell),
      maskMsg D x.link = some k ∧
        (attLin0 x S tl D rad).maskOf m j =
          m (⟨k, hk⟩ : Fin (sigListCalls D rad x.link).length)
            (jMask D.codes ((sigListCalls D rad x.link).get ⟨k, hk⟩).1 ⟨0, h0⟩ ⟨j, hc⟩) := by
  obtain ⟨_, k, hk, hm, h1, h2⟩ := masksUpTo_yes h rad
  refine ⟨k, hk, h1, Nat.lt_of_lt_of_le hj h2, hm, ?_⟩
  show (valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) m (.mask j)).getD 0 = _
  unfold valAt
  rw [seat_mask hm j]
  show (readAt D.codes (sigListCalls D rad x.link) m ⟨k, true, 0, j⟩).getD 0 = _
  unfold readAt
  rw [dif_pos hk, if_pos rfl, finOf_some h1, finOf_some (Nat.lt_of_lt_of_le hj h2)]
  rfl

end Guard

end VerifiableInference.Desc.First.Att.P
