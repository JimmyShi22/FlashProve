--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumReady.lean: the caller's promise in front of the masked sumcheck, under
which no function of the ledger that can refuse does so inside the part. Statements and proofs.

The part (Johnson/Desc/Part/MaskedSum4.lean) calls three functions of the ledger that can refuse:
Fork.publicPart (through it Fork.shown), Fork.hideRun (through it hideStep and Fork.hide) and
Fork.shown. The part has no place of its own: so the promise is the caller's.
  LedgerReady C k F : (S) the ledger's three arrays have their size; (P) every slot that the claimed
                      form names is below the number of slots and filled; (R) room: the sumcheck's
                      own slots and its end values' fit; (F) these slots are free. It reads C, k
                      and F alone: no round.
  ready_public      : publicPart returns. It spends (P).
  hear_returns_iff  : hear refuses only by its own tests: it returns just where the tests on the
                      plan and the reading of the rounds say yes. It spends (S), (P), and (R),
                      (F) on the end values' stretch.
  row_returns_ready : behind a hearing that returned at a ready ledger, row returns at the hearing's
                      own ledger. It spends (S), and (R), (F) on the own slots' stretch.
  shownEnds_returns : so does shownEnds. It spends (S).
  whole_returns_iff : whole refuses only by its own tests.
  ready_slots       : a fresh ledger with room is ready for a claimed form without slots.
The clauses are not idle: no_room_refuses, unfilled_refuses, taken_refuses, no_room_row_refuses. The
last: at a call without ends hear writes an empty run and cannot refuse for room: the own slots'
room is row's.
NOT REACHED: a row that is made late, at a ledger later than the hearing's: there the own slots must
still be free: row_returns_later takes that as a premise; that the blocks between keep them free is
no law here.
Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Part.MaskedSumKeeps
import Johnson.Desc.Part.MaskedSumLedgerNone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)

/-! ## The promise -/

/-- How many end values a call has. -/
def Call.endsN (k : Call) : Nat :=
  match k.ends with
  | none => 0
  | some e => e.n

/-- **The promise in front.** -/
def LedgerReady (C : Aff) (k : Call) (F : Fork) : Prop :=
  Sized F ∧ (∀ x ∈ C.slots.toList, x.1 < F.ns ∧ Filled F x.1) ∧
    F.next + ownSlots k.all + k.endsN ≤ F.ns ∧
    ∀ j, F.next ≤ j → j < F.next + ownSlots k.all + k.endsN → ¬ Filled F j

/-! ## Tools -/

/-- A slot that is not filled reads as free, whatever the default. -/
theorem free_getD {F : Fork} {j : Nat} (hs : F.gotF.size = F.ns) (hj : j < F.ns)
    (hf : ¬ Filled F j) : F.gotF.getD j true = false := by
  have hsz : j < F.gotF.size := by
    rw [hs]
    exact hj
  have eq : F.gotF.getD j true = F.gotF.getD j false := by
    simp [Array.getD_eq_getD_getElem?, hsz]
  rw [eq]
  cases hb : F.gotF.getD j false with
  | false => rfl
  | true => exact absurd hb hf

/-- As many end values are read as the call has. -/
theorem readAll_values_len {k : Call} {rs : List Fmt.RoundView} {R : Read} (hR : readAll k rs = some R) :
    R.values.length = k.endsN := by
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | some e =>
    obtain ⟨_, _, _, _, _, _, _, _, a5⟩ := readAll_spec hR
    exact a5.2.1
  | none =>
    rw [readAll_none_values hR]
    rfl

theorem public_ret (F : Fork) : ∀ (l : List (Nat × E)) (v : E),
    (∀ x ∈ l, x.1 < F.ns ∧ Filled F x.1) →
    (l.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y))
      v).isSome
  | [], _, _ => rfl
  | x :: l, v, h => by
    rw [List.foldlM_cons]
    obtain ⟨a, b⟩ := h x (by simp)
    have hs : F.shown x.1 = some (F.vp.getD x.1 zeroE) :=
      (OnBytes.PscRun.shown_iff F x.1 _).2 ⟨a, b, rfl⟩
    rw [hs]
    exact public_ret F l _ fun z hz => h z (List.mem_cons_of_mem _ hz)

/-- An empty run is put under no slot: it returns at every ledger. -/
theorem hideRun_nil (F : Fork) (first : Nat) (factor : E) :
    F.hideRun first ([] : List E).toArray factor = some F := rfl

/-! ## Nothing of the ledger refuses -/

/-- (R1) -/
theorem ready_public {C : Aff} {k : Call} {F : Fork} (h : LedgerReady C k F) :
    (F.publicPart C).isSome := by
  unfold Fork.publicPart
  rw [← Array.foldlM_toList]
  exact public_ret F _ _ h.2.1

/-- (R2) **hear refuses only by its own tests.** -/
theorem hear_returns_iff {C : Aff} {k : Call} {F : Fork} (h : LedgerReady C k F)
    (rs : List Fmt.RoundView) :
    (hear C k F rs).isSome ↔ shapeOk k = true ∧ (readAll k rs).isSome := by
  constructor
  · intro hy
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hy
    have hy' : hear C k F rs = some (y.1, y.2) := hy
    obtain ⟨hs, _, R, _, hR, _, _⟩ := hear_spec hy'
    exact ⟨hs, by rw [hR]; rfl⟩
  · rintro ⟨hs, hR0⟩
    obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hR0
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 (ready_public h)
    have hn := readAll_values_len hR
    obtain ⟨hS, _, hroom, hfree⟩ := h
    obtain ⟨G, hG⟩ := hideRun_retA
      ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork)
      (F.next + ownSlots k.all) R.values.toArray ((R.rounds.map (·.2)).getLastD zeroE) hS.2.2
      (by
        rw [List.size_toArray, hn]
        exact hroom)
      (by
        intro j a b
        rw [List.size_toArray, hn] at b
        exact free_getD (F := F) hS.2.2 (Nat.lt_of_lt_of_le b hroom)
          (hfree j (Nat.le_trans (Nat.le_add_right _ _) a) b))
    unfold hear
    simp only [hs, hT, hR, guard, if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [hG]
    try rfl

/-- A row that is made at a ledger F' returns, if the arrays have their size there, the own slots
fit and they are free there. -/
theorem row_returns_later {C : Aff} {k : Call} {F G F' : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) (hS : Sized F') (hroom : F.next + ownSlots k.all ≤ F'.ns)
    (hfree : ∀ j, F.next ≤ j → j < F.next + ownSlots k.all → ¬ Filled F' j) (S0 : E)
    (kept : Aff) : (row h S0 kept F').isSome := by
  obtain ⟨e1, _, e3⟩ := heard_lenK hh
  obtain ⟨G', hG'⟩ := hideRun_retA F' h.first
    (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE) hS.2.2
    (by
      rw [Array.size_replicate, e1, e3]
      exact hroom)
    (by
      intro j a b
      rw [Array.size_replicate, e1, e3] at b
      rw [e1] at a
      exact free_getD hS.2.2 (Nat.lt_of_lt_of_le b hroom) (hfree j a b))
  unfold row
  simp only [hG', Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rfl

/-- (R3) **Behind a hearing that returned at a ready ledger, row returns at the hearing's own
ledger.** -/
theorem row_returns_ready {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hL : LedgerReady C k F) (hh : hear C k F rs = some (h, G)) (S0 : E) (kept : Aff) :
    (row h S0 kept G).isSome := by
  obtain ⟨hS, _, hroom, hfree⟩ := hL
  have hl := hear_keeps hh
  obtain ⟨_, _, R, _, _, _, hw⟩ := hear_spec hh
  have hS2 : Sized ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork) := hS
  obtain ⟨_, _, _, b4⟩ := OnBytes.PscRun.hideRun_ok _ G _ _ _ hS2 hw
  refine row_returns_later hh (hl.sized hS) (by rw [hl.ns]; omega) (fun j a b hf => ?_) S0 kept
  exact hfree j a (by omega) ((b4 j (Or.inl b)).2.2.1 hf)

/-- (R4) -/
theorem shownEnds_returns {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hL : LedgerReady C k F) (hh : hear C k F rs = some (h, G)) :
    (shownEnds h k.endsN G).isSome := by
  obtain ⟨_, _, R, _, hR, _, _⟩ := hear_spec hh
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | none => rfl
  | some e =>
    have hs := ledger_shownEnds hL.1 hh hR (OnBytes.PscRun.Later.refl G)
    show (shownEnds h e.n G).isSome
    rw [hs]
    rfl

/-- (R5) whole refuses only by its own tests. -/
theorem whole_returns_iff {C : Aff} {k : Call} {F : Fork} (hL : LedgerReady C k F)
    (endTerm : List E → List E → E) (rs : List Fmt.RoundView) :
    (whole C k endTerm F rs).isSome ↔
      shapeOk k = true ∧ (readAll k rs).isSome ∧ k.ends.isSome := by
  constructor
  · intro hy
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hy
    have hy' : whole C k endTerm F rs = some (y.1, y.2.1, y.2.2) := hy
    obtain ⟨e, G, _, he, hh, _, _⟩ := whole_parts hy'
    obtain ⟨a, b⟩ := (hear_returns_iff hL rs).1 (by rw [hh]; rfl)
    exact ⟨a, b, by rw [he]; rfl⟩
  · rintro ⟨hs, hR0, he0⟩
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 he0
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 ((hear_returns_iff hL rs).2 ⟨hs, hR0⟩)
    have hh : hear C k F rs = some (y.1, y.2) := hy
    have h4 := shownEnds_returns hL hh
    have hen : k.endsN = e.n := by
      unfold Call.endsN
      rw [he]
    rw [hen] at h4
    obtain ⟨sh, hsh⟩ := Option.isSome_iff_exists.1 h4
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (row_returns_ready hL hh (endTerm y.1.r sh) {})
    unfold whole
    simp only [he, hy, hsh, hw, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl

/-- A fresh ledger with room is ready for a claimed form without slots. -/
theorem ready_slots (C : Aff) (k : Call) (n : Nat) (hC : C.slots = #[])
    (hn : ownSlots k.all + k.endsN ≤ n) : LedgerReady C k (({} : Fork).slots n) := by
  refine ⟨OnBytes.PscRun.slots_sized _ _, ?_, ?_, ?_⟩
  · intro x hx
    rw [hC] at hx
    simp at hx
  · show 0 + ownSlots k.all + k.endsN ≤ n
    omega
  · intro j _ _ hf
    have hf' : (Array.replicate n false).getD j false = true := hf
    by_cases hj : j < n
    · simp [Array.getD_eq_getD_getElem?, hj] at hf'
    · simp [Array.getD_eq_getD_getElem?, hj] at hf'

/-! ## The clauses are not idle -/

/-- **No room: hear refuses**, though the tests on the plan and the reading say yes: the toy call
with one end value wants three slots; the ledger has two. -/
theorem no_room_refuses : shapeOk ⟨0, [], some ⟨1, 1⟩⟩ = true ∧
    (readAll ⟨0, [], some ⟨1, 1⟩⟩ [toyRound 1, toyRound 1, toyRound 0]).isSome ∧
    hear {} ⟨0, [], some ⟨1, 1⟩⟩ (({} : Fork).slots 2) [toyRound 1, toyRound 1, toyRound 0] =
      none := by
  refine ⟨rfl, rfl, ?_⟩
  cases hy : hear {} ⟨0, [], some ⟨1, 1⟩⟩ (({} : Fork).slots 2)
      [toyRound 1, toyRound 1, toyRound 0] with
  | none => rfl
  | some y =>
    exfalso
    have hy' : hear {} ⟨0, [], some ⟨1, 1⟩⟩ (({} : Fork).slots 2)
      [toyRound 1, toyRound 1, toyRound 0] = some (y.1, y.2) := hy
    obtain ⟨_, _, R, _, hR, _, hw⟩ := hear_spec hy'
    have hn : R.values.length = 1 := readAll_values_len hR
    have hS0 : Sized (({} : Fork).slots 2) := OnBytes.PscRun.slots_sized _ _
    have hS : Sized ({ (({} : Fork).slots 2) with
        next := (({} : Fork).slots 2).next + ownSlots (Call.all ⟨0, [], some ⟨1, 1⟩⟩) +
          R.values.length } : Fork) := hS0
    obtain ⟨_, _, h3, _⟩ := OnBytes.PscRun.hideRun_ok _ y.2 _ _ _ hS hw
    have h4 : 2 + 0 < 2 := (h3 0 (by rw [List.size_toArray, hn]; exact Nat.one_pos)).1
    omega

/-- **A claimed form with a slot that is not filled: hear refuses**, at every call and all rounds.
-/
theorem unfilled_refuses (k : Call) (n : Nat) (rs : List Fmt.RoundView) :
    hear (Aff.slot 0) k (({} : Fork).slots n) rs = none := by
  cases hy : hear (Aff.slot 0) k (({} : Fork).slots n) rs with
  | none => rfl
  | some y =>
    exfalso
    have hy' : hear (Aff.slot 0) k (({} : Fork).slots n) rs = some (y.1, y.2) := hy
    obtain ⟨_, T, _, hT, _, _, _⟩ := hear_spec hy'
    have hf := ((OnBytes.PscRun.publicPart_value Reading.gl _ _ _ hT).1 (0, oneE)
      (by simp [Aff.slot])).2
    have hf' : (Array.replicate n false).getD 0 false = true := hf
    by_cases hj : 0 < n
    · simp [Array.getD_eq_getD_getElem?, hj] at hf'
    · simp [Array.getD_eq_getD_getElem?, hj] at hf'

/-- **An end value's slot that is taken: hear refuses.** -/
theorem taken_refuses :
    hear {} ⟨0, [], some ⟨1, 1⟩⟩ { (({} : Fork).slots 3) with gotF := #[false, false, true] }
      [toyRound 1, toyRound 1, toyRound 0] = none := by
  cases hy : hear {} ⟨0, [], some ⟨1, 1⟩⟩
      { (({} : Fork).slots 3) with gotF := #[false, false, true] }
      [toyRound 1, toyRound 1, toyRound 0] with
  | none => rfl
  | some y =>
    exfalso
    have hy' : hear {} ⟨0, [], some ⟨1, 1⟩⟩
      { (({} : Fork).slots 3) with gotF := #[false, false, true] }
      [toyRound 1, toyRound 1, toyRound 0] = some (y.1, y.2) := hy
    obtain ⟨_, _, R, _, hR, _, hw⟩ := hear_spec hy'
    have hn : R.values.length = 1 := readAll_values_len hR
    have hS : Sized ({ ({ (({} : Fork).slots 3) with gotF := #[false, false, true] } : Fork) with
        next := ({ (({} : Fork).slots 3) with gotF := #[false, false, true] } : Fork).next +
          ownSlots (Call.all ⟨0, [], some ⟨1, 1⟩⟩) + R.values.length } : Fork) :=
      ⟨by simp [Fork.slots], by simp [Fork.slots], rfl⟩
    obtain ⟨_, _, h3, _⟩ := OnBytes.PscRun.hideRun_ok _ y.2 _ _ _ hS hw
    exact (h3 0 (by rw [List.size_toArray, hn]; exact Nat.one_pos)).2.1 rfl

/-- **At a call without ends hear cannot refuse for room; row does**: one slot where two are wanted:
hear returns, and row refuses at the ledger that it hands back. -/
theorem no_room_row_refuses :
    ∃ (h : Heard) (G : Fork),
      hear {} ⟨0, [.plain 2], none⟩ (({} : Fork).slots 1) [toyRound 1, toyRound 1] = some (h, G) ∧
      ∀ (S0 : E) (kept : Aff), row h S0 kept G = none := by
  have hR0 : (readAll ⟨0, [.plain 2], none⟩ [toyRound 1, toyRound 1]).isSome := rfl
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hR0
  have hv : R.values = [] := readAll_none_values hR
  have hT0 : ((({} : Fork).slots 1).publicPart {}).isSome := rfl
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 hT0
  have hs : shapeOk ⟨0, [.plain 2], none⟩ = true := rfl
  have hy0 : (hear {} ⟨0, [.plain 2], none⟩ (({} : Fork).slots 1)
      [toyRound 1, toyRound 1]).isSome := by
    unfold hear
    simp only [hs, hT, hR, guard, if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [hv, hideRun_nil]
    try rfl
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hy0
  have hy' : hear {} ⟨0, [.plain 2], none⟩ (({} : Fork).slots 1) [toyRound 1, toyRound 1] =
      some (y.1, y.2) := hy
  refine ⟨y.1, y.2, hy', fun S0 kept => ?_⟩
  have hF : Sized (({} : Fork).slots 1) := OnBytes.PscRun.slots_sized _ _
  have hl := hear_keeps hy'
  obtain ⟨e1, _, e3⟩ := heard_lenK hy'
  have e1' : y.1.first = 0 := e1
  have e3' : (hidingAt (y.1.vars.zip y.1.r)).1.length = 2 := e3
  have hns : y.2.ns = 1 := hl.ns
  cases hr : row y.1 S0 kept y.2 with
  | none => rfl
  | some w =>
    exfalso
    have hr' : row y.1 S0 kept y.2 = some (w.1, w.2) := hr
    obtain ⟨_, _, h3, _⟩ := OnBytes.PscRun.hideRun_ok _ w.2 _ _ _ (hl.sized hF) (row_write hr')
    have h4 := (h3 1 (by rw [Array.size_replicate, e3']; exact Nat.one_lt_two)).1
    rw [e1', hns] at h4
    omega

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.ready_public
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_returns_iff
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_returns_later
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_returns_ready
#print axioms VerifiableInference.Desc.Part.MaskedSum.shownEnds_returns
#print axioms VerifiableInference.Desc.Part.MaskedSum.whole_returns_iff
#print axioms VerifiableInference.Desc.Part.MaskedSum.ready_slots
#print axioms VerifiableInference.Desc.Part.MaskedSum.no_room_refuses
#print axioms VerifiableInference.Desc.Part.MaskedSum.unfilled_refuses
#print axioms VerifiableInference.Desc.Part.MaskedSum.taken_refuses
#print axioms VerifiableInference.Desc.Part.MaskedSum.no_room_row_refuses
