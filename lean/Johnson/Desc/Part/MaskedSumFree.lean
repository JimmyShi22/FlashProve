--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Part/MaskedSumFree.lean: the masked sumcheck keeps the ledger's room, hands its
caller's promise on from call to call, and leaves its own slots owed until its row. Statements and
proofs, over Johnson/Desc/Part/MaskedSumReady.lean and the notions of
OnBytes/Tie/Pv/Psc/PscRoom.lean (FreeAbove, LedgerRoom, SlotsOwed, WritesAbove: on the ledger
alone).

I The invariant. hear_next, hear_freeAbove, row_next, row_freeAbove, whole_freeAbove: the part's
  functions keep FreeAbove (a row: where its stretch lies below the next slot); hear moves the next
  slot past the sumcheck's own slots and its end values'.
II The promise. ready_of_freeAbove, ready_of_room: the arrays' size, the invariant, the claimed
  form's slots filled and room give LedgerReady. ready_next: behind a hearing the next call owes its
  claimed form's slots filled, and one count. hear_room, whole_room, hearRow_room (the hearing, then
  the row at its ledger), row_room: they take room for what they take and m more, and give back room
  for m. hear_ends_filled: behind a hearing its end values' slots are filled: for a later call whose
  claimed form names them.
III The late row. hear_owes: behind a hearing the sumcheck's own stretch is owed. It stays owed
  through every step that writes above: another hearing is such a step (hear_writesAbove), and so is
  a hearing with its row at its ledger, and whole (hearRow_writesAbove, whole_writesAbove); and
  through another sumcheck's row on a stretch apart (row_keeps_owed); two hearings' own stretches
  are apart by their order (owed_apart). In the words of PscRoom.lean: a row writes within its own
  stretch (row_writesWithin); a hearing and whole spare every stretch, a row every stretch apart
  (hear_spares, whole_spares, row_spares): so a stretch stays owed along any row of these
  (owed_along there). row_returns_owed, row_returns_owed_at, rowLaid_returns_owed: at a ledger at
  which the stretch is still owed, the late row returns.
IV Two toys more for the promise's clauses: taken_own_row_refuses (a taken own slot: row refuses);
  unsized_refuses (marks of another size: hear refuses). owed_meets: hear_owes's premises can be
  met.
LIMITS. NOT EVERY STEP WRITES ABOVE: a row itself writes below the next slot. That every kind's own
writing raises the next slot first and writes below the new one, so that the room is kept, and that
the blocks between a hearing and its late row write above or on stretches apart, is shown here for
the part's own functions alone: for a kind's block it is not shown here. The next
call's filled slots are its caller's. That the lead was taken is not seen by any of this. No program
has asked these at a stored plan. Nothing on soundness, on an honest prover or on hiding.
-/
import Johnson.Desc.Part.MaskedSumReady
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled FreeAbove LedgerRoom SlotsOwed WritesAbove WritesWithin Spares
  filled_lt freeAbove_slots owed_of_writesAbove)

/-! ## Tools -/

/-- The hearing fills the end values' slots alone. -/
theorem hear_fills {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard} (hS : Sized F)
    (hh : hear C k F rs = some (h, G)) (j : Nat)
    (hj : j < F.next + ownSlots k.all ∨ F.next + ownSlots k.all + k.endsN ≤ j) :
    Filled G j ↔ Filled F j := by
  obtain ⟨_, _, R, _, hR, _, hw⟩ := hear_spec hh
  have hS2 : Sized ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork) := hS
  obtain ⟨_, _, _, b4⟩ := OnBytes.PscRun.hideRun_ok _ G _ _ _ hS2 hw
  exact (b4 j (by rw [List.size_toArray, readAll_values_len hR]; exact hj)).2.2

/-- The row fills the sumcheck's own slots alone. -/
theorem row_fills {h : Heard} {S0 : E} {kept f : Aff} {F' G' : Fork} (hS : Sized F')
    (hr : row h S0 kept F' = some (f, G')) (j : Nat)
    (hj : j < h.first ∨ h.first + (hidingAt (h.vars.zip h.r)).1.length ≤ j) :
    Filled G' j ↔ Filled F' j := by
  obtain ⟨_, _, _, b4⟩ := OnBytes.PscRun.hideRun_ok _ G' _ _ _ hS (row_write hr)
  exact (b4 j (by rw [Array.size_replicate]; exact hj)).2.2

/-! ## I The invariant -/

/-- The hearing moves the next slot past the sumcheck's own slots and its end values'. -/
theorem hear_next {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard} (hS : Sized F)
    (hh : hear C k F rs = some (h, G)) : G.next = F.next + ownSlots k.all + k.endsN := by
  obtain ⟨_, _, R, _, hR, _, hw⟩ := hear_spec hh
  have hS2 : Sized ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork) := hS
  obtain ⟨hsame, _, _, _⟩ := OnBytes.PscRun.hideRun_ok _ G _ _ _ hS2 hw
  rw [hsame.next]
  show F.next + ownSlots k.all + R.values.length = _
  rw [readAll_values_len hR]

theorem hear_freeAbove {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hS : Sized F) (hA : FreeAbove F) (hh : hear C k F rs = some (h, G)) : FreeAbove G := by
  intro j hj hf
  rw [hear_next hS hh] at hj
  exact hA j (by omega) ((hear_fills hS hh j (Or.inr hj)).1 hf)

theorem row_next {h : Heard} {S0 : E} {kept f : Aff} {F' G' : Fork} (hS : Sized F')
    (hr : row h S0 kept F' = some (f, G')) : G'.next = F'.next := by
  obtain ⟨hsame, _, _, _⟩ := OnBytes.PscRun.hideRun_ok _ G' _ _ _ hS (row_write hr)
  exact hsame.next

theorem row_freeAbove {h : Heard} {S0 : E} {kept f : Aff} {F' G' : Fork} (hS : Sized F')
    (hA : FreeAbove F') (hr : row h S0 kept F' = some (f, G'))
    (hb : h.first + (hidingAt (h.vars.zip h.r)).1.length ≤ F'.next) : FreeAbove G' := by
  intro j hj hf
  rw [row_next hS hr] at hj
  exact hA j hj ((row_fills hS hr j (Or.inr (Nat.le_trans hb hj))).1 hf)

theorem whole_freeAbove {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G' : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff} (hS : Sized F) (hA : FreeAbove F)
    (hw : whole C k endTerm F rs = some (h, f, G')) :
    FreeAbove G' ∧ G'.next = F.next + ownSlots k.all + k.endsN := by
  obtain ⟨_, G, _, _, hh, _, hr⟩ := whole_parts hw
  have hG : Sized G := (hear_keeps hh).sized hS
  obtain ⟨e1, _, e3⟩ := heard_lenK hh
  have hn := hear_next hS hh
  refine ⟨row_freeAbove hG (hear_freeAbove hS hA hh) hr (by rw [e1, e3, hn]; omega), ?_⟩
  rw [row_next hG hr, hn]

/-! ## II The promise from the invariant, and handed on -/

/-- **The promise from the invariant.** -/
theorem ready_of_freeAbove {C : Aff} {k : Call} {F : Fork} (hS : Sized F) (hA : FreeAbove F)
    (hP : ∀ x ∈ C.slots.toList, Filled F x.1)
    (hroom : F.next + ownSlots k.all + k.endsN ≤ F.ns) : LedgerReady C k F :=
  ⟨hS, fun x hx => ⟨filled_lt hS.2.2 (hP x hx), hP x hx⟩, hroom, fun j a _ => hA j a⟩

/-- **The promise handed on**: behind a hearing the next call owes its claimed form's slots filled,
and one count. -/
theorem ready_next {C C' : Aff} {k k' : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hS : Sized F) (hA : FreeAbove F) (hh : hear C k F rs = some (h, G))
    (hP' : ∀ x ∈ C'.slots.toList, Filled G x.1)
    (hroom' : F.next + ownSlots k.all + k.endsN + ownSlots k'.all + k'.endsN ≤ F.ns) :
    LedgerReady C' k' G :=
  ready_of_freeAbove ((hear_keeps hh).sized hS) (hear_freeAbove hS hA hh) hP'
    (by rw [hear_next hS hh, (hear_keeps hh).ns]; exact hroom')

/-- The promise from room: room for the call's slots and more, and the claimed form's slots filled.
-/
theorem ready_of_room {C : Aff} {k : Call} {F : Fork} {m : Nat}
    (h : LedgerRoom F (ownSlots k.all + k.endsN + m)) (hP : ∀ x ∈ C.slots.toList, Filled F x.1) :
    LedgerReady C k F :=
  ready_of_freeAbove h.sized h.free hP (by have := h.fits; omega)

/-- **The hearing takes room for what it takes and m more, and gives back room for m.** -/
theorem hear_room {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard} {m : Nat}
    (hR : LedgerRoom F (ownSlots k.all + k.endsN + m)) (hh : hear C k F rs = some (h, G)) :
    LedgerRoom G m :=
  ⟨(hear_keeps hh).sized hR.sized,
    by rw [hear_next hR.sized hh, (hear_keeps hh).ns]; have := hR.fits; omega,
    hear_freeAbove hR.sized hR.free hh⟩

/-- So does whole. -/
theorem whole_room {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G' : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff} {m : Nat}
    (hR : LedgerRoom F (ownSlots k.all + k.endsN + m))
    (hw : whole C k endTerm F rs = some (h, f, G')) : LedgerRoom G' m := by
  obtain ⟨a, b⟩ := whole_freeAbove hR.sized hR.free hw
  exact ⟨(whole_keeps hw).sized hR.sized,
    by rw [b, (whole_keeps hw).ns]; have := hR.fits; omega, a⟩

/-- A row whose stretch lies below the next slot keeps the room. -/
theorem row_room {h : Heard} {S0 : E} {kept f : Aff} {F' G' : Fork} {m : Nat}
    (hR : LedgerRoom F' m) (hr : row h S0 kept F' = some (f, G'))
    (hb : h.first + (hidingAt (h.vars.zip h.r)).1.length ≤ F'.next) : LedgerRoom G' m :=
  ⟨(row_keeps hr).sized hR.sized,
    by rw [row_next hR.sized hr, (row_keeps hr).ns]; exact hR.fits,
    row_freeAbove hR.sized hR.free hr hb⟩

/-- **The hearing, then the row at its ledger: they take room for what the sumcheck takes and m
more, and give back room for m.** -/
theorem hearRow_room {C : Aff} {k : Call} {F G G' : Fork} {rs : List Fmt.RoundView} {h : Heard} {S0 : E}
    {kept f : Aff} {m : Nat} (hR : LedgerRoom F (ownSlots k.all + k.endsN + m))
    (hh : hear C k F rs = some (h, G)) (hr : row h S0 kept G = some (f, G')) :
    LedgerRoom G' m := by
  obtain ⟨e1, _, e3⟩ := heard_lenK hh
  exact row_room (hear_room hR hh) hr (by rw [e1, e3, hear_next hR.sized hh]; omega)

/-- Behind a hearing its end values' slots are filled. -/
theorem hear_ends_filled {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hS : Sized F) (hh : hear C k F rs = some (h, G)) :
    ∀ j, j < k.endsN → Filled G (h.sEnd + j) := by
  obtain ⟨_, e2, _⟩ := heard_lenK hh
  obtain ⟨_, _, R, _, hR, _, hw⟩ := hear_spec hh
  have hS2 : Sized ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork) := hS
  obtain ⟨_, _, h3, _⟩ := OnBytes.PscRun.hideRun_ok _ G _ _ _ hS2 hw
  intro j hj
  rw [e2]
  exact (h3 j (by rw [List.size_toArray, readAll_values_len hR]; exact hj)).2.2.1

/-! ## III The late row -/

/-- Behind a hearing the sumcheck's own stretch is owed. -/
theorem hear_owes {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard} (hS : Sized F)
    (hA : FreeAbove F) (hh : hear C k F rs = some (h, G)) :
    SlotsOwed G h.first (ownSlots k.all) := by
  obtain ⟨e1, _, _⟩ := heard_lenK hh
  rw [e1]
  refine ⟨by rw [hear_next hS hh]; omega, fun j a b hf => ?_⟩
  exact hA j a ((hear_fills hS hh j (Or.inl b)).1 hf)

/-- A hearing writes above: so it keeps every stretch that is owed. -/
theorem hear_writesAbove {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hS : Sized F) (hh : hear C k F rs = some (h, G)) : WritesAbove F G :=
  ⟨(hear_keeps hh).next, fun j hj => hear_fills hS hh j (Or.inl (by omega))⟩

/-- Another sumcheck's row, on a stretch apart, keeps a stretch owed. -/
theorem row_keeps_owed {h : Heard} {S0 : E} {kept f : Aff} {F' G' : Fork} {a n : Nat}
    (hS : Sized F') (hr : row h S0 kept F' = some (f, G')) (ho : SlotsOwed F' a n)
    (hapart : a + n ≤ h.first ∨ h.first + (hidingAt (h.vars.zip h.r)).1.length ≤ a) :
    SlotsOwed G' a n := by
  refine ⟨by rw [row_next hS hr]; exact ho.1, fun j x y hf => ho.2 j x y ?_⟩
  refine (row_fills hS hr j ?_).1 hf
  rcases hapart with p | p
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- **A row writes within its sumcheck's own stretch.** -/
theorem row_writesWithin {C : Aff} {k : Call} {F G F' G' : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {S0 : E} {kept f : Aff} (hh : hear C k F rs = some (h, G)) (hS : Sized F')
    (hr : row h S0 kept F' = some (f, G')) : WritesWithin F' G' h.first (ownSlots k.all) := by
  obtain ⟨_, _, e3⟩ := heard_lenK hh
  have hp := OnBytes.PscRun.hideRun_writesWithin hS (row_write hr)
  rw [Array.size_replicate, e3] at hp
  exact hp

/-- A hearing spares every stretch. -/
theorem hear_spares {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard} (hS : Sized F)
    (hh : hear C k F rs = some (h, G)) (a n : Nat) : Spares F G a n :=
  Or.inl (hear_writesAbove hS hh)

/-- The hearing, then the row at its ledger, write above: all that they write lies at or above the
next slot of the ledger in front. -/
theorem hearRow_writesAbove {C : Aff} {k : Call} {F G G' : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {S0 : E} {kept f : Aff} (hS : Sized F) (hh : hear C k F rs = some (h, G))
    (hr : row h S0 kept G = some (f, G')) : WritesAbove F G' := by
  obtain ⟨e1, _, _⟩ := heard_lenK hh
  have hG : Sized G := (hear_keeps hh).sized hS
  have hw := hear_writesAbove hS hh
  refine ⟨by rw [row_next hG hr]; exact hw.1, fun j hj => ?_⟩
  exact (row_fills hG hr j (Or.inl (by rw [e1]; exact hj))).trans (hw.2 j hj)

/-- So whole writes above, and spares every stretch. -/
theorem whole_writesAbove {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G' : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff} (hS : Sized F)
    (hw : whole C k endTerm F rs = some (h, f, G')) : WritesAbove F G' := by
  obtain ⟨_, _, _, _, hh, _, hr⟩ := whole_parts hw
  exact hearRow_writesAbove hS hh hr

theorem whole_spares {C : Aff} {k : Call} {endTerm : List E → List E → E} {F G' : Fork}
    {rs : List Fmt.RoundView} {h : Heard} {f : Aff} (hS : Sized F)
    (hw : whole C k endTerm F rs = some (h, f, G')) (a n : Nat) : Spares F G' a n :=
  Or.inl (whole_writesAbove hS hw)

/-- A row spares every stretch that lies apart from its sumcheck's own. -/
theorem row_spares {C : Aff} {k : Call} {F G F' G' : Fork} {rs : List Fmt.RoundView} {h : Heard} {S0 : E}
    {kept f : Aff} {a n : Nat} (hh : hear C k F rs = some (h, G)) (hS : Sized F')
    (hr : row h S0 kept F' = some (f, G'))
    (hapart : a + n ≤ h.first ∨ h.first + ownSlots k.all ≤ a) : Spares F' G' a n :=
  Or.inr ⟨h.first, ownSlots k.all, row_writesWithin hh hS hr, hapart⟩

/-- Two hearings' own stretches are apart, by their order. -/
theorem owed_apart {C C2 : Aff} {k k2 : Call} {F G F2 G2 : Fork} {rs rs2 : List Fmt.RoundView}
    {h h2 : Heard} (hS : Sized F) (hh : hear C k F rs = some (h, G))
    (hh2 : hear C2 k2 F2 rs2 = some (h2, G2)) (hl : G.next ≤ F2.next) :
    h.first + ownSlots k.all ≤ h2.first := by
  obtain ⟨e1, _, _⟩ := heard_lenK hh
  obtain ⟨e2, _, _⟩ := heard_lenK hh2
  have hn := hear_next hS hh
  rw [e1, e2]
  omega

/-- **The late row returns**, at a ledger at which the sumcheck's own stretch is still owed. -/
theorem row_returns_owed {C : Aff} {k : Call} {F G F' : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) (hS : Sized F') (ho : SlotsOwed F' h.first (ownSlots k.all))
    (hroom : F.next + ownSlots k.all ≤ F'.ns) (S0 : E) (kept : Aff) :
    (row h S0 kept F').isSome := by
  obtain ⟨e1, _, _⟩ := heard_lenK hh
  rw [e1] at ho
  exact row_returns_later hh hS hroom ho.2 S0 kept

/-- The same with the room said at the stretch itself. -/
theorem row_returns_owed_at {C : Aff} {k : Call} {F G F' : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) (hS : Sized F') (ho : SlotsOwed F' h.first (ownSlots k.all))
    (hroom : h.first + ownSlots k.all ≤ F'.ns) (S0 : E) (kept : Aff) :
    (row h S0 kept F').isSome := by
  obtain ⟨e1, _, _⟩ := heard_lenK hh
  exact row_returns_owed hh hS ho (by rw [← e1]; exact hroom) S0 kept

/-- The same for a caller that writes by rowLaid. -/
theorem rowLaid_returns_owed {C : Aff} {k : Call} {F G F' : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) (hS : Sized F') (ho : SlotsOwed F' h.first (ownSlots k.all))
    (hroom : F.next + ownSlots k.all ≤ F'.ns) : (rowLaid h F').isSome := by
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (row_returns_owed hh hS ho hroom zeroE {})
  have hw' : row h zeroE {} F' = some (w.1, w.2) := hw
  rw [laid_of_row hw']
  rfl

/-! ## IV Tried -/

/-- hear_owes's premises can be met: at the smallest call without ends and a fresh ledger. -/
theorem owed_meets : ∃ (h : Heard) (G : Fork),
    hear {} ⟨0, [.plain 2], none⟩ (({} : Fork).slots 2) [toyRound 1, toyRound 1] = some (h, G) ∧
      SlotsOwed G h.first 2 := by
  obtain ⟨h, G, _, _, hh, _, _, _, e2⟩ := ledger_meets_none
  have ho := hear_owes (OnBytes.PscRun.slots_sized _ _) (freeAbove_slots 2) hh
  rw [e2] at ho
  exact ⟨h, G, hh, ho⟩

/-- **A taken own slot: row refuses**: at the call without ends and a ledger of two slots whose slot
0 is filled: hear returns, and row refuses at the ledger that it hands back. -/
theorem taken_own_row_refuses :
    ∃ (h : Heard) (G : Fork),
      hear {} ⟨0, [.plain 2], none⟩ { (({} : Fork).slots 2) with gotF := #[true, false] }
        [toyRound 1, toyRound 1] = some (h, G) ∧
      ∀ (S0 : E) (kept : Aff), row h S0 kept G = none := by
  have hR0 : (readAll ⟨0, [.plain 2], none⟩ [toyRound 1, toyRound 1]).isSome := rfl
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hR0
  have hv : R.values = [] := readAll_none_values hR
  have hT0 : (({ (({} : Fork).slots 2) with gotF := #[true, false] } : Fork).publicPart
      {}).isSome := rfl
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 hT0
  have hs : shapeOk ⟨0, [.plain 2], none⟩ = true := rfl
  have hy0 : (hear {} ⟨0, [.plain 2], none⟩
      { (({} : Fork).slots 2) with gotF := #[true, false] } [toyRound 1, toyRound 1]).isSome := by
    unfold hear
    simp only [hs, hT, hR, guard, if_true, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rw [hv, hideRun_nil]
    rfl
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hy0
  have hy' : hear {} ⟨0, [.plain 2], none⟩
      { (({} : Fork).slots 2) with gotF := #[true, false] } [toyRound 1, toyRound 1] =
      some (y.1, y.2) := hy
  refine ⟨y.1, y.2, hy', fun S0 kept => ?_⟩
  have hF : Sized ({ (({} : Fork).slots 2) with gotF := #[true, false] } : Fork) :=
    ⟨by simp [Fork.slots], by simp [Fork.slots], rfl⟩
  have hl := hear_keeps hy'
  obtain ⟨e1, _, e3⟩ := heard_lenK hy'
  have e1' : y.1.first = 0 := e1
  have e3' : (hidingAt (y.1.vars.zip y.1.r)).1.length = 2 := e3
  cases hr : row y.1 S0 kept y.2 with
  | none => rfl
  | some w =>
    exfalso
    have hr' : row y.1 S0 kept y.2 = some (w.1, w.2) := hr
    obtain ⟨_, _, h3, _⟩ := OnBytes.PscRun.hideRun_ok _ w.2 _ _ _ (hl.sized hF) (row_write hr')
    have h4 := (h3 0 (by rw [Array.size_replicate, e3']; exact Nat.two_pos)).2.1
    rw [e1'] at h4
    exact h4 (hl.keep 0 rfl).1

/-- **Marks of another size: hear refuses**, though the tests on the plan and the reading say yes.
The marks are too long (four at three slots): so the end value's slot is there and reads as free,
and the test on the size alone says no. -/
theorem unsized_refuses : shapeOk ⟨0, [], some ⟨1, 1⟩⟩ = true ∧
    (readAll ⟨0, [], some ⟨1, 1⟩⟩ [toyRound 1, toyRound 1, toyRound 0]).isSome ∧
    hear {} ⟨0, [], some ⟨1, 1⟩⟩
      { (({} : Fork).slots 3) with gotF := #[false, false, false, false] }
      [toyRound 1, toyRound 1, toyRound 0] = none := by
  refine ⟨rfl, rfl, ?_⟩
  cases hy : hear {} ⟨0, [], some ⟨1, 1⟩⟩
      { (({} : Fork).slots 3) with gotF := #[false, false, false, false] }
      [toyRound 1, toyRound 1, toyRound 0] with
  | none => rfl
  | some y =>
    exfalso
    have hy' : hear {} ⟨0, [], some ⟨1, 1⟩⟩
      { (({} : Fork).slots 3) with gotF := #[false, false, false, false] }
      [toyRound 1, toyRound 1, toyRound 0] = some (y.1, y.2) := hy
    obtain ⟨_, _, R, _, hR, _, hw⟩ := hear_spec hy'
    have hn : R.values.length = 1 := readAll_values_len hR
    obtain ⟨v, hv⟩ := List.length_eq_one_iff.mp hn
    rw [hv] at hw
    cases hw

end VerifiableInference.Desc.Part.MaskedSum

#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_next
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_freeAbove
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_freeAbove
#print axioms VerifiableInference.Desc.Part.MaskedSum.whole_freeAbove
#print axioms VerifiableInference.Desc.Part.MaskedSum.ready_of_freeAbove
#print axioms VerifiableInference.Desc.Part.MaskedSum.ready_next
#print axioms VerifiableInference.Desc.Part.MaskedSum.ready_of_room
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_room
#print axioms VerifiableInference.Desc.Part.MaskedSum.whole_room
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_room
#print axioms VerifiableInference.Desc.Part.MaskedSum.hearRow_room
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_ends_filled
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_owes
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_writesAbove
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_keeps_owed
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_writesWithin
#print axioms VerifiableInference.Desc.Part.MaskedSum.hear_spares
#print axioms VerifiableInference.Desc.Part.MaskedSum.hearRow_writesAbove
#print axioms VerifiableInference.Desc.Part.MaskedSum.whole_writesAbove
#print axioms VerifiableInference.Desc.Part.MaskedSum.whole_spares
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_spares
#print axioms VerifiableInference.Desc.Part.MaskedSum.owed_apart
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_returns_owed
#print axioms VerifiableInference.Desc.Part.MaskedSum.row_returns_owed_at
#print axioms VerifiableInference.Desc.Part.MaskedSum.rowLaid_returns_owed
#print axioms VerifiableInference.Desc.Part.MaskedSum.owed_meets
#print axioms VerifiableInference.Desc.Part.MaskedSum.taken_own_row_refuses
#print axioms VerifiableInference.Desc.Part.MaskedSum.unsized_refuses
