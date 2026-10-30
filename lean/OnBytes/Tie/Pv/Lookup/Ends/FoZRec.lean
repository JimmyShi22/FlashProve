-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoZRec.lean.
The tests on public numbers of the lookup on the digits: the clauses on the lookup's record, from
the success of the routine that makes it.

Fo.ZTests (OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsRun.lean) has ten clauses on the record of a
smallness test and a state's
arrays. HTailF2.piecesF makes the two calls z1, z2 and the lookup's record f9: it runs
Forest.shape on the two calls at the record's cap and lays the numbers of padding keys in. Five of
the ten clauses follow from that text.

Main names:
  `piecesF_cut`: tl.piecesF = .ok tl' gives f9, pub with
    Forest.shape #[tl'.z1.call, tl'.z2.call] tl'.lidb = .ok f9, Forest.pubAsk f9 pub = .ok () and
    tl'.f9 = { f9 with pub := pub }.
  `shape_cK`: Forest.shape calls lid = .ok fo gives fo.cK = clog2 calls.size.
  `callAsk_nk`: Forest.callAsk c = .ok () gives 5 ≤ c.k and c.n ≤ 62.
  `ZRec tl`: the five clauses (t4 to t8 of Fo.ZTests) as one record; `zRec_of_cut`, `zRec_pieces`:
    they hold of what piecesF returns.
  `ZRec.same`: they read z1, z2, f9 and lidb alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookDigitsBool
import OnBytes.Tie.Pv.Lookup.Port.FoShape

set_option autoImplicit false

namespace Fo.ZPlan
open Cb.Fo OnBytes OnBytes.Model OnBytes.Model.HTailF2

theorem bindX {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem jpX {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    ¬ c ∧ jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact ⟨hc, h⟩

/-- What the maker of the two calls runs, and what it lays into the record. -/
theorem piecesF_cut {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') :
    ∃ (f9 : Forest.Shape) (pub : Array Nat),
      Forest.shape #[tl'.z1.call, tl'.z2.call] tl'.lidb = .ok f9 ∧
      Forest.pubAsk f9 pub = .ok () ∧ tl'.f9 = { f9 with pub := pub } := by
  unfold piecesF at h
  obtain ⟨bz, _, h⟩ := bindX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨_, h⟩ := jpX h
  obtain ⟨f9, h9, h⟩ := bindX h
  obtain ⟨pub, _, h⟩ := bindX h
  obtain ⟨_, hp, h⟩ := bindX h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨f9, _, h9, hp, rfl⟩

theorem shape_cK {calls : Array Call} {lid : ℕ} {fo : Forest.Shape}
    (h : Forest.shape calls lid = .ok fo) : fo.cK = clog2 calls.size := by
  unfold Forest.shape at h
  obtain ⟨u, _, h⟩ := bindX h
  obtain ⟨-, h⟩ := jpX h
  obtain ⟨-, h⟩ := jpX h
  obtain ⟨-, h⟩ := jpX h
  obtain ⟨-, h⟩ := jpX h
  obtain ⟨-, h⟩ := jpX h
  obtain ⟨r, -, h⟩ := bindX h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := jpX h
  have e := (Except.ok.inj h).symm
  subst e
  rfl

theorem callAsk_nk {c : Call} (h : Forest.callAsk c = .ok ()) : 5 ≤ c.k ∧ c.n ≤ 62 := by
  unfold Forest.callAsk at h
  obtain ⟨h1, -⟩ := jpX h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at h1
  exact ⟨h1.1.1.1.1.1, h1.1.2⟩

/-- Five clauses of Fo.ZTests: those on the lookup's record. -/
structure ZRec (tl : HTailF2) : Prop where
  t4 : callsTest tl = true
  t5 : ∀ h0, Forest.shape #[tl.z1.call, tl.z2.call] tl.lidb = .ok h0 →
    { h0 with pub := tl.f9.pub } = tl.f9
  t6 : 2 ^ tl.f9.cK = tl.f9.NC
  t7 : 5 ≤ tl.f9.kT + tl.f9.cK
  t8 : ∀ q < 2, (tl.zOf q).call.n ≤ 63

theorem zRec_of_cut {tl : HTailF2} {f9 : Forest.Shape} {pub : Array Nat}
    (h9 : Forest.shape #[tl.z1.call, tl.z2.call] tl.lidb = .ok f9)
    (he : tl.f9 = { f9 with pub := pub }) : ZRec tl := by
  obtain ⟨m1, m2, -, m4, m5⟩ := shape_more h9
  have mc := shape_cK h9
  have a1 := callAsk_nk (m5 tl.z1.call (by simp))
  have a2 := callAsk_nk (m5 tl.z2.call (by simp))
  refine ⟨?_, fun h0 e0 => ?_, ?_, ?_, two_cases ?_ ?_⟩
  · unfold callsTest
    rw [he]
    show ([0, 1].all fun q => ((f9.calls[q]?).map (·.n)).getD 0 == (tl.zOf q).call.n) = true
    rw [m1]
    simp [HTailF2.zOf]
  · obtain rfl : f9 = h0 := Except.ok.inj (h9.symm.trans e0)
    rw [he]
  · rw [he]
    show 2 ^ f9.cK = f9.NC
    rw [mc, m2]
    show 2 ^ clog2 2 = 2
    decide
  · rw [he]
    show 5 ≤ f9.kT + f9.cK
    have := le_foldl_max #[tl.z1.call, tl.z2.call] 0 (by simp)
    rw [← m4] at this
    have e : (#[tl.z1.call, tl.z2.call] : Array Call)[0] = tl.z1.call := rfl
    rw [e] at this
    omega
  · show tl.z1.call.n ≤ 63
    omega
  · show tl.z2.call.n ≤ 63
    omega

theorem zRec_pieces {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') : ZRec tl' := by
  obtain ⟨f9, pub, h9, -, he⟩ := piecesF_cut h
  exact zRec_of_cut h9 he

/-- The five clauses read z1, z2, f9 and lidb alone. -/
theorem ZRec.same {a b : HTailF2} (T : ZRec a) (h1 : b.z1 = a.z1) (h2 : b.z2 = a.z2)
    (h9 : b.f9 = a.f9) (hl : b.lidb = a.lidb) : ZRec b := by
  have hz : ∀ q, b.zOf q = a.zOf q := fun q => by unfold HTailF2.zOf; rw [h1, h2]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := T.t4
    unfold callsTest at *
    simpa only [h9, hz] using this
  · rw [h1, h2, h9, hl]
    exact T.t5
  · rw [h9]
    exact T.t6
  · rw [h9]
    exact T.t7
  · intro q hq
    rw [hz]
    exact T.t8 q hq

end Fo.ZPlan
