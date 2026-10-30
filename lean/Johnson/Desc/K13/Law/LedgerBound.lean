--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Law/LedgerBound.lean: THE REAL BOUND ON AN ENTRY THAT THE LEDGER GIVES. "Within its
table" (Johnson/Desc/K13/Law/LedgerWithin.lean) is below 2 ^ (row bits + place bits): the cube of
powers of two. Here: at the ledger of k takes (`LedgerAt`), where an entry is left, the entry given
is entry k / m of row k % m, m the message's mask rows; THE ROW IS A REAL ROW, THE PLACE IS BELOW
THE ROW's LENGTH ell, AND THE NUMBER IS BELOW THE PAD's FIRST. Statements with their proofs.
  `nextOf_bound`     at the number that a ledger gives next (`nextOf`): four clauses. The fourth in
                     the program's own form of a pad's index (`Send.pad`, OnBytes/Iop/Send.lean):
                     (rows - 1) + place * 2 ^ rowBits at the place ell - answers.
  `takeEntry_bound`  at the pending row's take (`takeEntry`).
  `takeMaskP_is`     what a yes of the ground's take is; `takeMaskP_bound`: at that take.
  `pad_index_ge`     every place of the pad of a shape with a mask row lies in the mask table, at
                     that index or above; `nextOf_no_pad`: SO NO ENTRY GIVEN IS ONE OF THE PAD's.
CALLED: `nextOf_no` (LedgerNo.lean), `takenNo_eq` (OnBytes/Iop/LedgerPlaces.lean),
`freeAt_entry_lt`, `freeAt_below_pad` (Fmt/PlacesLaws.lean).
What is not claimed. That a record's ledger has `LedgerAt` at any k. That the record's field `pad`
is `Send.pad`'s list (the admitting lays it so). Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.LedgerNo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open Fmt.Places (entryNo freeAt freeCount freeAt_entry_lt freeAt_below_pad)
open VerifiableInference.Desc.First.Pend (takeEntry)
open VerifiableInference.Desc.Ground (takeMaskP takeMaskL ok has)
open Desc.Plain (DState)

/-- **The real bound**, at the number that the ledger of k takes gives next. -/
theorem nextOf_bound {st : Statement} {o k : ℕ} {x : Oracle} {l : Ledger} (h : LedgerAt st o k)
    (hx : st.oracles[o]? = some x) (hl : x.ledger = some l) (h0 : 0 < l.left) :
    nextOf l = entryNo x.shape.maskRows (k % x.shape.maskRows) (k / x.shape.maskRows) ∧
      k % x.shape.maskRows < x.shape.maskRows ∧
      k / x.shape.maskRows < (st.codes.mask.getD x.shape.maskCode default).ell ∧
      nextOf l < (x.shape.maskRows - 1) +
        ((st.codes.mask.getD x.shape.maskCode default).ell - x.shape.answers) *
          2 ^ ceilLog2 x.shape.maskRows := by
  have hn := nextOf_no h hx hl
  obtain ⟨x₀, l₀, hx₀, hl₀, hm, ha, _, _, hleft, _⟩ := h
  obtain rfl := Option.some.inj (hx₀.symm.trans hx)
  obtain rfl := Option.some.inj (hl₀.symm.trans hl)
  rw [free_is] at hleft
  have hk : k < freeCount x₀.shape.maskRows
      (st.codes.mask.getD x₀.shape.maskCode default).ell x₀.shape.answers := by omega
  have hs : x₀.shape.answers ≤ (st.codes.mask.getD x₀.shape.maskCode default).ell := by
    by_contra hc
    unfold freeCount at hk
    rw [if_pos (Or.inr (by omega))] at hk
    exact absurd hk (Nat.not_lt_zero _)
  rw [hn, takenNo_eq hm k]
  refine ⟨rfl, Nat.mod_lt k hm, freeAt_entry_lt hm ha hs hk, ?_⟩
  rw [Nat.mul_comm]
  exact (freeAt_below_pad hm hs k).2 hk

/-- At the pending row's take. -/
theorem takeEntry_bound {st : Statement} {o k c : ℕ} {x : Oracle} {l l' : Ledger}
    (h : LedgerAt st o k) (hx : st.oracles[o]? = some x) (hl : x.ledger = some l)
    (ht : takeEntry l = some (c, l')) :
    c = entryNo x.shape.maskRows (k % x.shape.maskRows) (k / x.shape.maskRows) ∧
      k % x.shape.maskRows < x.shape.maskRows ∧
      k / x.shape.maskRows < (st.codes.mask.getD x.shape.maskCode default).ell ∧
      c < (x.shape.maskRows - 1) +
        ((st.codes.mask.getD x.shape.maskCode default).ell - x.shape.answers) *
          2 ^ ceilLog2 x.shape.maskRows := by
  obtain ⟨h0, rfl, _⟩ := takeEntry_is ht
  exact nextOf_bound h hx hl h0

/-- What a yes of the ground's take of one entry is. -/
theorem takeMaskP_is {L : Type} {d d' : DState L} {o n : ℕ} (ht : takeMaskP d o = some (n, d')) :
    ∃ l, (d.st.oracles[o]?).bind (·.ledger) = some l ∧ 0 < l.left ∧ n = nextOf l ∧
      d' = { d with st := layLedger d.st o (taken l) } := by
  unfold takeMaskP at ht
  split at ht
  · rename_i hok
    cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none =>
      rw [hl] at ht
      cases ht
    | some l =>
      rw [hl] at ht
      have e : (nextOf l, { d with st := layLedger d.st o (taken l) }) = (n, d') :=
        Option.some.inj ht
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      have h0 : 0 < l.left := by
        simp only [ok, takeMaskL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
          hl] at hok
        exact of_decide_eq_true hok.2.2.2
      exact ⟨l, rfl, h0, rfl, rfl⟩
  · cases ht

/-- At the ground's take of one entry. -/
theorem takeMaskP_bound {L : Type} {d d' : DState L} {o k n : ℕ} {x : Oracle}
    (h : LedgerAt d.st o k) (hx : d.st.oracles[o]? = some x)
    (ht : takeMaskP d o = some (n, d')) :
    n = entryNo x.shape.maskRows (k % x.shape.maskRows) (k / x.shape.maskRows) ∧
      k % x.shape.maskRows < x.shape.maskRows ∧
      k / x.shape.maskRows < (d.st.codes.mask.getD x.shape.maskCode default).ell ∧
      n < (x.shape.maskRows - 1) +
        ((d.st.codes.mask.getD x.shape.maskCode default).ell - x.shape.answers) *
          2 ^ ceilLog2 x.shape.maskRows := by
  obtain ⟨l, hl, h0, rfl, _⟩ := takeMaskP_is ht
  rw [hx] at hl
  exact nextOf_bound h hx hl h0

/-- Every place of the pad of a shape with a mask row lies in the mask table, at the first place's
index or above. -/
theorem pad_index_ge {codes : Codes} {s : OracleShape} {places : List PadPlace}
    (hm : 0 < s.maskRows) (hp : Send.pad codes s = some places) :
    ∀ p ∈ places, p.part = .mask ∧
      (s.maskRows - 1) + ((codes.mask.getD s.maskCode default).ell - s.answers) *
        2 ^ ceilLog2 s.maskRows ≤ p.index := by
  unfold Send.pad Send.cube at hp
  simp only [decide_eq_true hm, if_true, Bool.true_or, Nat.one_mul] at hp
  split at hp
  · cases hp
  · obtain rfl := Option.some.inj hp
    intro p hpm
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hpm
    obtain ⟨i, _, t, _, rfl⟩ := hpm
    refine ⟨rfl, ?_⟩
    show _ ≤ (s.maskRows - 1) + _ * 2 ^ ceilLog2 s.maskRows
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _

/-- **No entry given is an entry of the pad.** -/
theorem nextOf_no_pad {st : Statement} {o k : ℕ} {x : Oracle} {l : Ledger}
    {places : List PadPlace} (h : LedgerAt st o k) (hx : st.oracles[o]? = some x)
    (hl : x.ledger = some l) (h0 : 0 < l.left) (hp : Send.pad st.codes x.shape = some places) :
    ∀ p ∈ places, nextOf l < p.index := by
  intro p hpm
  have hm : 0 < x.shape.maskRows := by
    obtain ⟨x₀, _, hx₀, _, hm, _⟩ := h
    obtain rfl := Option.some.inj (hx₀.symm.trans hx)
    exact hm
  exact Nat.lt_of_lt_of_le (nextOf_bound h hx hl h0).2.2.2 (pad_index_ge hm hp p hpm).2

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.nextOf_bound
#print axioms VerifiableInference.Desc.K13.Law.takeEntry_bound
#print axioms VerifiableInference.Desc.K13.Law.takeMaskP_is
#print axioms VerifiableInference.Desc.K13.Law.takeMaskP_bound
#print axioms VerifiableInference.Desc.K13.Law.pad_index_ge
#print axioms VerifiableInference.Desc.K13.Law.nextOf_no_pad
