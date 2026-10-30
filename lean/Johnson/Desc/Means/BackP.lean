-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/BackP.lean: no plain function on the statement loses a claim.

Johnson/Desc/Means/Back.lean shows of each of the pure effects on a statement that that file names
that Holds behind it gives Holds in front. This file carries that to the plain functions of
Johnson/Desc/First/Base/Ground.lean, each where it returns a state, and shows that they keep
NoneYet. The beginning of a test is in Johnson/Desc/Means/Holds.lean and Page.lean.

Main theorems: newGroupP_back, recvP_back, adoptP_back, admitP_back, joinP_back, addRowP_back,
addRowsP_back, takeMaskP_back, closeLedgerP_back, spendAsMaskP_back, elsewhereP_back; the same names
with _none for NoneYet, and beginRunP_none.

What is not claimed. The converses. That a block changes the statement by these functions alone.
Nothing on soundness.

-/
import Johnson.Desc.Means.Back

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)
open VerifiableInference.Desc.Ground Desc.Plain

variable {Lc : Type}

/-! ## NoneYet is kept -/

theorem newGroupP_none {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d'))
    (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold newGroupP at h
  split at h
  · obtain rfl : _ = d' := congrArg Prod.snd (Option.some.inj h)
    exact hN.sameOracles rfl
  · cases h

theorem recvP_none {d d' : DState Lc} {first : Nat} {sent : Array OracleNotice} {ids : Array Nat}
    (h : recvP first d sent = some (ids, d')) (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hN.stSent sent
  · cases h

theorem adoptP_none {d d' : DState Lc} {sent : Array OracleNotice}
    {given : Array (Nat × Fmt.Src)} {ids : Array Nat}
    (h : adoptP d sent given = some (ids, d')) (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hN.stSent sent
  · cases h

theorem admitP_none {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    exact hN.marked o (fun y => { y with
      sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
      ledger := Slice.freshLedger d.st.codes x.shape }) rfl fun _ => rfl
  · cases h

theorem joinP_none {d d' : DState Lc} {g o : Nat} {kept : Bool} (h : joinP d g o kept = some d')
    (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hN.onOracle o (fun x => { x with groups := x.groups ++ [g] }) rfl (fun _ => rfl)
      (fun _ => rfl)
  · cases h

theorem addRowP_none {d d' : DState Lc} {g : Nat} {row : Row} (h : addRowP d g row = some d')
    (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold addRowP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact hN.sameOracles rfl
  · cases h

theorem takeMaskP_none {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d'))
    (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact hN.onOracle o (fun x => { x with ledger := some { l with
      next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 } })
      rfl (fun _ => rfl) (fun _ => rfl)
  · cases h

theorem closeLedgerP_none {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d')
    (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold closeLedgerP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact hN.closeLedgers [o]
  · cases h

theorem spendAsMaskP_none {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d')
    (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold spendAsMaskP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact hN.onOracle o (fun x => { x with spentAsMask := true }) rfl (fun _ => rfl)
      (fun _ => rfl)
  · cases h

theorem elsewhereP_none {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hN : NoneYet d.st) : NoneYet d'.st := by
  unfold elsewhereP at h
  split at h
  · obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact hN.marked mine (fun x => { x with
      sampled := true, sampleRows := y.sampleRows.map (·.renamed mine), pad := y.pad }) rfl
      fun _ => rfl
  · cases h

theorem beginRunP_none {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) (hN : NoneYet d.st) : NoneYet d'.st := by
  obtain ⟨G, _, _, e⟩ := beginRunP_inv h
  rw [e]
  exact (hN.closeLedgers G.members.toList).sameOracles rfl

/-! ## Holds goes backwards -/

variable {K : Type} [CommRing K] (ρ : Reading K) {m : Words K}

theorem newGroupP_back {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d'))
    (hI : InOrder d.st) (hH : Holds ρ d'.st m) : Holds ρ d.st m := by
  unfold newGroupP at h
  split at h
  · obtain rfl : _ = d' := congrArg Prod.snd (Option.some.inj h)
    exact Holds.of_withGroup ρ hI a b hH
  · cases h

theorem recvP_back {d d' : DState Lc} {first : Nat} {sent : Array OracleNotice} {ids : Array Nat}
    (h : recvP first d sent = some (ids, d')) (hI : InOrder d.st) (hH : Holds ρ d'.st m) :
    Holds ρ d.st m := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact Holds.of_stSent ρ hI sent hH
  · cases h

theorem adoptP_back {d d' : DState Lc} {sent : Array OracleNotice}
    {given : Array (Nat × Fmt.Src)} {ids : Array Nat}
    (h : adoptP d sent given = some (ids, d')) (hI : InOrder d.st) (hH : Holds ρ d'.st m) :
    Holds ρ d.st m := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact Holds.of_stSent ρ hI sent hH
  · cases h

/-- A sample's answers are in: the clause "not sampled before" lets no claim be lost. -/
theorem admitP_back {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hI : InOrder d.st) (hN : NoneYet d.st)
    (hH : Holds ρ d'.st m) : Holds ρ d.st m := by
  unfold admitP at h
  by_cases c : ok (admitL d.st o rows) = true
  · rw [if_pos c] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, places, _, rfl⟩ := h
    simp only [ok, admitL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at c
    have c3 := c.2.2.1
    rw [hx, has_some] at c3
    refine Holds.of_admitted ρ hI hN o x.shape places rows (fun x' hx' => ?_) hH
    rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
    simpa using c3
  · rw [if_neg c] at h
    cases h

theorem joinP_back {d d' : DState Lc} {g o : Nat} {kept : Bool} (h : joinP d g o kept = some d')
    (hI : InOrder d.st) (hH : Holds ρ d'.st m) : Holds ρ d.st m := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact Holds.of_joined ρ hI g o kept G hH
  · cases h

/-- The adding of a row: all that was claimed before, and the new row. -/
theorem addRowP_back {d d' : DState Lc} {g : Nat} {row : Row} (h : addRowP d g row = some d')
    (hI : InOrder d.st) (hH : Holds ρ d'.st m) : Holds ρ d.st m ∧ Says ρ d.st row m := by
  obtain ⟨_, G, hG, _, e⟩ := addRowP_keeps h hI
  rw [e] at hH
  exact Holds.of_withRow ρ hI g row hG hH

theorem addRowsFrom_back (g : Nat) : ∀ (l : List Row) (d d' : DState Lc),
    addRowsFrom g l d = some d' → InOrder d.st → Holds ρ d'.st m → Holds ρ d.st m
  | [], d, d', h, _, hH => by
    obtain rfl := Option.some.inj h
    exact hH
  | row :: l, d, d', h, hI, hH => by
    unfold addRowsFrom at h
    obtain ⟨d1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (addRowP_back ρ h1 hI
      (addRowsFrom_back g l d1 d' h2 (addRowP_keeps h1 hI).1 hH)).1

theorem addRowsP_back {d d' : DState Lc} {g : Nat} {rows : List Row}
    (h : addRowsP d g rows = some d') (hI : InOrder d.st) (hH : Holds ρ d'.st m) :
    Holds ρ d.st m := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_back ρ g rows d d' h hI hH
  · cases h

theorem takeMaskP_back {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d'))
    (hI : InOrder d.st) (hH : Holds ρ d'.st m) : Holds ρ d.st m := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact Holds.of_onOracle ρ hI o (fun x => { x with ledger := some { l with
      next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 } })
      (fun _ => rfl) (fun _ => rfl) hH
  · cases h

theorem closeLedgerP_back {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d')
    (hI : InOrder d.st) (hH : Holds ρ d'.st m) : Holds ρ d.st m := by
  unfold closeLedgerP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact Holds.of_closeLedgers ρ hI [o] hH
  · cases h

theorem spendAsMaskP_back {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d')
    (hI : InOrder d.st) (hH : Holds ρ d'.st m) : Holds ρ d.st m := by
  unfold spendAsMaskP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact Holds.of_onOracle ρ hI o (fun x => { x with spentAsMask := true }) (fun _ => rfl)
      (fun _ => rfl) hH
  · cases h

/-- A message is sampled elsewhere: the clause "not sampled here" lets no claim be lost. -/
theorem elsewhereP_back {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hI : InOrder d.st) (hN : NoneYet d.st)
    (hH : Holds ρ d'.st m) : Holds ρ d.st m := by
  unfold elsewhereP at h
  by_cases c : ok (elsewhereL d.st mine other theirs) = true
  · rw [if_pos c] at h
    obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [ok, elsewhereL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at c
    have c4 := c.2.2.2.1
    refine Holds.back (S' := { d.st with oracles := d.st.oracles.modify mine fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine),
                 pad := y.pad } }) ρ hI
      (Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ fun _ => rfl)
      (fun g G hG => ⟨G, hG, fun _ c => c⟩)
      (samples_modify (f := fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine),
                 pad := y.pad }) fun x hx r hr => ?_) hH
    rw [hx, has_some] at c4
    rw [hN mine x hx (by simpa using c4)] at hr
    simp at hr
  · rw [if_neg c] at h
    cases h

end OnBytes.Means
