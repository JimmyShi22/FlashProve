-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/ClaimsP.lean: no plain function on the statement loses what the statement still
claims.

Johnson/Desc/Means/Claims.lean shows of each of the pure effects on a statement that that file
names, but the beginning of a test, that Claims behind it gives Claims in front. This file carries
that to the plain functions of Johnson/Desc/First/Base/Ground.lean, each where it returns a state,
and carries the joint at a batching to what the beginning of a test returns (beginRunP_catches).

Main theorems: newGroupP_claims, recvP_claims, adoptP_claims, admitP_claims, joinP_claims,
addRowP_claims, addRowsP_claims, takeMaskP_claims, closeLedgerP_claims, spendAsMaskP_claims,
elsewhereP_claims, beginRunP_catches.

What is not claimed. The converses. That a block changes the statement by these functions alone. No
chance is named. Nothing on soundness.

-/
import Johnson.Desc.Means.BackP
import Johnson.Desc.Means.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)
open VerifiableInference.Desc.Ground Desc.Plain

variable {Lc : Type}

/-! ## Claims goes backwards -/

variable {K : Type} [CommRing K] (ρ : Reading K) {m : Words K}

theorem newGroupP_claims {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d'))
    (hI : InOrder d.st) (hH : Claims ρ d'.st m) : Claims ρ d.st m := by
  unfold newGroupP at h
  split at h
  · obtain rfl : _ = d' := congrArg Prod.snd (Option.some.inj h)
    exact Claims.of_withGroup ρ hI a b hH
  · cases h

theorem recvP_claims {d d' : DState Lc} {first : Nat} {sent : Array OracleNotice} {ids : Array Nat}
    (h : recvP first d sent = some (ids, d')) (hI : InOrder d.st) (hH : Claims ρ d'.st m) :
    Claims ρ d.st m := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact Claims.of_stSent ρ hI sent hH
  · cases h

theorem adoptP_claims {d d' : DState Lc} {sent : Array OracleNotice}
    {given : Array (Nat × Fmt.Src)} {ids : Array Nat}
    (h : adoptP d sent given = some (ids, d')) (hI : InOrder d.st) (hH : Claims ρ d'.st m) :
    Claims ρ d.st m := by
  unfold adoptP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact Claims.of_stSent ρ hI sent hH
  · cases h

/-- A sample's answers are in: the clause "not sampled before" lets no claim be lost. -/
theorem admitP_claims {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hI : InOrder d.st) (hN : NoneYet d.st)
    (hH : Claims ρ d'.st m) : Claims ρ d.st m := by
  unfold admitP at h
  by_cases c : ok (admitL d.st o rows) = true
  · rw [if_pos c] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, places, _, rfl⟩ := h
    simp only [ok, admitL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at c
    have c3 := c.2.2.1
    rw [hx, has_some] at c3
    refine Claims.of_admitted ρ hI hN o x.shape places rows (fun x' hx' => ?_) hH
    rw [hx] at hx'
    obtain rfl := Option.some.inj hx'
    simpa using c3
  · rw [if_neg c] at h
    cases h

/-- A message joins a group: the clause "no test has begun" lets no sample row slip past its
test. -/
theorem joinP_claims {d d' : DState Lc} {g o : Nat} {kept : Bool} (h : joinP d g o kept = some d')
    (hI : InOrder d.st) (hH : Claims ρ d'.st m) : Claims ρ d.st m := by
  unfold joinP at h
  by_cases c : ok (joinL d.st g o kept) = true
  · rw [if_pos c] at h
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [ok, joinL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at c
    have c4 := c.2.2.2.1
    rw [hG, has_some] at c4
    exact Claims.of_joined ρ hI g o kept G hG (by simpa using c4) hH
  · rw [if_neg c] at h
    cases h

/-- The adding of a row: all that was claimed before, and the new row. -/
theorem addRowP_claims {d d' : DState Lc} {g : Nat} {row : Row} (h : addRowP d g row = some d')
    (hI : InOrder d.st) (hH : Claims ρ d'.st m) : Claims ρ d.st m ∧ Says ρ d.st row m := by
  obtain ⟨_, G, hG, _, e⟩ := addRowP_keeps h hI
  rw [e] at hH
  exact Claims.of_withRow ρ hI g row hG hH

theorem addRowsFrom_claims (g : Nat) : ∀ (l : List Row) (d d' : DState Lc),
    addRowsFrom g l d = some d' → InOrder d.st → Claims ρ d'.st m → Claims ρ d.st m
  | [], d, d', h, _, hH => by
    obtain rfl := Option.some.inj h
    exact hH
  | row :: l, d, d', h, hI, hH => by
    unfold addRowsFrom at h
    obtain ⟨d1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (addRowP_claims ρ h1 hI
      (addRowsFrom_claims g l d1 d' h2 (addRowP_keeps h1 hI).1 hH)).1

theorem addRowsP_claims {d d' : DState Lc} {g : Nat} {rows : List Row}
    (h : addRowsP d g rows = some d') (hI : InOrder d.st) (hH : Claims ρ d'.st m) :
    Claims ρ d.st m := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_claims ρ g rows d d' h hI hH
  · cases h

theorem takeMaskP_claims {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d'))
    (hI : InOrder d.st) (hH : Claims ρ d'.st m) : Claims ρ d.st m := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    exact Claims.of_onOracle ρ hI o (fun x => { x with ledger := some { l with
      next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1, left := l.left - 1 } })
      (fun _ => rfl) (fun _ => rfl) hH
  · cases h

theorem closeLedgerP_claims {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d')
    (hI : InOrder d.st) (hH : Claims ρ d'.st m) : Claims ρ d.st m := by
  unfold closeLedgerP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact Claims.of_closeLedgers ρ hI [o] hH
  · cases h

theorem spendAsMaskP_claims {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d')
    (hI : InOrder d.st) (hH : Claims ρ d'.st m) : Claims ρ d.st m := by
  unfold spendAsMaskP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact Claims.of_onOracle ρ hI o (fun x => { x with spentAsMask := true }) (fun _ => rfl)
      (fun _ => rfl) hH
  · cases h

/-- A message is sampled elsewhere: the clause "not sampled here" lets no claim be lost. -/
theorem elsewhereP_claims {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hI : InOrder d.st) (hN : NoneYet d.st)
    (hH : Claims ρ d'.st m) : Claims ρ d.st m := by
  unfold elsewhereP at h
  by_cases c : ok (elsewhereL d.st mine other theirs) = true
  · rw [if_pos c] at h
    obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [ok, elsewhereL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at c
    have c4 := c.2.2.2.1
    refine Claims.back (S' := { d.st with oracles := d.st.oracles.modify mine fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine),
                 pad := y.pad } }) ρ hI
      (Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ fun _ => rfl)
      (fun g G hG => ⟨G, hG, fun _ c => c⟩)
      (samples_modify (f := fun x =>
        { x with sampled := true, sampleRows := y.sampleRows.map (·.renamed mine),
                 pad := y.pad }) fun x hx r hr => ?_) (fun o' hp => hp.sameGroups rfl) hH
    rw [hx, has_some] at c4
    rw [hN mine x hx (by simpa using c4)] at hr
    simp at hr
  · rw [if_neg c] at h
    cases h

/-- **The joint at a batching, at what the beginning of a test returns.** For words of which not all
holds that the statement in front still claims: either not all holds that the statement behind still
claims, or the elements of K as which x reads, for some x at which the batched row holds of tables
that hold the words on the blocks, are fewer than the rows handed to the batching. -/
theorem beginRunP_catches [IsDomain K] [Finite K] {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) (hI : InOrder d.st) (hK : OpenKinds d.st)
    (hbad : ¬ Claims ρ d.st m) :
    ¬ Claims ρ d'.st m ∨
    Nat.card {y : K // ∃ (x : E) (out : GroupRow) (T : Tables K), ρ.val x = y ∧
      Bat.combine d'.st g input x = some out ∧ LaidOn d'.st input.layout m T ∧
      GroupSays ρ d'.st input.layout out T} ≤ input.rows.size - 1 := by
  obtain ⟨G, hG, rfl, e⟩ := beginRunP_inv h
  rw [e]
  exact claims_catches ρ hI hK g G hG hbad

end OnBytes.Means
