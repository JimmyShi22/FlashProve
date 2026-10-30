-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MembersCarried.lean: **THE SHARED CHAIN's RECORD CARRIES WHICH MESSAGES, BY NUMBER, ARE THE MEMBERS OF ITS TWO GROUPS: A FOURTH BOOL BESIDE "shape k".** One definition with code;
statements and proofs, in the blocks' own decide-form.

What for. The law of the proximity test speaks of "the members of the group under test", in the record's order. The table's seats are the plan's. Johnson/Desc/Sound/SeatsCarried.lean carries where the i-th
message of each sending was laid; here: that G_u's members are o_u and o_sp, G_omega's o_omega and o_sp, BY THEIR NUMBERS in the chain's statement, in that order; and what the small record notes of them.
  memOf d g        the members of the group number g, if it is there.
  membX sU k d     THE BOOL. sU: how many messages o_u's sending has. The numbers: o_u 0 · the first mask 1 · o_omega sU · o_sp sU + 1.
                   borders 0, 1: no message · 2: two groups, apart, without a member; no message · 3: sU messages; o_u and the mask noted · 4, 5: G_u = [0] · 6: o_omega and o_sp noted ·
                   7 … 9: G_u = [0, sU + 1], G_omega = [sU, sU + 1] · 10: G_omega still · 11, 12: what is noted of o_omega and o_sp still · behind: nothing.
  membX_first · membX_front · membX_k14 · membX_onGu · membX_onGomega · membX_end   EVERY BLOCK HANDS IT ON. UNDER: the plan has a split (sharedSplitNeeded) and its masks go ahead (masksAhead).
  membX_nine · membX_ten   what the two tests spend.   membX_twelve   what can be spent at the chain's last border.
Limits. WITH A SPLIT AND THE MASKS AHEAD ALONE. At the chain's own record St. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SeatsCarried
import Johnson.Desc.K1.Law.KeptAtRecord
import Johnson.Desc.K15.GroundInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (decideSend sendOwn)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)

section
variable {L : Type}

/-- The members of the group number g. -/
def memOf (d : DState L) (g : ℕ) : Option (Array ℕ) := (d.st.groups[g]?).map (·.members)

/-- A joining: the group's members with the new one at its place by number; every other group's as they were. -/
theorem joinP_mem (d d' : DState L) (g o : Nat) (kept : Bool) (h : joinP d g o kept = some d')
    (M : Array ℕ) (hM : memOf d g = some M) :
    memOf d' g = some (M.insertIdxIfInBounds (M.filter (· < o)).size o) ∧
      (∀ g', g' ≠ g → memOf d' g' = memOf d g') ∧ d'.st.oracles.size = d.st.oracles.size ∧
      d'.loc = d.loc := by
  obtain ⟨G, hG, rfl⟩ := _root_.Desc.K15.joinP_inv d d' g o kept h
  have eM : G.members = M := by
    unfold memOf at hM
    rw [hG] at hM
    exact Option.some.inj hM
  refine ⟨?_, fun g' hg => ?_, ?_, rfl⟩
  · unfold memOf
    show ((withMessageInGroup d.st g o kept G).groups[g]?).map (·.members) = _
    rw [joined_group d.st g o kept G hG, ← eM]
    rfl
  · unfold memOf
    show ((d.st.groups.modify g _)[g']?).map (·.members) = _
    rw [Array.getElem?_modify, if_neg (Ne.symm hg)]
  · show (d.st.oracles.modify o _).size = _
    rw [Array.size_modify]

/-- A row more: every group's members as they were. -/
theorem addRowP_mem (d d' : DState L) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    (∀ g', memOf d' g' = memOf d g') ∧ d'.st.oracles.size = d.st.oracles.size ∧ d'.loc = d.loc := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨fun g' => ?_, rfl, rfl⟩
    unfold memOf
    show ((d.st.groups.modify g _)[g']?).map (·.members) = _
    rw [Array.getElem?_modify]
    split
    · rw [Option.map_map]
      rfl
    · rfl
  · cases h

theorem addRowsFrom_mem (g : Nat) : ∀ (l : List Row) (d d' : DState L),
    addRowsFrom g l d = some d' →
    (∀ g', memOf d' g' = memOf d g') ∧ d'.st.oracles.size = d.st.oracles.size ∧ d'.loc = d.loc
  | [], d, d', h => by
    simp only [addRowsFrom, Option.some.injEq] at h
    subst h
    exact ⟨fun _ => rfl, rfl, rfl⟩
  | row :: l, d, d', h => by
    simp only [addRowsFrom, Option.bind_eq_some_iff] at h
    obtain ⟨d1, h1, h2⟩ := h
    obtain ⟨a1, a2, a3⟩ := addRowP_mem d d1 g row h1
    obtain ⟨b1, b2, b3⟩ := addRowsFrom_mem g l d1 d' h2
    exact ⟨fun g' => (b1 g').trans (a1 g'), b2.trans a2, b3.trans a3⟩

theorem addRowsP_mem (d d' : DState L) (g : Nat) (rows : List Row)
    (h : addRowsP d g rows = some d') :
    (∀ g', memOf d' g' = memOf d g') ∧ d'.st.oracles.size = d.st.oracles.size ∧ d'.loc = d.loc := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_mem g rows d d' h
  · cases h

theorem takeMaskP_mem (d d' : DState L) (o k : Nat) (h : takeMaskP d o = some (k, d')) :
    (∀ g', memOf d' g' = memOf d g') ∧ d'.st.oracles.size = d.st.oracles.size ∧ d'.loc = d.loc := by
  unfold takeMaskP at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨l, _, _, rfl⟩ := h
    refine ⟨fun _ => rfl, ?_, rfl⟩
    show (d.st.oracles.modify o _).size = _
    rw [Array.size_modify]
  · cases h

end

/-! ## The Bool -/

/-- **THE FOURTH BOOL BESIDE "shape k".** -/
def membX (sU k : ℕ) (d : St) : Bool :=
  let mU := memOf d d.loc.gU
  let mO := memOf d d.loc.gOmega
  let ap := d.loc.gOmega != d.loc.gU
  let nu := d.loc.oU.oracle == 0 && d.loc.firstMask == some 1
  let no := d.loc.oOmega == sU && d.loc.oSp == sU + 1
  if k ≤ 1 then d.st.oracles.size == 0
  else if k = 2 then ap && mU == some #[] && mO == some #[] && d.st.oracles.size == 0
  else if k = 3 then ap && mU == some #[] && mO == some #[] && d.st.oracles.size == sU && nu
  else if k ≤ 5 then ap && mU == some #[0] && mO == some #[] && d.st.oracles.size == sU && nu
  else if k = 6 then ap && mU == some #[0] && mO == some #[] && nu && no
  else if k ≤ 9 then ap && mU == some #[0, sU + 1] && mO == some #[sU, sU + 1] && nu && no
  else if k = 10 then ap && mO == some #[sU, sU + 1] && no
  else if k ≤ 12 then no
  else true

section
variable (sU : ℕ) (d : St)

theorem membX01 (k : ℕ) (hk : k ≤ 1) : membX sU k d = true ↔ d.st.oracles.size = 0 := by
  unfold membX
  simp [hk]

theorem membX2 : membX sU 2 d = true ↔ d.loc.gOmega ≠ d.loc.gU ∧ memOf d d.loc.gU = some #[] ∧
    memOf d d.loc.gOmega = some #[] ∧ d.st.oracles.size = 0 := by
  unfold membX
  simp [and_assoc]

theorem membX3 : membX sU 3 d = true ↔ d.loc.gOmega ≠ d.loc.gU ∧ memOf d d.loc.gU = some #[] ∧
    memOf d d.loc.gOmega = some #[] ∧ d.st.oracles.size = sU ∧ d.loc.oU.oracle = 0 ∧
    d.loc.firstMask = some 1 := by
  unfold membX
  simp [and_assoc]

theorem membX45 (k : ℕ) (hk : k = 4 ∨ k = 5) : membX sU k d = true ↔ d.loc.gOmega ≠ d.loc.gU ∧
    memOf d d.loc.gU = some #[0] ∧ memOf d d.loc.gOmega = some #[] ∧ d.st.oracles.size = sU ∧
    d.loc.oU.oracle = 0 ∧ d.loc.firstMask = some 1 := by
  unfold membX
  rcases hk with rfl | rfl <;> simp [and_assoc]

theorem membX6 : membX sU 6 d = true ↔ d.loc.gOmega ≠ d.loc.gU ∧ memOf d d.loc.gU = some #[0] ∧
    memOf d d.loc.gOmega = some #[] ∧ (d.loc.oU.oracle = 0 ∧ d.loc.firstMask = some 1) ∧
    d.loc.oOmega = sU ∧ d.loc.oSp = sU + 1 := by
  unfold membX
  simp [and_assoc]

theorem membX789 (k : ℕ) (hk : k = 7 ∨ k = 8 ∨ k = 9) : membX sU k d = true ↔
    d.loc.gOmega ≠ d.loc.gU ∧ memOf d d.loc.gU = some #[0, sU + 1] ∧
    memOf d d.loc.gOmega = some #[sU, sU + 1] ∧ (d.loc.oU.oracle = 0 ∧ d.loc.firstMask = some 1) ∧
    d.loc.oOmega = sU ∧ d.loc.oSp = sU + 1 := by
  unfold membX
  rcases hk with rfl | rfl | rfl <;> simp [and_assoc]

theorem membX10 : membX sU 10 d = true ↔ d.loc.gOmega ≠ d.loc.gU ∧
    memOf d d.loc.gOmega = some #[sU, sU + 1] ∧ d.loc.oOmega = sU ∧ d.loc.oSp = sU + 1 := by
  unfold membX
  simp [and_assoc]

theorem membX1112 (k : ℕ) (hk : k = 11 ∨ k = 12) : membX sU k d = true ↔
    d.loc.oOmega = sU ∧ d.loc.oSp = sU + 1 := by
  unfold membX
  rcases hk with rfl | rfl <;> simp

/-- Past the chain's end, at one record. -/
theorem membX_end (h : membX sU 11 d = true) : membX sU 12 d = true :=
  (membX1112 sU d 12 (.inr rfl)).2 ((membX1112 sU d 11 (.inl rfl)).1 h)

end

theorem membX_first (sU : ℕ) (codes : Codes) (key : TableKey) :
    membX sU 0 (first codes key) = true := (membX01 sU _ 0 (by omega)).2 rfl

theorem membX_front (sU : ℕ) (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontBlock c).decide d rs gs = .ok d')
    (hX : membX sU 0 d = true) : membX sU 1 d' = true := by
  rw [bookStep_front c d d' rs gs h]
  exact (membX01 sU d 1 (by omega)).2 ((membX01 sU d 0 (by omega)).1 hX)

/-- "LIN point". -/
theorem membX_point (p : Par) (hS : p.S.sharedSplitNeeded = true) (sU : ℕ) (d d' : St)
    (rs : List Fmt.RoundView) (h : linPoint p d rs = some d') (hX : membX sU 1 d = true) :
    membX sU 2 d' = true := by
  have h0 := (membX01 sU d 1 (by omega)).1 hX
  unfold linPoint at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    rw [if_pos hS] at h2
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
    obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
    obtain ⟨rfl, rfl⟩ := _root_.Desc.K15.newGroupP_inv d d1 _ _ gU h1
    obtain ⟨rfl, rfl⟩ := _root_.Desc.K15.newGroupP_inv _ d2 _ _ gO h3
    refine (membX2 sU _).2 ⟨?_, ?_, ?_, h0⟩
    · show (d.st.groups.push _).size ≠ d.st.groups.size
      rw [Array.size_push]
      omega
    · show (((d.st.groups.push _).push _)[d.st.groups.size]?).map (·.members) = _
      rw [Array.getElem?_push_lt (by rw [Array.size_push]; omega), Array.getElem_push_eq]
      rfl
    · show (((d.st.groups.push _).push _)[(d.st.groups.push _).size]?).map (·.members) = _
      rw [Array.getElem?_push_size]
      rfl
  · cases h

/-- What a sending at this chain's state notes: at a record with the small record and the groups in front, at the numbers from the count of messages on. -/
theorem sendAt_ids (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat)) (behind : St → Array Nat → Option St)
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups behind).decide d rs gs = .ok d') :
    ∃ a : St, a.loc = d.loc ∧ a.st.groups = d.st.groups ∧
      a.st.oracles.size = d.st.oracles.size + Q.sent.size ∧
      behind a ((Array.range Q.sent.size).map (· + d.st.oracles.size)) = some d' := by
  simp only [sendAt, Block.inside] at h
  obtain ⟨t, ht, h⟩ := ebind_ok h
  cases ht
  obtain ⟨t', ht', h⟩ := ebind_ok h
  simp only [sendOwn] at ht'
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := emap_ok ht'
  obtain ⟨_, k2, _⟩ := VerifiableInference.Desc.K1.decideSend_kept Q none _ x2 rs ids hx
  obtain ⟨x1, hr, _, _, es⟩ := decideSend_book Q none _ rs ids x2 hx
  obtain ⟨lay, _, _, r3, _, _⟩ := VerifiableInference.Desc.K1.recvP_received _ _ _ _ _ hr
  obtain ⟨_, _, _, hids, _⟩ := _root_.Desc.K15.recvP_inv _ _ _ _ _ hr
  have hb := named_some h
  refine ⟨{ st := x2.st, book := x2.book, roots := x2.roots, opened := x2.opened, loc := d.loc }, rfl,
    k2, es.trans r3, ?_⟩
  rw [← hids]
  exact hb

theorem ids_get (n s j v : ℕ) (h : ((Array.range n).map (· + s))[j]? = some v) : v = j + s := by
  rw [Array.getElem?_map, Array.getElem?_range] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem memOf_groups {a d : St} (h : a.st.groups = d.st.groups) (g : ℕ) : memOf a g = memOf d g := by
  unfold memOf
  rw [h]

/-- "send o_u". -/
theorem membX_sendU (P : P14) (hm : P.par.S.masksAhead = true) (n : String)
    (Q : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry) (groups : List (List Nat))
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups (behindU P.par)).decide d rs gs = .ok d')
    (hX : membX Q.sent.size 2 d = true) : membX Q.sent.size 3 d' = true := by
  obtain ⟨h1, h2, h3, h4⟩ := (membX2 _ d).1 hX
  obtain ⟨a, la, ga, sa, hb⟩ := sendAt_ids P n Q inFront groups _ d d' rs gs h
  unfold behindU at hb
  simp only [Option.bind_eq_bind, hm, if_true, Option.bind_eq_some_iff, Option.some.injEq,
    Option.map_eq_some_iff] at hb
  obtain ⟨mask, ⟨id1, e1, rfl⟩, o, e0, rfl⟩ := hb
  have v1 := ids_get _ _ _ _ e1
  have v0 := ids_get _ _ _ _ e0
  rw [h4] at v1 v0 sa
  refine (membX3 _ _).2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show a.loc.gOmega ≠ a.loc.gU
    rw [la]
    exact h1
  · show memOf a a.loc.gU = _
    rw [la, memOf_groups ga]
    exact h2
  · show memOf a a.loc.gOmega = _
    rw [la, memOf_groups ga]
    exact h3
  · show a.st.oracles.size = _
    rw [sa, Nat.zero_add]
  · exact v0
  · show some id1 = some 1
    rw [v1]

/-- "(rec_gamma)". -/
theorem membX_rec (p : Par) (sU : ℕ) (d d' : St) (rs : List Fmt.RoundView) (h : laysRec p d rs = some d')
    (hX : membX sU 3 d = true) : membX sU 4 d' = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (membX3 _ d).1 hX
  unfold laysRec at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, hj, rows, _, ha⟩ := h
  obtain ⟨a1, a2, a3, a4⟩ := joinP_mem d d1 _ _ _ hj _ h2
  obtain ⟨b1, b2, b3⟩ := addRowsP_mem d1 d' _ rows ha
  have l : d'.loc = d.loc := b3.trans a4
  refine (membX45 _ _ 4 (.inl rfl)).2 ⟨by rw [l]; exact h1, ?_, ?_, (b2.trans a3).trans h4,
    by rw [l]; exact h5, by rw [l]; exact h6⟩
  · rw [l, b1, a1, h5]
    simp
  · rw [l, b1, a2 _ h1]
    exact h3

/-- A place that leaves the members, the count of messages and the small record. -/
theorem membX_quiet (sU k : ℕ) (d d' : St) (hm : ∀ g, memOf d' g = memOf d g)
    (hs : d'.st.oracles.size = d.st.oracles.size) (hl : d'.loc = d.loc)
    (hk : k = 4 ∨ k = 7 ∨ k = 8) (hX : membX sU k d = true) : membX sU (k + 1) d' = true := by
  rcases hk with rfl | rfl | rfl
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (membX45 _ d 4 (.inl rfl)).1 hX
    exact (membX45 _ _ 5 (.inr rfl)).2 ⟨by rw [hl]; exact h1, by rw [hl, hm]; exact h2,
      by rw [hl, hm]; exact h3, hs.trans h4, by rw [hl]; exact h5, by rw [hl]; exact h6⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (membX789 _ d 7 (.inl rfl)).1 hX
    exact (membX789 _ _ 8 (.inr (.inl rfl))).2 ⟨by rw [hl]; exact h1, by rw [hl, hm]; exact h2,
      by rw [hl, hm]; exact h3, by rw [hl]; exact h4, by rw [hl]; exact h5, by rw [hl]; exact h6⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (membX789 _ d 8 (.inr (.inl rfl))).1 hX
    exact (membX789 _ _ 9 (.inr (.inr rfl))).2 ⟨by rw [hl]; exact h1, by rw [hl, hm]; exact h2,
      by rw [hl, hm]; exact h3, by rw [hl]; exact h4, by rw [hl]; exact h5, by rw [hl]; exact h6⟩

/-- "LOC". -/
theorem membX_loc (p : Par) (sU : ℕ) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : loc p d rs gs = some d')
    (hX : membX sU 4 d = true) : membX sU 5 d' = true := by
  unfold loc at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨rows, _, ha⟩ := h
    obtain ⟨b1, b2, b3⟩ := addRowsP_mem d d' _ rows ha
    exact membX_quiet sU 4 d d' b1 b2 b3 (.inl rfl) hX
  · cases h

/-- "send o_omega". -/
theorem membX_sendO (P : P14) (hS : P.par.S.sharedSplitNeeded = true) (sU : ℕ) (n : String)
    (Q : VerifiableInference.Desc.K1.Par) (inFront : Option Fmt.Entry) (groups : List (List Nat))
    (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (sendAt P n Q inFront groups (behindOmega P.par)).decide d rs gs = .ok d')
    (hX : membX sU 5 d = true) : membX sU 6 d' = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (membX45 _ d 5 (.inr rfl)).1 hX
  obtain ⟨a, la, ga, _, hb⟩ := sendAt_ids P n Q inFront groups _ d d' rs gs h
  unfold behindOmega at hb
  simp only [Option.bind_eq_bind, hS, if_true, Option.bind_eq_some_iff, Option.some.injEq] at hb
  obtain ⟨sp, e1, o, e0, rfl⟩ := hb
  have v1 := ids_get _ _ _ _ e1
  have v0 := ids_get _ _ _ _ e0
  rw [h4] at v1 v0
  refine (membX6 _ _).2 ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · show a.loc.gOmega ≠ a.loc.gU
    rw [la]
    exact h1
  · show memOf a a.loc.gU = _
    rw [la, memOf_groups ga]
    exact h2
  · show memOf a a.loc.gOmega = _
    rw [la, memOf_groups ga]
    exact h3
  · show a.loc.oU.oracle = 0
    rw [la]
    exact h5
  · show a.loc.firstMask = some 1
    rw [la]
    exact h6
  · show o = sU
    omega
  · show sp = sU + 1
    omega

/-- The joinings. -/
theorem membX_joins (p : Par) (hS : p.S.sharedSplitNeeded = true) (sU : ℕ) (d d' : St)
    (rs : List Fmt.RoundView) (h : joins p d rs = some d') (hX : membX sU 6 d = true) :
    membX sU 7 d' = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (membX6 _ d).1 hX
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, _, d1, j1, h⟩ := h
  rw [if_pos hS] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨d2, j2, j3⟩ := h
  obtain ⟨a1, a2, _, a4⟩ := joinP_mem d d1 _ _ _ j1 _ h3
  obtain ⟨b1, b2, _, b4⟩ := joinP_mem d1 d2 _ _ _ j2 _ a1
  have hU2 : memOf d2 d.loc.gU = some #[0] := by rw [b2 _ (Ne.symm h1), a2 _ (Ne.symm h1)]; exact h2
  obtain ⟨c1, c2, _, c4⟩ := joinP_mem d2 d' _ _ _ j3 _ hU2
  have l : d'.loc = d.loc := (c4.trans b4).trans a4
  refine (membX789 _ _ 7 (.inl rfl)).2 ⟨by rw [l]; exact h1, ?_, ?_, by rw [l]; exact h4,
    by rw [l]; exact h5, by rw [l]; exact h6⟩
  · rw [l, c1, h6]
    simp
  · rw [l, c2 _ h1, b1, h5, h6]
    simp

/-- "LIN zeta". -/
theorem membX_zeta (sU : ℕ) (d d' : St) (rs : List Fmt.RoundView) (h : linZeta d rs = some d')
    (hX : membX sU 7 d = true) : membX sU 8 d' = true := by
  unfold linZeta at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact (membX789 _ _ 8 (.inr (.inl rfl))).2 ((membX789 _ d 7 (.inl rfl)).1 hX)
  · cases h

/-- "SPLIT". -/
theorem membX_split (p : Par) (hS : p.S.sharedSplitNeeded = true) (sU : ℕ) (d d' : St)
    (rs : List Fmt.RoundView) (h : split p d rs = some d') (hX : membX sU 8 d = true) :
    membX sU 9 d' = true := by
  rcases rs with _ | ⟨r, _ | ⟨r2, rs⟩⟩
  · unfold split at h
    simp [hS] at h
  · obtain ⟨row, x, G, kappa, d₁, d₂, _, _, _, _, hk, h2, h3⟩ := split_inv p d d' r hS h
    obtain ⟨a1, a2, a3⟩ := takeMaskP_mem d d₁ _ _ hk
    obtain ⟨b1, b2, b3⟩ := addRowP_mem d₁ d₂ _ _ h2
    obtain ⟨c1, c2, c3⟩ := addRowP_mem d₂ d' _ _ h3
    exact membX_quiet sU 8 d d' (fun g => ((c1 g).trans (b1 g)).trans (a1 g))
      ((c2.trans b2).trans a2) ((c3.trans b3).trans a3) (.inr (.inr rfl)) hX
  · unfold split at h
    simp [hS] at h

/-- **K14's eight blocks hand it on.** i: the block's place in blocks P, from 0. -/
theorem membX_k14 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (sentU : Array OracleNotice)
    (hU : withU P.S = some sentU) (hS : P.par.S.sharedSplitNeeded = true)
    (hm : P.par.S.masksAhead = true)
    (i : ℕ) (b : Block St Unit) (hb : [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some b) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d')
    (hX : membX sentU.size (i + 1) d = true) : membX sentU.size (i + 2) d' = true := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hbl
  obtain ⟨sentU', hU', rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  obtain rfl : sentU' = sentU := Option.some.inj (hU'.symm.trans hU)
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  · obtain rfl := Option.some.inj (show some _ = some b from hb)
    exact membX_point _ hS _ d d' rs (why_some _ _ _ h) hX
  · obtain rfl := Option.some.inj (show some _ = some b from hb)
    have := membX_sendU P hm _ (parK1 P 2 "o_u and the first mask" sentU') _ _ d d' rs gs h
    rw [parK1_sent] at this
    exact this hX
  · obtain rfl := Option.some.inj (show some _ = some b from hb)
    exact membX_rec _ _ d d' rs (why_some _ _ _ h) hX
  · obtain rfl := Option.some.inj (show some _ = some b from hb)
    exact membX_loc _ _ d d' rs gs (why_some _ _ _ h) hX
  · obtain rfl := Option.some.inj (show some _ = some b from hb)
    exact membX_sendO P hS _ _ _ _ _ d d' rs gs h hX
  · obtain rfl := Option.some.inj (show some _ = some b from hb)
    exact membX_joins _ hS _ d d' rs (why_some _ _ _ h) hX
  · obtain rfl := Option.some.inj (show some _ = some b from hb)
    exact membX_zeta _ d d' rs (why_some _ _ _ h) hX
  · obtain rfl := Option.some.inj (show some _ = some b from hb)
    exact membX_split _ hS _ d d' rs (why_some _ _ _ h) hX
  · simp at hb

/-- **The test on G_u.** -/
theorem membX_onGu (sU : ℕ) (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs =
      .ok d') (hX : membX sU 9 d = true) : membX sU 10 d' = true := by
  obtain ⟨h1, _, h3, _, h5, h6⟩ := (membX789 _ d 9 (.inr (.inr rfl))).1 hX
  obtain ⟨_, _, c, l, _⟩ := VerifiableInference.Desc.K12.Coin.onGu_leaves p he ha d d' rs gs h
  have hlt : d.loc.gOmega < d.st.groups.size := by
    unfold memOf at h3
    obtain ⟨G, hG, _⟩ := Option.map_eq_some_iff.1 h3
    exact (Array.getElem?_eq_some_iff.1 hG).1
  refine (membX10 _ _).2 ⟨by rw [l]; exact h1, ?_, by rw [l]; exact h5, by rw [l]; exact h6⟩
  rw [l]
  unfold memOf
  rw [c _ hlt h1]
  exact h3

/-- What the test on G_u spends. -/
theorem membX_nine (sU : ℕ) (d : St) (h : membX sU 9 d = true) :
    memOf d d.loc.gU = some #[0, sU + 1] ∧ d.loc.firstMask = some 1 :=
  ⟨((membX789 _ d 9 (.inr (.inr rfl))).1 h).2.1, ((membX789 _ d 9 (.inr (.inr rfl))).1 h).2.2.2.1.2⟩

/-- What the test on G_omega spends. -/
theorem membX_ten (sU : ℕ) (d : St) (h : membX sU 10 d = true) :
    memOf d d.loc.gOmega = some #[sU, sU + 1] := ((membX10 _ d).1 h).2.1

/-- **The test on G_omega**: what the small record notes of o_omega and o_sp stays. -/
theorem membX_onGomega (sU : ℕ) (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs
      gs = .ok d') (hX : membX sU 10 d = true) : membX sU 11 d' = true := by
  obtain ⟨_, _, h5, h6⟩ := (membX10 _ d).1 hX
  have l := (VerifiableInference.Desc.K12.Coin.onGomega_leaves p he ha d d' rs gs h).2.2.2.1
  exact (membX1112 _ _ 11 (.inl rfl)).2 ⟨by rw [l]; exact h5, by rw [l]; exact h6⟩

/-- What can be spent at the chain's last border. -/
theorem membX_twelve (sU : ℕ) (d : St) (h : membX sU 12 d = true) :
    d.loc.oOmega = sU ∧ d.loc.oSp = sU + 1 := (membX1112 _ d 12 (.inr rfl)).1 h

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.membX_k14
#print axioms Desc.K14.Law.Fence.membX_onGu
#print axioms Desc.K14.Law.Fence.membX_nine
#print axioms Desc.K14.Law.Fence.membX_ten
#print axioms Desc.K14.Law.Fence.membX_onGomega
#print axioms Desc.K14.Law.Fence.membX_twelve
