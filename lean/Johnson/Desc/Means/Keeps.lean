-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Keeps.lean: what a row means stays as it was while the statement goes on.

The statement changes as a chain goes on: oracle messages are sent and admitted, groups are made,
messages join them, rows are added, a proximity test begins. None of these turns a code or the shape
of an oracle message that is there (Extends). This file shows that under Extends a row that names
earlier oracle messages alone has the same value on all words, that the conditions GroupOk and RowIn
and the group's layout stay, and that each of the library's pure effects gives Extends. With that:
the law of the adding of a row (addRow_means) and the law of the batching at the statement behind
the beginning of a test (begin_means).

Main definitions: Extends.
Main theorems: Extends.tableSize, value_extends, says_extends, RowIn.extends, GroupOk.extends,
layoutOf_extends; extends_withRow, extends_withGroup, extends_withMessageInGroup, extends_admitted,
extends_closeLedgers, extends_begun, extends_stSent; addRow_means, begin_means.

Plain records and pure functions of the program are named here, none that takes a context or runs:
Slice.withRow, withGroup, withMessageInGroup, admitted, closeLedgers, begun, runRows, stSent.

What is not claimed. That GroupOk holds after a message has joined: that is shown in
Johnson/Desc/Means/Order.lean (GroupOk.insert, InOrder.withMessageInGroup). Nothing on soundness.

-/
import Johnson.Desc.Means.Combine
import Johnson.Desc.Means.Tables
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {S S' S'' : Statement} {G G' : Group} {row : Row}

/-- A later statement: the codes are the same, and every oracle message that was there is there with
its shape. -/
structure Extends (S S' : Statement) : Prop where
  codes : S'.codes = S.codes
  shape : ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x →
    ∃ x' : Oracle, S'.oracles[o]? = some x' ∧ x'.shape = x.shape

theorem Extends.refl (S : Statement) : Extends S S := ⟨rfl, fun _ x h => ⟨x, h, rfl⟩⟩

theorem Extends.trans (h1 : Extends S S') (h2 : Extends S' S'') : Extends S S'' :=
  ⟨h2.codes.trans h1.codes, fun o x hx => by
    obtain ⟨x', hx', e'⟩ := h1.shape o x hx
    obtain ⟨x'', hx'', e''⟩ := h2.shape o x' hx'
    exact ⟨x'', hx'', e''.trans e'⟩⟩

theorem Extends.size (h : Extends S S') : S.oracles.size ≤ S'.oracles.size := by
  by_contra c
  have c' : S'.oracles.size < S.oracles.size := Nat.lt_of_not_le c
  obtain ⟨x', hx', _⟩ := h.shape _ _ (Array.getElem?_eq_getElem c')
  rw [Array.getElem?_eq_none (Nat.le_refl _)] at hx'
  cases hx'

/-- Statements with the same codes and, at each number, the same shape. -/
theorem Extends.of_shapes (hc : S'.codes = S.codes)
    (hs : ∀ o : Nat, (S'.oracles[o]?).map (fun x : Oracle => x.shape) =
      (S.oracles[o]?).map (fun x : Oracle => x.shape)) : Extends S S' :=
  ⟨hc, fun o x hx => by
    have e := hs o
    rw [hx] at e
    cases hx' : S'.oracles[o]? with
    | none =>
      rw [hx'] at e
      cases e
    | some x' =>
      rw [hx'] at e
      exact ⟨x', rfl, Option.some.inj e⟩⟩

/-! ## The tables stay -/

theorem Extends.has (h : Extends S S') {o : Nat} (ho : o < S.oracles.size) (part : Part) :
    S'.has o part = S.has o part := by
  obtain ⟨x', hx', e⟩ := h.shape o _ (Array.getElem?_eq_getElem ho)
  unfold Statement.has
  rw [hx', Array.getElem?_eq_getElem ho]
  dsimp only
  rw [e]

theorem Extends.rowBits (h : Extends S S') {o : Nat} (ho : o < S.oracles.size) (part : Part) :
    S'.rowBits o part = S.rowBits o part := by
  obtain ⟨x', hx', e⟩ := h.shape o _ (Array.getElem?_eq_getElem ho)
  unfold Statement.rowBits
  rw [hx', Array.getElem?_eq_getElem ho]
  dsimp only
  rw [e]

theorem Extends.placeBits (h : Extends S S') {o : Nat} (ho : o < S.oracles.size) (part : Part) :
    S'.placeBits o part = S.placeBits o part := by
  obtain ⟨x', hx', e⟩ := h.shape o _ (Array.getElem?_eq_getElem ho)
  unfold Statement.placeBits
  rw [hx', Array.getElem?_eq_getElem ho, h.codes]
  dsimp only
  rw [e]

theorem Extends.tableBits (h : Extends S S') {o : Nat} (ho : o < S.oracles.size) (part : Part) :
    S'.tableBits o part = S.tableBits o part := by
  unfold Statement.tableBits
  rw [h.rowBits ho, h.placeBits ho]

theorem Extends.tableSize (h : Extends S S') {o : Nat} (ho : o < S.oracles.size) (part : Part) :
    tableSize S' o part = tableSize S o part := by
  unfold Means.tableSize
  rw [h.has ho, h.tableBits ho]

/-! ## What a row means stays -/

/-- A row with no coefficient on later oracle messages has the same value in a later statement. -/
theorem value_extends (h : Extends S S') (r : Row) (m : Words K)
    (hz : ∀ o, S.oracles.size ≤ o → ∀ part i, ρ.val (r.coefficient o part i) = 0) :
    value ρ S' r m = value ρ S r m := by
  unfold value
  symm
  have e1 : ∀ o ∈ Finset.range S.oracles.size,
      onTable ρ S r m o .main + onTable ρ S r m o .mask =
        onTable ρ S' r m o .main + onTable ρ S' r m o .mask := by
    intro o ho
    unfold onTable
    rw [h.tableSize (Finset.mem_range.1 ho), h.tableSize (Finset.mem_range.1 ho)]
  rw [Finset.sum_congr rfl e1]
  apply Finset.sum_subset
  · intro o ho
    exact Finset.mem_range.2 (Nat.lt_of_lt_of_le (Finset.mem_range.1 ho) h.size)
  · intro o _ hno
    have hle : S.oracles.size ≤ o := Nat.le_of_not_lt fun c => hno (Finset.mem_range.2 c)
    unfold onTable
    simp only [hz o hle, zero_mul, Finset.sum_const_zero, add_zero]

/-- A summand that fits its place fits it at the group of all oracle messages. -/
theorem placeOk_all {o : Nat} {part : Part} {vars index : Nat}
    (hp : Blk.placeOk S G o part vars index = true) :
    Blk.placeOk S { code := 0, members := Array.range S.oracles.size } o part vars index =
      true := by
  obtain ⟨_, hh, hv, hi⟩ := (placeOk_iff _ _ _ _ _ _).1 hp
  exact (placeOk_iff _ _ _ _ _ _).2
    ⟨Array.mem_toList_iff.2 (Array.mem_range.2 (lt_of_has hh)), hh, hv, hi⟩

/-- A row that has passed the tests has no coefficient on later oracle messages. -/
theorem RowIn.off (hr : RowIn S G row) (o : Nat) (ho : S.oracles.size ≤ o)
    (part : Part) (i : Nat) : ρ.val (row.coefficient o part i) = 0 := by
  have hr' : RowIn S { code := 0, members := Array.range S.oracles.size } row :=
    ⟨fun t ht => placeOk_all (hr.terms t ht), fun u hu => placeOk_all (hr.units u hu),
      fun w hw => ⟨(hr.runs w hw).1, (hr.runs w hw).2.1, placeOk_all (hr.runs w hw).2.2⟩,
      fun f hf => ⟨placeOk_all (hr.forms f hf).1, (hr.forms f hf).2⟩⟩
  exact coefficient_off ρ hr' (fun hm =>
    absurd (Array.mem_range.1 (Array.mem_toList_iff.1 hm)) (Nat.not_lt.2 ho)) part i

/-- **A row that has passed the tests says in a later statement what it said.** -/
theorem says_extends (h : Extends S S') (hr : RowIn S G row) (m : Words K) :
    Says ρ S' row m ↔ Says ρ S row m := by
  unfold Says
  rw [value_extends ρ h row m (hr.off ρ)]

theorem short_extends (h : Extends S S') (hr : RowIn S G row) (m : Words K) :
    short ρ S' row m = short ρ S row m := by
  unfold short
  rw [value_extends ρ h row m (hr.off ρ)]

/-! ## The conditions stay -/

theorem placeOk_extends (h : Extends S S')
    (hsub : ∀ o ∈ G.members.toList, o ∈ G'.members.toList) {o : Nat} {part : Part}
    {vars index : Nat} (hp : Blk.placeOk S G o part vars index = true) :
    Blk.placeOk S' G' o part vars index = true := by
  obtain ⟨hm, hh, hv, hi⟩ := (placeOk_iff _ _ _ _ _ _).1 hp
  have ho := lt_of_has hh
  exact (placeOk_iff _ _ _ _ _ _).2
    ⟨hsub o hm, by rw [h.has ho]; exact hh, by rw [h.tableBits ho]; exact hv,
      by rw [h.tableBits ho]; exact hi⟩

/-- A row that has passed the tests passes them in a later statement, at a group that has the
members still. -/
theorem RowIn.extends (h : Extends S S')
    (hsub : ∀ o ∈ G.members.toList, o ∈ G'.members.toList) (hr : RowIn S G row) :
    RowIn S' G' row := by
  refine ⟨fun t ht => placeOk_extends h hsub (hr.terms t ht), fun u hu => ?_, fun w hw => ?_,
    fun f hf => ?_⟩
  · have hp := hr.units u hu
    rw [h.tableBits (lt_of_has ((placeOk_iff _ _ _ _ _ _).1 hp).2.1)]
    exact placeOk_extends h hsub hp
  · obtain ⟨h0, h1, hp⟩ := hr.runs w hw
    rw [h.tableBits (lt_of_has ((placeOk_iff _ _ _ _ _ _).1 hp).2.1)]
    exact ⟨h0, h1, placeOk_extends h hsub hp⟩
  · obtain ⟨hp, hfit⟩ := hr.forms f hf
    rw [h.tableBits (lt_of_has ((placeOk_iff _ _ _ _ _ _).1 hp).2.1)]
    exact ⟨placeOk_extends h hsub hp, hfit⟩

/-- A group that is in order is in order in a later statement, whatever has happened to its rows and
its mark. -/
theorem GroupOk.extends (h : Extends S S') (hOk : GroupOk S G) (hm : G'.members = G.members)
    (hk : G'.kept = G.kept) (hc : G'.code = G.code) (hz : G'.maskCode = G.maskCode) :
    GroupOk S' G' := by
  refine ⟨by rw [hm]; exact hOk.nodup, ?_, by rw [hm, hk]; exact hOk.marks, ?_, ?_⟩
  · intro o ho
    rw [hm] at ho
    exact Nat.lt_of_lt_of_le (hOk.there o ho) h.size
  · intro o ho x' hx'
    rw [hm] at ho
    have hx := Array.getElem?_eq_getElem (hOk.there o ho)
    obtain ⟨x'', hx'', e⟩ := h.shape o _ hx
    rw [hx'] at hx''
    obtain rfl := Option.some.inj hx''
    rw [e, hc]
    exact hOk.mainCode o ho _ hx
  · intro o ho x' hx'
    rw [hm] at ho
    have hx := Array.getElem?_eq_getElem (hOk.there o ho)
    obtain ⟨x'', hx'', e⟩ := h.shape o _ hx
    rw [hx'] at hx''
    obtain rfl := Option.some.inj hx''
    rw [e, hz]
    exact hOk.maskCode o ho _ hx

theorem getD_mem {A : Array Nat} {i : Nat} (hi : i < A.size) : A.getD i noId ∈ A.toList := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
  exact Array.mem_toList_iff.2 (Array.getElem_mem hi)

theorem sizesOf_extends (h : Extends S S') (hOk : GroupOk S G) (hm : G'.members = G.members)
    (hk : G'.kept = G.kept) (part : Part) : sizesOf S' G' part = sizesOf S G part := by
  unfold sizesOf
  rw [hm, hk]
  apply Array.map_congr_left
  intro i hi
  have ho := hOk.there _ (getD_mem (Array.mem_range.1 hi))
  dsimp only
  rw [h.has ho, h.rowBits ho]

/-- The layout of a group stays. -/
theorem layoutOf_extends (h : Extends S S') (hOk : GroupOk S G) (hm : G'.members = G.members)
    (hk : G'.kept = G.kept) (hc : G'.code = G.code) (hz : G'.maskCode = G.maskCode) :
    layoutOf S' G' = layoutOf S G := by
  unfold layoutOf
  rw [sizesOf_extends h hOk hm hk, sizesOf_extends h hOk hm hk, h.codes, hm, hk, hc, hz]

/-! ## The effects -/

theorem map_modify {β : Type} (φ : Oracle → β) (A : Array Oracle) (o o' : Nat)
    (f : Oracle → Oracle) (hf : ∀ x, φ (f x) = φ x) :
    ((A.modify o f)[o']?).map φ = (A[o']?).map φ := by
  rw [Array.getElem?_modify]
  split
  · cases A[o']? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · rfl

theorem extends_withRow (S : Statement) (g : Nat) (r : Row) : Extends S (Slice.withRow S g r) :=
  ⟨rfl, fun _ x h => ⟨x, h, rfl⟩⟩

theorem extends_withGroup (S : Statement) (a b : Nat) : Extends S (Slice.withGroup S a b) :=
  ⟨rfl, fun _ x h => ⟨x, h, rfl⟩⟩

theorem extends_withMessageInGroup (S : Statement) (g o : Nat) (k : Bool) (G : Group) :
    Extends S (Slice.withMessageInGroup S g o k G) :=
  Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ fun _ => rfl

theorem extends_admitted (S : Statement) (o : Nat) (s : OracleShape) (p : List PadPlace)
    (rows : Array Row) : Extends S (Slice.admitted S o s p rows) :=
  Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ fun _ => rfl

theorem extends_closeLedgers (S : Statement) (l : List Nat) :
    Extends S (Slice.closeLedgers S l) :=
  Extends.of_shapes (Slice.closeLedgers_codes l S) (Slice.closeLedgers_shape l S)

theorem extends_begun (S : Statement) (g : Nat) (G : Group) : Extends S (Slice.begun S g G) :=
  Extends.of_shapes (Slice.closeLedgers_codes G.members.toList S)
    (Slice.closeLedgers_shape G.members.toList S)

theorem extends_stSent (S : Statement) (sent : Array OracleNotice) :
    Extends S (Slice.stSent S sent) :=
  ⟨rfl, fun o x hx => by
    have ho : o < S.oracles.size := by
      by_contra c
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
      cases hx
    exact ⟨x, by rw [Slice.stSent_old S sent o ho]; exact hx, rfl⟩⟩

/-! ## The adding of a row -/

/-- The value of a row looks at the oracle messages and the codes alone. -/
theorem value_congr (h1 : S'.oracles = S.oracles) (h2 : S'.codes = S.codes) (r : Row)
    (m : Words K) : value ρ S' r m = value ρ S r m := by
  unfold value onTable tableSize Statement.has Statement.tableBits Statement.rowBits
    Statement.placeBits
  rw [h1, h2]

/-- **The adding of a row**: the group's rows are the rows before and the new row, and all of them
hold of the words just if the rows before held and the new row holds. -/
theorem addRow_means (S : Statement) (g : Nat) (G : Group) (row : Row)
    (hG : S.groups[g]? = some G) (m : Words K) :
    (Slice.withRow S g row).groups[g]? = some { G with rows := G.rows.push row } ∧
      (AllSay ρ (Slice.withRow S g row) (G.rows.push row).toList m ↔
        AllSay ρ S G.rows.toList m ∧ Says ρ S row m) := by
  refine ⟨Slice.withRow_group S g row G hG, ?_⟩
  have e : ∀ r, Says ρ (Slice.withRow S g row) r m ↔ Says ρ S r m := by
    intro r
    unfold Says
    rw [value_congr ρ (S := S) (S' := Slice.withRow S g row) rfl rfl]
  unfold AllSay
  simp only [Array.toList_push, List.mem_append, List.mem_singleton, e]
  constructor
  · intro h
    exact ⟨fun r hr => h r (Or.inl hr), h row (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ r (hr | rfl)
    · exact h1 r hr
    · exact h2

/-! ## The beginning of a test, and the batching behind it -/

theorem closeLedgers_groups : ∀ (l : List Nat) (S : Statement),
    (Slice.closeLedgers S l).groups = S.groups
  | [], _ => rfl
  | _ :: l, _ => closeLedgers_groups l _

/-- The group behind the beginning of its test. -/
theorem begun_group (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    (Slice.begun S g G).groups[g]? = some { G with inRun := true, rows := #[] } := by
  show ((Slice.closeLedgers S G.members.toList).groups.modify g _)[g]? = _
  rw [closeLedgers_groups, Array.getElem?_modify, if_pos rfl, hG]
  rfl

/-- **The batching behind the beginning of a test.** If every row that the test takes in has passed
the tests of the adding, Bat.combine at the statement behind the beginning returns a row, and for
all words that row is short, on the group's tables, of the sum of x^i times what row number i was
short of in the statement before. -/
theorem begin_means (S : Statement) (g : Nat) (G : Group) (x : E) (hG : S.groups[g]? = some G)
    (hOk : GroupOk S G) (hr : ∀ r ∈ (Slice.runRows S G).toList, RowIn S G r) :
    S.layout g = some (layoutOf S G) ∧
    ∃ out, Bat.combine (Slice.begun S g G) g ⟨layoutOf S G, Slice.runRows S G⟩ x = some out ∧
      MaskReady (layoutOf S G) out ∧ Clean ρ (Slice.begun S g G) (layoutOf S G) out ∧
      ∀ m : Words K,
        groupShort ρ (Slice.begun S g G) (layoutOf S G) out
            (tablesOf (Slice.begun S g G) (layoutOf S G) m) =
          hornerSum (ρ.val x) ((Slice.runRows S G).toList.map fun r => short ρ S r m) := by
  refine ⟨layout_eq S g G hG, ?_⟩
  have hE := extends_begun S g G
  have hG' := begun_group S g G hG
  have hOk' : GroupOk (Slice.begun S g G) { G with inRun := true, rows := #[] } :=
    hOk.extends hE rfl rfl rfl rfl
  have hL' : (Slice.begun S g G).layout g = some (layoutOf S G) := by
    rw [layout_eq _ g _ hG',
      layoutOf_extends (G' := { G with inRun := true, rows := #[] }) hE hOk rfl rfl rfl rfl]
  obtain ⟨out, h1, h2, hc, h3⟩ := combine_means ρ (Slice.begun S g G) g _ (layoutOf S G)
    (Slice.runRows S G) x hG' hL' hOk'
    (fun r h => RowIn.extends (G := G) hE (fun _ c => c) (hr r h))
  refine ⟨out, h1, h2, hc, fun m => ?_⟩
  rw [h3 m]
  congr 1
  apply List.map_congr_left
  intro r h
  exact short_extends ρ hE (hr r h) m

end OnBytes.Means
