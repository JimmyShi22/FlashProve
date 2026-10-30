-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Order.lean: the conditions of the laws on what a row means hold all along a
chain.

InOrder says of a statement: every group is in order (GroupOk), every open row of a group has passed
the tests of the adding at that group (RowIn), and every sample row of an oracle message names that
message alone, on tables that it has (RowOn). This file shows that the statement without groups and
oracle messages is in order, and that each pure effect of the library keeps a statement in order,
under what the call of that effect tests. With that, every row that a proximity test takes in meets
RowIn (InOrder.runRows), and the law of the batching holds at every statement in order
(begin_inOrder).

Main definitions: RowOn, InOrder.
Main theorems: RowIn.mono, RowOn.isIn, GroupOk.insert; InOrder.start, InOrder.withGroup,
InOrder.stSent, InOrder.admitted, InOrder.withMessageInGroup, InOrder.withRow, InOrder.begun,
InOrder.sameGroups; InOrder.runRows, begin_inOrder.

Plain records and pure functions of the program are named here, none that takes a context or runs:
Slice.withRow, withGroup, withMessageInGroup, admitted, closeLedgers, begun, runRows, stSent.

What is not claimed. That the sample rows which a chain admits meet RowOn: InOrder.admitted takes it
as a condition. That a block changes the statement by these effects alone. Nothing on soundness.

-/
import Johnson.Desc.Means.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {S S' : Statement} {G G' : Group} {row : Row}

/-! ## Rows on one oracle message -/

theorem placeOk_mono (hsub : ∀ o ∈ G.members.toList, o ∈ G'.members.toList) {o : Nat} {part : Part}
    {vars index : Nat} (hp : Blk.placeOk S G o part vars index = true) :
    Blk.placeOk S G' o part vars index = true := by
  obtain ⟨hm, h⟩ := (placeOk_iff _ _ _ _ _ _).1 hp
  exact (placeOk_iff _ _ _ _ _ _).2 ⟨hsub o hm, h⟩

/-- A row that has passed the tests at a group passes them at a group with more members. -/
theorem RowIn.mono (hsub : ∀ o ∈ G.members.toList, o ∈ G'.members.toList) (hr : RowIn S G row) :
    RowIn S G' row :=
  ⟨fun t ht => placeOk_mono hsub (hr.terms t ht), fun u hu => placeOk_mono hsub (hr.units u hu),
    fun w hw => ⟨(hr.runs w hw).1, (hr.runs w hw).2.1, placeOk_mono hsub (hr.runs w hw).2.2⟩,
    fun f hf => ⟨placeOk_mono hsub (hr.forms f hf).1, (hr.forms f hf).2⟩⟩

/-- Each summand of the row is on a table that the oracle message o has, and within it. -/
def RowOn (S : Statement) (o : Nat) (row : Row) : Prop :=
  RowIn S { code := 0, members := #[o] } row

/-- Such a row passes the tests at every group that has o as a member. -/
theorem RowOn.isIn {o : Nat} (h : RowOn S o row) (hm : o ∈ G.members.toList) : RowIn S G row :=
  RowIn.mono (fun o' ho' => by
    have e : o' = o := by simpa using ho'
    rw [e]
    exact hm) h

theorem RowOn.extends {o : Nat} (hE : Extends S S') (h : RowOn S o row) : RowOn S' o row :=
  RowIn.extends hE (fun _ c => c) h

/-! ## A group with one more member -/

theorem toList_insertIdxIfInBounds {α : Type} (A : Array α) (i : Nat) (a : α) :
    (A.insertIdxIfInBounds i a).toList = A.toList.insertIdx i a := by
  rcases A with ⟨l⟩
  simp

theorem size_insertIdxIfInBounds {α : Type} (A : Array α) (i : Nat) (a : α) (h : i ≤ A.size) :
    (A.insertIdxIfInBounds i a).size = A.size + 1 := by
  rw [← Array.length_toList, toList_insertIdxIfInBounds,
    List.length_insertIdx_of_le_length (by rw [Array.length_toList]; exact h), Array.length_toList]

/-- A group in order stays in order when an oracle message that is there, is no member yet and has
its rows under the group's codes is entered at a place among the members. -/
theorem GroupOk.insert (hOk : GroupOk S G) {o : Nat} {x : Oracle} (k : Bool) (pos : Nat)
    (hpos : pos ≤ G.members.size) (hx : S.oracles[o]? = some x) (hnew : o ∉ G.members.toList)
    (hc : x.shape.mainRows = 0 ∨ x.shape.code = G.code)
    (hz : x.shape.maskRows = 0 ∨ x.shape.maskCode = G.maskCode) :
    GroupOk S { G with
      members := G.members.insertIdxIfInBounds pos o
      kept := G.kept.insertIdxIfInBounds pos k } := by
  have hpos' : pos ≤ G.members.toList.length := by
    rw [Array.length_toList]
    exact hpos
  have hmem : ∀ o', o' ∈ (G.members.insertIdxIfInBounds pos o).toList ↔
      o' = o ∨ o' ∈ G.members.toList := by
    intro o'
    rw [toList_insertIdxIfInBounds]
    exact List.mem_insertIdx hpos'
  have ho : o < S.oracles.size := by
    by_contra c
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
    cases hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (G.members.insertIdxIfInBounds pos o).toList.Nodup
    rw [toList_insertIdxIfInBounds]
    exact (List.perm_insertIdx o _ hpos').nodup_iff.2 (List.nodup_cons.2 ⟨hnew, hOk.nodup⟩)
  · intro o' ho'
    rcases (hmem o').1 ho' with c | c
    · rw [c]
      exact ho
    · exact hOk.there o' c
  · show (G.kept.insertIdxIfInBounds pos k).size = (G.members.insertIdxIfInBounds pos o).size
    rw [size_insertIdxIfInBounds _ _ _ hpos,
      size_insertIdxIfInBounds _ _ _ (by rw [hOk.marks]; exact hpos), hOk.marks]
  · intro o' ho' x' hx'
    rcases (hmem o').1 ho' with c | c
    · rw [c, hx] at hx'
      obtain rfl := Option.some.inj hx'
      exact hc
    · exact hOk.mainCode o' c x' hx'
  · intro o' ho' x' hx'
    rcases (hmem o').1 ho' with c | c
    · rw [c, hx] at hx'
      obtain rfl := Option.some.inj hx'
      exact hz
    · exact hOk.maskCode o' c x' hx'

/-! ## A statement in order -/

/-- Every group is in order, every open row has passed the tests of the adding at its group, and
every sample row is on its own oracle message. -/
structure InOrder (S : Statement) : Prop where
  groups : ∀ (g : Nat) (G : Group), S.groups[g]? = some G → GroupOk S G
  rows : ∀ (g : Nat) (G : Group), S.groups[g]? = some G → ∀ r ∈ G.rows.toList, RowIn S G r
  samples : ∀ (o : Nat) (x : Oracle), S.oracles[o]? = some x →
    ∀ r ∈ x.sampleRows.toList, RowOn S o r

/-- The statement in front of a chain: no oracle message, no group. -/
theorem InOrder.start (codes : Codes) : InOrder { codes := codes, oracles := #[], groups := #[] } :=
  ⟨fun g G h => by simp at h, fun g G h => by simp at h, fun o x h => by simp at h⟩

/-- An effect that leaves the groups as they are, and after which every sample row is on its oracle
message. -/
theorem InOrder.sameGroups (h : InOrder S) (hE : Extends S S') (hg : S'.groups = S.groups)
    (hs : ∀ (o : Nat) (x' : Oracle), S'.oracles[o]? = some x' →
      ∀ r ∈ x'.sampleRows.toList, RowOn S' o r) : InOrder S' :=
  ⟨fun g G hG => (h.groups g G (hg ▸ hG)).extends hE rfl rfl rfl rfl,
    fun g G hG r hr => (h.rows g G (hg ▸ hG) r hr).extends hE fun _ c => c, hs⟩

/-- The sample rows stay on their oracle messages if the effect leaves them as they are. -/
theorem InOrder.samples_of (h : InOrder S) (hE : Extends S S')
    (hs : ∀ o : Nat, (S'.oracles[o]?).map (fun x : Oracle => x.sampleRows) =
      (S.oracles[o]?).map (fun x : Oracle => x.sampleRows)) (o : Nat) (x' : Oracle)
    (hx' : S'.oracles[o]? = some x') : ∀ r ∈ x'.sampleRows.toList, RowOn S' o r := by
  have e := hs o
  rw [hx'] at e
  cases hx : S.oracles[o]? with
  | none =>
    rw [hx] at e
    cases e
  | some x =>
    rw [hx] at e
    have e' : x'.sampleRows = x.sampleRows := Option.some.inj e
    intro r hr
    rw [e'] at hr
    exact (h.samples o x hx r hr).extends hE

/-- An effect that changes one group, and leaves the sample rows as they are. -/
theorem InOrder.oneGroup (h : InOrder S) (hE : Extends S S') (g : Nat) (f : Group → Group)
    (hg : S'.groups = S.groups.modify g f)
    (hs : ∀ o : Nat, (S'.oracles[o]?).map (fun x : Oracle => x.sampleRows) =
      (S.oracles[o]?).map (fun x : Oracle => x.sampleRows))
    (hf : ∀ G, S.groups[g]? = some G →
      GroupOk S' (f G) ∧ ∀ r ∈ (f G).rows.toList, RowIn S' (f G) r) : InOrder S' := by
  have key : ∀ (g' : Nat) (G' : Group), S'.groups[g']? = some G' →
      (∃ G, S.groups[g]? = some G ∧ f G = G') ∨ S.groups[g']? = some G' := by
    intro g' G' hG'
    rw [hg, Array.getElem?_modify] at hG'
    by_cases c : g = g'
    · rw [if_pos c] at hG'
      obtain ⟨G, h1, h2⟩ := Option.map_eq_some_iff.1 hG'
      exact Or.inl ⟨G, by rw [c]; exact h1, h2⟩
    · rw [if_neg c] at hG'
      exact Or.inr hG'
  refine ⟨fun g' G' hG' => ?_, fun g' G' hG' r hr => ?_, h.samples_of hE hs⟩
  · rcases key g' G' hG' with ⟨G, h1, rfl⟩ | c
    · exact (hf G h1).1
    · exact (h.groups g' G' c).extends hE rfl rfl rfl rfl
  · rcases key g' G' hG' with ⟨G, h1, rfl⟩ | c
    · exact (hf G h1).2 r hr
    · exact (h.rows g' G' c r hr).extends hE fun _ c => c

/-- One more group. -/
theorem InOrder.withGroup (h : InOrder S) (a b : Nat) : InOrder (Slice.withGroup S a b) := by
  have hE := extends_withGroup S a b
  have key : ∀ (g : Nat) (G : Group), (Slice.withGroup S a b).groups[g]? = some G →
      S.groups[g]? = some G ∨ G = { code := a, maskCode := b } := by
    intro g G hG
    have hG' : (S.groups.push { code := a, maskCode := b })[g]? = some G := hG
    rw [Array.getElem?_push] at hG'
    by_cases c : g = S.groups.size
    · rw [if_pos c] at hG'
      exact Or.inr (Option.some.inj hG').symm
    · rw [if_neg c] at hG'
      exact Or.inl hG'
  refine ⟨fun g G hG => ?_, fun g G hG r hr => ?_,
    fun o x hx r hr => (h.samples o x hx r hr).extends hE⟩
  · rcases key g G hG with c | rfl
    · exact (h.groups g G c).extends hE rfl rfl rfl rfl
    · constructor <;> simp
  · rcases key g G hG with c | rfl
    · exact (h.rows g G c r hr).extends hE fun _ c => c
    · simp at hr

/-- Oracle messages are sent. -/
theorem InOrder.stSent (h : InOrder S) (sent : Array OracleNotice) :
    InOrder (Slice.stSent S sent) := by
  have hE := extends_stSent S sent
  refine h.sameGroups hE rfl fun o x' hx' r hr => ?_
  by_cases ho : o < S.oracles.size
  · rw [Slice.stSent_old S sent o ho] at hx'
    exact (h.samples o x' hx' r hr).extends hE
  · obtain ⟨i, rfl⟩ : ∃ i, o = S.oracles.size + i := ⟨o - S.oracles.size, by omega⟩
    rw [Slice.stSent_new] at hx'
    obtain ⟨n, _, rfl⟩ := Option.map_eq_some_iff.1 hx'
    simp at hr

/-- An oracle message is admitted, with sample rows that are on it. -/
theorem InOrder.admitted (h : InOrder S) (o : Nat) (s : OracleShape) (p : List PadPlace)
    (rows : Array Row) (hr : ∀ r ∈ rows.toList, RowOn S o r) :
    InOrder (Slice.admitted S o s p rows) := by
  have hE := extends_admitted S o s p rows
  refine h.sameGroups hE rfl fun o' x' hx' r hr' => ?_
  by_cases c : o = o'
  · subst c
    cases hx : S.oracles[o]? with
    | none =>
      have e : (Slice.admitted S o s p rows).oracles[o]? = none := by
        simp [Slice.admitted, Array.getElem?_modify, hx]
      rw [e] at hx'
      cases hx'
    | some x =>
      rw [Slice.admitted_same S o s p rows x hx] at hx'
      obtain rfl := Option.some.inj hx'
      exact (hr r hr').extends hE
  · rw [Slice.admitted_other S o s p rows o' c] at hx'
    exact (h.samples o' x' hx' r hr').extends hE

/-- An oracle message joins a group, under what the call tests. -/
theorem InOrder.withMessageInGroup (h : InOrder S) (g o : Nat) (k : Bool) (G : Group) (x : Oracle)
    (hG : S.groups[g]? = some G) (hx : S.oracles[o]? = some x) (hnew : o ∉ G.members.toList)
    (hc : x.shape.mainRows = 0 ∨ x.shape.code = G.code)
    (hz : x.shape.maskRows = 0 ∨ x.shape.maskCode = G.maskCode) :
    InOrder (Slice.withMessageInGroup S g o k G) := by
  have hE := extends_withMessageInGroup S g o k G
  refine h.oneGroup hE g (fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size k }) rfl
    (fun o' => map_modify _ _ _ _ _ fun _ => rfl) fun G' hG' => ?_
  rw [hG] at hG'
  obtain rfl := Option.some.inj hG'
  have hpos : (G.members.filter (· < o)).size ≤ G.members.size := Array.size_filter_le
  refine ⟨((h.groups g G hG).insert k _ hpos hx hnew hc hz).extends hE rfl rfl rfl rfl, ?_⟩
  intro r hr
  refine RowIn.extends (G := G) hE (fun o' ho' => ?_) (h.rows g G hG r hr)
  show o' ∈ (G.members.insertIdxIfInBounds _ o).toList
  rw [toList_insertIdxIfInBounds]
  exact (List.mem_insertIdx (by rw [Array.length_toList]; exact hpos)).2 (Or.inr ho')

/-- A row that has passed the tests is added. -/
theorem InOrder.withRow (h : InOrder S) (g : Nat) (G : Group) (row : Row)
    (hG : S.groups[g]? = some G) (hr : RowIn S G row) : InOrder (Slice.withRow S g row) := by
  have hE := extends_withRow S g row
  refine h.oneGroup hE g (fun G => { G with rows := G.rows.push row }) rfl (fun _ => rfl)
    fun G' hG' => ?_
  rw [hG] at hG'
  obtain rfl := Option.some.inj hG'
  refine ⟨(h.groups g G hG).extends hE rfl rfl rfl rfl, ?_⟩
  intro r hr'
  have hr'' : r ∈ (G.rows.push row).toList := hr'
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr''
  rcases hr'' with c | rfl
  · exact RowIn.extends (G := G) hE (fun _ c => c) (h.rows g G hG r c)
  · exact RowIn.extends (G := G) hE (fun _ c => c) hr

theorem closeLedgers_sampleRows : ∀ (l : List Nat) (S : Statement) (o : Nat),
    ((Slice.closeLedgers S l).oracles[o]?).map (fun x : Oracle => x.sampleRows) =
      (S.oracles[o]?).map (fun x : Oracle => x.sampleRows)
  | [], _, _ => rfl
  | a :: l, S, o => by
    show ((Slice.closeLedgers _ l).oracles[o]?).map _ = _
    rw [closeLedgers_sampleRows l]
    exact map_modify _ _ _ _ _ fun _ => rfl

/-- A proximity test begins. -/
theorem InOrder.begun (h : InOrder S) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    InOrder (Slice.begun S g G) := by
  have hE := extends_begun S g G
  have hg : (Slice.begun S g G).groups =
      S.groups.modify g fun G => { G with inRun := true, rows := #[] } := by
    have e : (Slice.begun S g G).groups = (Slice.closeLedgers S G.members.toList).groups.modify g
        fun G => { G with inRun := true, rows := #[] } := rfl
    rw [e, closeLedgers_groups]
  refine h.oneGroup hE g _ hg (closeLedgers_sampleRows G.members.toList S) fun G' hG' => ?_
  exact ⟨(h.groups g G' hG').extends hE rfl rfl rfl rfl, fun r hr => by simp at hr⟩

/-! ## The rows that a proximity test takes in -/

theorem mem_samples (S : Statement) (r : Row) : ∀ (l : List Nat) (a : Array Row),
    r ∈ (l.foldl (fun a o => a ++ ((S.oracles[o]?).map (·.sampleRows)).getD #[]) a).toList →
    r ∈ a.toList ∨ ∃ o ∈ l, ∃ x : Oracle, S.oracles[o]? = some x ∧ r ∈ x.sampleRows.toList
  | [], _, h => Or.inl h
  | o :: l, a, h => by
    rw [List.foldl_cons] at h
    rcases mem_samples S r l _ h with c | ⟨o', h1, h2⟩
    · simp only [Array.toList_append, List.mem_append] at c
      rcases c with c | c
      · exact Or.inl c
      · cases hx : S.oracles[o]? with
        | none => simp [hx] at c
        | some x =>
          rw [hx] at c
          exact Or.inr ⟨o, by simp, x, hx, c⟩
    · exact Or.inr ⟨o', by simp [h1], h2⟩

/-- **Every row that a proximity test takes in has passed the tests**, at a statement in order. -/
theorem InOrder.runRows (h : InOrder S) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    ∀ r ∈ (Slice.runRows S G).toList, RowIn S G r := by
  intro r hr
  unfold Slice.runRows at hr
  simp only [Array.toList_append, List.mem_append, Array.toList_filter, List.mem_filter] at hr
  rcases hr with (c | c) | c
  · exact h.rows g G hG r c.1
  · rw [← Array.foldl_toList] at c
    rcases mem_samples S r _ _ c with c' | ⟨o, ho, x, hx, hr'⟩
    · simp at c'
    · exact (h.samples o x hx r hr').isIn ho
  · exact h.rows g G hG r c.1

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **The law of the batching, at every statement in order.** -/
theorem begin_inOrder (h : InOrder S) (g : Nat) (G : Group) (x : E) (hG : S.groups[g]? = some G) :
    S.layout g = some (layoutOf S G) ∧
    ∃ out, Bat.combine (Slice.begun S g G) g ⟨layoutOf S G, Slice.runRows S G⟩ x = some out ∧
      MaskReady (layoutOf S G) out ∧ Clean ρ (Slice.begun S g G) (layoutOf S G) out ∧
      ∀ m : Words K,
        groupShort ρ (Slice.begun S g G) (layoutOf S G) out
            (tablesOf (Slice.begun S g G) (layoutOf S G) m) =
          hornerSum (ρ.val x) ((Slice.runRows S G).toList.map fun r => short ρ S r m) :=
  begin_means ρ S g G x hG (h.groups g G hG) (h.runRows g G hG)

end OnBytes.Means
