-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontOpenRows.lean: every open row of a group whose
proximity test has not begun passes the ground's test of a new row once more, at the statement as it
is. Three clauses of that test read values: two read the row alone and so stay. The third says that
a row has no coefficient on a pad, and it stays along every function of the ground for two reasons:
a message joins a group only once it is sampled, and its pad is laid when it is sampled and never
again; a row names only members of its group, so it has no coefficient on a message that joins the
group later.

  OpenRowsPass            the sentence, with "every member is sampled" beside it
  rowL_later              the ground's test of a row at a later statement
  LaterAt, passes_later   what a step keeps of a statement, and that this keeps the sentence
  coefficient_absent, passes_joined   a message joins a group
  PassStays, groundKeeps_openRows, stKeeps_openRows   the relation, and that it meets all that the
                          library asks of a relation on the statement
  openRowsPass_reached    at every state that a fold over the first chain's members reaches

The marks of Johnson/Desc/Ground/Shape/Claims.lean (claimsAtB, rowRestS_grown) say the same of the
rows on shapes and marks; here the sentence is carried by the library's walk over the chain.

Limits.
- That a group is there and not under test is not said here: the sentence speaks of such a group. That
  any row lies open is not said either.
- The members' sample rows are not read.
- It speaks of states that a fold reaches.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.AtFull.Shape.OpenRowsOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Own (placeFits tableThere allZero)
open VerifiableInference.Desc.Ground (GroundKeeps ok rowL has)
open VerifiableInference.Desc.K13.Law (StKeeps)
open OnBytes.Means (SampledMembers)

/-- **Every member of a group is sampled, and every open row of a group whose test has not begun
passes the ground's test of a new row at this statement.** -/
def OpenRowsPass (T : Statement) : Prop :=
  SampledMembers T ∧ ∀ (g : ℕ) (G : Group), T.groups[g]? = some G → G.inRun = false →
    ∀ row ∈ G.rows.toList, ok (rowL T g row) = true

/-- What a later statement keeps of the places of a row: the codes, and the shape of each message. -/
structure KeepsShapes (A B : Statement) : Prop where
  codes : B.codes = A.codes
  shapes : ∀ (o : ℕ) (x : OnBytes.Oracle), A.oracles[o]? = some x →
    ∃ y : OnBytes.Oracle, B.oracles[o]? = some y ∧ y.shape = x.shape

theorem tableBits_later {A B : Statement} (K : KeepsShapes A B) {o : ℕ} {x : OnBytes.Oracle}
    (hx : A.oracles[o]? = some x) (part : Part) : B.tableBits o part = A.tableBits o part := by
  obtain ⟨y, hy, e⟩ := K.shapes o x hx
  simp only [Statement.tableBits, Statement.rowBits, Statement.placeBits, hx, hy, e, K.codes]

theorem placeFits_later {A B : Statement} (K : KeepsShapes A B) {G G' : Group}
    (hm : ∀ o, G.members.contains o = true → G'.members.contains o = true) {o vars index : ℕ}
    {part : Part} (h : placeFits A G o part vars index = true) :
    placeFits B G' o part vars index = true ∧ B.tableBits o part = A.tableBits o part := by
  unfold placeFits at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  cases hx : A.oracles[o]? with
  | none =>
    unfold tableThere at h2
    rw [hx] at h2
    cases h2
  | some x =>
    have e := tableBits_later K hx part
    obtain ⟨y, hy, e2⟩ := K.shapes o x hx
    refine ⟨⟨⟨⟨hm o h1, ?_⟩, by rw [e]; exact h3⟩, by rw [e]; exact h4⟩, e⟩
    unfold tableThere at h2 ⊢
    rw [hx] at h2
    rw [hy]
    simp only [Option.any_some] at h2 ⊢
    rw [e2]
    exact h2

/-- **The ground's test of a row at a later statement.** The group loses no member and keeps its mark.
Each pad of a member is one that the test read, or the row has no coefficient there. -/
theorem rowL_later {A B : Statement} (K : KeepsShapes A B) {g : ℕ} {row : OnBytes.Row} {G G' : Group}
    (hG : A.groups[g]? = some G) (hG' : B.groups[g]? = some G') (hr : G'.inRun = G.inRun)
    (hm : ∀ o, G.members.contains o = true → G'.members.contains o = true)
    (hp : ∀ o ∈ G'.members, ∀ q ∈ ((B.oracles[o]?).map (·.pad)).getD [],
      (o ∈ G.members ∧ q ∈ ((A.oracles[o]?).map (·.pad)).getD []) ∨
        allZero (row.coefficient o q.1 q.2) = true)
    (h : ok (rowL A g row) = true) : ok (rowL B g row) = true := by
  simp only [ok, rowL, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true, hG, hG', has,
    Option.map_some, Option.getD_some, Option.isSome_some] at h ⊢
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8⟩ := h
  simp only [Array.all_eq_true_iff_forall_mem, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h4 h5 h6 h7 h8 ⊢
  refine ⟨trivial, by rw [hr]; exact h2, h3, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨(h4 t ht).1, (placeFits_later K hm (h4 t ht).2).1⟩
  · intro u hu
    obtain ⟨a, e⟩ := placeFits_later K hm (h5 u hu)
    rw [e]
    exact a
  · intro w hw
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h6 w hw
    obtain ⟨a', e⟩ := placeFits_later K hm d
    rw [e]
    exact ⟨⟨⟨a, b⟩, c⟩, a'⟩
  · intro f hf
    obtain ⟨a, b⟩ := h7 f hf
    obtain ⟨a', e⟩ := placeFits_later K hm a
    rw [e]
    exact ⟨a', b⟩
  · intro o ho q hq
    rcases hp o ho q hq with ⟨h9, h10⟩ | h9
    · exact h8 o h9 q h10
    · exact h9

/-- What a step keeps of a statement: the shapes, a sampled message's pad, and of a group that is not
under test behind the step: it has no row, or it was there in front and not under test, with the same
members, and each of its rows lay there or passes the test in front. -/
structure LaterAt (A B : Statement) : Prop extends KeepsShapes A B where
  pads : ∀ (o : ℕ) (x : OnBytes.Oracle), A.oracles[o]? = some x → x.sampled = true →
    ∃ y : OnBytes.Oracle, B.oracles[o]? = some y ∧ y.pad = x.pad
  groups : ∀ (g : ℕ) (G' : Group), B.groups[g]? = some G' → G'.inRun = false →
    G'.rows = #[] ∨ ∃ G : Group, A.groups[g]? = some G ∧ G.inRun = false ∧ G'.members = G.members ∧
      ∀ r ∈ G'.rows.toList, r ∈ G.rows.toList ∨ ok (rowL A g r) = true

/-- A step that keeps this much keeps the sentence. -/
theorem passes_later {A B : Statement} (hM : SampledMembers A → SampledMembers B)
    (H : LaterAt A B) (hA : OpenRowsPass A) : OpenRowsPass B := by
  refine ⟨hM hA.1, fun g G' hG' hr row hrow => ?_⟩
  rcases H.groups g G' hG' hr with e | ⟨G, hG, hf, em, hrows⟩
  · rw [e] at hrow
    cases hrow
  · have hy : ok (rowL A g row) = true := by
      rcases hrows row hrow with h | h
      · exact hA.2 g G hG hf row h
      · exact h
    refine rowL_later H.toKeepsShapes hG hG' (by rw [hr, hf]) (fun o h => by rw [em]; exact h) ?_ hy
    intro o ho q hq
    left
    rw [em] at ho
    refine ⟨ho, ?_⟩
    obtain ⟨x, hx, hs⟩ := hA.1 g G hG o (Array.mem_toList_iff.2 ho)
    obtain ⟨y, hy', e⟩ := H.pads o x hx hs
    rw [hy', Option.map_some, Option.getD_some, e] at hq
    rw [hx, Option.map_some, Option.getD_some]
    exact hq

/-- A statement with the same groups, in which each message keeps its shape and a sampled message
its pad. -/
theorem later_of_sameGroups {A B : Statement} (K : KeepsShapes A B) (hg : B.groups = A.groups)
    (hp : ∀ (o : ℕ) (x : OnBytes.Oracle), A.oracles[o]? = some x → x.sampled = true →
      ∃ y : OnBytes.Oracle, B.oracles[o]? = some y ∧ y.pad = x.pad) : LaterAt A B where
  toKeepsShapes := K
  pads := hp
  groups := by
    intro g G' h hr
    rw [hg] at h
    exact Or.inr ⟨G', h, hr, rfl, fun r hm => Or.inl hm⟩

/-- One message is turned, with its shape, and its pad if it is sampled. -/
theorem later_modify (S : Statement) (o : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hs : ∀ x, (f x).shape = x.shape)
    (hp : ∀ x, S.oracles[o]? = some x → x.sampled = true → (f x).pad = x.pad) :
    LaterAt S { S with oracles := S.oracles.modify o f } := by
  refine later_of_sameGroups ⟨rfl, fun j x hx => ?_⟩ rfl fun j x hx hm => ?_
  · show ∃ y : OnBytes.Oracle, (S.oracles.modify o f)[j]? = some y ∧ y.shape = x.shape
    rw [Array.getElem?_modify]
    by_cases c : o = j
    · subst c
      exact ⟨f x, by rw [if_pos rfl, hx]; rfl, hs x⟩
    · exact ⟨x, by rw [if_neg c]; exact hx, rfl⟩
  · show ∃ y : OnBytes.Oracle, (S.oracles.modify o f)[j]? = some y ∧ y.pad = x.pad
    rw [Array.getElem?_modify]
    by_cases c : o = j
    · subst c
      exact ⟨f x, by rw [if_pos rfl, hx]; rfl, hp x hx hm⟩
    · exact ⟨x, by rw [if_neg c]; exact hx, rfl⟩

/-- New messages come in behind the old. -/
theorem later_sent (S : Statement) (sent : Array OracleNotice) : LaterAt S (stSent S sent) := by
  have key : ∀ (o : ℕ) (x : OnBytes.Oracle), S.oracles[o]? = some x →
      (stSent S sent).oracles[o]? = some x := by
    intro o x hx
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 hx
    show (S.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[o]? = some x
    rw [Array.getElem?_append_left hlt]
    exact hx
  exact later_of_sameGroups ⟨rfl, fun o x hx => ⟨x, key o x hx, rfl⟩⟩ rfl
    fun o x hx _ => ⟨x, key o x hx, rfl⟩

/-- Closing ledgers turns ledgers alone. -/
theorem closeLedgers_keeps : ∀ (l : List ℕ) (S : Statement) (o : ℕ) (x : OnBytes.Oracle),
    S.oracles[o]? = some x → ∃ y : OnBytes.Oracle, (closeLedgers S l).oracles[o]? = some y ∧
      y.shape = x.shape ∧ y.pad = x.pad
  | [], _, _, x, hx => ⟨x, hx, rfl, rfl⟩
  | a :: l, S, o, x, hx => by
    have e : closeLedgers S (a :: l) = closeLedgers { S with oracles := S.oracles.modify a fun x =>
        { x with ledger := x.ledger.map fun l => { l with closed := true } } } l := rfl
    rw [e]
    by_cases c : a = o
    · subst c
      have hx' : ({ S with oracles := S.oracles.modify a fun x =>
          { x with ledger := x.ledger.map fun l => { l with closed := true } } } : Statement).oracles[a]? =
          some { x with ledger := x.ledger.map fun l => { l with closed := true } } := by
        show (S.oracles.modify a _)[a]? = _
        rw [Array.getElem?_modify, if_pos rfl, hx]
        rfl
      obtain ⟨y, hy, e1, e2⟩ := closeLedgers_keeps l _ a _ hx'
      exact ⟨y, hy, e1, e2⟩
    · have hx' : ({ S with oracles := S.oracles.modify a fun x =>
          { x with ledger := x.ledger.map fun l => { l with closed := true } } } : Statement).oracles[o]? =
          some x := by
        show (S.oracles.modify a _)[o]? = _
        rw [Array.getElem?_modify, if_neg c]
        exact hx
      exact closeLedgers_keeps l _ o _ hx'

theorem closeLedgers_codes : ∀ (l : List ℕ) (S : Statement), (closeLedgers S l).codes = S.codes
  | [], _ => rfl
  | _ :: l, _ => closeLedgers_codes l _

/-- The beginning of a test. -/
theorem later_begun (S : Statement) (g : ℕ) (G : Group) : LaterAt S (begun S g G) where
  codes := closeLedgers_codes _ _
  shapes := fun o x hx => by
    obtain ⟨y, hy, e, -⟩ := closeLedgers_keeps G.members.toList S o x hx
    exact ⟨y, hy, e⟩
  pads := fun o x hx _ => by
    obtain ⟨y, hy, -, e⟩ := closeLedgers_keeps G.members.toList S o x hx
    exact ⟨y, hy, e⟩
  groups := by
    intro j G' h hr
    have e : (begun S g G).groups = S.groups.modify g
        (fun G => { G with inRun := true, rows := #[] }) := by
      have e₀ := OnBytes.Means.closeLedgers_groups G.members.toList S
      simp only [begun, e₀]
    rw [e, Array.getElem?_modify] at h
    by_cases c : g = j
    · subst c
      rw [if_pos rfl] at h
      obtain ⟨G₀, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact Or.inl rfl
    · rw [if_neg c] at h
      exact Or.inr ⟨G', h, hr, rfl, fun r hm => Or.inl hm⟩

/-- A new open row that passes the test. -/
theorem later_withRow (S : Statement) (g : ℕ) (row : OnBytes.Row) (h : ok (rowL S g row) = true) :
    LaterAt S (withRow S g row) where
  codes := rfl
  shapes := fun _ x hx => ⟨x, hx, rfl⟩
  pads := fun _ x hx _ => ⟨x, hx, rfl⟩
  groups := by
    intro j G' hG hr
    have hG' : (S.groups.modify g fun G => { G with rows := G.rows.push row })[j]? = some G' := hG
    rw [Array.getElem?_modify] at hG'
    by_cases c : g = j
    · subst c
      rw [if_pos rfl] at hG'
      obtain ⟨G₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hG'
      refine Or.inr ⟨G₀, h₀, hr, rfl, fun r hm => ?_⟩
      have hm' : r ∈ (G₀.rows.push row).toList := hm
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm'
      rcases hm' with hm' | rfl
      · exact Or.inl hm'
      · exact Or.inr h
    · rw [if_neg c] at hG'
      exact Or.inr ⟨G', hG', hr, rfl, fun r hm => Or.inl hm⟩

/-- A new group. -/
theorem later_withGroup (S : Statement) (code maskCode : ℕ) :
    LaterAt S (VerifiableInference.Desc.Ground.withGroup S code maskCode) where
  codes := rfl
  shapes := fun _ x hx => ⟨x, hx, rfl⟩
  pads := fun _ x hx _ => ⟨x, hx, rfl⟩
  groups := by
    intro j G' hG hr
    have hG' : (S.groups.push { code := code, maskCode := maskCode })[j]? = some G' := hG
    rw [Array.getElem?_push] at hG'
    split at hG'
    · obtain rfl := Option.some.inj hG'
      exact Or.inl rfl
    · exact Or.inr ⟨G', hG', hr, rfl, fun r hm => Or.inl hm⟩

/-- A fold that skips every entry leaves its start. -/
theorem foldl_skips {α β : Type} (l : List α) (f : β → α → β) (b : β) (h : ∀ a ∈ l, f b a = b) :
    l.foldl f b = b := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, h a List.mem_cons_self]
    exact ih fun a' ha' => h a' (List.mem_cons_of_mem _ ha')

/-- A row that names a message nowhere has coefficient 0 on it. -/
theorem coefficient_absent {r : OnBytes.Row} {o : ℕ} (part : Part) (i : ℕ)
    (ht : ∀ t ∈ r.terms, t.oracle ≠ o) (hu : ∀ u ∈ r.units, u.oracle ≠ o)
    (hw : ∀ w ∈ r.runs, w.oracle ≠ o) (hf : ∀ f ∈ r.forms, f.oracle ≠ o) :
    r.coefficient o part i = zeroE := by
  unfold Row.coefficient
  simp only []
  rw [← Array.foldl_toList, ← Array.foldl_toList, ← Array.foldl_toList, ← Array.foldl_toList]
  rw [foldl_skips _ _ _ fun t hm => by
      have := hf t (Array.mem_toList_iff.1 hm)
      simp [this]]
  rw [foldl_skips _ _ _ fun t hm => by
      have := hw t (Array.mem_toList_iff.1 hm)
      simp [this]]
  rw [foldl_skips _ _ _ fun t hm => by
      have := hu t (Array.mem_toList_iff.1 hm)
      simp [this]]
  rw [foldl_skips _ _ _ fun t hm => by
      have := ht t (Array.mem_toList_iff.1 hm)
      simp [this]]

/-- **A message joins a group.** It is named by no open row of the group, so the row has coefficient 0
on its pad. -/
theorem passes_joined {S : Statement} {g o : ℕ} {kept : Bool} {G : Group} {x : OnBytes.Oracle}
    (hG : S.groups[g]? = some G) (hx : S.oracles[o]? = some x) (hs : x.sampled = true)
    (hn : G.members.contains o = false) (hA : OpenRowsPass S) :
    OpenRowsPass (withMessageInGroup S g o kept G) := by
  have L := later_modify S o (fun x => { x with groups := x.groups ++ [g] }) (fun _ => rfl)
    fun _ _ _ => rfl
  have K : KeepsShapes S (withMessageInGroup S g o kept G) := ⟨rfl, L.shapes⟩
  have hpads : ∀ (j : ℕ) (y : OnBytes.Oracle), S.oracles[j]? = some y →
      (((withMessageInGroup S g o kept G).oracles[j]?).map (·.pad)) = some y.pad := by
    intro j y hy
    show ((S.oracles.modify o _)[j]?).map _ = _
    rw [Array.getElem?_modify]
    by_cases c : o = j
    · subst c
      rw [if_pos rfl, hy]
      rfl
    · rw [if_neg c, hy]
      rfl
  refine ⟨hA.1.withMessageInGroup g o kept G x hG hx hs, fun g' G' hG' hr row hrow => ?_⟩
  have hG'' : (S.groups.modify g fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept })[g']? = some G' :=
    hG'
  rw [Array.getElem?_modify] at hG''
  by_cases c : g = g'
  · subst c
    rw [if_pos rfl, hG] at hG''
    obtain rfl := Option.some.inj hG''
    have hmem : ∀ a, a ∈ G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o ↔
        a = o ∨ a ∈ G.members := by
      intro a
      have hpos : (G.members.filter (· < o)).size ≤ G.members.toList.length := by
        rw [Array.length_toList]
        exact Array.size_filter_le
      rw [← Array.mem_toList_iff, OnBytes.Means.toList_insertIdxIfInBounds,
        List.mem_insertIdx hpos, Array.mem_toList_iff]
    have hy := hA.2 g G hG hr row hrow
    obtain ⟨G₀, hG₀, C⟩ := VerifiableInference.Desc.K9L.rowL_clauses S g row hy
    obtain rfl : G = G₀ := Option.some.inj (hG.symm.trans hG₀)
    have hno : o ∉ G.members := by
      intro hm
      rw [Array.contains_eq_true_of_mem hm] at hn
      cases hn
    have placeMem : ∀ {j vars index : ℕ} {part : Part},
        Blk.placeOk S G j part vars index = true → j ≠ o := by
      intro j vars index part hp e
      subst e
      unfold Blk.placeOk at hp
      simp only [Bool.and_eq_true] at hp
      exact hno (Array.mem_of_contains_eq_true hp.1.1.1)
    refine rowL_later K hG hG' rfl (fun a ha => ?_) (fun a ha q hq => ?_) hy
    · exact Array.contains_eq_true_of_mem ((hmem a).2
        (Or.inr (Array.mem_of_contains_eq_true ha)))
    · rcases (hmem a).1 ha with rfl | ham
      · right
        rw [coefficient_absent _ _ (fun t ht => placeMem (C.terms t ht).2)
          (fun u hu => placeMem (C.units u hu)) (fun w hw => placeMem (C.runs w hw).2.2.2)
          (fun f hf => placeMem (C.forms f hf).1)]
        rfl
      · left
        refine ⟨ham, ?_⟩
        obtain ⟨y, hy', -⟩ := hA.1 g G hG a (Array.mem_toList_iff.2 ham)
        rw [hpads a y hy', Option.getD_some] at hq
        rw [hy', Option.map_some, Option.getD_some]
        exact hq
  · rw [if_neg c] at hG''
    refine rowL_later K hG'' hG' rfl (fun a h => h) (fun a ha q hq => Or.inl ⟨ha, ?_⟩)
      (hA.2 g' G' hG'' hr row hrow)
    obtain ⟨y, hy', -⟩ := hA.1 g' G' hG'' a (Array.mem_toList_iff.2 ha)
    rw [hpads a y hy', Option.getD_some] at hq
    rw [hy', Option.map_some, Option.getD_some]
    exact hq

/-- Closing ledgers keeps this much. -/
theorem later_closeLedgers (S : Statement) (l : List ℕ) : LaterAt S (closeLedgers S l) := by
  refine later_of_sameGroups ⟨closeLedgers_codes l S, fun o x hx => ?_⟩
    (OnBytes.Means.closeLedgers_groups l S) fun o x hx _ => ?_
  · obtain ⟨y, hy, e, -⟩ := closeLedgers_keeps l S o x hx
    exact ⟨y, hy, e⟩
  · obtain ⟨y, hy, -, e⟩ := closeLedgers_keeps l S o x hx
    exact ⟨y, hy, e⟩

/-- If it holds in front, it holds behind. -/
def PassStays (A B : Statement) : Prop := OpenRowsPass A → OpenRowsPass B

/-- **The ground's functions keep the sentence.** -/
theorem groundKeeps_openRows : GroundKeeps PassStays where
  refl := fun _ h => h
  trans := fun h k x => k (h x)
  newGroup := by
    intro L d d' code maskCode n h hA
    have hM := OnBytes.Means.newGroupP_members h hA.1
    unfold VerifiableInference.Desc.Ground.newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact passes_later (fun _ => hM) (later_withGroup _ _ _) hA
    · cases h
  recv := by
    intro L ft d d' sent ids h hA
    have hM := OnBytes.Means.recvP_members h hA.1
    unfold VerifiableInference.Desc.Ground.recvP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact passes_later (fun _ => hM) (later_sent _ _) hA
    · cases h
  admit := by
    intro L d d' o rows h hA
    have hM := OnBytes.Means.admitP_members h hA.1
    unfold VerifiableInference.Desc.Ground.admitP at h
    by_cases c : ok (VerifiableInference.Desc.Ground.admitL d.st o rows) = true
    · rw [if_pos c] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, hx, places, _, rfl⟩ := h
      simp only [ok, VerifiableInference.Desc.Ground.admitL, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true] at c
      obtain ⟨_, _, c3, _⟩ := c
      rw [hx, OnBytes.Means.has_some] at c3
      refine passes_later (fun _ => hM) (later_modify d.st o (fun y => { y with
        sampled := true, sampleRows := rows, pad := places.map fun p => (p.part, p.index),
        ledger := freshLedger d.st.codes x.shape }) (fun _ => rfl) fun y hy hs => ?_) hA
      rw [hx] at hy
      obtain rfl := Option.some.inj hy
      rw [hs] at c3
      cases c3
    · rw [if_neg c] at h
      cases h
  join := by
    intro L d d' g o kept h hA
    unfold VerifiableInference.Desc.Ground.joinP at h
    by_cases c : ok (VerifiableInference.Desc.Ground.joinL d.st g o kept) = true
    · rw [if_pos c] at h
      obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [ok, VerifiableInference.Desc.Ground.joinL, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true] at c
      obtain ⟨_, c2, c3, _, _, _, c7, _⟩ := c
      cases hx : d.st.oracles[o]? with
      | none =>
        rw [hx] at c2
        cases c2
      | some x =>
        rw [hx, OnBytes.Means.has_some] at c3
        rw [hG, OnBytes.Means.has_some] at c7
        exact passes_joined hG hx c3 (by simpa using c7) hA
    · rw [if_neg c] at h
      cases h
  addRow := by
    intro L d d' g row h hA
    have hM := OnBytes.Means.addRowP_members h hA.1
    unfold VerifiableInference.Desc.Ground.addRowP at h
    split at h
    · rename_i hok
      obtain rfl := Option.some.inj h
      exact passes_later (fun _ => hM) (later_withRow _ _ _ hok) hA
    · cases h
  takeMask := by
    intro L d d' o n h hA
    have hM := OnBytes.Means.takeMaskP_members h hA.1
    unfold VerifiableInference.Desc.Ground.takeMaskP at h
    split at h
    · obtain ⟨l, -, e⟩ := Option.map_eq_some_iff.1 h
      obtain rfl : _ = d' := congrArg Prod.snd e
      exact passes_later (fun _ => hM) (later_modify _ _ _ (fun _ => rfl) fun _ _ _ => rfl) hA
    · cases h
  closeLedger := by
    intro L d d' o h hA
    have hM := OnBytes.Means.closeLedgerP_members h hA.1
    unfold VerifiableInference.Desc.Ground.closeLedgerP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact passes_later (fun _ => hM) (later_closeLedgers _ _) hA
    · cases h
  spendAsMask := by
    intro L d d' o h hA
    have hM := OnBytes.Means.spendAsMaskP_members h hA.1
    unfold VerifiableInference.Desc.Ground.spendAsMaskP at h
    split at h
    · obtain rfl := Option.some.inj h
      exact passes_later (fun _ => hM) (later_modify _ _ _ (fun _ => rfl) fun _ _ _ => rfl) hA
    · cases h
  adopt := by
    intro L d d' sent given ids h hA
    have hM := OnBytes.Means.adoptP_members h hA.1
    unfold VerifiableInference.Desc.Ground.adoptP at h
    split at h
    · obtain ⟨lay, -, h⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨-, rfl⟩ := Prod.mk.inj h
      exact passes_later (fun _ => hM) (later_sent _ _) hA
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h hA
    have hM := OnBytes.Means.elsewhereP_members h hA.1
    unfold VerifiableInference.Desc.Ground.elsewhereP at h
    by_cases c : ok (VerifiableInference.Desc.Ground.elsewhereL d.st mine other theirs) = true
    · rw [if_pos c] at h
      obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
      simp only [ok, VerifiableInference.Desc.Ground.elsewhereL, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true] at c
      obtain ⟨_, _, _, c4, _⟩ := c
      refine passes_later (fun _ => hM) (later_modify d.st mine (fun x => { x with
        sampled := true, sampleRows := y.sampleRows.map (·.renamed mine), pad := y.pad })
        (fun _ => rfl) fun x hx hs => ?_) hA
      rw [hx, OnBytes.Means.has_some, hs] at c4
      cases c4
    · rw [if_neg c] at h
      cases h

/-- **The sentence meets all that the library asks of a relation on the statement.** -/
theorem stKeeps_openRows : StKeeps PassStays where
  ground := groundKeeps_openRows
  begun := fun T g G hA => passes_later (fun h => h.begun g G) (later_begun T g G) hA
  row := by
    intro lay im o n lin T r os' h hA
    obtain ⟨-, -, -, -, _, _, -, -, -, -, -, _, -, _, -, l, hl, c, l', ht, rfl, rfl⟩ :=
      (VerifiableInference.Desc.First.Pend.pendingRowO_iff lay im o n lin T.oracles _ _).1 h
    exact passes_later
      (fun h => h.onOracle im (fun x => { x with ledger := some l' }) rfl rfl fun _ hs => hs)
      (later_modify _ _ _ (fun _ => rfl) fun _ _ _ => rfl) hA

section Head
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open VerifiableInference.Desc (Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The chain's own start has no group. -/
theorem start_openRowsPass (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (p : ProofFile.InstPub) :
    OpenRowsPass (ProofFile.startS Zp p).st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : (ProofFile.startS Zp p).st.groups = #[] := by
    unfold ProofFile.startS
    dsimp only
    split
    · show Zp.s₀.st.groups = #[]
      rw [Meaning.K2.s0_first O.pub]
      rfl
    · rfl
  refine ⟨fun g G hG => ?_, fun g G hG => ?_⟩ <;> · rw [e] at hG; simp at hG

/-- **At every state that a fold over the first k members reaches from the chain's own start.** -/
theorem openRowsPass_reached (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (k ft : ℕ)
    (p : ProofFile.InstPub) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (y : S × List Fmt.RoundView × List OpenedColumn)
    (hf : foldBlocks ft (cF.blocksInOrder.take k) (ProofFile.startS Zp p) rs cols = .ok y) :
    OpenRowsPass y.1.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact Meaning.K2.open_fold_all (Meaning.K2.seatKeeps_by stKeeps_openRows)
    (Meaning.K2.seatBack_by stKeeps_openRows) O trivial (fun _ _ _ => trivial)
    (Johnson.AtFull.Shape.plans_at h) k hf (start_openRowsPass h p)

end Head

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.rowL_later
#print axioms ProofFile.Honest.K12.AtFile.passes_joined
#print axioms ProofFile.Honest.K12.AtFile.groundKeeps_openRows
#print axioms ProofFile.Honest.K12.AtFile.stKeeps_openRows
#print axioms ProofFile.Honest.K12.AtFile.openRowsPass_reached
