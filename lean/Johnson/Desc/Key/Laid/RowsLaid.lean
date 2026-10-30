-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/RowsLaid.lean: WHAT A YES OF K13's "rows" (Johnson/Desc/K13/Text.lean: behind
W's commitment: the request's own group, the joinings, the row (Eval)) SAYS OF THE RECORD BEHIND, as
one structure of plain facts; and that K13's "joinAll" keeps a statement in order. Definitions,
statements and proofs, over the library's texts.
  ok_bind, there_ok       tools: a yes of a bind; a value that must be there.
  joinAll_keeps           joinAll, a fold of the ground's joinP, keeps Means.InOrder
                          (Johnson/Desc/Means/Order.lean), by joinP_keeps (Page.lean). (A kin lies
                          in Johnson/Desc/K13/Keeps.lean: joinAll_keeps for a RELATION on the
                          two statements that all the ground's routines keep: another thing.)
  ins                     a member is entered at its place by number (the library's withMessageInGroup).
  JoinedTo g d d' l       the messages of the list l have joined group g, one behind the other: the
                          group's members; its rows and its mark as they were; every other group,
                          the codes, the book as they were; every message the same record but for
                          its list of groups.
  JoinedTo.refl, JoinedTo.trans, joinP_to, joinAll_to.
  RowsLaid S claim ids d d' lin : the facts. rows_laid : a yes of rows gives them, WHERE THE SHAPE
                          ASKS NO SPLIT's MESSAGE (S.ownSplitNeeded = false).
  laid_kind, evalRow_plain  the row (Eval) is a plain row.
  ins_two                 two members in rising order: the list of members is just these two.
  rowsLaid_irrefl         RowsLaid holds of no record and itself: a function that says yes to all
                          and hands the record on does not give it.
Limits. Of the ground's tests nothing is carried but what the fields say. With a split's message:
not typed. That the row (Eval) means anything: not here. Nothing on soundness or on hiding.
-/
import Johnson.Desc.K13.Text
import Johnson.Desc.K13.OwnLaws
import Johnson.Desc.Means.Page
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key.LaidW
open OnBytes OnBytes.Params OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc.Ground (newGroupP joinP addRowP addRowsP addRowsFrom)
open VerifiableInference.Desc.K13 (St there joinAll rows)

/-! ## Tools -/

theorem ok_bind {ε α β : Type} (x : Except ε α) (f : α → Except ε β) (b : β) :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

theorem there_ok {α : Type} (n : String) (o : Option α) (a : α) :
    there n o = .ok a ↔ o = some a := by
  cases o <;> simp [there]

/-! ## joinAll keeps a statement in order -/

/-- **K13's joinAll keeps a statement in order.** -/
theorem joinAll_keeps (g : Nat) : ∀ (l : List Nat) (d d' : St), joinAll g l d = .ok d' →
    Means.InOrder d.st → Means.InOrder d'.st
  | [], d, d', h, hI => by
    obtain rfl : d = d' := Except.ok.inj h
    exact hI
  | o :: l, d, d', h, hI => by
    unfold joinAll at h
    obtain ⟨e, h1, h2⟩ := (ok_bind _ _ _).1 h
    exact joinAll_keeps g l e d' h2 (Means.joinP_keeps ((there_ok _ _ _).1 h1) hI)

/-! ## Messages have joined a group -/

/-- A member is entered at its place by number. -/
def ins (m : Array Nat) (o : Nat) : Array Nat := m.insertIdxIfInBounds (m.filter (· < o)).size o

/-- The messages of l have joined group g, one behind the other. -/
structure JoinedTo {L : Type} (g : Nat) (d d' : DState L) (l : List Nat) : Prop where
  book : d'.book = d.book
  roots : d'.roots = d.roots
  opened : d'.opened = d.opened
  loc : d'.loc = d.loc
  codes : d'.st.codes = d.st.codes
  msgs : d'.st.oracles.size = d.st.oracles.size
  msg : ∀ (o : Nat) (x : OnBytes.Oracle), d.st.oracles[o]? = some x →
    ∃ gs, d'.st.oracles[o]? = some { x with groups := gs }
  size : d'.st.groups.size = d.st.groups.size
  other : ∀ i, g ≠ i → d'.st.groups[i]? = d.st.groups[i]?
  at_ : ∀ G, d.st.groups[g]? = some G → ∃ G', d'.st.groups[g]? = some G' ∧
    G'.members = l.foldl ins G.members ∧ G'.rows = G.rows ∧ G'.inRun = G.inRun

theorem JoinedTo.refl {L : Type} (g : Nat) (d : DState L) : JoinedTo g d d [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ x h => ⟨x.groups, h⟩, rfl, fun _ _ => rfl,
    fun G h => ⟨G, h, rfl, rfl, rfl⟩⟩

theorem JoinedTo.trans {L : Type} {g : Nat} {a b c : DState L} {l m : List Nat}
    (h1 : JoinedTo g a b l) (h2 : JoinedTo g b c m) : JoinedTo g a c (l ++ m) := by
  refine ⟨h2.book.trans h1.book, h2.roots.trans h1.roots, h2.opened.trans h1.opened,
    h2.loc.trans h1.loc, h2.codes.trans h1.codes, h2.msgs.trans h1.msgs, fun o x hx => ?_,
    h2.size.trans h1.size, fun i hi => (h2.other i hi).trans (h1.other i hi), fun G hG => ?_⟩
  · obtain ⟨q1, m1⟩ := h1.msg o x hx
    obtain ⟨q2, m2⟩ := h2.msg o _ m1
    exact ⟨q2, m2⟩
  · obtain ⟨G1, a1, b1, c1, e1⟩ := h1.at_ G hG
    obtain ⟨G2, a2, b2, c2, e2⟩ := h2.at_ G1 a1
    exact ⟨G2, a2, by rw [b2, b1, List.foldl_append], c2.trans c1, e2.trans e1⟩

/-- The ground's joinP's yes. -/
theorem joinP_to {L : Type} (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') : JoinedTo g d d' [o] := by
  unfold joinP at h
  split at h
  · cases hG : d.st.groups[g]? with
    | none =>
      rw [hG] at h
      cases h
    | some G0 =>
      rw [hG] at h
      obtain rfl := Option.some.inj h
      refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [withMessageInGroup], fun o' x hx => ?_, by simp [withMessageInGroup],
        fun i hi => by simp [withMessageInGroup, Array.getElem?_modify, hi], fun G hG' => ?_⟩
      · by_cases e : o = o'
        · subst e
          exact ⟨_, joined_same d.st g o kept G0 x hx⟩
        · exact ⟨x.groups, (joined_other d.st g o kept G0 o' e).trans hx⟩
      · obtain rfl : G0 = G := Option.some.inj (hG.symm.trans hG')
        exact ⟨_, joined_group d.st g o kept G0 hG, rfl, rfl, rfl⟩
  · cases h

theorem joinAll_to (g : Nat) : ∀ (l : List Nat) (d d' : St), joinAll g l d = .ok d' →
    JoinedTo g d d' l
  | [], d, d', h => by
    obtain rfl : d = d' := Except.ok.inj h
    exact JoinedTo.refl g d
  | o :: l, d, d', h => by
    unfold joinAll at h
    obtain ⟨e, h1, h2⟩ := (ok_bind _ _ _).1 h
    exact (joinP_to d e g o false ((there_ok _ _ _).1 h1)).trans (joinAll_to g l e d' h2)

/-! ## The row (Eval) is a plain row -/

/-- Adding placed tensors does not change a row's kind. (It follows addLaid_kind of our last chain's
Johnson/Desc/Third/Law/Sharp.lean, which this file does not import.) -/
theorem laid_kind (o : Nat) (lay : VectorLay) : ∀ (l : List Tensor) (row : OnBytes.Row),
    (addLaid row o lay l).kind = row.kind
  | [], _ => rfl
  | t :: l, row => laid_kind o lay l (row.add o .main (lay.onTable t))

theorem evalRow_plain (S : LinShape) (claim : LinClaim) (w : Nat) (wLay : VectorLay)
    (row : OnBytes.Row) (h : linEvalRow S claim w wLay = some row) : row.kind = .plain := by
  unfold linEvalRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, hrow⟩ := h
  rw [← hrow, laid_kind]

/-! ## What a yes of rows says -/

/-- **What a yes of K13's rows says of the record behind.** -/
structure RowsLaid (S : LinShape) (claim : LinClaim) (ids : Array Nat) (d d' : St)
    (lin : LinFirst) : Prop where
  /-- W is the first of the messages sent -/
  w : ids[0]? = some lin.w
  /-- the own group is the next group -/
  own : lin.own = d.st.groups.size
  claimIs : lin.claim = claim
  book : d'.book = d.book
  roots : d'.roots = d.roots
  opened : d'.opened = d.opened
  codes : d'.st.codes = d.st.codes
  msgs : d'.st.oracles.size = d.st.oracles.size
  /-- every message is the same record but for its list of groups -/
  msg : ∀ (o : Nat) (x : OnBytes.Oracle), d.st.oracles[o]? = some x →
    ∃ gs, d'.st.oracles[o]? = some { x with groups := gs }
  /-- one group more -/
  size : d'.st.groups.size = d.st.groups.size + 1
  /-- every older group is as it was -/
  older : ∀ i, i < d.st.groups.size → d'.st.groups[i]? = d.st.groups[i]?
  /-- the own group: the claim's masks' messages and W, each entered at its place by number; ONE
  open row, a plain one, WHICH IS THE CLAIM's (Eval); no test has begun -/
  last : ∃ G row, d'.st.groups[d.st.groups.size]? = some G ∧
    G.members = (listOfT (claim.masks.toList.map (·.oracle)) ++ [lin.w]).foldl ins #[] ∧
    G.rows = #[row] ∧ G.inRun = false ∧ row.kind = .plain ∧
    linEvalRow S claim lin.w (linLayW d.st.codes S) = some row
  /-- a statement in order stays in order -/
  order : Means.InOrder d.st → Means.InOrder d'.st

/-- **A YES OF rows GIVES RowsLaid**, where the shape asks no split's message. -/
theorem rows_laid (S : LinShape) (claim : LinClaim) (ids : Array Nat) (d d' : St) (lin : LinFirst)
    (hS : S.ownSplitNeeded = false) (h : rows S claim ids d = .ok (lin, d')) :
    RowsLaid S claim ids d d' lin := by
  unfold rows at h
  obtain ⟨w, hw, k1⟩ := (ok_bind _ _ _).1 h
  obtain ⟨b, hb, k2⟩ := (ok_bind _ _ _).1 k1
  obtain ⟨d₁, h1, k3⟩ := (ok_bind _ _ _).1 k2
  obtain ⟨d₂, h2, k4⟩ := (ok_bind _ _ _).1 k3
  obtain ⟨split, _, k5⟩ := (ok_bind _ _ _).1 k4
  obtain ⟨d₃, h3, k6⟩ := (ok_bind _ _ _).1 k5
  obtain ⟨mask, _, k7⟩ := (ok_bind _ _ _).1 k6
  obtain ⟨row, hr, k8⟩ := (ok_bind _ _ _).1 k7
  obtain ⟨d₄, h4, hfin⟩ := (ok_bind _ _ _).1 k8
  clear h k1 k2 k3 k4 k5 k6 k7 k8
  have hw := (there_ok _ _ _).1 hw
  have hb := (there_ok _ _ _).1 hb
  have h2 := (there_ok _ _ _).1 h2
  have h3 := (there_ok _ _ _).1 h3
  have hr := (there_ok _ _ _).1 hr
  -- K13's text asks K13.Own.evalRow (Johnson/Desc/K13/Text.lean); K13/OwnLaws.lean: evalRow_agrees
  rw [VerifiableInference.Desc.K13.Own.evalRow_agrees] at hr
  have h4 := (there_ok _ _ _).1 h4
  -- In this library (Johnson/Desc/K13/Text.lean) K13's text asks K13.Own.splitNeeded S, which is S.ownSplitNeeded by rfl (K13/OwnLaws.lean: splitNeeded_agrees)
  rw [show VerifiableInference.Desc.K13.Own.splitNeeded S = false from hS] at h3
  obtain rfl : d₂ = d₃ := Option.some.inj h3
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj
    (Except.ok.inj (show Except.ok _ = Except.ok (lin, d') from hfin))
  -- the new group
  have hb' : b = (d.st.groups.size,
      { d with st := VerifiableInference.Desc.Ground.withGroup d.st S.w.code S.ownMaskCode }) := by
    unfold newGroupP at hb
    split at hb
    · exact (Option.some.inj hb).symm
    · cases hb
  have hI0 : Means.InOrder d.st → Means.InOrder b.2.st := fun hI =>
    Means.newGroupP_keeps (g := b.1) (d' := b.2) hb hI
  -- the joinings
  have J := (joinAll_to b.1 _ b.2 d₁ h1).trans (joinP_to d₁ d₂ b.1 w false h2)
  -- the row
  have h4' : d₄ = { d₂ with st := withRow d₂.st b.1 row } := by
    unfold addRowsP at h4
    split at h4
    · simp only [addRowsFrom] at h4
      cases ha : addRowP d₂ b.1 row with
      | none => simp [ha] at h4
      | some e =>
        simp only [ha, Option.bind_some, Option.some.injEq] at h4
        subst h4
        unfold addRowP at ha
        split at ha
        · exact (Option.some.inj ha).symm
        · cases ha
    · cases h4
  have hI4 : Means.InOrder d₂.st → Means.InOrder d₄.st := fun hI => Means.addRowsP_keeps h4 hI
  have hb1 : b.1 = d.st.groups.size := by rw [hb']
  have hbst : b.2.st = VerifiableInference.Desc.Ground.withGroup d.st S.w.code S.ownMaskCode := by
    rw [hb']
  have hbg : b.2.st.groups[b.1]? = some { code := S.w.code, maskCode := S.ownMaskCode } := by
    rw [hbst, hb1]
    simp [VerifiableInference.Desc.Ground.withGroup]
  obtain ⟨G2, a2, m2, r2, i2⟩ := J.at_ _ hbg
  refine ⟨hw, hb1, rfl, ?_, ?_, ?_, ?_, ?_, fun o x hx => ?_, ?_, fun i hi => ?_, ?_, fun hI => ?_⟩
  · rw [h4']
    exact J.book.trans (by rw [hb'])
  · rw [h4']
    exact J.roots.trans (by rw [hb'])
  · rw [h4']
    exact J.opened.trans (by rw [hb'])
  · rw [h4']
    exact J.codes.trans (by rw [hbst]; rfl)
  · rw [h4']
    exact J.msgs.trans (by rw [hbst]; rfl)
  · rw [h4']
    exact J.msg o x (by rw [hbst]; exact hx)
  · rw [h4']
    show (withRow d₂.st b.1 row).groups.size = _
    rw [show (withRow d₂.st b.1 row).groups.size = d₂.st.groups.size by simp [withRow], J.size,
      hbst]
    simp [VerifiableInference.Desc.Ground.withGroup]
  · rw [h4']
    show (withRow d₂.st b.1 row).groups[i]? = _
    have ne : b.1 ≠ i := by omega
    rw [show (withRow d₂.st b.1 row).groups[i]? = d₂.st.groups[i]? by
      simp [withRow, Array.getElem?_modify, ne], J.other i ne, hbst]
    simp [VerifiableInference.Desc.Ground.withGroup, Array.getElem?_push, Nat.ne_of_lt hi]
  · refine ⟨{ G2 with rows := G2.rows.push row }, row, ?_, m2, ?_, i2, evalRow_plain _ _ _ _ _ hr,
      ?_⟩
    · rw [h4', ← hb1]
      exact withRow_group d₂.st b.1 row G2 a2
    · show G2.rows.push row = #[row]
      rw [r2]
      rfl
    · rw [← J.codes.trans (by rw [hbst]; rfl : b.2.st.codes = d.st.codes)]
      exact hr
  · exact hI4 (Means.joinP_keeps h2 (joinAll_keeps b.1 _ b.2 d₁ h1 (hI0 hI)))

/-- Two members in rising order. -/
theorem ins_two (i w : Nat) (h : i < w) : ([i] ++ [w]).foldl ins #[] = #[i, w] := by
  simp [ins, Array.insertIdxIfInBounds, h]

/-- RowsLaid holds of no record and itself: there is one group more behind. -/
theorem rowsLaid_irrefl (S : LinShape) (claim : LinClaim) (ids : Array Nat) (d : St)
    (lin : LinFirst) : ¬ RowsLaid S claim ids d d lin := fun h => by
  have := h.size
  omega

end VerifiableInference.Desc.Key.LaidW
