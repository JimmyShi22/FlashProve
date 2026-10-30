-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OkWordsOfRead.lean: the view of a chain that the verifier program's reader has read
passes the test that every word of a field's element is below the prime (`okView`,
OnBytes/Maker/OkView.lean).

Statements and proofs. No premise but the reading: none on the description, and none on its field.
The readers return a word of a field's element only if it is below the prime of the field that the
chain's plan names (`Fmt.rdElt`, Fmt/Rules1.lean); the first field's prime is below the second's,
which is the prime of the test.

Three steps.
  (A) `message_below`: the items of a message that was read (`Fmt.readItems`, Fmt/Rules8.lean).
  (B) `opening_below`: the columns of an opening that was read (`Fmt.readOpeningW`,
      Fmt/Rules7.lean), whichever tree it opens: the chain's own, one taken over, a stored table's.
  (C) `viewX_below`: an item of a round in the view is an item of that round as read; an opened
      column in the view is a column of an opening of a round as read (`Fmt.viewX`,
      Fmt/Rules8X.lean).
Between them `readX_below`: round by round, from the trace of a chain that was read (`readX_trace`,
OnBytes/Maker/ReadTrace.lean).

Main theorems.
  `okView_of_readX`   at the strict reader, at any function for the hash.
  `okView_of_read`    at the reader that the program runs.

`elt_below`, `pair_parts`, `ext_below` and `many_all` say again what
OnBytes/Maker/Page/KeyCleanOf.lean [not in this library] holds (`rdElt_lt`, `rdPair_parts`,
`rdExt_ok`, `rdMany_all`):
that file stands above the files that are to import this one. (`many_all` is also
`Run.TieTree.rdMany_all`, Run/Toy1TieTree.lean, and `elt_below` follows from `Fmt.only_elt`,
Fmt/Rules1Only.lean: both lie below this file. `Below.okF` and two arms of `GotBelow.okGot` are
KeyCleanOf's `okF_of`, `okE_of`.)

What is not claimed. What the test does not test (the head of OnBytes/Maker/OkView.lean): an item
that is a word or a root, what a round draws, and all that is in no view. The view here is that of a
chain as read (`OnBytes.viewOf`, OnBytes/Chain/Reader.lean), not the view that a file's reduction
makes of a typed transcript (`OnBytes.Maker.viewOf`, OnBytes/Maker/Whole.lean): nothing on a view
that has passed no reader. Nothing on what a chain proves. Nothing on soundness.


-/
import OnBytes.Maker.OkView
import OnBytes.Maker.ReadTrace

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.Tie

/-! ## Words below the prime -/

/-- The word is below the prime of the field in which the program computes. -/
def Below (w : UInt64) : Prop := w.toNat < Fmt.Fld.two.p

/-- Neither field's prime is above that prime. -/
theorem p_le_two (f : Fmt.Fld) : f.p ≤ Fmt.Fld.two.p := by
  cases f <;> decide

/-- It passes the program's test on a word. -/
theorem Below.okF {w : UInt64} (h : Below w) : OnBytes.okF w = true :=
  decide_eq_true (UInt64.lt_iff_toNat_lt.2 h)

/-- The words of an item that is an element of a field are below the prime. Of a word and of a root
nothing is asked. -/
def GotBelow : Fmt.ItemValue → Prop
  | .f x => Below x
  | .e t => Below t.1 ∧ Below t.2.1 ∧ Below t.2.2
  | .answer t => Below t.1 ∧ Below t.2.1 ∧ Below t.2.2
  | .word _ => True
  | .root _ => True

/-! ## The readers of the parts -/

theorem elt_below {f : Fmt.Fld} {b : ByteArray} {i j : ℕ} {w : UInt64}
    (h : Fmt.rdElt f b i = some (w, j)) : Below w := by
  unfold Fmt.rdElt at h
  split at h
  · split at h
    · rename_i hok
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact Nat.lt_of_lt_of_le (of_decide_eq_true hok) (p_le_two f)
    · cases h
  · cases h

theorem pair_parts {α β : Type} {ra : Fmt.Rd α} {rb : Fmt.Rd β} {b : ByteArray} {i k : ℕ}
    {x : α × β} (h : Fmt.rdPair ra rb b i = some (x, k)) :
    ∃ j, ra b i = some (x.1, j) ∧ rb b j = some (x.2, k) := by
  unfold Fmt.rdPair at h
  split at h
  · rename_i a j ha
    split at h
    · rename_i c k' hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨j, ha, hc⟩
    · cases h
  · cases h

theorem ext_below {f : Fmt.Fld} {b : ByteArray} {i k : ℕ} {t : UInt64 × UInt64 × UInt64}
    (h : Fmt.rdExt f b i = some (t, k)) : Below t.1 ∧ Below t.2.1 ∧ Below t.2.2 := by
  obtain ⟨j, h1, h2⟩ := pair_parts h
  obtain ⟨j', h3, h4⟩ := pair_parts h2
  exact ⟨elt_below h1, elt_below h3, elt_below h4⟩

/-- One item of a message. -/
theorem readItem_below {f : Fmt.Fld} {t : Fmt.Item} {b : ByteArray} {i j : ℕ} {x : Fmt.ItemValue}
    (h : Fmt.readItem f t b i = some (x, j)) : GotBelow x := by
  cases t with
  | f =>
    have h' : (Fmt.rdElt f b i).map (fun y => (Fmt.ItemValue.f y.1, y.2)) = some (x, j) := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨rfl, -⟩ := Prod.mk.inj e
    exact elt_below (w := y.1) (j := y.2) hy
  | e =>
    have h' : (Fmt.rdExt f b i).map (fun y => (Fmt.ItemValue.e y.1, y.2)) = some (x, j) := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨rfl, -⟩ := Prod.mk.inj e
    exact ext_below (t := y.1) (k := y.2) hy
  | word =>
    have h' : (Fmt.rdWord b i).map (fun y => (Fmt.ItemValue.word y.1, y.2)) = some (x, j) := h
    obtain ⟨y, -, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨rfl, -⟩ := Prod.mk.inj e
    exact trivial
  | root =>
    have h' : (Fmt.rdDigest b i).map (fun y => (Fmt.ItemValue.root y.1, y.2)) = some (x, j) := h
    obtain ⟨y, -, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨rfl, -⟩ := Prod.mk.inj e
    exact trivial
  | answer =>
    have h' : (Fmt.rdExt f b i).map (fun y => (Fmt.ItemValue.answer y.1, y.2)) = some (x, j) := h
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h'
    obtain ⟨rfl, -⟩ := Prod.mk.inj e
    exact ext_below (t := y.1) (k := y.2) hy

/-- A message's items. -/
theorem readItems_below {f : Fmt.Fld} : ∀ (ts : List Fmt.Item) (b : ByteArray) (i : ℕ)
    (l : List Fmt.ItemValue) (k : ℕ), Fmt.readItems f ts b i = some (l, k) → ∀ x ∈ l, GotBelow x
  | [], _, _, _, _, h, x, hx => by
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    cases hx
  | t :: ts, b, i, l, k, h, x, hx => by
    unfold Fmt.readItems at h
    split at h
    · rename_i a j ha
      split at h
      · rename_i l' k' hl
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
        rcases List.mem_cons.1 hx with rfl | hx
        · exact readItem_below ha
        · exact readItems_below ts b j l' k' hl x hx
      · cases h
    · cases h

/-- A whole message. -/
theorem message_below {f : Fmt.Fld} {ts : List Fmt.Item} {msg : ByteArray} {vals : List Fmt.ItemValue}
    (h : Fmt.whole (Fmt.readItems f ts) msg = some vals) : ∀ x ∈ vals, GotBelow x := by
  unfold Fmt.whole at h
  split at h
  · rename_i l j hl
    split at h
    · obtain rfl := Option.some.inj h
      exact readItems_below ts msg 0 _ j hl
    · cases h
  · cases h

/-- What is left without the roots was there. -/
theorem mem_of_noRoots {x : Fmt.ItemValue} : ∀ (l : List Fmt.ItemValue), x ∈ Fmt.noRoots l → x ∈ l
  | [], h => h
  | a :: l, h => by
    cases a
    case root d => exact List.mem_cons_of_mem _ (mem_of_noRoots l h)
    all_goals
      rcases List.mem_cons.1 h with rfl | h'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_noRoots l h')

/-- What holds of every value that a reader returns holds of all that it returns in a row. -/
theorem many_all {α : Type} {r : Fmt.Rd α} {P : α → Prop}
    (hr : ∀ b i x j, r b i = some (x, j) → P x) : ∀ (n : ℕ) (b : ByteArray) (i : ℕ) (l : List α)
    (k : ℕ), Fmt.rdMany r n b i = some (l, k) → ∀ x ∈ l, P x
  | 0, _, _, _, _, h, x, hx => by
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
    cases hx
  | n + 1, b, i, l, k, h, x, hx => by
    unfold Fmt.rdMany at h
    split at h
    · rename_i a j ha
      split at h
      · rename_i l' k' hl
        obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hr _ _ _ _ ha
        · exact many_all hr n b j l' k' hl x hx
      · cases h
    · cases h

/-- The words of all columns of an opening are below the prime. -/
def ColsBelow (y : OpenedY) : Prop := ∀ col ∈ y.2.2.cols, ∀ w ∈ col, Below w

/-- **An opening that the reader of an opening has handed out**, at any function for the hash. -/
theorem opening_below (h : HId) {cfg : ByteArray} {f : Fmt.Fld} {sb : ℕ} {sh : Fmt.Shape}
    {start : ByteArray} {xs : List ℕ} {b : ByteArray} {i : ℕ} {o : Fmt.OpenOut}
    (e : Fmt.readOpeningW (m := Id) h cfg f sb sh start xs b i = some o) :
    ∀ col ∈ o.cols, ∀ w ∈ col, Below w := by
  obtain ⟨-, cs, hp, hc, -⟩ := readOpening_some h cfg f sb sh start xs b i o e
  have hp' : Fmt.rdPair
      (Fmt.rdMany (Fmt.rdPair (Fmt.rdMany (Fmt.rdElt f) sh.W) (Fmt.rdBytes sb)) xs.length)
      (Fmt.rdMany Fmt.rdDigest (Fmt.walkPlaces sh.a xs).length) b i =
        some ((cs, o.given), o.next) := hp
  obtain ⟨j, h1, -⟩ := pair_parts hp'
  have hcs : ∀ c ∈ cs, ∀ w ∈ c.1, Below w :=
    many_all (P := fun c : List UInt64 × ByteArray => ∀ w ∈ c.1, Below w)
      (fun b' i' x j' hx => by
        obtain ⟨j'', g1, -⟩ := pair_parts hx
        exact many_all (P := Below) (fun _ _ _ _ hw => elt_below hw) _ _ _ _ _ g1)
      _ _ _ _ _ h1
  intro col hcol
  rw [hc] at hcol
  obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hcol
  exact hcs c hc'

/-! ## A round, and a chain -/

/-- Of a round as read: the items' words and the words of every opened column. -/
def RoundBelow (ro : Fmt.RoundOut) : Prop :=
  (∀ x ∈ ro.vals, GotBelow x) ∧ ∀ y ∈ ro.opens, ColsBelow y

theorem roundAt_below {h : HId} {cfg st : ByteArray} {P : Fmt.Plan} {run : Option ByteArray}
    {b : ByteArray} {x : Fmt.Round × List Fmt.Stored} {ro : Fmt.RoundOut} {c : Fmt.Chain}
    {roots : Array ByteArray} (H : RoundAt h cfg st P run b x ro c roots) : RoundBelow ro := by
  refine ⟨message_below H.vals, ?_⟩
  obtain ⟨cs, co, ho, h1, h2⟩ := H.opens
  intro y hy
  rw [ho] at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact forall₂_right (Q := ColsBelow)
      (fun _ y' ⟨_, _, A⟩ => by
        obtain ⟨i, e⟩ := A.read
        exact opening_below h e) h1 y hy
  · exact forall₂_right (Q := ColsBelow)
      (fun _ y' ⟨_, _, A⟩ => by
        obtain ⟨i, e⟩ := A.read
        exact opening_below h e) h2 y hy

theorem traceX_below {h : HId} {cfg st : ByteArray} {P : Fmt.Plan} {run : Option ByteArray}
    {b : ByteArray} : ∀ (xs : List (Fmt.Round × List Fmt.Stored)) (ros : List Fmt.RoundOut)
    (c : Fmt.Chain) (roots : Array ByteArray), TraceX h cfg st P run b xs ros c roots →
    ∀ ro ∈ ros, RoundBelow ro
  | [], [], _, _, _, _, hr => by cases hr
  | x :: xs, r :: ros, c, roots, H, ro, hr => by
    obtain ⟨H1, H2⟩ := H
    rcases List.mem_cons.1 hr with rfl | hr
    · exact roundAt_below H1
    · exact traceX_below xs ros _ _ H2 ro hr
  | [], _ :: _, _, _, H, _, _ => False.elim H
  | _ :: _, [], _, _, H, _, _ => False.elim H

/-- **A chain that the strict reader has read**, at any function for the hash: round by round. No
premise on the description: not on its field either. -/
theorem readX_below (h : HId) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    ∀ ro ∈ o.rounds.toList, RoundBelow ro := by
  obtain ⟨_, _, -, -, T⟩ := readX_trace h S seen b i o j e
  exact traceX_below _ _ _ _ T

/-! ## The view -/

/-- Of a view: the items' words of every round, and the words of every opened column. -/
def ViewBelow (v : Fmt.View) : Prop :=
  (∀ r ∈ v.rounds, ∀ x ∈ r.vals, GotBelow x) ∧ ∀ z ∈ v.opened, ∀ w ∈ z.2.2, Below w

/-- The opened columns of one round in a view are columns of that round's openings. -/
theorem openedX_below {first : ℕ} {ts : List Fmt.Stored} {ro : Fmt.RoundOut}
    (H : ∀ y ∈ ro.opens, ColsBelow y) : ∀ z ∈ Fmt.openedX first ts ro, ∀ w ∈ z.2.2, Below w := by
  intro z hz
  unfold Fmt.openedX at hz
  rcases List.mem_append.1 hz with hz | hz
  · obtain ⟨y, hy, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
    exact H y.2 (List.of_mem_zip hy).2 p.2 (List.of_mem_zip hp).2
  · unfold Fmt.openedOf at hz
    obtain ⟨y, hy, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
    exact H y (List.mem_of_mem_drop hy) p.2 (List.of_mem_zip hp).2

/-- The view of a chain whose rounds are so. -/
theorem viewX_below (S : Fmt.SpecX) (o : Fmt.ChainOut)
    (H : ∀ ro ∈ o.rounds.toList, RoundBelow ro) : ViewBelow (Fmt.viewX S o) := by
  constructor
  · intro r hr x hx
    have hr' : r ∈ o.rounds.toList.map
        (fun ro => (⟨Fmt.noRoots ro.vals, ro.drawn⟩ : Fmt.RoundView)) := hr
    obtain ⟨ro, hro, rfl⟩ := List.mem_map.1 hr'
    exact (H ro hro).1 x (mem_of_noRoots _ hx)
  · intro z hz
    have hz' : z ∈ (S.stored.zip o.rounds.toList).flatMap
        (fun y => Fmt.openedX S.base.firstTree y.1 y.2) := hz
    obtain ⟨y, hy, hz''⟩ := List.mem_flatMap.1 hz'
    exact openedX_below (H y.2 (List.of_mem_zip hy).2).2 z hz''

/-! ## The test -/

theorem GotBelow.okGot {x : Fmt.ItemValue} (h : GotBelow x) : OnBytes.Maker.okGot x = true := by
  cases x with
  | f y => exact Below.okF h
  | e t =>
    show (OnBytes.okF t.1 && OnBytes.okF t.2.1 && OnBytes.okF t.2.2) = true
    rw [Below.okF h.1, Below.okF h.2.1, Below.okF h.2.2]
    rfl
  | answer t =>
    show (OnBytes.okF t.1 && OnBytes.okF t.2.1 && OnBytes.okF t.2.2) = true
    rw [Below.okF h.1, Below.okF h.2.1, Below.okF h.2.2]
    rfl
  | word _ => rfl
  | root _ => rfl

theorem ViewBelow.okView {v : Fmt.View} (H : ViewBelow v) : OnBytes.Maker.okView v = true := by
  unfold OnBytes.Maker.okView
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨fun r hr => List.all_eq_true.2 fun x hx => (H.1 r hr x hx).okGot,
    fun z hz => List.all_eq_true.2 fun w hw => (H.2 z hz w hw).okF⟩

/-- **The view of a chain that the strict reader has read passes the test on the words**, at any
function for the hash. -/
theorem okView_of_readX (h : HId) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j)) :
    okView (Fmt.viewX S o) = true :=
  (viewX_below S o (readX_below h S seen b i o j e)).okView

/-- **The view of a chain that the program's reader has read passes the test on the words.** -/
theorem okView_of_read (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j)) :
    okView (viewOf S o) = true := by
  rw [viewOf_eq]
  exact okView_of_readX Fmt.formatHash S seen b i o j ((readChain_eq S seen b i).symm.trans e)

end OnBytes.Maker

#print axioms OnBytes.Maker.okView_of_readX
#print axioms OnBytes.Maker.okView_of_read
