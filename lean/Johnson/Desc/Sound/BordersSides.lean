-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BordersSides.lean: WHAT RIDES PAST A BLOCK OF THE FIRST CHAIN, CUT IN TWO SIDES.
The cut is the shared chain's table's, taken over for this table.

Why. The rule of the spine asks, for every item that is open in front of a block and that the block
does not close: from the item at (the statement behind, w) to the item at (the statement in front,
the extractor's value at w) (`Piece.Frames`, Johnson/Desc/Sound/Spine.lean). Two things turn there:
the witness and the statement.

What is said.
  THE WITNESS's SIDE IS THE TABLE's: `sameQ`: two witnesses have one component. `extQ_keeps`,
  `extQAt_keeps` (proved): the table's one extractor leaves every component that the row does not
  lay. `ridersClear` (proved): where the test `laysClear` says yes, no item of the computed open
  list that the block does not close reads a component that the block's row lays.
  `ReadsOkQ`: A PREMISE ON THE MEANING: an item reads the witness through the components that the
  table names for it (`Item.reads`): whoever fills a letter of `Meaning` owes it for that letter.
  `framesOfSides` (proved): under these, and where the block's extractor is the table's one (hx:
  `extQAt`), what is left of `Piece.Frames` at block number k is THE
  STATEMENT's SIDE, AT ONE w: the item says of the statement in front what it says of the statement
  behind: the frame facts by sort of item in the head of Johnson/Desc/First/Borders.lean.

Limits. `RidersClearQ` is asked at the rule's own open set; `ridersClear` gives it at the computed
list `openSets`: the two have the same members where `readsOpen` and `rowsApart` say yes
(Johnson/Desc/Sound/SpineList.lean): `ridersClearQ` joins them. `laysClear` has run at made-up
numbers alone.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.SpineList

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp laysOf laysSeats laysPads laysTok
  start rowOf stepOpen openSets readsOpen laysClear laysClearBy)

/-- Two witnesses have one component. -/
def sameQ {Cells Tok : Type} : Comp → Wit Cells Tok MsgT → Wit Cells Tok MsgT → Prop
  | .msg n, w, w' => w.msg n = w'.msg n
  | .pad j t, w, w' => w.pad j t = w'.pad j t
  | .tok, w, w' => w.tok = w'.tok
  | .cells, w, w' => w.cells = w'.cells

/-- **An item's meaning reads the witness through the components that the table names for it.** -/
def ReadsOkQ {P Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart)
    (Mg : Meaning P (Wit Cells Tok MsgT)) : Prop :=
  ∀ (i : Item) (a : P × First.S) (y : Strs) (w w' : Wit Cells Tok MsgT),
    (∀ c ∈ i.reads arr N links, sameQ c w w') → i.holds N Mg a y w → i.holds N Mg a y w'

/-- What the table says that block number k lays. Beyond the index: nothing. -/
def laysAtQ (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart) (ps : List Place) (k : ℕ) :
    List Comp :=
  (ps[k]?.map (laysOf arr N links)).getD []

/-- At no block does an item that rides read a component that the block's row lays. -/
def RidersClearQ (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart) (ps : List Place) : Prop :=
  ∀ (k : ℕ) (i : Item), openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
    ¬ insQ links ps k i → ∀ c ∈ i.reads arr N links, c ∉ laysAtQ arr N links ps k

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × First.S → Tok)

/-- **The table's extractor leaves every component that the row does not lay.** -/
theorem extQ_keeps (N : Numbers) (links : List ModelPart) (p : Place) (a : P × First.S) (y : Strs)
    (behind : Option (P × First.S)) (w : Wit Cells Tok MsgT) (c : Comp)
    (h : c ∉ laysOf arr N links p) :
    sameQ c w (extQ cs G arr smp ms decT c₀ tokOf N links p a y behind w) := by
  cases c with
  | msg n =>
    have hn : n ∉ (mineAt ms N links p).map (numOf arr) := by
      intro hm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hm
      have hs : x.1.seat x.2 ∈ laysSeats N links p := by
        have h2 := (List.mem_filter.1 hx).2
        simpa using h2
      exact h (List.mem_append_left _ (List.mem_append_left _
        (List.mem_flatMap.2 ⟨_, hs, List.mem_cons_self⟩)))
    exact (extAt_other cs G arr smp decT c₀ _ _ _ _ a y w n hn).symm
  | pad j t =>
    have hn : (j, t) ∉ (mineAt ms N links p ++ minePadAt ms N links p).map seatOf := by
      intro hm
      obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hm
      have he : x.1.seat x.2 = (j, t) := hxe
      rcases List.mem_append.1 hx with hx | hx
      · have hs : x.1.seat x.2 ∈ laysSeats N links p := by
          have h2 := (List.mem_filter.1 hx).2
          simpa using h2
        rw [he] at hs
        exact h (List.mem_append_left _ (List.mem_append_left _
          (List.mem_flatMap.2 ⟨_, hs, List.mem_cons_of_mem _ List.mem_cons_self⟩)))
      · have hs : x.1.seat x.2 ∈ laysPads N links p := by
          have h2 := (List.mem_filter.1 hx).2
          simpa using h2
        rw [he] at hs
        exact h (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨_, hs, rfl⟩)))
    exact (extAt_other_pad cs G arr smp decT c₀ _ _ _ _ a y w j t hn).symm
  | tok =>
    have ht : laysTok links p = false := by
      cases e : laysTok links p with
      | false => rfl
      | true =>
        exact absurd (List.mem_append_right _ (by rw [e]; exact List.mem_singleton.2 rfl)) h
    exact (extQ_keeps_token cs G arr smp ms decT c₀ tokOf N links p ht a y behind w).symm
  | cells => rfl

theorem extQAt_keeps {A : Type} {Fr : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) (c : Comp)
    (h : c ∉ laysAtQ arr N links ps k) :
    sameQ c w (extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w) := by
  unfold extQAt
  unfold laysAtQ at h
  cases e : ps[k]? with
  | none =>
    cases c <;> rfl
  | some p =>
    rw [e] at h
    exact extQ_keeps cs G arr smp ms decT c₀ tokOf N links p _ _ _ w c h

/-- **WHAT IS LEFT OF `Piece.Frames` AT BLOCK NUMBER k IS THE STATEMENT's SIDE, AT ONE w.** -/
theorem framesOfSides {A Cl : Type} {C : CK} {Fr : Frame} (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (get : A → P × First.S) (k : ℕ) (q : Piece C Fr A Cl (Wit Cells Tok MsgT))
    (hr : ReadsOkQ arr N links Mg) (hc : RidersClearQ arr N links ps)
    (hx : ∀ a τ b w, q.ior.red.out a τ = some b →
      q.ext a τ w = extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w)
    (hs : ∀ a τ b w i, q.ior.red.out a τ = some b →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i b w → meansQ N Mg get i a w) :
    q.Frames (onQ N Mg links ps get k) (onQ N Mg links ps get (k + 1)) (meansQ N Mg get)
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k) (insQ links ps k) := by
  intro a τ b w i _ hb _ ho hn hw
  rw [hx a τ b w hb]
  exact hr i _ _ w _
    (fun c hcc => extQAt_keeps cs G arr smp ms decT c₀ tokOf N links ps get k a b w c
      (hc k i ho hn c hcc))
    (hs a τ b w i hb ho hn hw)

end

/-- **Where the test says yes**: no item of the computed open list that the block does not close
reads a component that the block's row lays. -/
theorem ridersClear (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart) :
    ∀ (ps : List Place) (O : List Item), laysClear arr N links ps O = true →
    ∀ (k : ℕ) (p : Place), ps[k]? = some p → ∀ i ∈ (openSets links ps O)[k]?.getD [],
      i ∉ (rowOf links p).ins → ∀ c ∈ i.reads arr N links, c ∉ laysOf arr N links p
  | [], _, _, _, _, hp, _, _, _, _, _ => by simp at hp
  | p₀ :: ps, O, h, 0, p, hp, i, hi, hn, c, hc => by
    obtain rfl : p₀ = p := by simpa using hp
    have h1 : ((O.filter fun i => !(rowOf links p₀).ins.contains i).all fun i =>
        (i.reads arr N links).all fun t => !(laysOf arr N links p₀).contains t) = true :=
      (Eq.mp (Bool.and_eq_true _ _) h).1
    have hi' : i ∈ O := hi
    have h2 := List.all_eq_true.1 h1 i (List.mem_filter.2 ⟨hi', by simpa using hn⟩)
    have h3 := List.all_eq_true.1 h2 c hc
    simpa using h3
  | p₀ :: ps, O, h, k + 1, p, hp, i, hi, hn, c, hc =>
    ridersClear arr N links ps (stepOpen O (rowOf links p₀)) (Eq.mp (Bool.and_eq_true _ _) h).2 k p
      (by simpa using hp) i hi hn c hc

/-- **The same at the rule's own open set**, where the table's three tests say yes. -/
theorem ridersClearQ (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart) (ps : List Place)
    (h1 : laysClear arr N links ps (start links) = true)
    (h2 : readsOpen links ps (start links) = true) (h3 : rowsApart links ps = true) :
    RidersClearQ arr N links ps := by
  intro k i ho hn c hc hl
  unfold laysAtQ at hl
  cases e : ps[k]? with
  | none =>
    rw [e] at hl
    exact absurd hl (List.not_mem_nil)
  | some p =>
    rw [e] at hl
    have hk : k ≤ ps.length := by
      have := (List.getElem?_eq_some_iff.1 e).1
      exact Nat.le_of_lt this
    have hu : Item.unmarked ∈ start links := List.mem_append_left _ (List.mem_cons_self)
    have hL : i ∈ openL (insL links ps) (outsL links ps) (start links) k :=
      (openIsList Item (insL links ps) (outsL links ps) (start links) k i).1 ho
    have hO := (openL_iff_openSets links ps (start links) h2 h3 hu k hk i).1 hL
    have hni : i ∉ (rowOf links p).ins := fun hm => hn (by
      show i ∈ (rowQ links ps k).ins ++ (rowQ links ps k).ctx ++ [.unmarked]
      have er : rowQ links ps k = rowOf links p := by
        unfold rowQ
        rw [e]
        rfl
      rw [er]
      exact List.mem_append_left _ (List.mem_append_left _ hm))
    exact ridersClear arr N links ps (start links) h1 k p e i hO hni c hc hl

end VerifiableInference.Desc.Sound
