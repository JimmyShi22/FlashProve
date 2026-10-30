-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OpenSetAtEnd.lean: WHAT IS OPEN AT THE FIRST TABLE's LAST BORDER, AT EVERY
LAWFUL LIST OF SEGMENTS: three statements, as definitions, and their proofs.

The table of joints of a proof file's first chain (Johnson/Desc/First/Borders.lean) computes the set
of open items at each border from the blocks' rows (`openSets`, `stepOpen`, `rowOf`). At a written
list of segments a set can be evaluated. Here the last two sets are described at every list.
  `endOpenOnly`: at the last border nothing is open but "no mark", three pins and the one claim.
  `endOpenPins`: W's pin and the index masks' pin are open there.
  `sealOpenOnly`: the like of the first, one border in front (in front of the seal).
How (namespace OpenEnd). (1) FROM ABOVE, `sim_rows`: if every open item is "far" (a property that
is claimed at the end too) or the image under a map f of a member of a small list L, and each row's
ins and outs are a model row's under f (`IsMap`), then the same holds behind the rows, with L
stepped by the model rows. (2) FROM BELOW, `lays_map`: a Bool on the model rows (`lays`) says that
an item which f fixes is surely open behind them; then it is open behind the rows. (3) A segment's
rows at the number k + 1 are its rows at the number 1 with every segment's number raised by k
(`sh k`): by unfolding, row by row (`isMap_seg`); likewise the rows behind the last segment. (4) The
model lists are closed terms: the kernel evaluates them. (5) An induction over the segments carries
`Inv`: what is open in front of segment m is one of four standing items, a part of the relation of
a segment from m on, or what segment m - 1 hands on.
Limits. The fence `linksOk` is spent only to bar the empty list: the sorts' order plays no part. The
table is read as it lies in this tree: a turned row wants the file compiled anew. `several := true`
alone (with the block that joins the pending claims). Nothing on any block, any meaning, any plan;
nothing on soundness.

-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (ModelPart Item openSets start flatPlaces linksOk)

/-- The items that the table computes as open at the first chain's last border. -/
def endOpen (links : List ModelPart) : List Item :=
  (openSets links (flatPlaces true links true) (start links))[(flatPlaces true links
    true).length]?.getD []

/-- **(D′a), THE STATEMENT.** Nothing but "no mark", three pins and the one claim is open there. -/
def EndOpenOnly : Prop :=
  ∀ links : List ModelPart, linksOk links = true → ∀ i ∈ endOpen links,
    i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne

/-- **(D′b), THE STATEMENT.** W's pin and the index masks' pin are open there. -/
def EndOpenPins : Prop :=
  ∀ links : List ModelPart, linksOk links = true → Item.pinV ∈ endOpen links ∧ Item.pinI ∈ endOpen links

/-- The like one border in front (in front of the seal): what the seal's tie reads. -/
def sealOpen (links : List ModelPart) : List Item :=
  (openSets links (flatPlaces true links true) (start links))[(flatPlaces true links
    true).length - 1]?.getD []

/-- **(D′c), THE STATEMENT.** -/
def SealOpenOnly : Prop :=
  ∀ links : List ModelPart, linksOk links = true → ∀ i ∈ sealOpen links,
    i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne

/-- TRIES, by the kernel: the three hold at six short lawful lists. -/
def tryB (links : List ModelPart) : Bool :=
  ((endOpen links).all fun i => i == .unmarked || i == .pinW || i == .pinI || i == .pinV ||
      i == .pileOne) && (endOpen links).contains .pinV && (endOpen links).contains .pinI &&
    (sealOpen links).all fun i => i == .unmarked || i == .pinW || i == .pinI || i == .pinV ||
      i == .pileOne

set_option maxRecDepth 1000000 in
example : ([[.head], [.layers, .head], [.attention, .head], [.layers, .layers, .head],
    [.attention, .attention, .head], [.attention, .layers, .attention, .head]] :
      List (List ModelPart)).all tryB = true := by decide +kernel


namespace OpenEnd
open VerifiableInference.Desc VerifiableInference.Desc.First

/-! ## 1 The open set behind a list of rows -/

/-- The open set behind a list of rows. -/
def runRows (rows : List BlockRow) (O : List Item) : List Item := rows.foldl stepOpen O

theorem run_append (r s : List BlockRow) (O : List Item) :
    runRows (r ++ s) O = runRows s (runRows r O) := by
  simp [runRows, List.foldl_append]

/-- The open set at the border behind a first stretch of the places. -/
theorem openSets_at (links : List ModelPart) : ∀ (ps qs : List Place) (O : List Item),
    (openSets links (ps ++ qs) O)[ps.length]? = some (runRows (ps.map (rowOf links)) O)
  | [], qs, _ => by cases qs <;> rfl
  | p :: ps, qs, O => by
    show (O :: openSets links (ps ++ qs) (stepOpen O (rowOf links p)))[ps.length + 1]? = _
    rw [List.getElem?_cons_succ]
    exact openSets_at links ps qs _

theorem mem_step_elim {O : List Item} {r : BlockRow} {i : Item} (h : i ∈ stepOpen O r) :
    (i ∈ O ∧ i ∉ r.ins) ∨ i ∈ r.outs := by
  simp only [stepOpen, List.mem_append, List.mem_filter] at h
  rcases h with ⟨hO, hc⟩ | ⟨ho, _⟩
  · refine Or.inl ⟨hO, fun hin => ?_⟩
    simp [hin] at hc
  · exact Or.inr ho

theorem mem_step_keep {O : List Item} {r : BlockRow} {i : Item} (h : i ∈ O) (hn : i ∉ r.ins) :
    i ∈ stepOpen O r := by
  simp only [stepOpen, List.mem_append, List.mem_filter]
  exact Or.inl ⟨h, by simp [hn]⟩

theorem mem_step_out {O : List Item} {r : BlockRow} {i : Item} (h : i ∈ r.outs) :
    i ∈ stepOpen O r := by
  simp only [stepOpen, List.mem_append, List.mem_filter]
  cases hb : (List.filter (fun i => !r.ins.contains i) O).contains i with
  | false =>
    first
      | exact Or.inr ⟨h, rfl⟩
      | exact Or.inr ⟨h, by rw [hb]; rfl⟩
  | true =>
    have hm : i ∈ List.filter (fun i => !r.ins.contains i) O := List.mem_of_elem_eq_true hb
    exact Or.inl (List.mem_filter.1 hm)

/-! ## 2 Rows that are model rows under a map -/

/-- What the row r closes and opens is what the model row r₁ closes and opens, under f. -/
structure IsMap (f : Item → Item) (r r₁ : BlockRow) : Prop where
  ins : r.ins = r₁.ins.map f
  outs : r.outs = r₁.outs.map f

theorem isMap_id (r : BlockRow) : IsMap id r r := ⟨(List.map_id _).symm, (List.map_id _).symm⟩

theorem sim_step (f : Item → Item) (Far : Item → Prop) {r r₁ : BlockRow} {O L : List Item}
    (hf : IsMap f r r₁) (h : ∀ i ∈ O, Far i ∨ ∃ j ∈ L, i = f j) :
    ∀ i ∈ stepOpen O r, Far i ∨ ∃ j ∈ stepOpen L r₁, i = f j := by
  intro i hi
  rcases mem_step_elim hi with ⟨hO, hn⟩ | ho
  · rcases h i hO with hF | ⟨j, hj, e⟩
    · exact Or.inl hF
    · refine Or.inr ⟨j, mem_step_keep hj fun hin => hn ?_, e⟩
      rw [e, hf.ins]
      exact List.mem_map.2 ⟨j, hin, rfl⟩
  · rw [hf.outs] at ho
    obtain ⟨j, hj, e⟩ := List.mem_map.1 ho
    exact Or.inr ⟨j, mem_step_out hj, e.symm⟩

/-- **From above, along a list of rows.** keys: what numbers the rows; g: the rows; g₁: the model
rows. -/
theorem sim_rows {κ : Type} (f : Item → Item) (Far : Item → Prop) (g g₁ : κ → BlockRow) :
    ∀ (keys : List κ) (O L : List Item), (∀ k ∈ keys, IsMap f (g k) (g₁ k)) →
      (∀ i ∈ O, Far i ∨ ∃ j ∈ L, i = f j) →
      ∀ i ∈ runRows (keys.map g) O, Far i ∨ ∃ j ∈ runRows (keys.map g₁) L, i = f j
  | [], _, _, _, h => h
  | k :: ks, O, L, hk, h =>
    sim_rows f Far g g₁ ks (stepOpen O (g k)) (stepOpen L (g₁ k))
      (fun x hx => hk x (List.mem_cons_of_mem _ hx))
      (sim_step f Far (hk k (List.mem_cons.2 (Or.inl rfl))) h)

/-- The item x is surely open behind the rows. b: it is surely open in front. -/
def lays (x : Item) : List BlockRow → Bool → Bool
  | [], b => b
  | r :: rs, b => lays x rs ((b && !r.ins.contains x) || r.outs.contains x)

/-- **From below, along a list of rows**, for an item that f fixes and nothing else is sent to. -/
theorem lays_map {κ : Type} (f : Item → Item) (x : Item) (hx : f x = x)
    (hinj : ∀ j, f j = x → j = x) (g g₁ : κ → BlockRow) :
    ∀ (keys : List κ) (b : Bool) (O : List Item), (∀ k ∈ keys, IsMap f (g k) (g₁ k)) →
      (b = true → x ∈ O) → lays x (keys.map g₁) b = true → x ∈ runRows (keys.map g) O
  | [], _, _, _, hb, h => hb h
  | k :: ks, b, O, hk, hb, h => by
    refine lays_map f x hx hinj g g₁ ks _ (stepOpen O (g k))
      (fun y hy => hk y (List.mem_cons_of_mem _ hy)) ?_ h
    intro hb'
    have hm := hk k (List.mem_cons.2 (Or.inl rfl))
    cases ho : (g₁ k).outs.contains x with
    | true =>
      apply mem_step_out
      rw [hm.outs]
      exact List.mem_map.2 ⟨x, List.mem_of_elem_eq_true ho, hx⟩
    | false =>
      cases hi : (g₁ k).ins.contains x with
      | true =>
        rw [ho, hi] at hb'
        simp at hb'
      | false =>
        rw [ho, hi] at hb'
        have hb1 : b = true := by simpa using hb'
        refine mem_step_keep (hb hb1) fun hin => ?_
        rw [hm.ins] at hin
        obtain ⟨j, hj, e⟩ := List.mem_map.1 hin
        rw [hinj j e] at hj
        have ht : (g₁ k).ins.contains x = true := List.elem_eq_true_of_mem hj
        rw [hi] at ht
        cases ht

theorem all_nil {κ : Type} {p : κ → Prop} : ∀ x ∈ ([] : List κ), p x := by
  intro x hx
  cases hx

theorem all_cons {κ : Type} {p : κ → Prop} {a : κ} {l : List κ} (h : p a) (t : ∀ x ∈ l, p x) :
    ∀ x ∈ a :: l, p x := by
  intro x hx
  rcases List.mem_cons.1 hx with e | hx
  · subst e
    exact h
  · exact t x hx

/-! ## 3 The rows at any number are the rows at the number 1, raised -/

/-- Every segment's number in an item raised by k. -/
def sh (k : Nat) : Item → Item
  | .constr s p => .constr (k + s) p
  | .pin s m => .pin (k + s) m
  | .pinKept s => .pinKept (k + s)
  | .tie s => .tie (k + s)
  | .forms s p r => .forms (k + s) p r
  | .formsT s p r => .formsT (k + s) p r
  | .worth s p w => .worth (k + s) p w
  | .wo s => .wo (k + s)
  | .totalB s => .totalB (k + s)
  | .total s => .total (k + s)
  | .row s c => .row (k + s) c
  | .carry s => .carry (k + s)
  | .pinI => .pinI
  | .pinV => .pinV
  | .pinW => .pinW
  | .pile => .pile
  | .pileOne => .pileOne
  | .wrow => .wrow
  | .unmarked => .unmarked

theorem sh_pinI (k : Nat) (j : Item) (h : sh k j = .pinI) : j = .pinI := by
  cases j <;> first | rfl | cases h

theorem sh_pinV (k : Nat) (j : Item) (h : sh k j = .pinV) : j = .pinV := by
  cases j <;> first | rfl | cases h

/-- The numbers of a segment's blocks. -/
def pieces : ModelPart → List Nat
  | .head => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  | _ => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- One row is its model row, raised: by unfolding; else by rewriting. -/
macro "seg_tac" : tactic =>
  `(tactic| first
    | exact ⟨rfl, rfl⟩
    | exact ⟨by simp [segRow, backRow, shift, joinAt, earlyRuns, formsOf, rowsOf, pinsOf, sh],
        by simp [segRow, backRow, shift, joinAt, earlyRuns, formsOf, rowsOf, pinsOf, sh]⟩)

theorem isMap_seg (sub : ModelPart) (k : Nat) :
    ∀ j ∈ pieces sub, IsMap (sh k) (segRow sub (k + 1) j) (segRow sub 1 j) := by
  cases sub
  · exact
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_nil
  · exact
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_nil
  · exact
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
      all_cons (by seg_tac) <|
      all_nil

/-- A place with the segment's number written into it. -/
def relink (m : Nat) (p : Place) : Place := { p with link := some m }

theorem relink_eq (m : Nat) (sub : ModelPart) : (linkPlaces m sub).map (relink m) = linkPlaces m sub := by
  cases sub <;> rfl

theorem pieces_eq (m : Nat) (sub : ModelPart) : (linkPlaces m sub).map (·.piece) = pieces sub := by
  cases sub <;> rfl

/-- **A segment's rows in the table are `segRow` at its blocks' numbers.** -/
theorem rows_link (links : List ModelPart) (m : Nat) (sub : ModelPart) (h : links[m]? = some sub) :
    (linkPlaces m sub).map (rowOf links) = (pieces sub).map (segRow sub m) := by
  have key : (rowOf links ∘ relink m) = (segRow sub m ∘ fun p => p.piece) := by
    funext p
    simp [rowOf, relink, h]
  calc (linkPlaces m sub).map (rowOf links)
      = ((linkPlaces m sub).map (relink m)).map (rowOf links) := by rw [relink_eq]
    _ = (linkPlaces m sub).map (segRow sub m ∘ fun p => p.piece) := by rw [List.map_map, key]
    _ = ((linkPlaces m sub).map (·.piece)).map (segRow sub m) := by rw [List.map_map]
    _ = (pieces sub).map (segRow sub m) := by rw [pieces_eq]

/-- The places behind the last segment, without the seal's. -/
def back4 : List Place := addresses none (backKinds true)

/-- The seal's place. -/
def sealP : Place := frameAt none ((backKinds true).length + 1)

theorem isMap_back4 (k : Nat) : ∀ p ∈ back4, IsMap (sh k) (backRow (k + 1) p) (backRow 1 p) :=
  all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
    all_cons (by seg_tac) <| all_nil

theorem isMap_back5 (k : Nat) :
    ∀ p ∈ back4 ++ [sealP], IsMap (sh k) (backRow (k + 1) p) (backRow 1 p) :=
  all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_cons (by seg_tac) <|
    all_cons (by seg_tac) <| all_cons (by seg_tac) <| all_nil

theorem rows_back4 (links : List ModelPart) :
    back4.map (rowOf links) = back4.map (backRow links.length) := rfl

theorem rows_back5 (links : List ModelPart) :
    (back4 ++ [sealP]).map (rowOf links) = (back4 ++ [sealP]).map (backRow links.length) := rfl

/-! ## 4 The model lists, by the kernel -/

/-- What of the first segment can be open in front of it. -/
def L0 : List Item := [.constr 0 .idn, .constr 0 .lookCalls, .constr 0 .rider, .constr 0 .small]

/-- The model of what of a later segment can be open in front of it, with what is handed to it. -/
def L1 : List Item :=
  [.constr 1 .idn, .constr 1 .lookCalls, .constr 1 .rider, .constr 1 .small, .carry 0, .pinKept 0]

/-- The model of what the blocks behind the last segment meet. -/
def LB : List Item := [.carry 0, .pinKept 0, .pile]

set_option maxRecDepth 1000000 in
theorem seg_end0 (sub : ModelPart) : ∀ j ∈ runRows ((pieces sub).map (segRow sub 0)) L0,
    j = Item.pinI ∨ j = Item.carry 0 ∨ j = Item.pinKept 0 := by
  cases sub <;> decide +kernel

set_option maxRecDepth 1000000 in
theorem seg_end1 (sub : ModelPart) : ∀ j ∈ runRows ((pieces sub).map (segRow sub 1)) L1,
    j = Item.carry 1 ∨ j = Item.pinKept 1 := by
  cases sub <;> decide +kernel

set_option maxRecDepth 1000000 in
theorem back_end4 : ∀ j ∈ runRows (back4.map (backRow 1)) LB,
    j = Item.pileOne ∨ j = Item.pinV := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem back_end5 : ∀ j ∈ runRows ((back4 ++ [sealP]).map (backRow 1)) LB,
    j = Item.pileOne ∨ j = Item.pinV := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem lay0 (sub : ModelPart) : lays .pinI ((pieces sub).map (segRow sub 0)) false = true := by
  cases sub <;> decide +kernel

set_option maxRecDepth 1000000 in
theorem lay1 (sub : ModelPart) : lays .pinI ((pieces sub).map (segRow sub 1)) true = true := by
  cases sub <;> decide +kernel

set_option maxRecDepth 1000000 in
theorem layI : lays .pinI ((back4 ++ [sealP]).map (backRow 1)) true = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem layV : lays .pinV ((back4 ++ [sealP]).map (backRow 1)) false = true := by
  decide +kernel

/-! ## 5 What can be open in front of a segment -/

/-- The four items that stand along the segments. -/
def Base (i : Item) : Prop := i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pile

/-- A part of the relation of a segment from m on. -/
def Later (n m : Nat) (i : Item) : Prop :=
  ∃ q, m ≤ q ∧ q < n ∧
    (i = .constr q .idn ∨ i = .constr q .lookCalls ∨ i = .constr q .rider ∨ i = .constr q .small)

/-- What the segment in front of m hands on. -/
def Handed (m : Nat) (i : Item) : Prop := ∃ k, m = k + 1 ∧ (i = .carry k ∨ i = .pinKept k)

/-- What can be open in front of segment m of n. -/
def Inv (n m : Nat) (O : List Item) : Prop := ∀ i ∈ O, Base i ∨ Later n m i ∨ Handed m i

theorem seg_step (links : List ModelPart) (n m : Nat) (sub : ModelPart) (h : links[m]? = some sub)
    (O : List Item) (hO : Inv n m O) :
    Inv n (m + 1) (runRows ((linkPlaces m sub).map (rowOf links)) O) := by
  rw [rows_link links m sub h]
  cases m with
  | zero =>
    have prem : ∀ i ∈ O, (Base i ∨ Later n (0 + 1) i) ∨ ∃ j ∈ L0, i = id j := by
      intro i hi
      rcases hO i hi with hB | ⟨q, _, hq2, hc⟩ | ⟨k', hk, _⟩
      · exact Or.inl (Or.inl hB)
      · by_cases e : q = 0
        · subst e
          rcases hc with rfl | rfl | rfl | rfl
          · exact Or.inr ⟨.constr 0 .idn, by decide, rfl⟩
          · exact Or.inr ⟨.constr 0 .lookCalls, by decide, rfl⟩
          · exact Or.inr ⟨.constr 0 .rider, by decide, rfl⟩
          · exact Or.inr ⟨.constr 0 .small, by decide, rfl⟩
        · exact Or.inl (Or.inr ⟨q, by omega, hq2, hc⟩)
      · omega
    intro i hi
    rcases sim_rows id (fun i => Base i ∨ Later n (0 + 1) i) (segRow sub 0) (segRow sub 0)
      (pieces sub) O L0 (fun j _ => isMap_id _) prem i hi with (hB | hL) | ⟨j, hj, e⟩
    · exact Or.inl hB
    · exact Or.inr (Or.inl hL)
    · rcases seg_end0 sub j hj with rfl | rfl | rfl
      · exact Or.inl (Or.inr (Or.inr (Or.inl e)))
      · exact Or.inr (Or.inr ⟨0, rfl, Or.inl e⟩)
      · exact Or.inr (Or.inr ⟨0, rfl, Or.inr e⟩)
  | succ k =>
    have prem : ∀ i ∈ O, (Base i ∨ Later n (k + 1 + 1) i) ∨ ∃ j ∈ L1, i = sh k j := by
      intro i hi
      rcases hO i hi with hB | ⟨q, hq1, hq2, hc⟩ | ⟨k', hk, hc⟩
      · exact Or.inl (Or.inl hB)
      · by_cases e : q = k + 1
        · subst e
          rcases hc with rfl | rfl | rfl | rfl
          · exact Or.inr ⟨.constr 1 .idn, by decide, rfl⟩
          · exact Or.inr ⟨.constr 1 .lookCalls, by decide, rfl⟩
          · exact Or.inr ⟨.constr 1 .rider, by decide, rfl⟩
          · exact Or.inr ⟨.constr 1 .small, by decide, rfl⟩
        · exact Or.inl (Or.inr ⟨q, by omega, hq2, hc⟩)
      · have e : k' = k := by omega
        subst e
        rcases hc with rfl | rfl
        · exact Or.inr ⟨.carry 0, by decide, rfl⟩
        · exact Or.inr ⟨.pinKept 0, by decide, rfl⟩
    intro i hi
    rcases sim_rows (sh k) (fun i => Base i ∨ Later n (k + 1 + 1) i) (segRow sub (k + 1))
      (segRow sub 1) (pieces sub) O L1 (isMap_seg sub k) prem i hi with (hB | hL) | ⟨j, hj, e⟩
    · exact Or.inl hB
    · exact Or.inr (Or.inl hL)
    · rcases seg_end1 sub j hj with rfl | rfl
      · exact Or.inr (Or.inr ⟨k + 1, rfl, Or.inl e⟩)
      · exact Or.inr (Or.inr ⟨k + 1, rfl, Or.inr e⟩)

/-- The places of the segments of a list that begins at the number m. -/
def midFrom (l : List ModelPart) (m : Nat) : List Place :=
  (l.zipIdx m).flatMap fun x => linkPlaces x.2 x.1

theorem midFrom_cons (s : ModelPart) (l : List ModelPart) (m : Nat) :
    midFrom (s :: l) m = linkPlaces m s ++ midFrom l (m + 1) := by
  first
    | rfl
    | simp [midFrom, List.zipIdx_cons, List.flatMap_cons]

/-- **From above, along the segments.** -/
theorem segs_step (links : List ModelPart) (n : Nat) : ∀ (l : List ModelPart) (m : Nat) (O : List Item),
    (∀ t sub, l[t]? = some sub → links[m + t]? = some sub) → Inv n m O →
      Inv n (m + l.length) (runRows ((midFrom l m).map (rowOf links)) O)
  | [], _, _, _, hO => hO
  | s :: l, m, O, hl, hO => by
    rw [midFrom_cons, List.map_append, run_append]
    have h0 : links[m]? = some s := hl 0 s (by simp)
    have ht : ∀ t sub, l[t]? = some sub → links[m + 1 + t]? = some sub := by
      intro t sub hts
      have := hl (t + 1) sub (by simpa using hts)
      rwa [show m + (t + 1) = m + 1 + t by omega] at this
    have := segs_step links n l (m + 1) _ ht (seg_step links n m s h0 O hO)
    rwa [show m + 1 + l.length = m + (s :: l).length by
      simp only [List.length_cons]; omega] at this

/-- **From below, along the later segments**: the index masks' pin stays open. -/
theorem pinI_segs (links : List ModelPart) : ∀ (l : List ModelPart) (k : Nat) (O : List Item),
    (∀ t sub, l[t]? = some sub → links[k + 1 + t]? = some sub) → Item.pinI ∈ O →
      Item.pinI ∈ runRows ((midFrom l (k + 1)).map (rowOf links)) O
  | [], _, _, _, h => h
  | s :: l, k, O, hl, h => by
    rw [midFrom_cons, List.map_append, run_append]
    have h0 : links[k + 1]? = some s := hl 0 s (by simp)
    rw [rows_link links (k + 1) s h0]
    refine pinI_segs links l (k + 1) _ ?_ ?_
    · intro t sub hts
      have := hl (t + 1) sub (by simpa using hts)
      rwa [show k + 1 + (t + 1) = k + 1 + 1 + t by omega] at this
    · exact lays_map (sh k) .pinI rfl (sh_pinI k) (segRow s (k + 1)) (segRow s 1) (pieces s) true O
        (isMap_seg s k) (fun _ => h) (lay1 s)

theorem zipIdx_bounds : ∀ (l : List ModelPart) (m : Nat) (x : ModelPart × Nat), x ∈ l.zipIdx m →
    m ≤ x.2 ∧ x.2 < m + l.length
  | [], _, _, h => by simp at h
  | a :: l, m, x, h => by
    have hl : (a :: l).length = l.length + 1 := rfl
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with e | h'
    · subst e
      exact ⟨Nat.le_refl _, by show m < _; omega⟩
    · have := zipIdx_bounds l (m + 1) x h'
      omega

theorem inv_start (links : List ModelPart) : Inv links.length 0 (start links) := by
  intro i hi
  unfold start at hi
  rcases List.mem_append.1 hi with h | h
  · have h' : i = .unmarked ∨ i = .pinW ∨ i = .pile := by simpa using h
    rcases h' with e | e | e
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr (Or.inl e))
    · exact Or.inl (Or.inr (Or.inr (Or.inr e)))
  · obtain ⟨x, hx, hi'⟩ := List.mem_flatMap.1 h
    have hb := zipIdx_bounds links 0 x hx
    have h' : i = .constr x.2 .idn ∨ i = .constr x.2 .lookCalls ∨ i = .constr x.2 .rider ∨
        i = .constr x.2 .small := by simpa using hi'
    exact Or.inr (Or.inl ⟨x.2, hb.1, by omega, h'⟩)

/-- The chain's places: the front, the segments, the four behind them; then the seal. -/
theorem flat_eq (links : List ModelPart) : flatPlaces true links true =
    ((frameAt none 0 :: midFrom links 0) ++ back4) ++ [sealP] := rfl

/-- What is open behind the front and the segments. -/
def behindSegs (links : List ModelPart) : List Item :=
  runRows ((midFrom links 0).map (rowOf links)) (stepOpen (start links) {})

theorem run_front (links : List ModelPart) (bp : List Place) :
    runRows (((frameAt none 0 :: midFrom links 0) ++ bp).map (rowOf links)) (start links) =
      runRows (bp.map (rowOf links)) (behindSegs links) := by
  rw [List.map_append, run_append]
  all_goals rfl

/-- **From above: behind a stretch bp of the blocks behind the last segment.** -/
theorem five_behind (links : List ModelPart) (k : Nat) (hn : links.length = k + 1) (bp : List Place)
    (hr : bp.map (rowOf links) = bp.map (backRow links.length))
    (hf : ∀ p ∈ bp, IsMap (sh k) (backRow (k + 1) p) (backRow 1 p))
    (he : ∀ j ∈ runRows (bp.map (backRow 1)) LB, j = Item.pileOne ∨ j = Item.pinV) :
    ∀ i ∈ runRows (((frameAt none 0 :: midFrom links 0) ++ bp).map (rowOf links)) (start links),
      i = Item.unmarked ∨ i = Item.pinW ∨ i = Item.pinI ∨ i = Item.pinV ∨ i = Item.pileOne := by
  rw [run_front, hr, hn]
  have h0 : Inv links.length 0 (stepOpen (start links) {}) := by
    intro i hi
    rcases mem_step_elim hi with ⟨hO, _⟩ | ho
    · exact inv_start links i hO
    · cases ho
  have h1 : Inv links.length (0 + links.length) (behindSegs links) :=
    segs_step links links.length links 0 _ (fun t sub h => by rwa [Nat.zero_add]) h0
  rw [Nat.zero_add, hn] at h1
  have prem : ∀ i ∈ behindSegs links,
      (i = Item.unmarked ∨ i = Item.pinW ∨ i = Item.pinI) ∨ ∃ j ∈ LB, i = sh k j := by
    intro i hi
    rcases h1 i hi with (e | e | e | e) | ⟨q, hq1, hq2, _⟩ | ⟨k', hk, hc⟩
    · exact Or.inl (Or.inl e)
    · exact Or.inl (Or.inr (Or.inl e))
    · exact Or.inl (Or.inr (Or.inr e))
    · exact Or.inr ⟨.pile, by decide, e⟩
    · omega
    · have e : k' = k := by omega
      subst e
      rcases hc with rfl | rfl
      · exact Or.inr ⟨.carry 0, by decide, rfl⟩
      · exact Or.inr ⟨.pinKept 0, by decide, rfl⟩
  intro i hi
  rcases sim_rows (sh k) (fun i => i = Item.unmarked ∨ i = Item.pinW ∨ i = Item.pinI)
    (backRow (k + 1)) (backRow 1) bp _ LB hf prem i hi with (e | e | e) | ⟨j, hj, e⟩
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr (Or.inl e))
  · rcases he j hj with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))

/-- The index masks' pin is open behind the segments of a list that is not empty. -/
theorem pinI_behind (s : ModelPart) (l : List ModelPart) : Item.pinI ∈ behindSegs (s :: l) := by
  unfold behindSegs
  rw [midFrom_cons, List.map_append, run_append, rows_link (s :: l) 0 s (by simp)]
  refine pinI_segs (s :: l) l 0 _ (fun t sub hts => ?_) ?_
  · rw [show 0 + 1 + t = t + 1 by omega]
    simpa using hts
  · exact lays_map id .pinI rfl (fun _ h => h) (segRow s 0) (segRow s 0) (pieces s) false _
      (fun _ _ => isMap_id _) (fun h => by cases h) (lay0 s)

theorem endOpen_eq (links : List ModelPart) : endOpen links =
    runRows (((frameAt none 0 :: midFrom links 0) ++ (back4 ++ [sealP])).map (rowOf links))
      (start links) := by
  have h := openSets_at links (flatPlaces true links true) [] (start links)
  rw [List.append_nil] at h
  unfold endOpen
  rw [h, flat_eq, List.append_assoc]
  all_goals rfl

theorem sealOpen_eq (links : List ModelPart) : sealOpen links =
    runRows (((frameAt none 0 :: midFrom links 0) ++ back4).map (rowOf links)) (start links) := by
  have h := openSets_at links ((frameAt none 0 :: midFrom links 0) ++ back4) [sealP] (start links)
  unfold sealOpen
  rw [flat_eq, show (((frameAt none 0 :: midFrom links 0) ++ back4) ++ [sealP]).length - 1 =
    ((frameAt none 0 :: midFrom links 0) ++ back4).length by
      simp only [List.length_append, List.length_cons, List.length_nil]; omega, h]
  all_goals rfl

end OpenEnd

open OpenEnd in
/-- **(D′a).** -/
theorem endOpenOnly : EndOpenOnly := by
  intro links hl
  cases links with
  | nil => exact absurd hl (by decide)
  | cons s l =>
    rw [endOpen_eq]
    exact five_behind (s :: l) l.length rfl _ (rows_back5 _) (isMap_back5 _) back_end5

open OpenEnd in
/-- **(D′b).** -/
theorem endOpenPins : EndOpenPins := by
  intro links hl
  cases links with
  | nil => exact absurd hl (by decide)
  | cons s l =>
    rw [endOpen_eq, run_front, rows_back5]
    exact ⟨lays_map (sh l.length) .pinV rfl (sh_pinV _) (VerifiableInference.Desc.First.backRow
        (l.length + 1)) (VerifiableInference.Desc.First.backRow 1) (back4 ++ [sealP]) false _
        (isMap_back5 _) (fun h => by cases h) layV,
      lays_map (sh l.length) .pinI rfl (sh_pinI _) (VerifiableInference.Desc.First.backRow
        (l.length + 1)) (VerifiableInference.Desc.First.backRow 1) (back4 ++ [sealP]) true _
        (isMap_back5 _) (fun _ => pinI_behind s l) layI⟩

open OpenEnd in
/-- **(D′c).** -/
theorem sealOpenOnly : SealOpenOnly := by
  intro links hl
  cases links with
  | nil => exact absurd hl (by decide)
  | cons s l =>
    rw [sealOpen_eq]
    exact five_behind (s :: l) l.length rfl _ (rows_back4 _) (isMap_back4 _) back_end4

end VerifiableInference.Desc.K13.Law
