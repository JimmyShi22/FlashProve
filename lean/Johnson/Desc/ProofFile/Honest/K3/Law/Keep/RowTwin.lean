-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/RowTwin.lean: two rows of parts that stand pair by pair,
one whose parts pass something on and one whose parts pass nothing on: where each pair shows the
same rounds at every state that satisfies an invariant, and each part of the first row carries the
invariant on, the two rows played alone show the same rounds. Conditional on `RowSame`, which is the
list of these hypotheses. General in the parts: no sub-protocol is named. Definitions that the
statements need, and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a part played alone is `alone`
(Honest/SumLaw/Terms.lean); a row played alone is `aloneRow`, the state behind a part's moves
`endFrom`, behind a row's `endRow` (Honest/K3/Law/PlayPart.lean). The invariant speaks of the
challenges heard and of what is passed on; the input w is fixed.

What is defined.
  `RowRel Rel`: the coins of two rows stand in the relation Rel pair by pair. No coin is moved from
    one type to the other.
  `PairSame w I I' p q Rel`: the hypotheses on one pair. As many moves; at coins in the relation and
    at every state with I in front, p and q played alone show the same; behind p's moves I' holds.
  `RowSame w Rel Inv j ps qs`: `PairSame` at each pair: the pair number i of the two lists at Inv (j
    + i) in front and Inv (j + i + 1) behind.

What is shown.
  `endFrom_input`, `endFrom_heard`, `endFrom_eq`: moves leave the input as it is and lay their
    challenges behind those heard. `endRow_input`, `endRow_heard`, `endRow_eq`: the same of a row.
  `RowSame.length`: the two rows have as many parts. `RowSame.moves`: and as many moves.
  `aloneRow_twin`: **the two rows played alone show the same rounds.** Conditional on `RowSame`.
  `endRow_twin`: behind the first row the invariant holds at the number behind the last part.
    Conditional on `RowSame`.
  `rowSame_zipIdx`: `RowSame` of two rows that are made of one numbered list, from `PairSame` at
    each of its members.
  `rowRel_total_zipIdx`: for such rows: where each pair has, for all coins of its first part, coins
    of its second in the relation, so have the rows.

Hypotheses that remain. `RowSame`: whoever calls the theorems shows `PairSame` of each pair. Makers
of `PairSame` for three sorts of parts: Honest/K3/Law/Keep/Bridge.lean. A pair of rows at which it
holds, and one at which it holds at no invariant and the rounds differ:
Honest/K3/Law/Keep/RowTwinToy.lean [not in this library]. In the plain facts: `h`: as many
challenges as moves; `h1`, `h2`: (in `state_eq`) the state's input and what it has heard.

Imported. Honest/K3/Law/SumFits.lean, for `endFrom_unit`, and through it
Honest/K3/Law/PlayPart.lean.

Users. Honest/K3/Law/Keep/Bridge.lean imports this file, and through it
Honest/K3/Law/Keep/RowKeepLaw.lean.

Limits. The second row's parts pass nothing on (their own state is `Unit`). The hypothesis `rounds`
of `PairSame` is asked at all that was shown (every list of rounds, every value of the columns
opened) and at every list of challenges, not along a run alone.
Whether a pair has coins in the relation is a hypothesis of `rowRel_total_zipIdx`. Nothing is said
on stops or on the shapes of messages.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SumFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open ProofFile.Honest.SumLaw (alone aloneFrom)

variable {V W X C : Type}

/-! ## 1 The state behind moves, behind a row -/

/-- Moves leave the input as it is. -/
theorem endFrom_input : ∀ (ms : List (Move C W X)) (t : State W X) (ds : List Fmt.Drawn),
    (endFrom ms t ds).input = t.input
  | [], _, _ => rfl
  | _ :: _, _, [] => rfl
  | mv :: ms, t, d :: ds => by
    show (endFrom ms { t.hears d with own := mv.hand (t.hears d) } ds).input = _
    rw [endFrom_input ms]
    rfl

/-- Behind as many challenges as there are moves, these are laid behind those heard. -/
theorem endFrom_heard : ∀ (ms : List (Move C W X)) (t : State W X) (ds : List Fmt.Drawn),
    ds.length = ms.length → (endFrom ms t ds).heard = t.heard ++ ds
  | [], _, [], _ => (List.append_nil _).symm
  | mv :: ms, t, d :: ds, h => by
    show (endFrom ms { t.hears d with own := mv.hand (t.hears d) } ds).heard = _
    rw [endFrom_heard ms _ ds (by simp only [List.length_cons] at h; omega)]
    show (t.heard ++ [d]) ++ ds = _
    rw [List.append_assoc]
    rfl
  | [], _, _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega

/-- A state, of its input and of what it has heard. -/
theorem state_eq (t : State W X) {i : W} {hd : List Fmt.Drawn} (h1 : t.input = i)
    (h2 : t.heard = hd) : t = ⟨i, hd, t.own⟩ := by
  subst h1
  subst h2
  rfl

/-- The two as one equation. -/
theorem endFrom_eq (ms : List (Move C W X)) (t : State W X) (ds : List Fmt.Drawn)
    (h : ds.length = ms.length) :
    endFrom ms t ds = ⟨t.input, t.heard ++ ds, (endFrom ms t ds).own⟩ :=
  state_eq _ (endFrom_input ms t ds) (endFrom_heard ms t ds h)

/-- A row's moves leave the input as it is. -/
theorem endRow_input : ∀ (ps : List (Part V W X)) (t : State W X) (ds : List Fmt.Drawn),
    (endRow ps t ds).input = t.input
  | [], _, _ => rfl
  | p :: ps, t, ds => by
    show (endRow ps (endFrom p.moves t (ds.take p.moves.length)) (ds.drop p.moves.length)).input = _
    rw [endRow_input ps, endFrom_input]

/-- Behind as many challenges as the row has moves, these are laid behind those heard. -/
theorem endRow_heard : ∀ (ps : List (Part V W X)) (t : State W X) (ds : List Fmt.Drawn),
    ds.length = (ps.map (·.moves.length)).sum → (endRow ps t ds).heard = t.heard ++ ds
  | [], _, [], _ => (List.append_nil _).symm
  | [], _, _ :: _, h => by simp at h
  | p :: ps, t, ds, h => by
    simp only [List.map_cons, List.sum_cons] at h
    show (endRow ps (endFrom p.moves t (ds.take p.moves.length)) (ds.drop p.moves.length)).heard = _
    rw [endRow_heard ps _ _ (by rw [List.length_drop]; omega),
      endFrom_heard p.moves t _ (by rw [List.length_take]; omega), List.append_assoc,
      List.take_append_drop]

/-- The two as one equation. -/
theorem endRow_eq (ps : List (Part V W X)) (t : State W X) (ds : List Fmt.Drawn)
    (h : ds.length = (ps.map (·.moves.length)).sum) :
    endRow ps t ds = ⟨t.input, t.heard ++ ds, (endRow ps t ds).own⟩ :=
  state_eq _ (endRow_input ps t ds) (endRow_heard ps t ds h)

/-! ## 2 The hypotheses -/

/-- **The coins of two rows stand in a relation pair by pair.** Rel: the relation, for each pair of
parts. Rows of different lengths: false. -/
def RowRel (Rel : (p : Part V W X) → (q : Part V W Unit) → p.Coins → q.Coins → Prop) :
    (ps : List (Part V W X)) → (qs : List (Part V W Unit)) → RowCoins ps → RowCoins qs → Prop
  | [], [], _, _ => True
  | p :: ps, q :: qs, c, c' => Rel p q c.1 c'.1 ∧ RowRel Rel ps qs c.2 c'.2
  | _, _, _, _ => False

/-- **The hypotheses on one pair.** A definition, meant as a hypothesis. w: the input. I: the
invariant in front of the pair: of the challenges heard and of what is passed on. I': behind it.
Rel: the relation in which the two parts' coins stand. -/
structure PairSame (w : W) (I I' : List Fmt.Drawn → X → Prop) (p : Part V W X) (q : Part V W Unit)
    (Rel : p.Coins → q.Coins → Prop) : Prop where
  /-- as many moves -/
  len : p.moves.length = q.moves.length
  /-- played alone, at a state with I, the two show the same -/
  rounds : ∀ (c : p.Coins) (c' : q.Coins) (h : List Fmt.Drawn) (x : X) (seen : Seen)
    (ds : List Fmt.Drawn), Rel c c' → I h x →
    alone p c ⟨w, h, x⟩ seen ds = alone q c' ⟨w, h, ()⟩ seen ds
  /-- from a state with I, behind p's moves I' holds -/
  stays : ∀ (h : List Fmt.Drawn) (x : X) (ds : List Fmt.Drawn), I h x →
    ds.length = p.moves.length → I' (h ++ ds) (endFrom p.moves ⟨w, h, x⟩ ds).own

/-- **The hypotheses on two rows**: `PairSame` at each pair. A definition, meant as a hypothesis.
Inv n: the invariant in front of the part number n. j: the number of the lists' first parts. Rows of
different lengths: false. -/
def RowSame (w : W) (Rel : (p : Part V W X) → (q : Part V W Unit) → p.Coins → q.Coins → Prop)
    (Inv : Nat → List Fmt.Drawn → X → Prop) :
    Nat → List (Part V W X) → List (Part V W Unit) → Prop
  | _, [], [] => True
  | j, p :: ps, q :: qs =>
    PairSame w (Inv j) (Inv (j + 1)) p q (Rel p q) ∧ RowSame w Rel Inv (j + 1) ps qs
  | _, _, _ => False

section
variable {w : W} {Rel : (p : Part V W X) → (q : Part V W Unit) → p.Coins → q.Coins → Prop}
  {Inv : Nat → List Fmt.Drawn → X → Prop}

/-- The two rows have as many parts. -/
theorem RowSame.length : ∀ {j : Nat} {ps : List (Part V W X)} {qs : List (Part V W Unit)},
    RowSame w Rel Inv j ps qs → ps.length = qs.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, h => congrArg (· + 1) (RowSame.length h.2)
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

/-- The two rows have as many moves, part by part. -/
theorem RowSame.moves : ∀ {j : Nat} {ps : List (Part V W X)} {qs : List (Part V W Unit)},
    RowSame w Rel Inv j ps qs → ps.map (·.moves.length) = qs.map (·.moves.length)
  | _, [], [], _ => rfl
  | _, p :: ps, q :: qs, h => by
    rw [List.map_cons, List.map_cons, h.1.len, RowSame.moves h.2]
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

end

/-! ## 3 The two rows show the same rounds -/

/-- **Two rows that stand pair by pair, played alone, show the same rounds.** Conditional on
`RowSame`; at coins in the relation and at a state with the invariant in front of the first part. -/
theorem aloneRow_twin (w : W)
    (Rel : (p : Part V W X) → (q : Part V W Unit) → p.Coins → q.Coins → Prop)
    (Inv : Nat → List Fmt.Drawn → X → Prop) :
    ∀ (ps : List (Part V W X)) (qs : List (Part V W Unit)) (j : Nat), RowSame w Rel Inv j ps qs →
      ∀ (c : RowCoins ps) (c' : RowCoins qs), RowRel Rel ps qs c c' →
      ∀ (h : List Fmt.Drawn) (x : X) (seen : Seen) (ds : List Fmt.Drawn), Inv j h x →
      aloneRow ps c ⟨w, h, x⟩ seen ds = aloneRow qs c' ⟨w, h, ()⟩ seen ds
  | [], [], _, _, _, _, _, _, _, _, [], _ => rfl
  | [], [], _, _, _, _, _, _, _, _, _ :: _, _ => rfl
  | [], _ :: _, _, H, _, _, _, _, _, _, _, _ => H.elim
  | _ :: _, [], _, H, _, _, _, _, _, _, _, _ => H.elim
  | p :: ps, q :: qs, j, H, c, c', hc, h, x, seen, ds, hI => by
    have hp : PairSame w (Inv j) (Inv (j + 1)) p q (Rel p q) := H.1
    show (alone p c.1 ⟨w, h, x⟩ seen (ds.take p.moves.length)).bind (fun y =>
        (aloneRow ps c.2 (endFrom p.moves ⟨w, h, x⟩ (ds.take p.moves.length)) (seen.plus y)
          (ds.drop p.moves.length)).map (y ++ ·)) =
      (alone q c'.1 ⟨w, h, ()⟩ seen (ds.take q.moves.length)).bind fun y =>
        (aloneRow qs c'.2 (endFrom q.moves ⟨w, h, ()⟩ (ds.take q.moves.length)) (seen.plus y)
          (ds.drop q.moves.length)).map (y ++ ·)
    rw [← hp.len, hp.rounds c.1 c'.1 h x seen _ hc.1 hI]
    cases hal : alone q c'.1 ⟨w, h, ()⟩ seen (ds.take p.moves.length) with
    | none => rfl
    | some y =>
      have hq : (ds.take p.moves.length).length = q.moves.length :=
        (aloneFrom_length c'.1 q.moves _ seen _ y hal).1
      have hlen : (ds.take p.moves.length).length = p.moves.length := hq.trans hp.len.symm
      have e1 := endFrom_eq p.moves ⟨w, h, x⟩ (ds.take p.moves.length) hlen
      have e2 : endFrom q.moves ⟨w, h, ()⟩ (ds.take p.moves.length) =
          ⟨w, h ++ ds.take p.moves.length, ()⟩ := endFrom_unit q.moves _ _ hq
      show (aloneRow ps c.2 (endFrom p.moves ⟨w, h, x⟩ (ds.take p.moves.length)) (seen.plus y)
          (ds.drop p.moves.length)).map (y ++ ·) =
        (aloneRow qs c'.2 (endFrom q.moves ⟨w, h, ()⟩ (ds.take p.moves.length)) (seen.plus y)
          (ds.drop p.moves.length)).map (y ++ ·)
      rw [e2, e1]
      exact congrArg (Option.map (y ++ ·)) (aloneRow_twin w Rel Inv ps qs (j + 1) H.2 c.2 c'.2 hc.2
        _ _ _ _ (hp.stays h x _ hI hlen))

/-- **Behind the first row the invariant holds**, at the number behind the row's last part.
Conditional on `RowSame`. -/
theorem endRow_twin (w : W)
    (Rel : (p : Part V W X) → (q : Part V W Unit) → p.Coins → q.Coins → Prop)
    (Inv : Nat → List Fmt.Drawn → X → Prop) :
    ∀ (ps : List (Part V W X)) (qs : List (Part V W Unit)) (j : Nat), RowSame w Rel Inv j ps qs →
      ∀ (h : List Fmt.Drawn) (x : X) (ds : List Fmt.Drawn), Inv j h x →
      ds.length = (ps.map (·.moves.length)).sum →
      Inv (j + ps.length) (h ++ ds) (endRow ps ⟨w, h, x⟩ ds).own
  | [], [], j, _, h, x, [], hI, _ => by
    show Inv j (h ++ []) x
    rw [List.append_nil]
    exact hI
  | [], [], _, _, _, _, _ :: _, _, hl => by simp at hl
  | [], _ :: _, _, H, _, _, _, _, _ => H.elim
  | _ :: _, [], _, H, _, _, _, _, _ => H.elim
  | p :: ps, q :: qs, j, H, h, x, ds, hI, hl => by
    simp only [List.map_cons, List.sum_cons] at hl
    have hlen : (ds.take p.moves.length).length = p.moves.length := by
      rw [List.length_take]
      omega
    have e1 := endFrom_eq p.moves ⟨w, h, x⟩ (ds.take p.moves.length) hlen
    have ih := endRow_twin w Rel Inv ps qs (j + 1) H.2 (h ++ ds.take p.moves.length)
      (endFrom p.moves ⟨w, h, x⟩ (ds.take p.moves.length)).own (ds.drop p.moves.length)
      (H.1.stays h x _ hI hlen) (by rw [List.length_drop]; omega)
    have en : j + 1 + ps.length = j + (ps.length + 1) := by omega
    rw [en, List.append_assoc, List.take_append_drop] at ih
    show Inv (j + (ps.length + 1)) (h ++ ds)
      (endRow ps (endFrom p.moves ⟨w, h, x⟩ (ds.take p.moves.length))
        (ds.drop p.moves.length)).own
    rw [e1]
    exact ih

/-! ## 4 Rows that are made of one numbered list -/

/-- `RowSame` of two rows that are made of one numbered list: from `PairSame` at each member, at the
invariants of the member's number. -/
theorem rowSame_zipIdx {α : Type} (w : W)
    (Rel : (p : Part V W X) → (q : Part V W Unit) → p.Coins → q.Coins → Prop)
    (Inv : Nat → List Fmt.Drawn → X → Prop) (F : α × Nat → Part V W X)
    (G : α × Nat → Part V W Unit) :
    ∀ (l : List α) (j : Nat),
      (∀ y ∈ l.zipIdx j, PairSame w (Inv y.2) (Inv (y.2 + 1)) (F y) (G y) (Rel (F y) (G y))) →
      RowSame w Rel Inv j ((l.zipIdx j).map F) ((l.zipIdx j).map G)
  | [], _, _ => True.intro
  | a :: l, j, h => by
    have h0 := h (a, j) (by rw [List.zipIdx_cons]; exact List.mem_cons_self)
    have ht := rowSame_zipIdx w Rel Inv F G l (j + 1) fun y hy =>
      h y (by rw [List.zipIdx_cons]; exact List.mem_cons_of_mem _ hy)
    rw [List.zipIdx_cons, List.map_cons, List.map_cons]
    exact ⟨h0, ht⟩

/-- **Coins in the relation exist for such rows**, where they exist for each pair: for all coins of
the first row there are coins of the second that stand in the relation to them, pair by pair. Some
coins: not said to be a run's: never cited of a run; of a run cite the forms at lent coins
(`lotsSame_lent`, `lotsPlayed_lent`, `lotsWhole_lent`, Honest/K3/Law/Keep/LentLots.lean
[not in this library]). -/
theorem rowRel_total_zipIdx {α : Type}
    (Rel : (p : Part V W X) → (q : Part V W Unit) → p.Coins → q.Coins → Prop)
    (F : α × Nat → Part V W X) (G : α × Nat → Part V W Unit) :
    ∀ (l : List α) (j : Nat),
      (∀ y ∈ l.zipIdx j, ∀ c : (F y).Coins, ∃ c' : (G y).Coins, Rel (F y) (G y) c c') →
      ∀ c : RowCoins ((l.zipIdx j).map F),
        ∃ c' : RowCoins ((l.zipIdx j).map G), RowRel Rel _ _ c c'
  | [], _, _, _ => ⟨(), True.intro⟩
  | a :: l, j, h, c => by
    let c₀ : (F (a, j)).Coins × RowCoins ((l.zipIdx (j + 1)).map F) := c
    obtain ⟨c₁, h₁⟩ := h (a, j) (by rw [List.zipIdx_cons]; exact List.mem_cons_self) c₀.1
    obtain ⟨c₂, h₂⟩ := rowRel_total_zipIdx Rel F G l (j + 1)
      (fun y hy => h y (by rw [List.zipIdx_cons]; exact List.mem_cons_of_mem _ hy)) c₀.2
    exact ⟨((c₁, c₂) : (G (a, j)).Coins × RowCoins ((l.zipIdx (j + 1)).map G)), h₁, h₂⟩

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.rowRel_total_zipIdx
#print axioms ProofFile.Honest.K3.Law.endFrom_input
#print axioms ProofFile.Honest.K3.Law.endFrom_heard
#print axioms ProofFile.Honest.K3.Law.state_eq
#print axioms ProofFile.Honest.K3.Law.endFrom_eq
#print axioms ProofFile.Honest.K3.Law.endRow_input
#print axioms ProofFile.Honest.K3.Law.endRow_heard
#print axioms ProofFile.Honest.K3.Law.endRow_eq
#print axioms ProofFile.Honest.K3.Law.RowSame.length
#print axioms ProofFile.Honest.K3.Law.RowSame.moves
#print axioms ProofFile.Honest.K3.Law.aloneRow_twin
#print axioms ProofFile.Honest.K3.Law.endRow_twin
#print axioms ProofFile.Honest.K3.Law.rowSame_zipIdx
