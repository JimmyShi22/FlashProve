-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/TableTabs.lean
(kind K9's soundness lemma, Sound/FormsQ.lean): THEOREMS: AT THE TABLE's ONE
ACCESSOR (Law/AtTable.lean: tabAt) THE WITNESS's TABLES ARE THE SAME FUNCTION IN FRONT OF AND BEHIND
EACH OF K9's TWO PIECES: the row's hypotheses htabb and htab, and AtTable's hpart, paid down to ONE
DUTY MORE A RUN: it keeps the record's book of trees.
The accessor reads a record through its book and through its statement's numbers of row bits.
  tabQ_bits, book_part, book_set, tabAt_same   the tools.
  MoveBook, moves_book, drawMoves_book   the duty of a move; a row of moves, and a draw with moves
                behind it, keep the book (K9's own writings keep it: book_set).
  gather_book, steps_book   the duty of a step's moves from the like of each run and quiet move.
  tabAt_moves   htabb: a yes of a piece that holds a draw with moves keeps tabAt; and a part is
                there behind it (hpart).
  tabAt_equation   htab: a yes of the piece that holds the one equation's block keeps tabAt: the
                door lays a row and takes mask entries: neither turns a number of bits.
Not claimed: the duty of any real run.

-/
import Johnson.Desc.First.Batch.Law.AtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where RunOf Window gather)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-- The accessor reads a statement through its numbers of row bits alone. -/
theorem tabQ_bits (own : List (ℕ × ℕ)) (st st' : Statement) (book : TreeBook)
    (rd : ℕ × ℕ → MsgQ) (h : SameBits st st') : tabQ own st' book rd = tabQ own st book rd := by
  funext o part J
  unfold tabQ
  rw [(h o part).1]

/-- K9's part holds the record's own book. -/
theorem book_part (s : S) (a : K9.Part) (h : atS.get? s = some a) : a.d.book = s.book := by
  simp only [atS] at h
  obtain ⟨L, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨F, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tl, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨u, _, h⟩ := Option.bind_eq_some_iff.1 h
  rw [← Option.some.inj h]

/-- The lens's writing leaves the book. -/
theorem book_set (s : S) (a : K9.Part) : (atS.set s a).book = s.book := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [atS, S.putLink, S.putFork, ho]
  | _ => rfl

/-- The same book and the same numbers of bits: the same tables. -/
theorem tabAt_same (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (s s' : S) (a a' : K9.Part)
    (ha : atS.get? s = some a) (ha' : atS.get? s' = some a') (hbits : SameBits a.d.st a'.d.st)
    (hbook : s'.book = s.book) : tabAt own rd s' = tabAt own rd s := by
  simp only [tabAt, ha, ha']
  rw [book_part s' a' ha', book_part s a ha, hbook]
  exact tabQ_bits own _ _ _ rd hbits

/-- The duty of a move. -/
def MoveBook : Move S → Prop
  | .add g => ∀ e c e₁, g e = .ok (c, e₁) → e₁.book = e.book
  | .quiet h => ∀ e e₁, h e = .ok e₁ → e₁.book = e.book

theorem moves_book : ∀ (ms : List (Move S)), (∀ m ∈ ms, MoveBook m) →
    ∀ (e e' : S) (c : List Claim), MovesYes atS ms e e' c → e'.book = e.book
  | [], _, e, e', c, hy => by
    obtain ⟨rfl, _⟩ := hy
    rfl
  | m :: l, hms, e, e', c, hy => by
    obtain ⟨u, c₁, c₂, h1, h2, _⟩ := hy
    have i := moves_book l (fun q hq => hms q (List.mem_cons_of_mem _ hq)) u e' c₂ h2
    have hm := hms m List.mem_cons_self
    rw [i]
    cases m with
    | add g =>
      obtain ⟨e₁, s, G, hg, _, _, rfl⟩ := h1
      rw [book_set]
      exact hm e c₁ e₁ hg
    | quiet h => exact hm e u h1.1

/-- A draw with moves behind it keeps the book. -/
theorem drawMoves_book {Cl : Type} (p : Where) (ms : List (Move S)) (b : Block S Cl)
    (hb : DrawMoves atS p ms b) (hms : ∀ m ∈ ms, MoveBook m) (ft : ℕ) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s' : S) (k : ℕ) (h : b.step ft s rs cols = .ok (s', k)) :
    s'.book = s.book := by
  obtain ⟨r, x, a, o, cls, _, _, _, _, hy⟩ := hb ft s rs cols s' k h
  rw [moves_book ms hms _ _ _ hy, book_set]

/-- A gathering keeps the book if each of its runs does. -/
theorem gather_book (ws : S → List Window) (cut : List (Nat × String)) :
    ∀ (runs : List (RunOf S)), (∀ r ∈ runs, ∀ n e c e₁, r.2 n e = .ok (c, e₁) → e₁.book = e.book) →
      ∀ x x' : List Claim × S, runs.foldlM (gstep ws cut) x = .ok x' → x'.2.book = x.2.book
  | [], _, x, x', h => by
    have e : x = x' := Except.ok.inj h
    rw [e]
  | r :: l, hr, x, x', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨z, hz, h⟩ := ok_bind h
    obtain ⟨c, e, hc, rfl⟩ := gstep_ok hz
    rw [gather_book ws cut l (fun r' h' => hr r' (List.mem_cons_of_mem _ h')) _ _ h]
    exact hr r List.mem_cons_self _ _ _ _ hc

/-- The duty of the steps' moves, from one duty a run. -/
theorem steps_book {P K : Type} (l : List (Step S P K))
    (hr : ∀ r ∈ runsOf l, ∀ n e c e₁, r.run.2 n e = .ok (c, e₁) → e₁.book = e.book)
    (hq : ∀ s ∈ l, ∀ e e₁, s.behind e = .ok e₁ → e₁.book = e.book) :
    ∀ m ∈ (movesOf l).map (·.move), MoveBook m := by
  intro m hm
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hm
  obtain ⟨s, hs, hm1⟩ := List.mem_flatMap.1 hm0
  simp only [Step.moves, List.mem_cons, List.mem_nil_iff, or_false] at hm1
  rcases hm1 with rfl | rfl
  · intro e c e₁ h
    rw [gather_eq] at h
    exact gather_book s.ws s.cut (s.runs.map (·.run)) (fun r hr' => by
      obtain ⟨r0, h0, rfl⟩ := List.mem_map.1 hr'
      exact hr r0 (List.mem_flatMap.2 ⟨s, hs, h0⟩)) ([], e) (c, e₁) h
  · exact hq s hs

variable {W Cl : Type} {C : CK} {F : Frame}

/-- **htabb and hpart**: along a piece that holds a draw with moves behind it. -/
theorem tabAt_moves (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (p : Where) (ms : List (Move S))
    (b : Block S Cl) (hb : DrawMoves atS p ms b) (hkd : ∀ m ∈ ms, MoveDoor atS m)
    (hbk : ∀ m ∈ ms, MoveBook m) (pb : Piece C F S Cl W) (hpb : pb.b = below b)
    (a b' : S × F.E.Str) (τ : _root_.Iop.Tr (uLT C pb.ds)) (hout : pb.ior.red.out a τ = some b') :
    tabAt own rd b'.1 = tabAt own rd a.1 ∧ (atS.get? b'.1).isSome = true := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨h1, h2⟩ := drawMoves_door atS (fun s a h => by
    obtain ⟨a', e0, _, e2, e3⟩ := atS_reads s a h
    exact ⟨a', e0, e2, e3⟩) p ms b hb hkd _ _ _ _ _ _ hs
  obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨a1, ha1, _, d1⟩ := h2 a0 ha0
  refine ⟨tabAt_same own rd a.1 b'.1 a0 a1 ha0 ha1 ?_
    (drawMoves_book p ms b hb hbk _ _ _ _ _ _ hs), by simp [ha1]⟩
  rw [d1]
  exact SameBits.refl _

/-- **htab**: along the piece that holds the one equation's block. -/
theorem tabAt_equation (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → MsgQ) (pw : Where)
    (pe : Piece C F S Cl W) (hpe : pe.b = below (K9.oneEquation atS pw)) (a b' : S × F.E.Str)
    (τ : _root_.Iop.Tr (uLT C pe.ds)) (hout : pe.ior.red.out a τ = some b') :
    tabAt own rd b'.1 = tabAt own rd a.1 := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨a0, out, ha0, hdoor, hs'⟩ := oneEquation_inv atS pw _ _ _ _ _ k hs
  obtain ⟨n, q, G, row, d1, _, _, _, hrow, hd, _, _⟩ := door_parts _ _ _ _ _ out hdoor
  obtain ⟨a1, ha1, _, _, e3⟩ :=
    atS_reads a.1 { a0 with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha0])
  rw [← hs'] at ha1
  have hst : a1.d.st = out.d.st := e3
  refine tabAt_same own rd a.1 b'.1 a0 a1 ha0 ha1 ?_ (by rw [hs', book_set])
  rw [hst, hd]
  exact (asRow_bits _ _ _ _ _ _ hrow).trans (withRow_bits _ _ _)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.tabAt_same
#print axioms VerifiableInference.Desc.K9L.drawMoves_book
#print axioms VerifiableInference.Desc.K9L.steps_book
#print axioms VerifiableInference.Desc.K9L.tabAt_moves
#print axioms VerifiableInference.Desc.K9L.tabAt_equation
