-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/KeepsTl.lean
(kind K9's soundness lemma; on another house's ask): THEOREMS: K9's LENS's WRITING LEAVES THE
SMALLNESS TEST's RECORD AND THE LINK's LIST OF TABLES. So Law/KeepsField.lean's machine (moves_keep,
drawMoves_keep, isMoves_keep, equation_keep, join_keeps), which is general in the field f and asks
"hset: the lens's writing leaves f", can be called at these two fields.
  tl_set, funs_set   the two fields behind atS.set.
  tlFuns_set    hset at f := fun s => (s.tl?, s.funs?).
  tl_putLink, funs_putLink   the same behind S.putLink (for "shut": shut_keep's hput).
  batch_tl      **the seated batching's form (one adding behind the draw)**: the block's own two
                writings, the draw's and the adding's, leave both fields: behind the block they are
                what the gatherer left, and the gatherer was called at the two fields of the record
                in front. (THE PAIR IS NOT KEPT OVER THE WHOLE BLOCK: the gatherer runs
                "K8.equations", which writes the record.)
  add_keepsFuns the list of tables alone is kept over a draw with moves behind it, where each move
                leaves it.
WHERE THE PAIR CAN BE CALLED AS IT STANDS (tlFuns_set, the two putLink lemmas): at the one
equation's block (equation_keep) and at "shut" (shut_keep): no run stands in them.
Not claimed: that any run of any kind leaves either field (MoveKeeps at each move is a premise).

-/
import Johnson.Desc.First.Batch.Law.KeepsField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.First (S)

theorem tl_set (s : S) (a : K9.Part) : (atS.set s a).tl? = s.tl? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [atS, S.putLink, S.putFork, S.tl?, ho]
  | _ => rfl

theorem funs_set (s : S) (a : K9.Part) : (atS.set s a).funs? = s.funs? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [atS, S.putLink, S.putFork, S.funs?, ho]
  | _ => rfl

/-- hset at the two fields. -/
theorem tlFuns_set (s : S) (a : K9.Part) :
    ((atS.set s a).tl?, (atS.set s a).funs?) = (s.tl?, s.funs?) := by
  rw [tl_set, funs_set]

theorem tl_putLink (s : S) (L : LinkCtx) : (s.putLink L).tl? = s.tl? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putLink, S.tl?, ho]
  | _ => rfl

theorem funs_putLink (s : S) (L : LinkCtx) : (s.putLink L).funs? = s.funs? := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putLink, S.funs?, ho]
  | _ => rfl

/-- **The seated batching's form, one adding behind the draw: THE BLOCK's OWN TWO WRITINGS (the
draw's and the adding's) LEAVE THE TWO FIELDS**: behind the block they are what the gatherer g left,
and g was called at a record with the two fields of the record in front. -/
theorem batch_tl {Cl : Type} (p : Where) (g : S → Except String (List Claim × S)) (b : Block S Cl)
    (hb : DrawMoves atS p [.add g] b) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (s' : S) (k : ℕ) (h : b.step ft s rs cols = .ok (s', k)) :
    ∃ s₀ e cls, s₀.tl? = s.tl? ∧ s₀.funs? = s.funs? ∧ g s₀ = .ok (cls, e) ∧
      s'.tl? = e.tl? ∧ s'.funs? = e.funs? := by
  obtain ⟨r, x, a, o, cls, _, _, _, _, u, c, c', ⟨e, q, G, hg, _, _, hu⟩, ⟨hs', _⟩, _⟩ :=
    hb ft s rs cols s' k h
  refine ⟨_, e, c, tl_set s _, funs_set s _, hg, ?_, ?_⟩
  · rw [hs', hu, tl_set]
  · rw [hs', hu, funs_set]

/-- **The list of tables stays over a draw with moves behind it**, where each move leaves it. -/
theorem add_keepsFuns {Cl : Type} (p : Where) (ms : List (Move S)) (b : Block S Cl)
    (hb : DrawMoves atS p ms b) (hms : ∀ m ∈ ms, MoveKeeps (fun s : S => s.funs?) m) (ft : ℕ)
    (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b.step ft s rs cols = .ok (s', k)) : s'.funs? = s.funs? :=
  drawMoves_keep (fun s : S => s.funs?) funs_set p ms b hb hms ft s rs cols s' k h

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.tlFuns_set
#print axioms VerifiableInference.Desc.K9L.batch_tl
#print axioms VerifiableInference.Desc.K9L.add_keepsFuns
