-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/OnAFree.lean
(kind K9's soundness lemma; the law of a link on the road of moves): THEOREMS: THE BOOK-KEEPING IN
FRONT OF THE BATCHING (k9OnA, Law/Borders.lean) NEED NOT BE PROMISED: EVERY CLAUSE OF IT IS A TEST
THAT THE DRAW ITSELF MAKES. Where a clause fails the first piece has no yes, and nothing is to be
shown.
  yes_onA       **a yes of a block that is a draw with moves behind it gives k9OnA of the state in
                front** (by Law/OnLemmas.lean: drawnClean_tests: the draw's own tests are the
                promise's seven clauses; that K9's lens gives a part there stands in DrawMoves;
                OnLemmas' onA_of_draw says the like of the draw's block alone).
  goodIn_of_yes a piece that is good under "on and D" is good under "on" alone, if each of its
                yeses gives D of the statement in front.
  inMoves_light **THE JOINING WITH BOTH TAKEN OUT OF THE PROMISE**: k9OnA (by the draw's own yes)
                and a public sentence C on the fixed part (by Law/RowsNumber.lean: inMoves_rows).
                JoinAsks is asked at "Ok and C" and "on0 and k9OnA and C"; the row is had at on0
                alone. OF hready THERE IS THEN LEFT TO PROMISE: on0 a -> Ok (fixed9 phi a.1).
Not claimed: Ok at any state; hR1, hR2, hR3 (Law/RowsRide.lean pays them under duties).

-/
import Johnson.Desc.First.Batch.Law.OnLemmas
import Johnson.Desc.First.Batch.Law.RowsNumber

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (onJ relJ JoinAsks)
open _root_.Run.PQ (CK)
open _root_.Run (ckP)
open _root_.Iop (Doomed)

/-- **A yes of a draw with moves behind it gives the book-keeping in front.** -/
theorem yes_onA {Cl : Type} (p : Where) (ms : List (Move S)) (b : Block S Cl)
    (hb : DrawMoves atS p ms b) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S)
    (k : ℕ) (h : b.step ft s rs cols = .ok (s', k)) : k9OnA s = true := by
  obtain ⟨r, x, a, o, cls, _, _, ha, ho, _⟩ := hb ft s rs cols s' k h
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, _⟩ := drawnClean_tests _ _ _ _ _ _ _ ho
  simp [k9OnA, ha, c1, c2, c3, c4, c5, c6, c7]

variable {α W Cl : Type} {F : Frame}

/-- A condition that each yes of the piece gives need not be promised. -/
theorem goodIn_of_yes {C : CK} (q : Piece C F S Cl W) (on on' D : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop) (g : q.GoodIn (fun a => on a ∧ D a) on' R R')
    (hD : ∀ a τ b, on a → q.ior.red.out a τ = some b → D a) : q.GoodIn on on' R R' := by
  intro a ha
  by_cases hd : D a
  · exact g a ⟨ha, hd⟩
  · exact Doomed.of_forall _ _ fun τ b hout => absurd (hD a τ b ha hout) hd

/-- **The joining with the book-keeping and a public sentence taken out of the promise.** -/
theorem inMoves_light (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)) (d N j : ℕ) (b₁ b₂ b₃ : Block S Cl)
    (pb pq pe : Piece (ckP .two) F S Cl W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (H : JoinAsks φ (fun q => Ok q ∧ C q) Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe
      (fun a => (on0 a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1)) on1 on2 on3 tabOf ctx)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hR1 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', on1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → Rw a) :
    EachGoodIn (onJ on0 on1 on2 on3 j) (relJR (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx Rw j) j
      [pb, pq, pe] := by
  obtain ⟨g1, g2, g3, _⟩ := inMoves_rows C Rw φ Ok Fu p pw ms₁ ms₂ d N j b₁ b₂ b₃ pb pq pe
    (fun a => on0 a ∧ k9OnA a.1 = true) on1 on2 on3 tabOf ctx H
    (fun a τ b' ha => h01 a τ b' ha.1) (fun a τ b' ha => hR1 a τ b' ha.1) hR2 hR3
  have o0 : ∀ x : S × F.E.Str → Prop, onJ x on1 on2 on3 j j = x := fun x => by
    funext a
    simp [onJ]
  have o1 : ∀ x : S × F.E.Str → Prop, onJ x on1 on2 on3 j (j + 1) = on1 := fun x => by
    funext a
    simp [onJ]
  have o2 : ∀ x : S × F.E.Str → Prop, onJ x on1 on2 on3 j (j + 1 + 1) = on2 := fun x => by
    funext a
    unfold onJ
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
  have o3 : ∀ x : S × F.E.Str → Prop, onJ x on1 on2 on3 j (j + 1 + 1 + 1) = on3 := fun x => by
    funext a
    unfold onJ
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  rw [o0, o1] at g1
  rw [o1, o2] at g2
  rw [o2, o3] at g3
  refine ⟨?_, ?_, ?_, trivial⟩
  · rw [o0, o1]
    refine goodIn_of_yes pb on0 on1 (fun a => k9OnA a.1 = true) _ _ g1 fun a τ b _ hout => ?_
    obtain ⟨_, _, hfold⟩ := Piece.out_below H.hpb hout
    obtain ⟨k, hs⟩ := fold_one hfold
    exact yes_onA p _ b₁ H.hb₁ _ _ _ _ _ k hs
  · rw [o1, o2]
    exact g2
  · rw [o2, o3]
    exact g3

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.yes_onA
#print axioms VerifiableInference.Desc.K9L.goodIn_of_yes
#print axioms VerifiableInference.Desc.K9L.inMoves_light
