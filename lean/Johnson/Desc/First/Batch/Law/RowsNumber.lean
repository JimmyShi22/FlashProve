-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/RowsNumber.lean
(kind K9's soundness lemma; the law of a link on the road of moves): THEOREMS: THE NUMBER UNDER THE
TEST ON THE EXPONENTS ("the plan's claims and the ties' and reads' indices are at most the rows of
the batching element's round": plan + top <= rows) NEED NOT BE PROMISED IN FRONT OF THE BATCHING: IT
CAN RIDE BACKWARD IN THE CONTEXT, AND THE DOOR's OWN YES GIVES IT.
No text tests that number in front of the draw; the door tests the equality behind it
("K9.rows-counted"). The joining's hypothesis (LinkJoin.JoinAsks) asks hok wherever the promise Ok
holds of the fixed part, and hready asks Ok at every state with on0: so the number would have to be
promised there.
  inMoves_under   **THE JOINING, WITH A PUBLIC SENTENCE C ON THE FIXED PART TAKEN OUT OF THE
                PROMISE.** JoinAsks is asked at the letters "Ok and C", "on0 and C"; the row is had
                at on0 ALONE, if the context behind the first piece gives C of the state in front
                (hC). NO CLAUSE OF JoinAsks TURNS: it is a corollary of inMoves. Why: at a
                state with on0 of which C fails no witness has the context behind any yes of the
                first piece: the relation behind holds of nobody, and nothing is to be shown.
  relJR, inMoves_rows   **THE SAME WITHOUT THE CONTEXT**: a public sentence Rw on the statement
                stands beside the joining's relations AT THE TWO INNER BOUNDARIES ALONE: the first
                piece takes it behind itself (there it gives C in front: hR1), the second hands it
                backward (hR2), THE THIRD PROVES IT FROM ITS OWN YES (hR3). In front of the three
                and behind them the relations are the joining's own: nobody else carries anything.
  rowsFit       the sentence: plan + top8 <= rows, read off the fixed part.
  termsOk_le    the test on the exponents grows with d.
  door_rows     **A YES OF THE ONE EQUATION's STEP GIVES THE NUMBER, AS AN EQUATION**: where the
                rows owed are "rows" and the indices laid are "top": rows = the plan's claims + top.
                (By door_counts, Johnson/Meaning/K8Rows.lean.)
Not claimed: hC at a segment of the protocol; who carries the sentence from the door back to the
first piece (the context's clauses hcq, hce of JoinAsks, at a context that holds it).

-/
import Johnson.Meaning.K8Rows
import Johnson.Desc.First.Batch.Law.JoinMoves
import Johnson.Desc.First.Batch.Law.K8Disc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.LinkJoin (onJ relJ JoinAsks)
open _root_.Run (ckP)
open _root_.Iop (Doomed)

variable {α W Cl : Type} {F : Frame}

/-- **The joining, with a public sentence on the fixed part taken out of the promise.** -/
theorem inMoves_under (C : α × Option Pub9 → Prop) (φ : S → α) (Ok : α × Option Pub9 → Prop)
    (Fu : S → Prop) (p pw : Where) (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E))
    (d N j : ℕ) (b₁ b₂ b₃ : Block S Cl) (pb pq pe : Piece (ckP .two) F S Cl W)
    (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (H : JoinAsks φ (fun q => Ok q ∧ C q) Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe
      (fun a => on0 a ∧ C (fixed9 φ a.1)) on1 on2 on3 tabOf ctx)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hC : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → ctx b' w → C (fixed9 φ a.1)) :
    EachGoodIn (onJ on0 on1 on2 on3 j) (relJ (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx j) j
      [pb, pq, pe] := by
  obtain ⟨g1, g2, g3, _⟩ := inMoves α W Cl F φ (fun q => Ok q ∧ C q) Fu p pw ms₁ ms₂ d N j b₁ b₂
    b₃ pb pq pe (fun a => on0 a ∧ C (fixed9 φ a.1)) on1 on2 on3 tabOf ctx H
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
  have r1 : ∀ b w, relJ (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx j (j + 1) b w → ctx b w := fun b w h => by
    simp only [relJ, Nat.add_eq_left, Nat.succ_ne_zero, if_false, if_true] at h
    exact h.2
  rw [o0, o1] at g1
  rw [o1, o2] at g2
  rw [o2, o3] at g3
  refine ⟨?_, ?_, ?_, trivial⟩
  · rw [o0, o1]
    intro a ha
    by_cases hc : C (fixed9 φ a.1)
    · exact g1 a ⟨ha, hc⟩
    · exact Doomed.of_forall _ _ fun τ b hout =>
        ⟨h01 a τ b ha hout, fun w hw => absurd (hC a τ b w ha hout (r1 b w hw)) hc⟩
  · rw [o1, o2]
    exact g2
  · rw [o2, o3]
    exact g3

/-- The joining's relations, with a public sentence Rw on the statement beside them at the two inner
boundaries. -/
def relJR (O : Others S (α × Option Pub9) Cb.Gl.E)
    (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)) (N : ℕ)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (Rw : S × F.E.Str → Prop) (j : ℕ) : ℕ → S × F.E.Str → W → Prop := fun i a w =>
  relJ O ms₁ ms₂ N tabOf ctx j i a w ∧ (i = j + 1 ∨ i = j + 2 → Rw a)

/-- **THE SAME WITHOUT THE CONTEXT: THE PUBLIC SENTENCE STANDS IN THE RELATIONS AT THE TWO INNER
BOUNDARIES ALONE.** The first piece takes it behind itself (hR1: there it gives C in front); the
second hands it backward (hR2); THE THIRD PROVES IT FROM ITS OWN YES (hR3). In front of the three
and behind them the relations are the joining's own. -/
theorem inMoves_rows (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)) (d N j : ℕ) (b₁ b₂ b₃ : Block S Cl)
    (pb pq pe : Piece (ckP .two) F S Cl W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (H : JoinAsks φ (fun q => Ok q ∧ C q) Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe
      (fun a => on0 a ∧ C (fixed9 φ a.1)) on1 on2 on3 tabOf ctx)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hR1 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', on1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → Rw a) :
    EachGoodIn (onJ on0 on1 on2 on3 j) (relJR (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx Rw j) j
      [pb, pq, pe] := by
  obtain ⟨g1, g2, g3, _⟩ := inMoves α W Cl F φ (fun q => Ok q ∧ C q) Fu p pw ms₁ ms₂ d N j b₁ b₂
    b₃ pb pq pe (fun a => on0 a ∧ C (fixed9 φ a.1)) on1 on2 on3 tabOf ctx H
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
    intro a ha
    by_cases hc : C (fixed9 φ a.1)
    · exact goodIn_conseq pb g1 (fun _ h => h) (fun _ h => h)
        (fun _ _ _ h => ⟨h, fun e => absurd e (by omega)⟩) (fun _ _ _ h => h.1) a ⟨ha, hc⟩
    · exact Doomed.of_forall _ _ fun τ b hout =>
        ⟨h01 a τ b ha hout, fun w hw => absurd (hR1 a τ b ha hout (hw.2 (Or.inl rfl))) hc⟩
  · rw [o1, o2]
    exact goodIn_conseq pq (goodIn_and pq g2 (Q := fun a _ => Rw a) (Q' := fun b _ => Rw b)
        (fun a τ b _ ha hout hq => hR2 a τ b ha hout hq))
      (fun _ h => h) (fun _ h => h) (fun _ _ _ h => ⟨h.1, fun _ => h.2⟩)
      (fun _ _ _ h => ⟨h.1, h.2 (Or.inr rfl)⟩)
  · rw [o2, o3]
    exact goodIn_conseq pe (goodIn_and pe g3 (Q := fun a _ => Rw a) (Q' := fun _ _ => True)
        (fun a τ b _ ha hout _ => hR3 a τ b ha hout))
      (fun _ h => h) (fun _ h => h) (fun _ _ _ h => ⟨h.1, fun _ => h.2⟩)
      (fun _ _ _ h => ⟨h.1, trivial⟩)

/-- The sentence: the plan's claims and the ties' and reads' indices are at most "rows". -/
def rowsFit (rows : ℕ) (π : α → Option HTailF2 × Option (Array HFun)) (q : α × Option Pub9) :
    Prop :=
  ∀ v tlb funs, q.2 = some v → π q.1 = (some tlb, some funs) →
    v.F.planClaimsF + top8 tlb funs ≤ rows

/-- The test on the exponents grows with d. -/
theorem termsOk_le {K : Type} [Field K] (t : List (ℕ × K)) (d d' : ℕ) (h : Desc.TermsOk K t d)
    (hd : d ≤ d') : Desc.TermsOk K t d' :=
  ⟨h.1, fun x hx => Nat.le_trans (h.2 x hx) hd⟩

/-- **A yes of the one equation's step gives the number, as an equation.** -/
theorem door_rows (pw : Where) (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S)
    (k : ℕ) (h : (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok (s', k))
    (a : K9.Part) (ha : atS.get? s = some a) (rows top : ℕ) (ho : a.owed = some rows)
    (hl : a.laid = some top) : rows = a.F.planClaimsF + top := by
  obtain ⟨a0, out, ha0, hdoor, _⟩ := oneEquation_inv atS pw ft s rs cols s' k h
  obtain rfl : a0 = a := Option.some.inj (ha0.symm.trans ha)
  obtain ⟨n, h1, _, _, h4⟩ := _root_.Meaning.K8.door_counts hdoor
  have e1 : n = top := Option.some.inj (h1.symm.trans hl)
  have e2 : a0.F.planClaimsF + n = rows := Option.some.inj (h4.symm.trans ho)
  omega

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.inMoves_under
#print axioms VerifiableInference.Desc.K9L.inMoves_rows
#print axioms VerifiableInference.Desc.K9L.door_rows
