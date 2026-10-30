-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/DrawBridgeProofs.lean: THE SMALLNESS TEST, THE HONEST PROVER's
SIDE: proofs of the statements of Honest/K8/DrawBridge.lean: from a yes of the kind's own block, and
from the array of digits as it is made, to the premises of Honest/K8/SmallLaw.lean, and so to the
library's two sentences behind the draw. LEMMAS ON THE HONEST PROVER's SIDE; NONE OF THE LIBRARY's
GOALS.

  `rowT`, `endT`, `lenT`   "laid in a row" for a list of shapes: matrix, rows to an entry, first
                     entry
  `inARow_map`, `rowT_append`, `layFamily_row`, `tabs_row`   the place's shapes are laid in a row
  `getD_of_all`     what holds of every entry of a list and of 0 holds of every reading with the
                     fallback 0
  `same_of_yes`, `drawLaid_of_yes`, `inARow_of_tabs`, `inARow_of_yes`, `zzBy_of_zzOf`,
  **`small_at_yes`**, **`small_at_silence`**
The limits are those of Honest/K8/DrawBridge.lean.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.DrawBridge
import Johnson.Desc.ProofFile.Honest.K8.SmallLawProofs
import Johnson.Desc.ProofFile.Honest.K8.PartLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Par MeansAtS tabs layFamily firstColumns putTl_tl)
open VerifiableInference.Desc.First.K8.Honest

/-! ## The place's shapes are laid in a row -/

/-- The entries of a table of the shape t, at the matrices' columns ks and rows ms. -/
def lenT (ks ms : List ℕ) (t : ℕ × ℕ × ℕ) : ℕ := ks.getD t.1 0 * (ms.getD t.1 0 / t.2.1)

/-- A list of shapes is laid in a row from entry e on. -/
def rowT (ks ms : List ℕ) : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | e, t :: l => t.2.2 == e && rowT ks ms (e + lenT ks ms t) l

/-- The first entry behind a list of shapes that begins at e. -/
def endT (ks ms : List ℕ) (e : ℕ) (l : List (ℕ × ℕ × ℕ)) : ℕ :=
  l.foldl (fun e t => e + lenT ks ms t) e

theorem inARow_map (q : Par) : ∀ (fs : List HFun) (e : ℕ),
    inARow q e fs = rowT q.ks q.ms e (fs.map fun Fn => (Fn.mat, Fn.len, Fn.start))
  | [], _ => rfl
  | f :: fs, e => by
    unfold inARow
    rw [List.map_cons]
    unfold rowT
    rw [inARow_map q fs]
    rfl

theorem rowT_append (ks ms : List ℕ) : ∀ (l₁ l₂ : List (ℕ × ℕ × ℕ)) (e : ℕ),
    rowT ks ms e (l₁ ++ l₂) = (rowT ks ms e l₁ && rowT ks ms (endT ks ms e l₁) l₂)
  | [], _, _ => by simp [rowT, endT]
  | t :: l₁, l₂, e => by
    show (t.2.2 == e && rowT ks ms (e + lenT ks ms t) (l₁ ++ l₂)) =
      ((t.2.2 == e && rowT ks ms (e + lenT ks ms t) l₁) &&
        rowT ks ms (endT ks ms (e + lenT ks ms t) l₁) l₂)
    rw [rowT_append ks ms l₁ l₂, Bool.and_assoc]

/-- One family's tables are laid in a row, and the number handed on is the first entry behind. -/
theorem layFamily_row (p : Par) (a : ℕ × ℕ × ℕ) (e : ℕ) :
    rowT p.ks p.ms e (layFamily p a e).1 = true ∧
      (layFamily p a e).2 = endT p.ks p.ms e (layFamily p a e).1 := by
  unfold layFamily
  induction a.2.1 with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · show rowT p.ks p.ms e (_ ++ [_]) = true
      rw [rowT_append, h1, Bool.true_and]
      unfold rowT
      rw [← h2]
      simp [rowT]
    · show _ + _ = endT p.ks p.ms e (_ ++ [_])
      unfold endT
      rw [List.foldl_append]
      show _ = endT p.ks p.ms e _ + _
      rw [← h2]
      rfl

/-- The fold over the families keeps "laid in a row, with the first entry behind". -/
theorem tabs_fold (p : Par) : ∀ (asks : List (ℕ × ℕ × ℕ)) (x : List (ℕ × ℕ × ℕ) × ℕ),
    rowT p.ks p.ms 0 x.1 = true → x.2 = endT p.ks p.ms 0 x.1 →
    rowT p.ks p.ms 0
      (asks.foldl (fun x a => let y := layFamily p a x.2; (x.1 ++ y.1, y.2)) x).1 = true
  | [], _, h, _ => h
  | a :: asks, x, h1, h2 => by
    rw [List.foldl_cons]
    obtain ⟨g1, g2⟩ := layFamily_row p a x.2
    refine tabs_fold p asks _ ?_ ?_
    · show rowT p.ks p.ms 0 (x.1 ++ (layFamily p a x.2).1) = true
      rw [rowT_append, h1, Bool.true_and, ← h2]
      exact g1
    · show (layFamily p a x.2).2 = endT p.ks p.ms 0 (x.1 ++ (layFamily p a x.2).1)
      unfold endT
      rw [List.foldl_append]
      show _ = endT p.ks p.ms (endT p.ks p.ms 0 x.1) _
      rw [← h2]
      exact g2

/-- The place's shapes are laid in a row from entry 0 on. -/
theorem tabs_row (p : Par) : rowT p.ks p.ms 0 (tabs p) = true :=
  tabs_fold p p.asks ([], 0) rfl rfl

theorem inARow_of_tabs : Spec.inARow_of_tabs := by
  intro p q fs h hf
  rw [inARow_map, hf, h.ks, h.ms]
  exact tabs_row p

/-! ## Behind a yes -/

theorem same_of_yes : Spec.same_of_yes := by
  intro p s s' r tl' h ht
  obtain ⟨tl, hs, _, _, _, _, hk, hm, htau, _, rfl⟩ := h
  rw [putTl_tl s tl _ hs] at ht
  obtain rfl := Option.some.inj ht
  exact ⟨⟨hk, hm, htau⟩, rfl⟩

theorem inARow_of_yes : Spec.inARow_of_yes := by
  intro p s s' r tl' h ht
  have hsame := (same_of_yes p s s' r tl' h ht).1
  obtain ⟨tl, hs, _, _, _, _, _, _, _, htabs, rfl⟩ := h
  rw [putTl_tl s tl _ hs] at ht
  obtain rfl := Option.some.inj ht
  exact inARow_of_tabs p _ _ hsame htabs

/-- The matrices' first columns read their numbers of columns alone. -/
theorem firstColumns_same {p q : Par} (h : p.ks = q.ks) : firstColumns p = firstColumns q := by
  unfold firstColumns
  rw [h]

/-- What holds of every entry of a list and of 0 holds of every reading with the fallback 0. -/
theorem getD_of_all (P : ℤ → Prop) (l : List ℤ) (h : ∀ t ∈ l, P t) (h0 : P 0) (n : ℕ) :
    P (l.toArray.getD n 0) := by
  by_cases hn : n < l.length
  · have e : l.toArray.getD n 0 = l[n] := by simp [hn]
    rw [e]
    exact h _ (List.getElem_mem hn)
  · have e : l.toArray.getD n 0 = 0 := by simp [hn]
    rw [e]
    exact h0

theorem drawLaid_of_yes : Spec.drawLaid_of_yes := by
  intro p s s' r tl' h hfit hks ht hcols
  obtain ⟨hsame, hcf⟩ := same_of_yes p s s' r tl' h ht
  obtain ⟨tl, hs, _, _, _, hNM, hk, _, _, _, rfl⟩ := h
  rw [putTl_tl s tl _ hs] at ht
  obtain rfl := Option.some.inj ht
  unfold drawFit at hfit
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hfit
  refine ⟨⟨hcols, ?_, ?_⟩, ?_, fun n => ?_⟩
  · show 0 < tl.NM
    rw [hNM]
    exact List.length_pos_iff.2 hks
  · show tl.NM = tl.mats.size
    rw [hNM, ← hk]
    simp
  · exact (firstColumns_same hsame.ks).symm
  · show (r.drawn.trits.toArray.getD n 0 = -1 ∨ _ = 0 ∨ _ = 1)
    refine getD_of_all (fun x => x = -1 ∨ x = 0 ∨ x = 1) _ (fun t ht => ?_)
      (Or.inr (Or.inl rfl)) n
    rcases hfit.1.1.1.2 t ht with (h1 | h1) | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

/-! ## The array of digits as it is made -/

theorem zzBy_of_zzOf : Spec.zzBy_of_zzOf := by
  intro tl A mats C trits hcf hA u hu col hc
  rw [hA u hu col hc, hcf]
  unfold zzOf
  exact map_natCast (algebraMap Cb.Gl.F Cb.Gl.E) _

/-! ## The library's two sentences -/

/-- **Behind a yes of the draw, where no combination leaves its window, at a table made of the
cells, the library's two sentences hold.** -/
theorem small_at_yes : Spec.small_at_yes := by
  intro W A w p s s' r tl' a h hfit hks ht hcols hX hT hZ hl
  obtain ⟨hsame, hcf⟩ := same_of_yes p s s' r tl' h ht
  have hD := drawLaid_of_yes p s s' r tl' h hfit hks ht hcols
  obtain ⟨hF, h3⟩ := hX tl' ht
  have hl' : leaves (parOfTail tl') a tl'.cfF = none := by
    rw [leaves_same hsame, hcf]
    exact hl
  obtain ⟨h1, h2⟩ := small_of_honest tl' (A w) a hD hF h3 hT hZ hl'
  exact ⟨⟨tl', ht, h1⟩, ⟨tl', ht, h2⟩⟩

/-- **The same where the part's second stop is silent behind its round.** -/
theorem small_at_silence : Spec.small_at_silence := by
  intro W A w p s s' r tl' v front h hfit hks ht hcols hX hT hZ hq
  exact small_at_yes W A w p s s' r tl' v.cell h hfit hks ht hcols hX hT hZ
    (smallHid_none p v front r.drawn hq)

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.small_at_silence
#print axioms ProofFile.Honest.K8.same_of_yes
#print axioms ProofFile.Honest.K8.drawLaid_of_yes
#print axioms ProofFile.Honest.K8.inARow_of_tabs
#print axioms ProofFile.Honest.K8.inARow_of_yes
#print axioms ProofFile.Honest.K8.zzBy_of_zzOf
#print axioms ProofFile.Honest.K8.small_at_yes
#print axioms ProofFile.Honest.K8.lenT
#print axioms ProofFile.Honest.K8.rowT
#print axioms ProofFile.Honest.K8.endT
#print axioms ProofFile.Honest.K8.inARow_map
#print axioms ProofFile.Honest.K8.rowT_append
#print axioms ProofFile.Honest.K8.layFamily_row
#print axioms ProofFile.Honest.K8.tabs_fold
#print axioms ProofFile.Honest.K8.tabs_row
#print axioms ProofFile.Honest.K8.firstColumns_same
#print axioms ProofFile.Honest.K8.getD_of_all
