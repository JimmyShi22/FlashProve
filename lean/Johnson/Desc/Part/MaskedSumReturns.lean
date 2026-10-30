-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Part/MaskedSumReturns.lean: THE PART "THE MASKED SUMCHECK": THE HEARING RETURNS.
Statements and proofs, in the part's letters. All lemmas on this part that lay so far go FROM a
return (Part/MaskedSumShape.lean: hear_spec). Here is the other direction.
WHAT IT DOES NOT SHOW. That the row is worth 0; that the prover's program sends such rounds; nothing
on soundness, on probabilities or on hiding. What was shown and the factors behind a run of layings
are not said here (Kinds/Law/Ledger.lean: hideRun_frame says them from a return).
WHAT IT IS.
  FreeIn F a b       the ledger has the numbers below b, a mark for each of its numbers, and the
                     numbers from a up to b are free.
  hide_returns, hideSteps_returns, hideRun_returns   a run of layings under free numbers returns;
                     behind it: the same count of numbers, the same next number, and just these
                     numbers marked more.
  shown_returns      what was shown under a marked number is handed out.
  hear_returns       where the call's shape is right, the start form has a public part, the reader
                     returns and the end values' numbers are free: hear returns, with every field
                     of what it hands back; the marks behind it.
  rowLaid_returns    where the sumcheck's own numbers are free: rowLaid returns; the marks.
getD_set is getD_set! (Kinds/Law/Ledger.lean), typed again because that file stands
above the kinds.

-/
import Johnson.Desc.Part.MaskedSumHonest
import Johnson.Desc.Part.MaskedSumMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Part.MaskedSum
open OnBytes
open OnBytes.Model (Aff Fork)

/-- The numbers below b are there, each number has a mark, and those from a up to b are free. -/
def FreeIn (F : Fork) (a b : Nat) : Prop :=
  b ≤ F.ns ∧ F.gotF.size = F.ns ∧ ∀ j, a ≤ j → j < b → F.gotF.getD j true = false

theorem FreeIn.sub {F : Fork} {a b a' b' : Nat} (h : FreeIn F a b) (ha : a ≤ a') (hb : b' ≤ b) :
    FreeIn F a' b' :=
  ⟨by have := h.1; omega, h.2.1, fun j h1 h2 => h.2.2 j (by omega) (by omega)⟩

theorem getD_set {α : Type} (a : Array α) (j i : Nat) (x z : α) (hj : j < a.size) :
    (a.set! j x).getD i z = if i = j then x else a.getD i z := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h : i = j
  · subst h; simp [hj]
  · have h' : ¬ j = i := fun e => h e.symm
    simp [h, h']

/-- What a run of layings under the numbers from a up to b leaves of the ledger's frame. -/
def Marked (F G : Fork) (a b : Nat) : Prop :=
  G.ns = F.ns ∧ G.next = F.next ∧ G.gotF.size = G.ns ∧
    ∀ i z, G.gotF.getD i z = if a ≤ i ∧ i < b then true else F.gotF.getD i z

theorem hide_returns {F : Fork} {j : Nat} (x f : E) (h : FreeIn F j (j + 1)) :
    ∃ G, F.hide j x f = some G ∧ Marked F G j (j + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hj : j < F.ns := by omega
  have hc : (decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true) = true := by
    simp [hj, h2, h3 j (le_refl _) (by omega)]
  refine ⟨{ F with gotF := F.gotF.set! j true, vp := F.vp.set! j x, mf := F.mf.set! j f }, ?_, rfl,
    rfl, ?_, ?_⟩
  · unfold Fork.hide
    rw [if_pos hc]
  · simp [h2]
  · intro i z
    show (F.gotF.set! j true).getD i z = _
    rw [getD_set _ _ _ _ _ (by rw [h2]; exact hj)]
    by_cases hi : i = j
    · rw [if_pos hi, if_pos (by omega)]
    · rw [if_neg hi, if_neg (by omega)]

theorem hideSteps_returns (f : E) : ∀ (l : List E) (j : Nat) (F : Fork),
    FreeIn F j (j + l.length) →
    ∃ G, l.foldlM (Fork.hideStep f) (j, F) = some (j + l.length, G) ∧ Marked F G j (j + l.length)
  | [], j, F, h => ⟨F, rfl, rfl, rfl, h.2.1, fun i z => by
      rw [if_neg]
      simp only [List.length_nil]
      omega⟩
  | x :: xs, j, F, h => by
    have hl : j + (x :: xs).length = j + 1 + xs.length := by
      rw [List.length_cons]
      omega
    rw [hl] at h ⊢
    obtain ⟨H, a0, a1, a2, a3, a4⟩ := hide_returns x f (h.sub (le_refl _) (by omega))
    obtain ⟨G, b0, b1, b2, b3, b4⟩ := hideSteps_returns f xs (j + 1) H
      ⟨by rw [a1]; exact h.1, a3, fun i hi hi' => by
        rw [a4, if_neg (by omega)]
        exact h.2.2 i (by omega) hi'⟩
    refine ⟨G, ?_, by rw [b1, a1], by rw [b2, a2], b3, fun i z => ?_⟩
    · rw [List.foldlM_cons]
      have hstep : Fork.hideStep f (j, F) x = some (j + 1, H) := by simp [Fork.hideStep, a0]
      rw [hstep]
      exact b0
    · rw [b4, a4]
      by_cases h1 : j + 1 ≤ i ∧ i < j + 1 + xs.length
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1]
        by_cases h2 : j ≤ i ∧ i < j + 1
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]

/-- **A run of layings under free numbers returns.** -/
theorem hideRun_returns (F : Fork) (first : Nat) (v : Array E) (f : E)
    (h : FreeIn F first (first + v.size)) :
    ∃ G, F.hideRun first v f = some G ∧ Marked F G first (first + v.size) := by
  obtain ⟨G, a0, a⟩ := hideSteps_returns f v.toList first F (by rwa [Array.length_toList])
  rw [Array.length_toList] at a0 a
  refine ⟨G, ?_, a⟩
  unfold Fork.hideRun
  rw [← Array.foldlM_toList, a0]

theorem Marked.free {F G : Fork} {a b a' b' : Nat} (h : Marked F G a b) (hf : FreeIn F a' b')
    (hd : b ≤ a' ∨ b' ≤ a) : FreeIn G a' b' :=
  ⟨by rw [h.1]; exact hf.1, h.2.2.1, fun j h1 h2 => by
    rw [h.2.2.2, if_neg (by omega)]
    exact hf.2.2 j h1 h2⟩

theorem shown_returns {F : Fork} {j : Nat} (hj : j < F.ns) (hg : F.gotF.getD j false = true) :
    F.shown j = some (F.vp.getD j zeroE) := by
  unfold Fork.shown
  rw [if_pos (by simp [hj, hg])]

/-- **THE HEARING RETURNS.** -/
theorem hear_returns (C : Aff) (k : Call) (hk : shapeOk k = true) (F : Fork) (T : E)
    (hT : F.publicPart C = some T) (rs : List Fmt.RoundView) (R : Read) (hR : readAll k rs = some R)
    (hfree : FreeIn F (F.next + ownSlots k.all) (F.next + ownSlots k.all + R.values.length)) :
    ∃ G, hear C k F rs = some
        ({ start := C, target := T, eps := R.eps,
           claim := after k.all R.rounds (addE R.mu (mulE R.eps T)), first := F.next,
           vars := k.all, r := R.rounds.map (·.2), sEnd := F.next + ownSlots k.all }, G) ∧
      G.ns = F.ns ∧ G.next = F.next + ownSlots k.all + R.values.length ∧ G.gotF.size = G.ns ∧
      ∀ i z, G.gotF.getD i z =
        if F.next + ownSlots k.all ≤ i ∧ i < F.next + ownSlots k.all + R.values.length then true
        else F.gotF.getD i z := by
  obtain ⟨G, hG, g1, g2, g3, g4⟩ := hideRun_returns
    ({ F with next := F.next + ownSlots k.all + R.values.length } : Fork)
    (F.next + ownSlots k.all) R.values.toArray ((R.rounds.map (·.2)).getLastD zeroE)
    (by rw [List.size_toArray]; exact hfree)
  rw [List.size_toArray] at g4
  refine ⟨G, ?_, g1, g2, g3, g4⟩
  unfold hear
  simp only [List.getLastD_eq_getLast?, List.getLast?_map] at hG
  simp [hk, hT, hR, hG]

/-- **The writing of the row returns.** n: any number of free numbers that holds the hiding
polynomial's coefficients. -/
theorem rowLaid_returns (h : Heard) (F : Fork)
    (hfree : FreeIn F h.first (h.first + (hidingAt (h.vars.zip h.r)).1.length)) :
    ∃ G, rowLaid h F = some G ∧
      Marked F G h.first (h.first + (hidingAt (h.vars.zip h.r)).1.length) := by
  obtain ⟨G, hG, g⟩ := hideRun_returns F h.first
    (Array.replicate (hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE)
    (by rw [Array.size_replicate]; exact hfree)
  rw [Array.size_replicate] at g
  exact ⟨G, hG, g⟩

end VerifiableInference.Desc.Part.MaskedSum
