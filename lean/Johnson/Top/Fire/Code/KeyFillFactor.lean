-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyFillFactor.lean: AT A YES OF A HELD BLOCK THAT IS A SENDING, EVERY DRAWN SEED's FACTOR READS AS NO 0. The sending's decision refuses a factor whose three RAW words are 0 (K1/Own.lean: «a seed's factor is 0»); the reading takes residues: (p, 0, 0) is not (0, 0, 0) and reads as 0.
But a block AS A PIECE HOLDS IT (held := (below b).lift …) decides only behind viewWordsBelowPrime: every word of the rounds' drawn elements is below the prime. K1.reads_exists TAKES IT FROM THERE: every factor spelt by words below the prime (hok) and not (0, 0, 0) (hnz) ⟹ the seeds read as joint seeds. HERE hok IS PAID FROM THE HELD BLOCK's YES; hnz is the sending's own test (asks).
  held_okView    the held block's yes holds viewWordsBelowPrime of what it was shown (held_decide drops this half)
  drawn_ok       viewWordsBelowPrime gives, at each round, that every drawn element's three words are below the prime
  cut_factor     a cut seed's factor is the zero element or one of the elements drawn
  okE_drawn      three words below the prime: the library's okE
  factor_ok      at a round whose drawn words are below the prime every cut seed's factor is spelt by words below the prime: K1.reads_exists' premise hok
OBJECT: held | viewWordsBelowPrime; seedsOf | cutSeeds | K1.reads_exists (its premise) · USER: Johnson/Top/Fire/Code/KeyFillStep.lean (its premise F1) · LETTERS: all.
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.Plain.PaidKeeps
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K1 (Par seedsOf cutSeeds)

/-- **The held block's yes holds the words' test.** -/
theorem held_okView {P S Cl : Type} (b : Block S Cl) (a a' : P × S) (rs : List _root_.Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : (held b : Block (P × S) Cl).decide a rs gs = .ok a') : viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ = true := by
  have h' : ((if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide a.2 rs gs
      else .error "a word is not below the prime").map fun s => (a.1, s)) = .ok a' := h
  by_contra hn
  rw [if_neg hn] at h'
  cases h'

theorem drawn_ok (v : _root_.Fmt.View) (h : viewWordsBelowPrime v = true) (r : _root_.Fmt.RoundView) (hr : r ∈ v.rounds) :
    (r.drawn.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true := by
  unfold viewWordsBelowPrime at h
  rw [Bool.and_eq_true] at h
  have h1 := List.all_eq_true.1 h.1 r hr
  rw [Bool.and_eq_true] at h1
  exact h1.1

theorem cut_factor (v : ℕ) : ∀ (n : ℕ) (l : List E) (sd : List E × E), sd ∈ cutSeeds v n l → sd.2 = zeroE ∨ sd.2 ∈ l
  | 0, _, _, h => by cases h
  | n + 1, l, sd, h => by
    rcases List.mem_cons.1 h with rfl | h
    · show (l.drop v).headD zeroE = zeroE ∨ (l.drop v).headD zeroE ∈ l
      cases hd : l.drop v with
      | nil => exact Or.inl rfl
      | cons x t => exact Or.inr (List.mem_of_mem_drop (hd ▸ List.mem_cons_self))
    · rcases cut_factor v n _ sd h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_of_mem_drop h)

theorem okE_drawn (x : _root_.Fmt.Ext3) (h : (decide (x.1 < fieldPrimeWord) && decide (x.2.1 < fieldPrimeWord) && decide (x.2.2 < fieldPrimeWord)) = true) : okE (E.ofTriple x) = true := h

/-- **K1.reads_exists' premise on the words.** -/
theorem factor_ok (P : Par) (r₁ : _root_.Fmt.RoundView)
    (hok : (r₁.drawn.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true) : ∀ s ∈ seedsOf P r₁, okE s.2 = true := by
  intro s hs
  rcases cut_factor _ _ _ _ hs with e | e
  · rw [e]
    decide
  · obtain ⟨x, hx, ex⟩ := List.mem_map.1 e
    rw [← ex]
    exact okE_drawn x (List.all_eq_true.1 hok x hx)

end LPFD

#print axioms LPFD.held_okView
#print axioms LPFD.drawn_ok
#print axioms LPFD.cut_factor
#print axioms LPFD.okE_drawn
#print axioms LPFD.factor_ok
