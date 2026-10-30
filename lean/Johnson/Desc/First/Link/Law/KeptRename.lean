-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/KeptRename.lean: THE FOLDED COMPLEX WITH KEPT SLOTS (`Sg.cKept`,
OnBytes/Slice/CsRowKept.lean), ITS KEPT SLOTS RENAMED ALONG A BIJECTION: «a code word is near the
word with the given long symbols, and a vector has a target on its message» passes from the slots'
type K to K'. For two kinds' files that type one group over two lists: only the type of the kept
slots names the list. Definitions and a theorem.

  `eJ φ`, `eQ φ`, `eA φ`: the coordinates of messages, of randomness and of long symbols at K', read
    at K: a kept slot κ' as φ.symm κ'; everything else as it is. Bijections.
  `near_rename`: **φ : K ≃ K' · a pair c of s.cKept K whose encoding parts from wordOf s K g in at
    most e long positions, with ∑ j, v j * c.1 j = τ ⊢ a pair c' of s.cKept K' whose encoding parts
    from wordOf s K' (fun q α' => g q (eA φ α')) in at most e long positions, with ∑ j', v (eJ φ j')
    * c'.1 j' = τ.**
Limits. Book-keeping on one code. Nothing on soundness.
-/
import Johnson.Top.H0.K2Hands.StrMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice Cb Iop IOR
open VerifiableInference.Desc.First.K2Hands (wordOf)

variable (s : Sg) {K K' : Type} [Fintype K] [DecidableEq K] [Fintype K'] [DecidableEq K']
  (φ : K ≃ K')

/-- A message's coordinate at K', read at K. -/
def eJ : (s.cKept K').J ≃ (s.cKept K).J :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.optionCongr φ.symm) (Equiv.refl _)) (Equiv.refl _)

/-- A coordinate of the randomness at K', read at K. -/
def eQ : (s.cKept K').Q ≃ (s.cKept K).Q :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.optionCongr φ.symm) (Equiv.refl _)) (Equiv.refl _)

/-- A long symbol's coordinate at K', read at K. -/
def eA : (s.cKept K').Aa ≃ (s.cKept K).Aa :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.optionCongr φ.symm) (Equiv.refl _)) (Equiv.refl _)

/-- The long symbols of the renamed encoding. -/
theorem T_enc_rename (c : (s.cKept K).N.Wit) (x : s.Ps) (α' : (s.cKept K').Aa) :
    (s.cKept K').T ((s.cKept K').enc (fun j' => c.1 (eJ s φ j')) fun q' => c.2 (eQ s φ q')) x α' =
      (s.cKept K).T ((s.cKept K).enc c.1 c.2) x (eA s φ α') := by
  rcases α' with ⟨o, u⟩ | u | u <;> rfl

/-- The long symbols of the renamed word. -/
theorem T_word_rename (g : s.Ps → (s.cKept K).Aa → GE) (x : s.Ps) (α' : (s.cKept K').Aa) :
    (s.cKept K').T (wordOf s K' fun q β => g q (eA s φ β)) x α' =
      (s.cKept K).T (wordOf s K g) x (eA s φ α') := by
  rcases α' with ⟨o, u⟩ | u | u <;> rfl

/-- **THE KEPT SLOTS RENAMED.** -/
theorem near_rename (g : s.Ps → (s.cKept K).Aa → GE) (v : (s.cKept K).J → GE) (τ : GE) (e : ℕ)
    (h : ∃ c : (s.cKept K).N.Wit,
      offCnt (Ex := (s.cKept K).ext) (wordOf s K g) ((s.cKept K).N.enc c.1 c.2) ≤ e ∧
        ∑ j, v j * c.1 j = τ) :
    ∃ c' : (s.cKept K').N.Wit,
      offCnt (Ex := (s.cKept K').ext) (wordOf s K' fun q β => g q (eA s φ β))
          ((s.cKept K').N.enc c'.1 c'.2) ≤ e ∧
        ∑ j', v (eJ s φ j') * c'.1 j' = τ := by
  obtain ⟨c, h1, h2⟩ := h
  refine ⟨(fun j' => c.1 (eJ s φ j'), fun q' => c.2 (eQ s φ q')), ?_, ?_⟩
  · refine Nat.le_trans (Nat.le_of_eq ?_) h1
    unfold offCnt
    congr 1
    funext x
    refine propext (not_congr ⟨fun hx => ?_, fun hx => ?_⟩)
    · funext α
      have := congrFun hx ((eA s φ).symm α)
      have e1 := T_word_rename s φ g x ((eA s φ).symm α)
      have e2 := T_enc_rename s φ c x ((eA s φ).symm α)
      rw [Equiv.apply_symm_apply] at e1 e2
      exact e1.symm.trans (this.trans e2)
    · funext α'
      exact (T_word_rename s φ g x α').trans
        ((congrFun hx (eA s φ α')).trans (T_enc_rename s φ c x α').symm)
  · rw [← h2]
    exact (eJ s φ).sum_comp fun j => v j * c.1 j

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.T_enc_rename
#print axioms VerifiableInference.Desc.LinkJoin.T_word_rename
#print axioms VerifiableInference.Desc.LinkJoin.near_rename
