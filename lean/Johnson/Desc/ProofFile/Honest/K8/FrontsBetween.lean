-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/FrontsBetween.lean: BETWEEN TWO ENTRIES OF `frontsOf`
(Johnson/Desc/ProofFile/Honest/Fall.lean) LIES THE VERIFIER's OWN FOLD (`foldBlocks`) OVER THE
MEMBERS BETWEEN. Statements and proofs. General in the state, the claims and the description: no
run, no prover, no kind. LEMMAS; NONE OF THE LIBRARY's GOALS.

  **`frontsOf_drop`**   from entry n on, the list of `frontsOf` is the list of `frontsOf` over the
      members from n on, from entry n's state, at some rounds and columns
  **`frontsOf_between`**   where there are entries n and n + m: the fold over the m members from n
      on, from entry n's state, ends at entry n + m's state
  `frontsOf_earlier`   where there is an entry n there is an entry at every smaller number
By: `frontsOf_zero` (Honest/K8/FrontsStep.lean) · `frontsOf_fold` (FrontsAgree.lean).
Limits. Which rounds and columns the fold is at is not said.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K8.FrontsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc

variable {S Cl : Type}

/-- **From entry n on.** -/
theorem frontsOf_drop (ft : Nat) : ∀ (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat) (e : Place × S × List Fmt.Drawn),
    (frontsOf ft bs s rs cols)[n]? = some e →
    ∃ rs' cols', (frontsOf ft bs s rs cols).drop n = frontsOf ft (bs.drop n) e.2.1 rs' cols'
  | bs, s, rs, cols, 0, e, he => by
    rw [frontsOf_zero ft bs s rs cols e he]
    exact ⟨rs, cols, rfl⟩
  | [], _, _, _, _ + 1, _, he => by
    simp [frontsOf] at he
  | b :: l, s, rs, cols, n + 1, e, he => by
    have hu : frontsOf ft (b :: l) s rs cols =
        if (rs.take b.rounds.length).length != b.rounds.length then [] else
        (b.place, s, (rs.take b.rounds.length).map (·.drawn)) ::
          match b.step ft s (rs.take b.rounds.length) cols with
          | .error _ => []
          | .ok (s', k) => frontsOf ft l s' (rs.drop b.rounds.length) (cols.drop k) := by
      conv_lhs => unfold frontsOf
      rfl
    rw [hu] at he ⊢
    split at he
    · simp at he
    · rename_i hg
      rw [if_neg hg]
      rw [List.getElem?_cons_succ] at he
      cases hst : b.step ft s (rs.take b.rounds.length) cols with
      | error x =>
        rw [hst] at he
        simp at he
      | ok y =>
        obtain ⟨s', k⟩ := y
        rw [hst] at he
        simp only at he ⊢
        rw [List.drop_succ_cons, List.drop_succ_cons]
        exact frontsOf_drop ft l s' _ _ n e he

/-- **Between two entries lies the fold.** -/
theorem frontsOf_between (ft : Nat) (bs : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n m : Nat) (e e' : Place × S × List Fmt.Drawn)
    (he : (frontsOf ft bs s rs cols)[n]? = some e)
    (he' : (frontsOf ft bs s rs cols)[n + m]? = some e') :
    ∃ rs' cols' r c, foldBlocks ft ((bs.drop n).take m) e.2.1 rs' cols' = .ok (e'.2.1, r, c) := by
  obtain ⟨rs', cols', hd⟩ := frontsOf_drop ft bs s rs cols n e he
  have h : (frontsOf ft (bs.drop n) e.2.1 rs' cols')[m]? = some e' := by
    rw [← hd, List.getElem?_drop]
    exact he'
  obtain ⟨r, c, hf⟩ := frontsOf_fold ft _ _ _ _ m e' h
  exact ⟨rs', cols', r, c, hf⟩

/-- Where there is an entry there are the earlier ones. -/
theorem frontsOf_earlier {α : Type} (l : List α) {n : Nat} {e : α} (he : l[n]? = some e) {k : Nat}
    (hk : k ≤ n) : ∃ e₀, l[k]? = some e₀ := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.1 he).1
  exact ⟨l[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.frontsOf_drop
#print axioms ProofFile.Honest.K8.frontsOf_between
#print axioms ProofFile.Honest.K8.frontsOf_earlier
