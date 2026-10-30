-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeRow.lean: from the parts of a list to a sub-protocol of a chain:
a prover's side beside the side whose parts have other moves, which may pass on another type of
value. Where the two lists of moves are related part by part (`MovesTo`, Honest/AlikeParts.lean),
the sub-protocol's rounds are related (`StepsAlike`, `memberSteps`, Honest/AlikeChain.lean).
Definitions, and lemmas with their proofs.

  1  `ReRow`, `reRow`, `RowSame`   other moves for each part of a list; the list with them; "the two
     lists are given the same coins", part by part
  2  `StrAlike.mapError`, `lendPart_re`, `lendRow_re`   the book gives both lists the same, or
     returns the same error for both
  3  `RowTo`, `reRow_lens`, `rowSteps_re`   the hypothesis on the moves, part by part; the two
     lists' rounds are related
  4  `member_re`   the sub-protocol at whose place the two prover's sides are

No equation between types. `p.reMove mvs` has the counts of `p` by construction, so the coins of the
two first parts have one type; the rest of the two lists' coins are compared by recursion
(`RowSame`).

Limits.
  * One relation `T` between the two carried states, the same before and after every part.
  * The second list has to be given in the form `reRow ps R`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.AlikeParts
import Johnson.Desc.ProofFile.Honest.AlikeChain
import Johnson.Desc.ProofFile.Honest.Law.Steps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Oracle Place)

variable {S Cl V W X X' : Type}

/-! ## 1 A list of parts with other moves -/

/-- Other moves for each part of a list. -/
def ReRow (X' : Type) : List (Part V W X) → Type
  | [] => Unit
  | p :: ps => List (Move p.Coins W X') × ReRow X' ps

/-- **The list with these moves.** -/
def reRow : (ps : List (Part V W X)) → ReRow X' ps → List (Part V W X')
  | [], _ => []
  | p :: ps, R => p.reMove R.1 :: reRow ps R.2

/-- The two lists' coins are the same, part by part. -/
def RowSame : (ps : List (Part V W X)) → (R : ReRow X' ps) → RowCoins ps →
    RowCoins (reRow ps R) → Prop
  | [], _, _, _ => True
  | _ :: ps, R, c, c' => c.1 = c'.1 ∧ RowSame ps R.2 c.2 c'.2

/-! ## 2 What the book gives -/

theorem StrAlike.mapError {α β : Type} {P : α → β → Prop} (g : String → String) :
    ∀ {x : Except String α} {y : Except String β}, StrAlike P x y →
      StrAlike P (x.mapError g) (y.mapError g)
  | .ok _, .ok _, q => q
  | .error _, .error _, q => congrArg g q
  | .ok _, .error _, q => False.elim q
  | .error _, .ok _, q => False.elim q

theorem StrAlike.self {α : Type} : ∀ x : Except String α, StrAlike (fun a b => a = b) x x
  | .ok _ => rfl
  | .error _ => rfl

/-- What a part is given depends on its counts alone. -/
theorem lendPart_re (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Addr) (p : Part V W X) (mvs : List (Move p.Coins W X')) :
    lendPart B rows look a (p.reMove mvs) = lendPart B rows look a p := by
  unfold lendPart
  dsimp only [Part.reMove]
  by_cases h : (p.takes != dueAt rows a) = true
  · simp only [if_pos h]
  · simp only [if_neg h]
    cases (look a).2.cut ⟨0, 0⟩ p.takes <;> rfl

/-- **The book gives both lists the same coins, or returns an error with the same words for both.**
-/
theorem lendRow_re (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) :
    ∀ (ps : List (Part V W X)) (R : ReRow X' ps) (j : Nat),
      StrAlike (RowSame ps R) (lendRow B rows look a ps j) (lendRow B rows look a (reRow ps R) j)
  | [], _, _ => True.intro
  | p :: ps, R, j =>
    StrAlike.bind
      (P := fun (c : p.Coins) (c' : p.Coins) => c = c')
      (f := fun c => (lendRow B rows look a ps (j + 1)).map fun r => (c, r))
      (g := fun c => (lendRow B rows look a (reRow ps R.2) (j + 1)).map fun r => (c, r))
      (fun _ _ e => StrAlike.map (fun _ _ q => ⟨e, q⟩) (lendRow_re B rows look a ps R.2 (j + 1)))
      (by
        rw [lendPart_re]
        exact StrAlike.self _)

/-! ## 3 The two lists' rounds -/

/-- **The hypothesis on the moves, part by part**: as many moves; and from every pair of carried
states in `T`, at all coins and whatever was shown, the two lists of moves say the same and lead to
states in `T` again. -/
def RowTo (T : State W X → State W X' → Prop) : (ps : List (Part V W X)) → ReRow X' ps → Prop
  | [], _ => True
  | p :: ps, R =>
    (R.1.length = p.moves.length ∧
      ∀ (c : p.Coins) (t : State W X) (t' : State W X') (seen : List Fmt.RoundView), T t t' →
        MovesTo c T p.moves R.1 t t' seen) ∧
    RowTo T ps R.2

theorem Placed.rounds_eq_sum (h : Placed V W X) :
    h.rounds = (h.parts.map (·.moves.length)).sum := by
  unfold Placed.rounds
  rw [foldl_moves, Nat.zero_add]

theorem reRow_lens (T : State W X → State W X' → Prop) :
    ∀ (ps : List (Part V W X)) (R : ReRow X' ps), RowTo T ps R →
      (reRow ps R).map (·.moves.length) = ps.map (·.moves.length)
  | [], _, _ => rfl
  | p :: ps, R, h => by
    show R.1.length :: (reRow ps R.2).map (·.moves.length) =
      p.moves.length :: ps.map (·.moves.length)
    rw [h.1.1, reRow_lens T ps R.2 h.2]

theorem reRow_length : ∀ (ps : List (Part V W X)) (R : ReRow X' ps),
    (reRow ps R).length = ps.length
  | [], _ => rfl
  | _ :: ps, R => congrArg (· + 1) (reRow_length ps R.2)

/-- **The two lists' rounds are related.** `rs`: the sub-protocol's rounds, as many as the list has.
-/
theorem rowSteps_re (nm : String) (a : Place) (v : Option V)
    (T : State W X → State W X' → Prop) :
    ∀ (ps : List (Part V W X)) (R : ReRow X' ps) (j : Nat)
      (rs : List (Fmt.DeclaredRound × List Oracle)) (c : RowCoins ps) (c' : RowCoins (reRow ps R)),
      RowTo T ps R → RowSame ps R c c' → rs.length = (ps.map (·.moves.length)).sum →
      StepsAlike (MidBy T) (MidBy T) (rowSteps nm a v ps j rs c)
        (rowSteps nm a v (reRow ps R) j rs c')
  | [], _, _, _, _, _, _, _, _ => StepsAlike.nil (MidBy T)
  | p :: ps, R, j, rs, c, c', h, hc, hl => by
    have hl' : rs.length = p.moves.length + (ps.map (·.moves.length)).sum := by
      rw [hl, List.map_cons, List.sum_cons]
    have e1 : (rs.take p.moves.length).length = p.moves.length := by
      rw [List.length_take, hl']
      omega
    have e2 : (rs.drop p.moves.length).length = (ps.map (·.moves.length)).sum := by
      rw [List.length_drop, hl']
      omega
    show StepsAlike (MidBy T) (MidBy T)
      (p.steps nm ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
        rowSteps nm a v ps (j + 1) (rs.drop p.moves.length) c.2)
      ((p.reMove R.1).steps nm ⟨a, j⟩ (rs.take R.1.length) v c'.1 ++
        rowSteps nm a v (reRow ps R.2) (j + 1) (rs.drop R.1.length) c'.2)
    rw [h.1.1, ← hc.1]
    exact StepsAlike.append
      ⟨steps_faced p R.1 nm ⟨a, j⟩ _ v c.1 h.1.1, fun m m' q =>
        steps_alike p R.1 nm ⟨a, j⟩ _ v c.1 T m m' h.1.1 e1 q.1 q.2.1
          (h.1.2 c.1 m.st m'.st m.seen q.2.2)⟩
      (rowSteps_re nm a v T ps R.2 (j + 1) _ c.2 c'.2 h.2 hc.2 e2)

/-! ## 4 The sub-protocol -/

/-- **The sub-protocol at whose place the two prover's sides are.** -/
theorem member_re (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (b : Block S Cl) (hs : List (Placed V W X)) (hs' : List (Placed V W X'))
    (T : State W X → State W X' → Prop) (h : Placed V W X) (R : ReRow X' h.parts)
    (hf : (hs.find? fun h => h.place == b.place) = some h)
    (hf' : (hs'.find? fun h => h.place == b.place) = some ⟨h.place, reRow h.parts R⟩)
    (hT : RowTo T h.parts R) :
    StrAlike (StepsAlike (MidBy T) (MidBy T)) (memberSteps B rows look v b hs)
      (memberSteps B rows look v b hs') := by
  unfold memberSteps
  have er : (⟨h.place, reRow h.parts R⟩ : Placed V W X').rounds = h.rounds := by
    rw [Placed.rounds_eq_sum, Placed.rounds_eq_sum]
    exact congrArg List.sum (reRow_lens T h.parts R hT)
  by_cases h0 : (b.oracles.length != b.rounds.length) = true
  · rw [if_pos h0, if_pos h0]
    exact rfl
  · rw [if_neg h0, if_neg h0, hf, hf']
    dsimp only
    rw [er, reRow_lens T h.parts R hT, reRow_length]
    by_cases h1 : (h.rounds != b.rounds.length) = true
    · rw [if_pos h1, if_pos h1]
      exact rfl
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : (B.cuts.lookup b.place != some (h.parts.map (·.moves.length))) = true
      · rw [if_pos h2, if_pos h2]
        exact rfl
      · rw [if_neg h2, if_neg h2]
        by_cases h3 : (rows.any (fun r =>
            r.1.place == b.place && decide (h.parts.length ≤ r.1.part))) = true
        · rw [if_pos h3, if_pos h3]
          exact rfl
        · rw [if_neg h3, if_neg h3]
          by_cases h4 : (B.ahead.any (fun e =>
              e.spender.place == b.place && decide (h.parts.length ≤ e.spender.part))) = true
          · rw [if_pos h4, if_pos h4]
            exact rfl
          · rw [if_neg h4, if_neg h4]
            have g0 : b.oracles.length = b.rounds.length :=
              Decidable.byContradiction fun hne => h0 (bne_iff_ne.2 hne)
            have g1 : h.rounds = b.rounds.length :=
              Decidable.byContradiction fun hne => h1 (bne_iff_ne.2 hne)
            have gl : (b.rounds.zip b.oracles).length = (h.parts.map (·.moves.length)).sum := by
              rw [List.length_zip, g0, Nat.min_self, ← g1, Placed.rounds_eq_sum]
            exact StrAlike.map
              (fun c c' q => rowSteps_re b.name b.place v T h.parts R 0 _ c c' hT q gl)
              (StrAlike.mapError _ (lendRow_re B rows look b.place h.parts R 0))

end ProofFile.Honest

#print axioms ProofFile.Honest.lendPart_re
#print axioms ProofFile.Honest.lendRow_re
#print axioms ProofFile.Honest.rowSteps_re
#print axioms ProofFile.Honest.member_re
#print axioms ProofFile.Honest.StrAlike.mapError
#print axioms ProofFile.Honest.StrAlike.self
#print axioms ProofFile.Honest.Placed.rounds_eq_sum
#print axioms ProofFile.Honest.reRow_lens
#print axioms ProofFile.Honest.reRow_length
