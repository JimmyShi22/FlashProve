--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/DrawsThatFit.lean: THE OUTPUT HEAD'S OWN ROUNDS: AT ALL PUBLIC
NUMBERS p THERE IS A LIST OF CHALLENGES THAT THE SUB-PROTOCOL's DECLARED ROUNDS CAN DRAW (drawsFit
p.rounds ds = true), AND THE TYPE OF EVERY ROW's COINS HAS A MEMBER. No premise.

What it is for. A statement "at all coins and all challenges that fit" says something only where
there are such: these two lemmas say that there are.

What it is not. TWO LEMMAS ON FORM. The list is made up: every drawn element is (1, 0, 0), every
position and matrix entry 0, no digest: nobody is said to draw it. The coins are all 0. Nothing on
soundness, on completeness or on what a proof hides.

  fitOne             a challenge made up to fit a declared round. A definition for proofs alone.
  head_known         the format knows the name of each of the sub-protocol's declared rounds.
  drawFit_fitOne     fitOne fits its round, where the format knows the round's name.
  drawsFit_fitOne    the like for a list of rounds.
  head_draws_exist   there is a list of challenges that fits.
  rowCoins_nonempty  the type of a row's coins has a member.
CALLED: nothing beyond the definitions (drawFit, drawsFit, RowCoins: Honest/Frame.lean; drawsMarkedNonzeroHaveNonzeroWords:
Johnson/Desc/Block.lean). head_known's proof follows head_unsealed's (Honest/K6/Law/Rounds.lean)
line for line.
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (drawsMarkedNonzeroHaveNonzeroWords fieldPrimeWord)
open VerifiableInference.Desc.Kinds

/-- A challenge made up to fit a declared round: every element (1, 0, 0), every position and matrix
entry 0, no digest. A definition for proofs alone. -/
def fitOne (d : Fmt.DeclaredRound) : Fmt.Drawn :=
  ⟨List.replicate d.entry.drawE (1, 0, 0), List.replicate d.entry.poss 0,
    List.replicate d.entry.trits 0, none⟩

/-- The format knows the name of each of the sub-protocol's declared rounds. No premise. -/
theorem head_known (p : Head.Par) :
    ∀ z ∈ p.rounds, (Fmt.kindOf z.entry.name).isSome = true := by
  intro z hz
  obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hz
  letI := p.sizes
  show (Fmt.kindOf R.name).isSome = true
  simp only [Head.rounds, Norm.rounds, FinalNorm.rounds, drawPoint.rounds, drawJoin.rounds,
    sendThenBatch.rounds, level.rounds, sumcheck.rounds, List.mem_append, List.mem_cons,
    List.mem_replicate, List.not_mem_nil, or_false] at hR
  simp only [or_assoc] at hR
  rcases hR with rfl | rfl | h | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl |
    rfl | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl
  case inr.inr.inl =>
    have hN0 : Norm.lNI = 0 := rfl
    rw [hN0] at h
    simp at h
  all_goals (dsimp only; decide)

/-- fitOne fits its round, where the format knows the round's name. -/
theorem drawFit_fitOne (d : Fmt.DeclaredRound) (h : (Fmt.kindOf d.entry.name).isSome = true) :
    drawFit d (fitOne d) = true := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 h
  have h1 : ((fitOne d).elems.length == d.entry.drawE) = true := by
    show ((List.replicate d.entry.drawE _).length == d.entry.drawE) = true
    rw [List.length_replicate]
    exact beq_self_eq_true _
  have h2 : ((fitOne d).poss.length == d.entry.poss) = true := by
    show ((List.replicate d.entry.poss _).length == d.entry.poss) = true
    rw [List.length_replicate]
    exact beq_self_eq_true _
  have h3 : ((fitOne d).trits.length == d.entry.trits) = true := by
    show ((List.replicate d.entry.trits _).length == d.entry.trits) = true
    rw [List.length_replicate]
    exact beq_self_eq_true _
  have h4 : (fitOne d).poss.all (· < 2 ^ d.entry.logN) = true := by
    refine List.all_eq_true.2 fun x hx => ?_
    rw [List.eq_of_mem_replicate hx]
    exact decide_eq_true (Nat.two_pow_pos _)
  have h5 : (fitOne d).trits.all (fun t => t == -1 || t == 0 || t == 1) = true := by
    refine List.all_eq_true.2 fun x hx => ?_
    rw [List.eq_of_mem_replicate hx]
    rfl
  have h6 : drawsMarkedNonzeroHaveNonzeroWords d ⟨[], fitOne d⟩ = true := by
    unfold drawsMarkedNonzeroHaveNonzeroWords
    rw [hk]
    refine List.all_eq_true.2 fun x hx => ?_
    obtain ⟨a, b⟩ := x
    have hb : b = (1, 0, 0) := List.eq_of_mem_replicate (List.of_mem_zip hx).2
    rw [hb, Bool.or_eq_true]
    exact Or.inr (by dsimp only; decide)
  have h7 : (fitOne d).elems.all
      (fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true := by
    refine List.all_eq_true.2 fun x hx => ?_
    rw [List.eq_of_mem_replicate hx]
    decide
  unfold drawFit
  rw [h1, h2, h3, h4, h5, h6, h7]
  rfl

/-- The like for a list of rounds. -/
theorem drawsFit_fitOne : ∀ zs : List Fmt.DeclaredRound,
    (∀ z ∈ zs, (Fmt.kindOf z.entry.name).isSome = true) → drawsFit zs (zs.map fitOne) = true
  | [], _ => rfl
  | z :: zs, h => by
    show (drawFit z (fitOne z) && drawsFit zs (zs.map fitOne)) = true
    rw [drawFit_fitOne z (h z List.mem_cons_self),
      drawsFit_fitOne zs fun w hw => h w (List.mem_cons_of_mem _ hw)]
    rfl

/-- **THERE IS A LIST OF CHALLENGES THAT THE DECLARED ROUNDS CAN DRAW.** No premise. -/
theorem head_draws_exist (p : Head.Par) : ∃ ds, drawsFit p.rounds ds = true :=
  ⟨_, drawsFit_fitOne _ (head_known p)⟩

/-- **THE TYPE OF A ROW's COINS HAS A MEMBER.** No premise. -/
theorem rowCoins_nonempty {V W X : Type} : ∀ ps : List (Part V W X), Nonempty (RowCoins ps)
  | [] => ⟨()⟩
  | p :: ps =>
    let ⟨b⟩ := rowCoins_nonempty ps
    ⟨((default : p.Coins), b)⟩

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.fitOne
#print axioms ProofFile.Honest.K6.head_known
#print axioms ProofFile.Honest.K6.drawFit_fitOne
#print axioms ProofFile.Honest.K6.drawsFit_fitOne
#print axioms ProofFile.Honest.K6.head_draws_exist
#print axioms ProofFile.Honest.K6.rowCoins_nonempty
