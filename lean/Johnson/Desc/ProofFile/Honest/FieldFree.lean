-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FieldFree.lean: what the field costs a side whose proofs do not speak
of it: nothing. Whoever has `Good` (Side.lean), from its own condition before the place to its own
condition after it, has `Good` with the field beside both (`WithField`, FieldGood.lean); and so for
a list (`Lettered.withField`, Owed.lean): that is what `Owed.good` asks of the list.

  `Good.weaken`   `Good` from a stronger condition before the place: `plays` and `acc` alone name it
  `Good.withField`   from `Good` at A and B to `Good` with the field beside both
  `Lettered.goodAt_withField`   the same for a list

Limits.
  * `plays` says B at `Mid.took`: a proof of `plays` that ends at the state after the rounds,
    without the columns taken, has to be led to the state that has taken them.
  * A side whose parts read the field cannot start from its own condition alone: it needs the field
    among its hypotheses (`Lettered.goodAt_field`, FieldOwed.lean).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.FieldOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type}

section
variable {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
  {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {ord : List Place}
  {chain firstTree : Nat} {A A' B : Coins Bk → S → Mid W X → Env → Prop}
  {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
  {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}

/-- `Good` from a stronger condition before the place. -/
theorem Good.weaken (h : ∀ k s m E, A' k s m E → A k s m E)
    (g : Good pre φ σ Bk ord chain firstTree A B On bud) :
    Good pre φ σ Bk ord chain firstTree A' B On bud :=
  ⟨g.fits, fun k s m E ds hA => g.plays k s m E ds (h k s m E hA),
    fun k s m E ds hA => g.acc k s m E ds (h k s m E hA), g.exact, g.fresh⟩

/-- **From `Good` at A and B to `Good` with the field beside both.** -/
theorem Good.withField {decls : List Fmt.DeclaredRound} {base : List OpenedColumn} {skip : Nat}
    (g : Good pre φ σ Bk ord chain firstTree A B On bud) :
    Good pre φ σ Bk ord chain firstTree (WithField chain firstTree decls base skip A)
      (WithField chain firstTree (decls ++ σ.block.rounds) base skip B) On bud :=
  Good.field (g.weaken fun _ _ _ _ h => h.1)

end

/-- **The same for a list: who has `goodAt` of a list has what `Owed.good` asks of it.** -/
theorem Lettered.goodAt_withField {Bk : ProverCoinCounts} {L : Lettered Bk S Cl V W X Pb}
    {chain firstTree skip : Nat} {bs : List (Block S Cl)} {base : List OpenedColumn}
    {earlier : List (Nat × Nat × List Fmt.DeclaredRound)} {φ : Face V W Pb} {ord : List Place}
    {fs : List (Fall S)}
    (h : L.goodAt earlier φ bs ord chain firstTree fs) :
    (L.withField chain firstTree bs base skip).goodAt earlier φ bs ord chain firstTree
      fs :=
  Lettered.goodAt_field fun σ hσ => (h σ hσ).weaken fun _ _ _ _ x => x.1

end ProofFile.Honest

#print axioms ProofFile.Honest.Good.weaken
#print axioms ProofFile.Honest.Good.withField
#print axioms ProofFile.Honest.Lettered.goodAt_withField
