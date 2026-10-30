-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/FieldGood.lean: what the one law buys (`FieldAt.step`,
`FieldFit.step`, FieldLaw.lean): whoever proves `Good` (Side.lean) at a side, from a condition
before the place that has the field beside it, to its own condition after the place, has `Good` with
the field beside that condition too. The field's half after the place is paid here, once, for every
side: also for a side whose parts never read the field.

  `roundsUpTo_seated`   at a list's side, `roundsUpTo` is `roundsBefore` and then the rounds of the
     side's own sub-protocol
  `WithField`   a condition with `FieldAt` and `FieldFit` beside it
  `plays_field`   the field `plays` of `Good`
  `Good.field`   `Good` whole

Limits.
  * That the field's condition holds at a chain's start is not proved.
  * No example.
  * No lemma states `Good.field` at `Lettered.withField` (Owed.lean): `roundsUpTo_seated` and
    `Good.field` are its two pieces.
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `plays_field`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.FieldLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type}

/-- At a list's side, `roundsUpTo` is `roundsBefore` and then the rounds of the side's own
sub-protocol. -/
theorem roundsUpTo_seated {Bk : ProverCoinCounts} {L : Lettered Bk S Cl V W X Pb} {bs : List (Block S Cl)}
    {fs : List (Fall S)} {σ : Side S Cl V W X Pb} (h : L.side bs fs = some σ) :
    roundsUpTo bs L.place = roundsBefore bs L.place ++ σ.block.rounds := by
  unfold Lettered.side Side.seated at h
  unfold roundsUpTo
  cases hf : bs.find? fun b => b.place == L.place with
  | none =>
    rw [hf] at h
    cases h
  | some b =>
    rw [hf] at h
    obtain rfl := Option.some.inj h
    rfl

/-- A condition with what the field holds, and the law's three side conditions, beside it. -/
def WithField {Bk : ProverCoinCounts} (chain firstTree : Nat) (decls : List Fmt.DeclaredRound) (base : List OpenedColumn)
    (skip : Nat) (A : Coins Bk → S → Mid W X → Env → Prop) :
    Coins Bk → S → Mid W X → Env → Prop :=
  fun k s m E => A k s m E ∧ FieldAt chain firstTree decls base skip m E ∧ FieldFit decls skip m E

section
variable {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {chain firstTree skip : Nat}
  {decls : List Fmt.DeclaredRound} {base : List OpenedColumn} {A B : Coins Bk → S → Mid W X → Env → Prop}

/-- **The field `plays` of `Good`**: from the field beside A to B, it gives the field beside B. -/
theorem plays_field
    (h : ∀ k s m E ds, WithField chain firstTree decls base skip A k s m E →
      drawsFit σ.block.rounds ds = true → σ.stopAt φ m.st.input m.loc ds = none →
      ∃ (c : RowCoins σ.half.parts) (y : List Played × Mid W X) (cols : List OpenedColumn),
        lendRow Bk (Bk.rowsOf chain) (k.look chain) σ.block.place σ.half.parts 0 = .ok c ∧
        play (σ.half.steps σ.block (φ.sees m.st.input) c) ds [] m = .ok y ∧
        fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree σ.block.rounds ds)
          [] = .ok cols ∧
        ∀ s' n, σ.block.step firstTree s (roundsOf y.1) cols = .ok (s', n) →
          B k s' (Mid.took y.2 cols) (E.add y.1)) :
    ∀ k s m E ds, WithField chain firstTree decls base skip A k s m E →
      drawsFit σ.block.rounds ds = true → σ.stopAt φ m.st.input m.loc ds = none →
      ∃ (c : RowCoins σ.half.parts) (y : List Played × Mid W X) (cols : List OpenedColumn),
        lendRow Bk (Bk.rowsOf chain) (k.look chain) σ.block.place σ.half.parts 0 = .ok c ∧
        play (σ.half.steps σ.block (φ.sees m.st.input) c) ds [] m = .ok y ∧
        fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree σ.block.rounds ds)
          [] = .ok cols ∧
        ∀ s' n, σ.block.step firstTree s (roundsOf y.1) cols = .ok (s', n) →
          WithField chain firstTree (decls ++ σ.block.rounds) base skip B k s'
            (Mid.took y.2 cols) (E.add y.1) := by
  intro k s m E ds hA hf hs
  obtain ⟨c, y, cols, h1, h2, h3, h4⟩ := h k s m E ds hA hf hs
  obtain ⟨-, hF, hFit⟩ := hA
  exact ⟨c, y, cols, h1, h2, h3, fun s' n hst =>
    ⟨h4 s' n hst, hF.step hFit.2.2 hFit.1 hFit.2.1 h2 h3,
      hFit.step h2 (drawsFit_length _ _ hf).symm⟩⟩

/-- **`Good` whole**: who has `Good` from the field beside A to B has it to the field beside B. -/
theorem Good.field {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {ord : List Place}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre φ σ Bk ord chain firstTree
      (WithField chain firstTree decls base skip A) B On bud) :
    Good pre φ σ Bk ord chain firstTree (WithField chain firstTree decls base skip A)
      (WithField chain firstTree (decls ++ σ.block.rounds) base skip B) On bud :=
  ⟨g.fits, plays_field g.plays, g.acc, g.exact, g.fresh⟩

end

end ProofFile.Honest

#print axioms ProofFile.Honest.roundsUpTo_seated
#print axioms ProofFile.Honest.plays_field
#print axioms ProofFile.Honest.Good.field
#print axioms ProofFile.Honest.WithField
