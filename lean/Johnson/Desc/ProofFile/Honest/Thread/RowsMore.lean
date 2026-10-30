-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/RowsMore.lean: HOW AN AUTHOR's `Good` REACHES A LAID ROW, IN
THE FORM IN WHICH THE KINDS' AUTHORS HOLD THEIR SIDES. Every side that they have typed is a value of
the frame's `Side.seated` (Honest/Side.lean): the member at a place of a description's list, a row
of parts with simulators, and falls: none, the author's own, or a parameter. The file's rule
(`file_owed_rows`, Honest/Thread/Rows.lean) asks `Good` at the side of the LAID row, with the WHOLE
chain's falls, at the `pre` of the row's place (`preOf`, Honest/Rule.lean). Lemmas; no definition.
General: no kind is named.

  1  `fallOf_congr`, `seated_congr`   the falls at a place, as one, read the falls AT THAT PLACE
     alone; so does a seated side. (Since `Good.refall` nothing here leans on these two.)
  2  `hand_of_seated`   the rule's premise at a laid row IS the sentence on `Side.seated` at the
     row's own place and parts: by unfolding
  3  `hand_of_house`   **from an author's own side**: σ₀, the value of `Side.seated` at WHATEVER
     falls fs₀ the author has seated it; `Good` at σ₀, at whatever letters. NO EQUATION ON THE FALLS
     (`seated_refall`, `Good.refall`: Rows.lean)
  4  `half_of_zip`   a row that is typed as parts.zip sims has these parts for its half, where there
     are at least as many simulators as parts: `zip` cuts to the shorter list without a word

WHAT AN AUTHOR ADDS, then: its `Good` at that `pre` · hσ (its side is seated: a look-up by the
place: an evaluation, or `lay_side_at` of Rows.lean) · for the prover's halves: the count of
`half_of_zip`.

Limits. Conditional lemmas on our own definitions. `Good`'s parameter `pre` is free in
`hand_of_seated` and `hand_of_house`: the same in premise and end. None is one of the library's
goals. This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y Pb : Type} {Bk : ProverCoinCounts}

/-! ## 1 The falls at a place -/

/-- **The falls at a place, as one, read the falls at that place alone.** -/
theorem fallOf_congr {fs fs' : List (Fall S)} {a : Place}
    (h : (fs.filter fun f => f.place == a) = fs'.filter fun f => f.place == a) :
    fallOf fs a = fallOf fs' a := by
  funext s ds
  unfold fallOf
  rw [h]

/-- So does a seated side. -/
theorem seated_congr {bs : List (Block S Cl)} {a : Place} {row : List (Part V W Y × Sim Pb)}
    {fs fs' : List (Fall S)} (h : fallOf fs a = fallOf fs' a) :
    Side.seated bs a row fs = Side.seated bs a row fs' := by
  unfold Side.seated
  rw [h]

/-! ## 2 and 3 What an author hands in of `Good` -/

/-- **The rule's premise at a laid row is the sentence on `Side.seated`** at the row's own place and
parts: no letter of the laying is read. -/
theorem hand_of_seated {φ : Face V W Pb} {ord : List Place} {chain ft : Nat} {fs : List (Fall S)}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (r : Unlettered V W Y Pb) (T : W → Thread Bk S Cl V W Y Pb)
    (Sd : W → Nat → Coins Bk → Mid W Y → Prop) (bs : List (Block S Cl))
    (h : ∀ σ, Side.seated bs r.place r.row fs = some σ →
      ∃ A' B', Good pre φ σ Bk ord chain ft A' B' r.On r.bud) :
    ∀ σ, (r.lay T Sd bs).side bs fs = some σ →
      ∃ A' B', Good pre φ σ Bk ord chain ft A' B' (r.lay T Sd bs).On (r.lay T Sd bs).bud := h

/-- **FROM AN AUTHOR's OWN SIDE.** fs₀: the falls at which the author has seated its side. fs: the
chain's. Nothing ties the two. -/
theorem hand_of_house {φ : Face V W Pb} {ord : List Place} {chain ft : Nat}
    {fs fs₀ : List (Fall S)} (r : Unlettered V W Y Pb) (T : W → Thread Bk S Cl V W Y Pb)
    (Sd : W → Nat → Coins Bk → Mid W Y → Prop) {bs : List (Block S Cl)}
    {σ₀ : Side S Cl V W Y Pb} {A' B' : Coins Bk → S → Mid W Y → Env → Prop}
    {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (hσ : Side.seated bs r.place r.row fs₀ = some σ₀)
    (g : Good pre φ σ₀ Bk ord chain ft A' B' r.On r.bud) :
    ∀ σ, (r.lay T Sd bs).side bs fs = some σ →
      ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁ (r.lay T Sd bs).On (r.lay T Sd bs).bud := by
  intro σ h
  have h' : Side.seated bs r.place r.row fs = some σ := h
  rw [seated_refall hσ fs] at h'
  obtain rfl := Option.some.inj h'
  exact ⟨_, _, g.refall _⟩

/-! ## 4 A row that is typed as parts.zip sims -/

/-- **Its half has these parts**, where there are at least as many simulators as parts. -/
theorem half_of_zip (a : Place) (ps : List (Part V W Y)) (ss : List (Sim Pb))
    (On : (u : Member V W Y Pb) → CsAll u.part.carries → Mid W Y → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (h : ps.length ≤ ss.length) :
    (⟨a, ps.zip ss, On, bud⟩ : Unlettered V W Y Pb).half = ⟨a, ps⟩ :=
  congrArg (Placed.mk a) (List.map_fst_zip h)

end ProofFile.Honest

#print axioms ProofFile.Honest.fallOf_congr
#print axioms ProofFile.Honest.seated_congr
#print axioms ProofFile.Honest.hand_of_seated
#print axioms ProofFile.Honest.hand_of_house
#print axioms ProofFile.Honest.half_of_zip
