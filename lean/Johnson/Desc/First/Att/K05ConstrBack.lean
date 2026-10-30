-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ConstrBack.lean: kind K5: THE ITEM constr RIDES BACK OVER THE KIND's BLOCK: where it holds at the verifier's state after the block it holds at the state in front: the clauses "constr" (n ≠ m) and "ctxSmall" of K5FillRel
(Att/K05Riders.lean).

THE SHAPE. The meaning that is meant has, by its make,
  constr n p a y w  ↔  if p = .lookDigits then dP n a y w else (p = .small → bs n w) ∧ ∀ M i, decT y.cell a = some M → Hd M i → body n p i a y w :
the state a.2 and the strings y enter through dP, through the decoder decT and through body alone. That make's own file stands in a cone that does not compile on this ground: so THE SHAPE IS A PREMISE HERE (hC: an "iff" at values).
THE DECODER: hT: it reads nothing that the kind's lay turns (already a premise where the clause "decodes" is paid); the stored table's symbols are one at y and y' (SameBelow's first clause). So decT gives ONE value at the two states.

Main names: constr_back (one lemma, at every n and p) · k5FillRel_small · k5FillRel_constr (the two clauses' texts) · small_fits · constr_fits (Lean's own checks that the conclusions are the fields' types: each calls the theorem itself; they prove
nothing new).
PREMISES: hC · hT · for "ctxSmall": hBs: at (m, .small) the body reads neither the state nor the strings (at the meaning that is meant: the integer model's clause on the witness's integers) · for "constr": hD, hB: dP and body ride back over the lay, UNDER ALL THAT THE CLAUSE HAS IN HAND (the promise in front, "no mark", the hearing's return: so the ledger and what was heard are the heard ones, not any): AT THE
  MEANING THAT IS MEANT THESE SPEAK OF TWO LETTERS OF OTHER KINDS' FILES (the digits' part; the head's part) and of the request's reading: NAMED, NOT PAID.
THE LETTERS UNDER "FOR ALL": hC: a law of the meaning's make · hT: s fenced by s.here = .att a; c, h, G free on purpose (the decoder must not read what ANY lay turns) · hBs: a law on a letter of the filling · hD, hB: s, y fenced by the promise; hd, G pinned by the hearing's equation.
IS IT EMPTY HERE? Implications.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart onAt Part)
open VerifiableInference.Desc.Sound (Frame strsOf)

section
variable {Pp W Cells Ix : Type} {Fr : Frame} (Mg : Meaning Pp W) (π : Pp) (base : ℕ)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × First.S → Option Cells)
  (hT : ∀ c s a h G, s.here = .att a → decT c (π, behind s a h G) = decT c (π, s))
  (Hd : Cells → Ix → Prop) (bs : ℕ → W → Prop) (dP : ℕ → Pp × First.S → Strs → W → Prop)
  (body : ℕ → Part → Ix → Pp × First.S → Strs → W → Prop)
  (hC : ∀ n p a y w, Mg.constr n p a y w ↔
    if p = .lookDigits then dP n a y w
    else (p = .small → bs n w) ∧ ∀ M i, decT y.cell a = some M → Hd M i → body n p i a y w)
include hT hC

/-- **The item rides back**, at every segment n and part p. -/
theorem constr_back (n : ℕ) (p : Part) (Gd : First.S → First.AttOwn → Heard → Fork → Fr.E.Str → Prop)
    (hD : ∀ s att hd G (y y' : Fr.E.Str) w, Gd s att hd G y → s.here = .att att → SameBelow Fr base y y' →
      dP n (π, behind s att hd G) (strsOf Fr y') w → dP n (π, s) (strsOf Fr y) w)
    (hB : ∀ i s att hd G (y y' : Fr.E.Str) w, Gd s att hd G y → s.here = .att att → SameBelow Fr base y y' →
      body n p i (π, behind s att hd G) (strsOf Fr y') w → body n p i (π, s) (strsOf Fr y) w) :
    ∀ s att hd G (y y' : Fr.E.Str) w, Gd s att hd G y → s.here = .att att → SameBelow Fr base y y' →
      Mg.constr n p (π, behind s att hd G) (strsOf Fr y') w → Mg.constr n p (π, s) (strsOf Fr y) w := by
  intro s att hd G y y' w hg e hy h
  have hc : (strsOf Fr y').cell = (strsOf Fr y).cell := by
    show VerifiableInference.Desc.Sound.cellAt Fr y' = VerifiableInference.Desc.Sound.cellAt Fr y
    unfold VerifiableInference.Desc.Sound.cellAt
    rw [hy.1]
  rw [hC] at h ⊢
  by_cases hp : p = .lookDigits
  · rw [if_pos hp] at h ⊢
    exact hD s att hd G y y' w hg e hy h
  · rw [if_neg hp] at h ⊢
    refine ⟨h.1, fun M i hM hH => hB i s att hd G y y' w hg e hy (h.2 M i ?_ hH)⟩
    rw [hc, hT _ _ _ _ _ e]
    exact hM

/-- **The clause "ctxSmall" of K5FillRel.** -/
theorem k5FillRel_small (N : Numbers) (links : List ModelPart) (m : ℕ) (pl : Place) (O : List Item) (Q : List Pub)
    (own : Params.AttentionRounds)
    (hBs : ∀ i a a' y y' w, body m .small i a y w → body m .small i a' y' w) :
    ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
      Mg.constr m .small (π, behind s att hd G) (strsOf Fr y') w → Mg.constr m .small (π, s) (strsOf Fr y) w := by
  intro s att hd G _ y y' w _ _ e _ hy h
  rw [hC] at h ⊢
  rw [if_neg (by decide)] at h ⊢
  have hc : (strsOf Fr y').cell = (strsOf Fr y).cell := by
    show VerifiableInference.Desc.Sound.cellAt Fr y' = VerifiableInference.Desc.Sound.cellAt Fr y
    unfold VerifiableInference.Desc.Sound.cellAt
    rw [hy.1]
  refine ⟨h.1, fun M i hM hH => hBs i _ _ _ _ w (h.2 M i ?_ hH)⟩
  rw [hc, hT _ _ _ _ _ e]
  exact hM

/-- **The clause "constr" of K5FillRel.** -/
theorem k5FillRel_constr (N : Numbers) (links : List ModelPart) (m : ℕ) (pl : Place) (O : List Item) (Q : List Pub)
    (own : Params.AttentionRounds)
    (hD : ∀ n, n ≠ m → ∀ s att hd G rs (y y' : Fr.E.Str) w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
      dP n (π, behind s att hd G) (strsOf Fr y') w → dP n (π, s) (strsOf Fr y) w)
    (hB : ∀ n p, n ≠ m → ∀ i s att hd G rs (y y' : Fr.E.Str) w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
      body n p i (π, behind s att hd G) (strsOf Fr y') w → body n p i (π, s) (strsOf Fr y) w) :
    ∀ n p, n ≠ m → ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
      Mg.constr n p (π, behind s att hd G) (strsOf Fr y') w → Mg.constr n p (π, s) (strsOf Fr y) w :=
  fun n p hn s att hd G rs y y' w hon hm e hh hy h =>
    constr_back Mg π base decT hT Hd bs dP body hC n p
      (fun s att hd G y => onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) ∧ s.failed = none ∧
        ∃ rs, hear own (att.F, rs, 0) = some (hd, G, [], 0))
      (fun s att hd G y y' w hg e hy => by
        obtain ⟨g1, g2, rs, g3⟩ := hg
        exact hD n hn s att hd G rs y y' w g1 g2 e g3 hy)
      (fun i s att hd G y y' w hg e hy => by
        obtain ⟨g1, g2, rs, g3⟩ := hg
        exact hB n p hn i s att hd G rs y y' w g1 g2 e g3 hy)
      s att hd G y y' w ⟨hon, hm, rs, hh⟩ e hy h

theorem small_fits (N : Numbers) (links : List ModelPart) (m : ℕ) (pl : Place) (O : List Item) (Q : List Pub)
    (own : Params.AttentionRounds) (hBs : ∀ i a a' y y' w, body m .small i a y w → body m .small i a' y' w)
    (R : K5FillRel Mg N links π Fr base m pl O Q own) : K5FillRel Mg N links π Fr base m pl O Q own :=
  { R with ctxSmall := (k5FillRel_small Mg π base decT hT Hd bs dP body hC N links m pl O Q own hBs) }

theorem constr_fits (N : Numbers) (links : List ModelPart) (m : ℕ) (pl : Place) (O : List Item) (Q : List Pub)
    (own : Params.AttentionRounds)
    (hD : ∀ n, n ≠ m → ∀ s att hd G rs (y y' : Fr.E.Str) w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
      dP n (π, behind s att hd G) (strsOf Fr y') w → dP n (π, s) (strsOf Fr y) w)
    (hB : ∀ n p, n ≠ m → ∀ i s att hd G rs (y y' : Fr.E.Str) w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
      body n p i (π, behind s att hd G) (strsOf Fr y') w → body n p i (π, s) (strsOf Fr y) w)
    (R : K5FillRel Mg N links π Fr base m pl O Q own) : K5FillRel Mg N links π Fr base m pl O Q own :=
  { R with constr := (k5FillRel_constr Mg π base decT hT Hd bs dP body hC N links m pl O Q own hD hB) }

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.constr_back
#print axioms VerifiableInference.Desc.First.Att.P.k5FillRel_small
#print axioms VerifiableInference.Desc.First.Att.P.k5FillRel_constr
#print axioms VerifiableInference.Desc.First.Att.P.small_fits
#print axioms VerifiableInference.Desc.First.Att.P.constr_fits
