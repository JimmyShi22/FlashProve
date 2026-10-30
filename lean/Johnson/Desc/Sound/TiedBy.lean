-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/TiedBy.lean: `TiedAt` (Johnson/Desc/Sound/ChainOfPromises.lean) WITH THE KIND'S
OWN FOUR WORDS NAMED, in the place of "there are". One definition, one lemma.

What is said. `TiedBy k q o o' R R'`: the eight clauses of `TiedAt k q` at the conditions o, o' and
the relations R, R': the law; the five ties; "a mark stays"; "the stored table decodes with the
record" rides. `TiedBy.tiedAt`: it gives `TiedAt`.

Limits: those of ChainOfPromises.lean. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.ChainOfPromises

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S)

/-- **`TiedAt` with the kind's own words named.** -/
def TiedBy (k : ℕ) (q : Piece C Fr A Cl W) (o o' : A × Fr.E.Str → Prop)
    (R R' : A × Fr.E.Str → W → Prop) : Prop :=
  q.GoodIn o o' R R' ∧
    (∀ a, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none → o a) ∧
    (∀ a τ b, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → onQ N Mg links ps get (k + 1) b) ∧
    (∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R' b w) ∧
    (∀ a τ b w, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w)) ∧
    (∀ a τ b w i, onQ N Mg links ps get k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
      relQ N Mg links ps get (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i a (q.ext a τ w)) ∧
    (∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none) ∧
    (∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2))

theorem TiedBy.tiedAt {k : ℕ} {q : Piece C Fr A Cl W} {o o' : A × Fr.E.Str → Prop}
    {R R' : A × Fr.E.Str → W → Prop} (h : TiedBy N Mg links ps get k q o o' R R') :
    TiedAt N Mg links ps get k q := ⟨o, o', R, R', h⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.TiedBy.tiedAt
