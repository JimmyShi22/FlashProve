-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/LkN/KnowAt.lean: rules for `TWhole.KnowAt` (Cb/G6/Cut.lean): two reductions in a row, other
joints, a step without rounds in front or behind, a round in which the verifier draws, a family in a
row, and the passage from a fixed tuple of messages to oracle messages with samples.

Definitions and statements. The proofs: Cb/LkN/KnowAtProofs.lean. No protocol occurs here.
All statements are of reductions (`IOR`) and lists of errors. No type in them names an honest side.
Everywhere the extractor is `idX`: the further witness is handed back.

Main names:
  `Spec.knowAt_seq`: two in a row: errors in a row.
  `Spec.knowAt_conseq`: fewer statements, a larger input relation, a smaller output relation.
  `Spec.knowAt_post`, `Spec.knowAt_pre`: a map of the explicit part behind or in front; the oracles
    are copied.
  `Spec.knowAt_draw`: a round in which the verifier draws, from a count of bad values.
  `rChain X R n`, `eChain X R ε n`: the reductions R 0, .., R n in a row, bracketed to the left, and
    their errors. `Spec.knowAt_chain`.
  `Spec.knowAt_sig`: over a signature S (Cb/Ld/LdSig.lean): knowledge soundness of
    `R.keep S.Smp S.ext` from `S.over A` to `S.over B`, and the condition is carried.
  `Spec.knowAt_of_good`: a `GoodAt` gives `KnowAt`.
  `idX`: the extractor. `andW A P`: the joint A, and P of the witness. `Spec.knowAt_andW`: what
    reads the witness alone may be put beside both joints.

Limits: nothing on an honest prover. No statement bounds an error.
Terms: lean/GLOSSARY.md.

-/
import Cb.G6.Cut
import Cb.Ld.LdBattKit

set_option autoImplicit false

namespace Cb.LkN
open Iop Prob Hiop TWhole IOR

/-- The extractor that hands the further witness back. -/
@[reducible] def idX {M Xi Wp : Type} {Ei : ExtSpec} {s : Shape} :
    M → Xi × Ei.Str → Tr s → Wp → Wp := fun _ _ _ wp => wp

/-- The joint A, and P of the witness. -/
def andW {K X W : Type} {Ex : ExtSpec} (A : Rels K X Ex W) (P : W → Prop) : Rels K X Ex W :=
  ⟨fun x y w => A.rel x y w ∧ P w, fun a w => A.relR a w ∧ P w, A.on, A.core⟩

/-- The reductions R 0, .., R n in a row. -/
noncomputable def rChain {Ex : ExtSpec} (X : ℕ → Type) (R : ∀ l, IOR (X l) Ex (X (l + 1)) Ex) :
    ∀ n, IOR (X 0) Ex (X (n + 1)) Ex
  | 0 => R 0
  | n + 1 => (rChain X R n).seq (R (n + 1))

/-- Their errors in a row. -/
noncomputable def eChain {Ex : ExtSpec} (X : ℕ → Type) (R : ∀ l, IOR (X l) Ex (X (l + 1)) Ex)
    (ε : ∀ l, Err (R l).shape) : ∀ n, Err (rChain X R n).shape
  | 0 => ε 0
  | n + 1 => Err.app (eChain X R ε n) (ε (n + 1))

end Cb.LkN

namespace Cb.Spec
open Iop Prob Hiop TWhole IOR Cb.LkN

/-- States: two reductions in a row. -/
def knowAt_seq : Prop :=
  ∀ (K M X₁ X₂ X₃ Wp : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (A : Rels K X₁ E₁ (M × Wp)) (B : Rels K X₂ E₂ (M × Wp)) (C : Rels K X₃ E₃ (M × Wp))
      (ε₁ : Err R₁.shape) (ε₂ : Err R₂.shape),
    KnowAt R₁ A B idX ε₁ → KnowAt R₂ B C idX ε₂ → KnowAt (R₁.seq R₂) A C idX (Err.app ε₁ ε₂)

/-- States: the same reduction between other joints. -/
def knowAt_conseq : Prop :=
  ∀ (K K' M Xi Xo Wp : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo)
      (A : Rels K Xi Ei (M × Wp)) (B : Rels K Xo Eo (M × Wp))
      (A' : Rels K' Xi Ei (M × Wp)) (B' : Rels K' Xo Eo (M × Wp)) (ε : Err R.shape),
    KnowAt R A B idX ε → (∀ a, A'.on a → A.on a) → (∀ a w, A'.on a → A.relR a w → A'.relR a w) →
    (∀ b w, B'.relR b w → B.relR b w) → (∀ b, B.on b → B'.on b) → KnowAt R A' B' idX ε

/-- States: a map of the explicit part behind R. -/
def knowAt_post : Prop :=
  ∀ (K M Xi Xo Xo' Wp : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (φ : Xo → Xo')
      (A : Rels K Xi Ei (M × Wp)) (B : Rels K Xo Eo (M × Wp)) (C : Rels K Xo' Eo (M × Wp))
      (ε : Err R.shape),
    KnowAt R A B idX ε → (∀ x y, B.on (x, y) → C.on (φ x, y)) →
    (∀ x y w, B.on (x, y) → C.relR (φ x, y) w → B.relR (x, y) w) →
    KnowAt (R.post (fun x => some (φ x)) (ExtMap.id Eo)) A C idX ε

/-- States: a map of the explicit part in front of R. -/
def knowAt_pre : Prop :=
  ∀ (K M Xi Xi' Xo Wp : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (φ : Xi' → Xi)
      (A' : Rels K Xi' Ei (M × Wp)) (A : Rels K Xi Ei (M × Wp)) (B : Rels K Xo Eo (M × Wp))
      (ε : Err R.shape),
    KnowAt R A B idX ε → (∀ x y, A'.on (x, y) → A.on (φ x, y)) →
    (∀ x y w, A'.on (x, y) → A.relR (φ x, y) w → A'.relR (x, y) w) →
    KnowAt (R.pre (fun x => some (φ x)) (ExtMap.id Ei)) A' B idX ε

/-- States: a round in which the verifier draws: for each tuple of messages at most `err` values
lead from a false statement to a true one. -/
def knowAt_draw : Prop :=
  ∀ (K M X X' : Type) (Ex : ExtSpec) (Wp D : Type) [Fintype D] [Nonempty D] (nx : X → D → X')
      (A : Rels K X Ex (M × Wp)) (A' : Rels K X' Ex (M × Wp)) (err : ℕ),
    (∀ x y β, A.on (x, y) → A'.on (nx x β, y)) →
    (∀ x y (m : M), A.on (x, y) →
      cnt (fun β => ∃ wp, A'.relR (nx x β, y) (m, wp) ∧ ¬ A.relR (x, y) (m, wp)) ≤ err) →
    KnowAt (IOR.draw D nx Ex) A A' idX ((err, ()) : ℕ × Unit)

/-- States: a family in a row. -/
def knowAt_chain : Prop :=
  ∀ (K M Wp : Type) (Ex : ExtSpec) (X : ℕ → Type) (R : ∀ l, IOR (X l) Ex (X (l + 1)) Ex)
      (ε : ∀ l, Err (R l).shape) (A : ∀ l, Rels K (X l) Ex (M × Wp)) (n : ℕ),
    (∀ l ≤ n, KnowAt (R l) (A l) (A (l + 1)) idX (ε l)) →
    KnowAt (rChain X R n) (A 0) (A (n + 1)) idX (eChain X R ε n)

/-- States: from each fixed tuple of messages to oracle messages with samples. -/
def knowAt_sig : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (Kc St St' Wp : Type) (E₀ E₀' : ExtSpec)
      (R : IOR St E₀ St' E₀') (A : Rels Kc St E₀ (S.Msg × Wp)) (B : Rels Kc St' E₀' (S.Msg × Wp))
      (ε : Err R.shape),
    KnowAt R A B idX ε →
    (R.keep S.Smp S.ext).red.Know (S.over A).on (S.over A).relR (S.over B).relR
      (fun _ _ w => w) ε ∧
    ∀ a τ b, (S.over A).on a → (R.keep S.Smp S.ext).red.out a τ = some b → (S.over B).on b

/-- States: what reads the witness alone may be put beside both joints. -/
def knowAt_andW : Prop :=
  ∀ (K M Xi Xo Wp : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (A : Rels K Xi Ei (M × Wp))
      (B : Rels K Xo Eo (M × Wp)) (ε : Err R.shape) (Q : M × Wp → Prop),
    KnowAt R A B idX ε → KnowAt R (andW A Q) (andW B Q) idX ε

/-- States: the whole bundle gives its four clauses on the verifier. -/
def knowAt_of_good : Prop :=
  ∀ (K M Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (R : IOR Xi Ei Xo Eo)
      (H : R.Honest (M × Wi) (M × Wo)) (A : Rels K Xi Ei (M × Wi)) (B : Rels K Xo Eo (M × Wo))
      (ext : M → Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R),
    GoodAt R H A B ext P → KnowAt R A B ext P.err

end Cb.Spec
