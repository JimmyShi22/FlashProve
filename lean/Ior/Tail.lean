-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Tail.lean: one invariant for a piece of a chain, and the rules that put pieces together.
The file is about the sequential composition of many interactive oracle reductions (IORs).

Definitions and statements; the proofs are in Ior/TailProofs.lean.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement. An extractor "decodes" if it is a function d of the
input's implicit part alone (`fun y _ _ => d y`); the rule for such extractors: `Spec.good_seq_dec`,
Ior/Chain.lean.
`H.withheld w x` is the union of two sets of verifier randomness that the honest side names:
`H.Bad`, which takes no argument, and `H.Hid w x`, which takes the witness and the explicit
statement. `R.tie ρ p` is a finite set of positions of the implicit instance, for each ρ and each
position p of the prover's oracles; it enters `R.given`.

Why: an IOP of proximity is a chain piece ; piece ; .. ; last block, and the parameter list that is
wanted of the whole asks for more than the bundle of Ior/Chain.lean. `Piece` is what is asked of one
piece; what is asked of the whole chain is at `TailTr`, `Spec.tailTr_end` (Cb/Ld/LdTowerKit.lean,
over `GoodT`).

Main names:
  `Piece R H A B ext P qi qo`:
    `good`: the bundle `Good`;
    `noHid`: nothing hidden is withheld;
    `noTie`: no oracle of R gives away a symbol of the implicit instance in this sense:
      `∀ ρ p, R.tie ρ p = ∅` (data: see `given`, Ior/Honest.lean);
    `bears`: R bears what follows (Ior/Bears.lean), from sets within qo to sets within qi.
  `Spec.piece_seq_dec`, `Spec.piece_pre`: see their docstrings.

Limits: the rules are conditional; they give no protocol. Errors are lists, one count for each round
(they are never summed here).
Terms: lean/GLOSSARY.md.
-/
import Ior.Bears

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- A piece of a chain. -/
structure Piece (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R)
    (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop) : Prop where
  good  : Good R H A B ext P
  noHid : ∀ w x, H.Hid w x = ∅
  noTie : ∀ ρ p, R.tie ρ p = ∅
  bears : R.Bears P.bud qi qo

end IOR

namespace Spec
open IOR

/-- A piece whose extractor decodes its input statement, then any piece, is a piece whose extractor
decodes (the middle implicit instance may read verifier messages: a fold). -/
def piece_seq_dec : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (d : E₁.Str → W₁)
      (e₂ : E₂.Str → Orcs R₂.shape → W₃ → W₂) (P₁ : Nums K R₁) (P₂ : Nums K R₂)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop) (qc : Finset E₃.Pos → Prop),
    Piece R₁ H₁ A B (fun y _ _ => d y) P₁ qa qb → Piece R₂ H₂ B C e₂ P₂ qb qc →
    Piece (R₁.seq R₂) (H₁.seq H₂) A C (fun y _ _ => d y) (P₁.seq P₂) qa qc

open Classical in
/-- A step without rounds before a piece. -/
def piece_pre : Prop :=
  ∀ (K Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wi' Wo : Type)
      (H : R.Honest Wi Wo) (A' : Rels K Xi' Ei' Wi') (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R) (f : Xi' → Option Xi)
      (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi) (back : Ei'.Str → Wi → Wi')
      (qi : Finset Ei.Pos → Prop) (qi' : Finset Ei'.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    Step f g m back A' A → Piece R H A B ext P qi qo → (∀ S, qi S → qi' (S.biUnion g.src)) →
    Piece (R.pre f g) (H.pre f g m) A' B
      (fun y o w => back y (ext (g.map y) o w)) (P.pre f g) qi' qo

end Spec
end Iop
