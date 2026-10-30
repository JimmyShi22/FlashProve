-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerKit.lean: pieces and tails of a chain whose extractors may read the whole statement and
the whole transcript.

In standard terms: this file is about sequential composition of interactive oracle reductions. It
defines two records of properties, one for a part of a chain that does not end it (a piece,
`PieceTr`) and one for a part that ends it, to a statement without oracles (a tail, `TailTr`), and
proves that parts with these records compose.

Definitions, statements (each a `Prop` in `Iop.Spec`) and proofs. No protocol, no code occurs here.
`PieceTr` is the analogue, over the bundle `IOR.GoodT` (Ior/KnowCollGood.lean), of `IOR.Piece`
(Ior/Tail.lean), which is over `IOR.Good`.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why: a proximity test is a chain piece ; piece ; .. ; last block. Of the whole one needs more than
the bundle: nothing hidden is withheld; zero knowledge at no further reads, so that all nested
budgets are discharged; the verifier itself reads all that is tied to its positions; a bound on what
is needed of the input oracles.
`Spec.piece_seq_dec` (Ior/Tail.lean) asks that the first piece's extractor decode. Beyond
unique decoding there is no decoder: extractors go backwards, from a witness of the output
statement, and may read verifier messages and plain parts. With `GoodT` the rule for chains asks
nothing of extractors, so the two rules for chains here (`Spec.pieceTr_seq`, `Spec.tailTr_cons`)
have no side condition.

`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge. `H.withheld w x` is the union of two sets of verifier randomness
that the honest side names: `H.Bad`, which takes no argument, and `H.Hid w x`, which takes the
witness and the explicit statement. `noHid`: the set `H.Hid w x` is empty for all w and x. `noTie`:
the set `R.tie ρ p` is empty for all ρ and p. `R.tie ρ p` is a finite set of positions of the
implicit instance, for each ρ and each position p of the prover's oracles; it enters `R.given`.
`R.Tied`: for every ρ and every position p that the verifier reads in the prover's oracles,
`R.tie ρ p` lies within the positions that the verifier reads in the implicit instance.
`R.Bears bud qi qo`: for every ρ and every set U of positions of the new implicit instance for which
qo holds, `bud ρ` holds of the positions `R.srcO ρ q` for q in U, and qi holds of `R.need ρ U`.
`P.bud ρ T` is a predicate on the verifier's randomness ρ and a set T of further positions; the
equation of the clause `exact` of `Good` is asked, for each (x, y, w) in `A.rel`, exactly at the
pairs (ρ, T) for which `bud ρ T` holds and ρ lies outside `H.Hid w x`. These conditions stand here
inside the definitions `PieceTr` and `TailTr`.

Main names:
  `PieceTr R H A B ext P qi qo`: `GoodT`; nothing hidden is withheld (`noHid`:
    `∀ w x, H.Hid w x = ∅`); nothing is tied (`noTie`: `∀ ρ p, R.tie ρ p = ∅`; data: see `given`,
    Ior/Honest.lean); R bears what follows (`bears`; Ior/Bears.lean), from sets of positions within
    qo to sets within qi.
  `TailTr Q H A B ext P qi`: for Q to a statement without oracles: `GoodT`; nothing hidden is
    withheld (`noHid`); the verifier reads all that is tied to its positions (`tied`); Q bears
    "nothing follows" (`bears`).
  `Spec.pieceTr_of_piece`: from `Piece` (Ior/Tail.lean) to `PieceTr`, at the same numbers and
    demands on positions.
  `Spec.pieceTr_seq`, `Spec.tailTr_cons`: errors in a row, probabilities added, budgets composed,
    extractors composed (d: the value where the first verifier rejects).
  `Spec.pieceTr_mono`, `Spec.tailTr_mono`: weaker demands on positions.
  `Spec.pieceTr_pure`: a step without rounds (Ior/Frame.lean: `Step`) is a piece, if qi holds of the
    sources of every set within qo.
  `Spec.tailTr_end`: under the hypotheses of its statement, what a whole chain has at the end:
    strings (`Q.shape.IsPoint`), local, complete outside a public set (`∀ w x, H.Hid w x = ∅`), its
    probability, knowledge sound with its extractor ext, honest-verifier exact zero knowledge at
    T = ∅ (`Honest.Exact`, Ior/Honest.lean), `Tied`, and what the simulator is given (in particular
    what the verifier reads) is within qi (in this sense:
    `∀ ρ, qi (Q.given ρ ∅) ∧ Q.extReads ρ ⊆ Q.given ρ ∅`; `given`: Ior/Honest.lean).

Notation:
  `R`, `Q`: of type `IOR` (Ior/Ior.lean);
  `H`: of type `R.Honest`, `Q.Honest` (Ior/Honest.lean);
  `A`, `B`: joints (`IOR.Rels`, Ior/Chain.lean), with the fields
    `rel`: the relation of the honest side;
    `relR`: its relaxation: what knowledge soundness speaks of;
    `on`: the statements of which knowledge soundness speaks;
    `core`;
  `P`: of type `IOR.Nums` (Ior/Chain.lean; fields `err`, `pBad`, `pHid`, `bud`, `cov`);
  `qi`, `qo`: predicates on sets of positions, of types `Finset Ei.Pos → Prop`,
    `Finset Eo.Pos → Prop`.

Limits: this file says nothing on further reads of the chain's own oracles by a distinguisher,
beside what follows in the chain. A tail here ends in zero knowledge of the verifier's view alone.
So a prover that wrote its witness into a blinded oracle that nobody reads would pass
(Ior/BatchTest.lean: `exact_empty`, `not_exact_one`).
The rules are conditional; they give no protocol.
Errors are lists, one count for each round; they are never summed here.
This file says nothing on running times of extractors.

Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollGood
import Ior.TailProofs
import Ior.FrameProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- A piece of a chain, with an extractor that may read the statement and the transcript. -/
structure PieceTr (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R)
    (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop) : Prop where
  good  : GoodT R H A B ext P
  noHid : ∀ w x, H.Hid w x = ∅
  noTie : ∀ ρ p, R.tie ρ p = ∅
  bears : R.Bears P.bud qi qo

/-- A tail of a chain: to a statement without oracles. -/
structure TailTr (Q : IOR Xi Ei Xo extNone) (H : Q.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo extNone Wo) (ext : Xi × Ei.Str → Tr Q.shape → Wo → Wi)
    (P : Nums K Q) (qi : Finset Ei.Pos → Prop) : Prop where
  good  : GoodT Q H A B ext P
  noHid : ∀ w x, H.Hid w x = ∅
  tied  : Q.Tied
  bears : Q.Bears P.bud qi fun _ => True

end IOR

namespace Spec
open IOR

def pieceTr_of_piece : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Ei.Str → Orcs R.shape → Wo → Wi)
      (P : Nums K R) (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    Piece R H A B ext P qi qo → PieceTr R H A B (fun a τ w => ext a.2 τ.read w) P qi qo

/-- A piece, then a piece, is a piece. -/
def pieceTr_seq : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop) (qc : Finset E₃.Pos → Prop),
    PieceTr R₁ H₁ A B e₁ P₁ qa qb → PieceTr R₂ H₂ B C e₂ P₂ qb qc →
    PieceTr (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂) qa qc

/-- A piece, then a tail, is a tail. -/
def tailTr_cons : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ : ExtSpec) (R : IOR X₁ E₁ X₂ E₂) (Q : IOR X₂ E₂ X₃ extNone)
      (W₁ W₂ W₃ : Type) (H₁ : R.Honest W₁ W₂) (H₂ : Q.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ extNone W₃) (e₁ : X₁ × E₁.Str → Tr R.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr Q.shape → W₃ → W₂) (d : W₁) (P₁ : Nums K R) (P₂ : Nums K Q)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop),
    PieceTr R H₁ A B e₁ P₁ qa qb → TailTr Q H₂ B C e₂ P₂ qb →
    TailTr (R.seq Q) (H₁.seq H₂) A C (IOR.extSeq R Q e₁ e₂ d) (P₁.seq P₂) qa

/-- Weaker demands on positions. -/
def pieceTr_mono : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (qi qi' : Finset Ei.Pos → Prop) (qo qo' : Finset Eo.Pos → Prop),
    PieceTr R H A B ext P qi qo → (∀ S, qi S → qi' S) →
    (∀ U, qo' U → qo U) → PieceTr R H A B ext P qi' qo'

def tailTr_mono : Prop :=
  ∀ (K Xi Xo : Type) (Ei : ExtSpec) (Q : IOR Xi Ei Xo extNone) (Wi Wo : Type) (H : Q.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo extNone Wo) (ext : Xi × Ei.Str → Tr Q.shape → Wo → Wi)
      (P : Nums K Q) (qi qi' : Finset Ei.Pos → Prop),
    TailTr Q H A B ext P qi → (∀ S, qi S → qi' S) → TailTr Q H A B ext P qi'

open Classical in
/-- Under the two hypotheses below, a step without rounds is a piece. -/
def pieceTr_pure : Prop :=
  ∀ (K X X' : Type) (E E' : ExtSpec) (W W' : Type) (A : Rels K X E W) (B : Rels K X' E' W')
      (f : X → Option X') (g : ExtMap E E') (m : X × W → X' × W') (back : E.Str → W' → W)
      (qi : Finset E.Pos → Prop) (qo : Finset E'.Pos → Prop),
    Step f g m back A B → (∀ U, qo U → qi (U.biUnion g.src)) →
    PieceTr (IOR.pure f g) (Honest.pure f g m) A B (fun a _ w => back a.2 w) (Nums.pure K f g) qi qo

/-- What a whole chain has at the end. -/
def tailTr_end : Prop :=
  ∀ (K Xi Xo : Type) (Ei : ExtSpec) (Q : IOR Xi Ei Xo extNone) (Wi Wo : Type) (H : Q.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo extNone Wo) (ext : Xi × Ei.Str → Tr Q.shape → Wo → Wi)
      (P : Nums K Q) (qi : Finset Ei.Pos → Prop),
    TailTr Q H A B ext P qi →
    Nonempty Q.shape.IsPoint ∧ Q.IsLocal ∧ H.Acc A.rel B.rel ∧ (∀ w x, H.Hid w x = ∅) ∧
    prRho H.Bad ≤ P.pBad ∧ Q.red.Know A.on A.relR B.relR ext P.err ∧
    H.Exact A.rel (fun _ T => T = ∅) ∧ Q.Tied ∧ ∀ ρ, qi (Q.given ρ ∅) ∧ Q.extReads ρ ⊆ Q.given ρ ∅

end Spec

open IOR

theorem pieceTr_of_piece : Spec.pieceTr_of_piece := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨goodT_of_good _ _ _ _ _ _ _ _ _ _ _ _ _ h.good, h.noHid, h.noTie, h.bears⟩

theorem pieceTr_seq : Spec.pieceTr_seq := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ qa qb qc h₁ h₂
  exact ⟨goodT_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ h₁.good h₂.good,
    noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid h₂.noHid,
    noTie_seq _ _ _ _ _ _ _ _ h₁.noTie h₂.noTie,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears h₂.bears⟩

theorem tailTr_cons : Spec.tailTr_cons := by
  intro K X₁ X₂ X₃ E₁ E₂ R Q W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ qa qb h₁ h₂
  exact ⟨goodT_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ h₁.good h₂.good,
    noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid h₂.noHid,
    tied_seq _ _ _ _ _ _ _ _ h₁.noTie h₂.tied,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears h₂.bears⟩

theorem pieceTr_mono : Spec.pieceTr_mono := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hi ho =>
  ⟨h.good, h.noHid, h.noTie, bears_mono _ _ _ _ _ _ _ _ _ _ _ h.bears (fun _ _ hb => hb) hi ho⟩

theorem tailTr_mono : Spec.tailTr_mono := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hi =>
  ⟨h.good, h.noHid, h.tied,
    bears_mono _ _ _ _ _ _ _ _ _ _ _ h.bears (fun _ _ hb => hb) hi (fun _ hU => hU)⟩

open Classical in
theorem pieceTr_pure : Spec.pieceTr_pure := by
  intro K X X' E E' W W' A B f g m back qi qo hS hq
  refine ⟨goodT_of_good _ _ _ _ _ _ _ _ _ _ _ (fun y _ w => back y w) _
      (good_pure K X X' E E' W W' A B f g m back hS),
    fun _ _ => rfl, fun _ _ => rfl,
    fun ρ U hU => ⟨trivial, ?_⟩⟩
  convert hq U hU using 1
  ext q
  simp [IOR.need, IOR.given, IOR.pure]

theorem tailTr_end : Spec.tailTr_end := by
  intro K Xi Xo Ei Q Wi Wo H A B ext P qi h
  have he := bears_end _ _ _ _ Q P.bud qi _ h.bears trivial
  refine ⟨h.good.point, h.good.isLocal, h.good.acc, h.noHid, h.good.prBad, h.good.know, ?_, h.tied,
    fun ρ => ⟨(he ρ).2, fun q hq => mem_given.2 (Or.inl hq)⟩⟩
  obtain ⟨S, hS⟩ := h.good.exact
  exact ⟨S, fun x y w hR ρ hρ T hT => hS x y w hR ρ hρ T (hT ▸ (he ρ).1)⟩

end Iop
