-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerKitChain.lean: under the hypotheses below, a chain of pieces, some of which are masked
blocks and some whole tests, is a piece (one that may tie, if it holds whole tests); if it ends a
protocol it is a tail.

In standard terms: sequential composition of interactive oracle reductions, for chains of any
length. From properties of the single steps and one property of the whole chain (`c.Ok`), the chain
taken as one step gets the records of properties of Cb/Ld/LdTowerKit.lean and
Cb/Ld/LdLinCloseKit.lean (`PieceTr`, `TailTr`, `ClosedTr`).
`PieceTr`, a piece of a chain, asks of a reduction between two joints the bundle `IOR.GoodT` and
three further clauses, `noHid`, `noTie` and `bears`, which Cb/Ld/LdTowerKit.lean states (`bears`
through `IOR.Bears`, Ior/Bears.lean); `IOR.Piece` (Ior/Tail.lean) asks the same over `IOR.Good`.
`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`ClosedTr`, a closed piece (in Lean's words: a piece of a chain that may tie), asks of a reduction
between two joints the bundle `IOR.GoodT` and four further clauses, `noHid`, `tied`, `free` and
`bears`, which Cb/Ld/LdLinCloseKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`,
Ior/Bears.lean). `IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one
reduction, with its honest side, between two joints, at given numbers; among its clauses:
completeness between the honest relations, outside sets of verifier randomness whose probabilities
further clauses bound by the numbers; round-by-round knowledge soundness (`Know`) between the
relaxed relations, on the input joint's set of statements, with a given extractor, at the numbers'
list of errors; and one on honest-verifier zero knowledge. `GoodB` is `IOR.GoodT` without its clause
on zero knowledge. In this file's statements the three records stand as hypotheses and as
conclusions.

Definitions, statements (a `Prop` in `Iop.Spec` each, but for four unfolding lemmas on `SidesC`,
`SidesCT`) and proofs. No protocol, no code occurs here.

Why: `PieceTr`, `TailTr` (Cb/Ld/LdTowerKit.lean) and `ClosedTr` (Cb/Ld/LdLinCloseKit.lean: a piece
that may tie, so that whole tests may stand in the middle of a chain) ask the whole bundle `GoodT`
of each piece. A block whose masks were sent in advance (Ior/Masked.lean) is `GoodM`, not `GoodT`:
it has no zero knowledge of its own (exactly: `masked_not_exact`, Ior/Masked.lean).
Ior/KnowCollPiece.lean takes the notions apart: all of the bundle but zero knowledge (`GoodB`) and
the budgets' half (`Side`, `SideT`) go piece by piece; zero knowledge is asked of the whole chain
(Ior/KnowCollRulesChain.lean: `c.Ok`, `chain_ok`). Here the parts are put together again, at the
three notions.

Main names:
  `Spec.pieceTr_iff`, `Spec.tailTr_iff`, `Spec.closedTr_iff`: a piece is a `PieceB` that is
    honest-verifier zero knowledge in the exact form (`Honest.Exact`, Ior/Honest.lean); likewise a
    tail, and a piece that may tie.
  `SideC R H bud qi qo`: the budgets' half of a piece that may tie: nothing hidden is withheld
    (`noHid`: `∀ w x, H.Hid w x = ∅`); the verifier reads all that is tied to its positions (`tied`:
    `R.Tied`, Ior/Batch.lean); those of its own positions that survive are tied to nothing (`free`:
    `R.Free`, Cb/Ld/LdLinCloseKit.lean); it bears what follows (`bears`: `R.Bears bud qi qo`,
    Ior/Bears.lean). `ClosedB`: `GoodB` and that half.
    `R.tie ρ p` is a finite set of positions of the implicit instance, for each ρ and each position
    p of the prover's oracles; it enters `R.given`. `R.Tied`: for every ρ and every position p that
    the verifier reads in the prover's oracles, `R.tie ρ p` lies within the positions that the
    verifier reads in the implicit instance. `R.Free`: for every ρ, every position q of the new
    implicit instance and every p in `R.srcO ρ q`, the set `R.tie ρ p` is empty.
    `R.Bears bud qi qo`: for every ρ and every set U of positions of the new implicit instance for
    which qo holds, `bud ρ` holds of the positions `R.srcO ρ q` for q in U, and qi holds of
    `R.need ρ U`. The three conditions stand here inside the definition `SideC`.
  `Spec.sideC_of_side`, `Spec.sideC_seq`, `Spec.sideT_consC`: every `Side` is one; two in a row;
    one, then a last piece.
  `Spec.pieceTr_seq_masked`, `Spec.closedTr_seq_masked`: a piece that is fresh for the block's masks
    (Ior/KnowCollRulesMask.lean), then a masked block with the budgets' half, is a piece. Likewise
    for a piece that may tie. (The half of a masked block: Ior/KnowCollPiece.lean, `side_of_mm`.)
On chains (bracketed to the left; sub-protocols are chains and are appended):
  `Spec.chain_piece`, `Spec.chain_closed`: see their doc comments.
  `Spec.chain_tail`: `c.Ok` and `c.SidesCT qa`, for a chain to a statement without oracles: the
    chain as one link is a `TailTr`. So `Spec.tailTr_end` (Cb/Ld/LdTowerKit.lean: see its row in
    that head) applies to that link: honest-verifier zero knowledge at no further reads (T = ∅); all
    nested budgets discharged; errors in a row.
  `Spec.chain_tail_append`: the form for a sub-protocol whose closing is a parameter: a core chain
    c₀ (`Ok`, `SidesC`) and a closing chain c that comes after it (`c.OkFrom c₀`: its masked links'
    masks may have been sent in c₀; `c.SidesCT`): `(c₀.append c).link d` is a `TailTr`.

Notation:
  `c`: a chain of links, bracketed to the left (`IOR.Chain`, Ior/KnowCollRulesChain.lean);
  `c.link d`: the chain as one link (in the same file);
  `d`: an argument of `link`, of type `A.W`;
  `c.Ok`: the first link has `GoodT`; each later link `l` has `l.GoodT`, or `l.GoodM D` for some
    `D : MaskData` with `FreshFor` of the chain before it (in the same file);
  `c.OkFrom c₀`: every link `l` of c has `l.GoodT`, or `l.GoodM D` with `FreshFor` of c₀ and the
    links of c before it (Ior/KnowCollPiece.lean);
  `qi`, `qo`, `qa`, `qb`, `qc`: predicates on sets of positions of an implicit instance;
  `bud`: by type `Rho R.shape → Finset (OPos R.shape) → Prop`.

Limits: a closing that holds a masked block whose masks were sent before the closing is no tail by
itself, and no rule can make it one: it is not zero knowledge for every witness (Ior/Masked.lean:
`masked_not_exact`). A statement that takes "a closing with TailTr" as a hypothesis cannot be
applied to such a closing. The closing has to be a chain with a condition relative to what stands
before it.
Mind the brackets: `(c₀.append c).link d` is bracketed to the left; "c₀ as one link, then c as one
link" is another term, of which nothing is said here.
What the head of Cb/Ld/LdTowerKit.lean lists as not said is not said here either: no further reads
by a distinguisher.
This file says nothing on batches.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseKit
import Ior.KnowCollPiece

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- The budgets' half of a piece that may tie. -/
structure SideC (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
    (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop) : Prop where
  noHid : ∀ w x, H.Hid w x = ∅
  tied  : R.Tied
  free  : R.Free
  bears : R.Bears bud qi qo

/-- A piece that may tie, without zero knowledge of its own. -/
structure ClosedB (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R)
    (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop) : Prop where
  base : GoodB R H A B ext P
  side : SideC R H P.bud qi qo

def Link.SideC {A B : Joint K} (l : Link K A B)
    (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop) : Prop :=
  IOR.SideC l.R l.H l.P.bud qa qb

namespace Chain

/-- Every link has the half that may tie, with some demands on positions at the joints between. -/
def SidesC :
    {A B : Joint K} → Chain K A B → (Finset A.E.Pos → Prop) → (Finset B.E.Pos → Prop) → Prop
  | _, _, .one l, qa, qb => l.SideC qa qb
  | _, _, .snoc (B := B) c l, qa, qc => ∃ qb : Finset B.E.Pos → Prop, c.SidesC qa qb ∧ l.SideC qb qc

/-- the same for a chain that ends a protocol: the last link has the half of a last piece -/
def SidesCT : {A B : Joint K} → Chain K A B → (Finset A.E.Pos → Prop) → Prop
  | _, _, .one l, qa => l.SideT qa
  | _, _, .snoc (B := B) c l, qa => ∃ qb : Finset B.E.Pos → Prop, c.SidesC qa qb ∧ l.SideT qb

end Chain
end IOR

namespace Spec
open IOR

def pieceTr_iff : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    PieceTr R H A B ext P qi qo ↔ PieceB R H A B ext P qi qo ∧ H.Exact A.rel P.bud

def tailTr_iff : Prop :=
  ∀ (K Xi Xo : Type) (Ei : ExtSpec) (Q : IOR Xi Ei Xo extNone) (Wi Wo : Type) (H : Q.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo extNone Wo) (ext : Xi × Ei.Str → Tr Q.shape → Wo → Wi)
      (P : Nums K Q) (qi : Finset Ei.Pos → Prop),
    TailTr Q H A B ext P qi ↔ TailB Q H A B ext P qi ∧ H.Exact A.rel P.bud

def closedTr_iff : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
      (P : Nums K R) (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    ClosedTr R H A B ext P qi qo ↔ ClosedB R H A B ext P qi qo ∧ H.Exact A.rel P.bud

def sideC_of_side : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    Side R H bud qi qo → SideC R H bud qi qo

def sideC_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃)
      (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop) (qa : Finset E₁.Pos → Prop)
      (qb : Finset E₂.Pos → Prop) (qc : Finset E₃.Pos → Prop),
    SideC R₁ H₁ b₁ qa qb → SideC R₂ H₂ b₂ qb qc →
    SideC (R₁.seq R₂) (H₁.seq H₂) (budSeq R₁ R₂ b₁ b₂) qa qc

def sideT_consC : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂)
      (H₂ : R₂.Honest W₂ W₃) (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop),
    SideC R₁ H₁ b₁ qa qb → SideT R₂ H₂ b₂ qb → SideT (R₁.seq R₂) (H₁.seq H₂) (budSeq R₁ R₂ b₁ b₂) qa

/-- A piece that is fresh for the block's masks, then a masked block with the budgets' half, is a
piece. -/
def pieceTr_seq_masked : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃)
      (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂) (D : MaskData R₂ W₂)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop) (qc : Finset E₃.Pos → Prop),
    PieceTr R₁ H₁ A B e₁ P₁ qa qb → H₁.Fresh A.rel P₁.bud D.kc D.Mk D.put →
    GoodM R₂ H₂ B C e₂ P₂ D → Side R₂ H₂ P₂.bud qb qc →
    PieceTr (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂) qa qc

def closedTr_seq_masked : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃)
      (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂) (D : MaskData R₂ W₂)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop) (qc : Finset E₃.Pos → Prop),
    ClosedTr R₁ H₁ A B e₁ P₁ qa qb → H₁.Fresh A.rel P₁.bud D.kc D.Mk D.put →
    GoodM R₂ H₂ B C e₂ P₂ D → Side R₂ H₂ P₂.bud qb qc →
    ClosedTr (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂) qa qc

def chain_sidesC : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W)
      (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop),
    c.SidesC qa qb → (c.link d).SideC qa qb

def chain_sidesCT : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W) (qa : Finset A.E.Pos → Prop),
    c.SidesCT qa → (c.link d).SideT qa

def sidesC_of_sides : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B)
      (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop),
    c.Sides qa qb → c.SidesC qa qb

def sidesC_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C) (qa : Finset A.E.Pos → Prop)
      (qb : Finset B.E.Pos → Prop) (qc : Finset C.E.Pos → Prop),
    c.SidesC qa qb → c'.SidesC qb qc → (c.append c').SidesC qa qc

def sidesCT_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C)
      (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop),
    c.SidesC qa qb → c'.SidesCT qb → (c.append c').SidesCT qa

/-- Under `c.Ok` and `c.Sides qa qb`, the chain as one link is a piece. -/
def chain_piece : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W)
      (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop),
    c.Ok → c.Sides qa qb →
    PieceTr (c.link d).R (c.link d).H A.rels B.rels (c.link d).ext (c.link d).P qa qb

/-- Under `c.Ok` and `c.SidesC qa qb`, the chain as one link is a piece that may tie. -/
def chain_closed : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W)
      (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop),
    c.Ok → c.SidesC qa qb →
    ClosedTr (c.link d).R (c.link d).H A.rels B.rels (c.link d).ext (c.link d).P qa qb

/-- Under `c.Ok` and `c.SidesCT qa`, for a chain to a statement without oracles, the chain as one
link is a tail. -/
def chain_tail : Prop :=
  ∀ (K : Type) (A : Joint K) (X W : Type) (Cr : Rels K X extNone W)
      (c : Chain K A ⟨X, extNone, W, Cr⟩) (d : A.W) (qa : Finset A.E.Pos → Prop),
    c.Ok → c.SidesCT qa → TailTr (c.link d).R (c.link d).H A.rels Cr (c.link d).ext (c.link d).P qa

/-- A core chain c₀, and a closing chain c, to a statement without oracles, that comes after it:
under `c₀.Ok`, `c.OkFrom c₀`, `c₀.SidesC qa qb` and `c.SidesCT qb`, `(c₀.append c).link d` is a
tail. -/
def chain_tail_append : Prop :=
  ∀ (K : Type) (A B : Joint K) (X W : Type) (Cr : Rels K X extNone W)
      (c₀ : Chain K A B) (c : Chain K B ⟨X, extNone, W, Cr⟩) (d : A.W)
      (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop),
    c₀.Ok → c.OkFrom c₀ → c₀.SidesC qa qb → c.SidesCT qb →
    TailTr ((c₀.append c).link d).R ((c₀.append c).link d).H A.rels Cr ((c₀.append c).link d).ext
      ((c₀.append c).link d).P qa

end Spec

open IOR IOR.Chain

namespace IOR.Chain
variable {K : Type} {A B C : Joint K}

theorem sidesC_one (l : Link K A B) (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop) :
    (Chain.one l).SidesC qa qb ↔ l.SideC qa qb := by rw [SidesC]
theorem sidesC_snoc (c : Chain K A B) (l : Link K B C)
    (qa : Finset A.E.Pos → Prop) (qc : Finset C.E.Pos → Prop) :
    (c.snoc l).SidesC qa qc ↔ ∃ qb : Finset B.E.Pos → Prop, c.SidesC qa qb ∧ l.SideC qb qc := by
  rw [SidesC]
theorem sidesCT_one (l : Link K A B) (qa : Finset A.E.Pos → Prop) :
    (Chain.one l).SidesCT qa ↔ l.SideT qa := by rw [SidesCT]
theorem sidesCT_snoc (c : Chain K A B) (l : Link K B C) (qa : Finset A.E.Pos → Prop) :
    (c.snoc l).SidesCT qa ↔ ∃ qb : Finset B.E.Pos → Prop, c.SidesC qa qb ∧ l.SideT qb := by
  rw [SidesCT]

end IOR.Chain

theorem pieceTr_iff : Spec.pieceTr_iff := fun K Xi Xo Ei Eo R Wi Wo H A B ext P _ _ =>
  ⟨fun h =>
      ⟨⟨((goodT_iff K Xi Xo Ei Eo R Wi Wo H A B ext P).1 h.good).1, h.noHid, h.noTie, h.bears⟩,
        h.good.exact⟩,
    fun h =>
      ⟨(goodT_iff K Xi Xo Ei Eo R Wi Wo H A B ext P).2 ⟨h.1.base, h.2⟩,
        h.1.side.noHid, h.1.side.noTie, h.1.side.bears⟩⟩

theorem tailTr_iff : Spec.tailTr_iff := fun K Xi Xo Ei Q Wi Wo H A B ext P _ =>
  ⟨fun h =>
      ⟨⟨((goodT_iff K Xi Xo Ei extNone Q Wi Wo H A B ext P).1 h.good).1, h.noHid, h.tied, h.bears⟩,
        h.good.exact⟩,
    fun h =>
      ⟨(goodT_iff K Xi Xo Ei extNone Q Wi Wo H A B ext P).2 ⟨h.1.base, h.2⟩,
        h.1.side.noHid, h.1.side.tied, h.1.side.bears⟩⟩

theorem closedTr_iff : Spec.closedTr_iff := fun K Xi Xo Ei Eo R Wi Wo H A B ext P _ _ =>
  ⟨fun h =>
      ⟨⟨((goodT_iff K Xi Xo Ei Eo R Wi Wo H A B ext P).1 h.good).1,
          h.noHid, h.tied, h.free, h.bears⟩,
        h.good.exact⟩,
    fun h =>
      ⟨(goodT_iff K Xi Xo Ei Eo R Wi Wo H A B ext P).2 ⟨h.1.base, h.2⟩,
        h.1.side.noHid, h.1.side.tied, h.1.side.free, h.1.side.bears⟩⟩

theorem sideC_of_side : Spec.sideC_of_side := fun _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨h.noHid, fun ρ p _ => by rw [h.noTie ρ p]; exact Finset.empty_subset _,
    fun ρ _ p _ => h.noTie ρ p, h.bears⟩

theorem sideC_seq : Spec.sideC_seq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
  ⟨noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid h₂.noHid,
    tied_seq_free _ _ _ _ _ _ _ _ h₁.tied h₁.free h₂.tied,
    tieFree_seq _ _ _ _ _ _ _ _ h₁.free h₂.free,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears h₂.bears⟩

theorem sideT_consC : Spec.sideT_consC := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
  ⟨noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid h₂.noHid,
    tied_seq_free _ _ _ _ _ _ _ _ h₁.tied h₁.free h₂.tied,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears h₂.bears⟩

theorem pieceTr_seq_masked : Spec.pieceTr_seq_masked := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ D qa qb qc h₁ hF g₂ s₂
  exact ⟨goodT_seq_masked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ D h₁.good hF g₂,
    noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid s₂.noHid,
    noTie_seq _ _ _ _ _ _ _ _ h₁.noTie s₂.noTie,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears s₂.bears⟩

theorem closedTr_seq_masked : Spec.closedTr_seq_masked := by
  intro K X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ W₁ W₂ W₃ H₁ H₂ A B C e₁ e₂ d P₁ P₂ D qa qb qc h₁ hF g₂ s₂
  have s := sideC_seq _ _ _ _ _ _ R₁ R₂ _ _ _ H₁ H₂ P₁.bud P₂.bud qa qb qc
    ⟨h₁.noHid, h₁.tied, h₁.free, h₁.bears⟩ (sideC_of_side _ _ _ _ _ _ _ _ _ _ _ s₂)
  exact ⟨goodT_seq_masked _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ D h₁.good hF g₂, s.noHid,
    s.tied, s.free, s.bears⟩

theorem chain_sidesC : Spec.chain_sidesC := by
  intro K A B c d
  induction c with
  | one l =>
      intro qa qb h
      rw [link_one]
      exact (sidesC_one l qa qb).1 h
  | snoc c l ih =>
      intro qa qc h
      obtain ⟨qb, h1, h2⟩ := (sidesC_snoc c l qa qc).1 h
      rw [link_snoc]
      exact sideC_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ih qa qb h1) h2

theorem chain_sidesCT : Spec.chain_sidesCT := by
  intro K A B c d qa h
  cases c with
  | one l =>
      rw [link_one]
      exact (sidesCT_one l qa).1 h
  | snoc c l =>
      obtain ⟨qb, h1, h2⟩ := (sidesCT_snoc c l qa).1 h
      rw [link_snoc]
      exact sideT_consC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (chain_sidesC K _ _ c d qa qb h1) h2

theorem sidesC_of_sides : Spec.sidesC_of_sides := by
  intro K A B c
  induction c with
  | one l =>
      intro qa qb h
      exact (sidesC_one l qa qb).2 (sideC_of_side _ _ _ _ _ _ _ _ _ _ _ ((sides_one l qa qb).1 h))
  | snoc c l ih =>
      intro qa qc h
      obtain ⟨qb, h1, h2⟩ := (sides_snoc c l qa qc).1 h
      exact (sidesC_snoc c l qa qc).2 ⟨qb, ih qa qb h1, sideC_of_side _ _ _ _ _ _ _ _ _ _ _ h2⟩

theorem sidesC_append : Spec.sidesC_append := by
  intro K A B C c c'
  induction c' with
  | one l =>
      intro qa qb qc h h'
      rw [append_one]
      exact (sidesC_snoc c l qa qc).2 ⟨qb, h, (sidesC_one l qb qc).1 h'⟩
  | snoc c' l ih =>
      intro qa qb qc h h'
      obtain ⟨q, h1, h2⟩ := (sidesC_snoc c' l qb qc).1 h'
      rw [append_snoc]
      exact (sidesC_snoc _ l qa qc).2 ⟨q, ih qa qb q h h1, h2⟩

theorem sidesCT_append : Spec.sidesCT_append := by
  intro K A B C c c' qa qb h h'
  cases c' with
  | one l =>
      rw [append_one]
      exact (sidesCT_snoc c l qa).2 ⟨qb, h, (sidesCT_one l qb).1 h'⟩
  | snoc c' l =>
      obtain ⟨q, h1, h2⟩ := (sidesCT_snoc c' l qb).1 h'
      rw [append_snoc]
      exact (sidesCT_snoc _ l qa).2 ⟨q, sidesC_append K _ _ _ c c' qa qb q h h1, h2⟩

theorem chain_piece : Spec.chain_piece := fun K A B c d qa qb hO hS =>
  have s := chain_sides K A B c d qa qb hS
  ⟨chain_ok K A B c d hO, s.noHid, s.noTie, s.bears⟩

theorem chain_closed : Spec.chain_closed := fun K A B c d qa qb hO hS =>
  have s := chain_sidesC K A B c d qa qb hS
  ⟨chain_ok K A B c d hO, s.noHid, s.tied, s.free, s.bears⟩

theorem chain_tail : Spec.chain_tail := fun K A X W Cr c d qa hO hS =>
  have s := chain_sidesCT K A ⟨X, extNone, W, Cr⟩ c d qa hS
  ⟨chain_ok K A ⟨X, extNone, W, Cr⟩ c d hO, s.noHid, s.tied, s.bears⟩

theorem chain_tail_append : Spec.chain_tail_append := fun K A B X W Cr c₀ c d qa qb h₀ h s₀ s =>
  chain_tail K A X W Cr (c₀.append c) d qa ((ok_append K A B ⟨X, extNone, W, Cr⟩ c₀ c).2 ⟨h₀, h⟩)
    (sidesCT_append K A B ⟨X, extNone, W, Cr⟩ c₀ c qa qb s₀ s)

end Iop
