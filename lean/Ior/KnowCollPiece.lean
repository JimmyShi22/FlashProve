-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollPiece.lean: pieces of a chain without zero knowledge of their own (`PieceB`, `TailB`);
the budgets' half of a piece as a record of its own (`Side`, `SideT`), with rules for two in a row
and for chains; a chain that stands behind another (`OkFrom`).

The matter is book-keeping for long compositions of interactive oracle reductions (IORs,
Ior/Ior.lean): which oracle positions each reduction needs of the one before it.
Definitions, statements and proofs. No protocol, no code occurs here.
`H.withheld w x` is the union of two sets of verifier randomness that the honest side names:
`H.Bad`, which takes no argument, and `H.Hid w x`, which takes the witness and the explicit
statement.
`R.tie ρ p` is a finite set of positions of the implicit instance, for each ρ and each position p
of the prover's oracles; it enters `R.given`.
`GoodT`: Ior/KnowCollGood.lean. `GoodB`, `GoodM`: Ior/Masked.lean. `R.Tied`: Ior/Batch.lean.
`Joint`, `Link`, `Chain`: Ior/KnowCollRulesChain.lean. `Rels`, `Nums`: Ior/Chain.lean.

Why: of a piece of a chain one asks more than the bundle:
  nothing hidden is withheld,
  no oracle gives away a symbol of the implicit instance (data: see `given`, Ior/Honest.lean),
  and the piece bears what follows (Ior/Bears.lean),
so that at the end of a chain all nested budgets are discharged.
The notions that say so (`PieceTr`, `TailTr`, Cb/Ld/LdTowerKit.lean: pieces and tails over `GoodT`)
ask the whole bundle of each piece, honest-verifier zero knowledge included.
A block whose masks were sent earlier (Ior/Masked.lean: `GoodM`) is not zero knowledge by itself
(`masked_not_exact`, under its premises); nor is any part of a chain that begins with such a block
or holds one whose masks were sent before the part begins [no theorem here].
E.g. the closing of a proximity test, which splits a row by a mask entry that the test has sent
some rounds before.
So: honest-verifier zero knowledge is asked of the whole chain only (Ior/KnowCollRulesChain.lean:
`c.Ok`, `chain_ok`; exactly: `Chain.Ok`: `.one l => l.GoodT`;
`.snoc c l => c.Ok ∧ (l.GoodT ∨ ∃ D : MaskData l.R _, l.GoodM D ∧ c.FreshFor D.kc D.Mk D.put)`),
and all the rest goes piece by piece.

Main names:
  `Side R H bud qi qo`: the budgets' half of a piece: nothing hidden is withheld; no tie; R bears
    what follows, from sets of positions within qo to sets within qi.
  `SideT R H bud qi`: of a last piece: nothing hidden is withheld; the verifier reads all that is
    tied to its positions; R bears what follows, from all sets of positions to sets within qi.
  `PieceB`, `TailB`: `GoodB` (all of the bundle but zero knowledge) and that half.
  `Spec.side_seq`, `Spec.sideT_cons`, `Spec.pieceB_seq`, `Spec.tailB_cons`: two in a row.
  `Spec.side_of_mm`: a masked block has the half almost for nothing: it sends no oracle and
    withholds nothing; what is left to show: the budget bears the empty set, and what is needed of
    the input oracles is within qi.
  `c.Sides qa qb`, `c.SidesT qa`: the half for a chain of links (Ior/KnowCollRulesChain.lean).
  `Spec.chain_sides`, `Spec.chain_sidesT`: then the chain as one link has it. `Spec.sides_append`,
    `Spec.sidesT_append`: two chains in a row.

A chain that stands behind another:
  `c.OkFrom c₀`: c stands behind c₀: every link of c is `GoodT`, or it is `GoodM` and its masks are
    fresh after all that comes before it, c₀ included. The masks of a link of c may have been sent
    in c₀.
  `Spec.ok_append`: `(c₀.append c).Ok` if and only if `c₀.Ok` and `c.OkFrom c₀`. So a sub-protocol
    can take its closing as a parameter: a chain with `OkFrom` the rounds before it, not a
    reduction with zero knowledge of its own.
  `Spec.okFrom_of_ok`: a chain that is `Ok` by itself is `Ok` behind every chain.
  `Spec.freshFor_append`: see its docstring.

Limits: mind the brackets. `c₀.append c` is the chain of all links, bracketed to the left; "c₀ as
one link, then c as one link" is another term (the shapes are equal, not by definition), and no
rule here speaks of it (the rules for two in a row, `Spec.side_seq`, `Spec.sideT_cons`,
`Spec.pieceB_seq`, `Spec.tailB_cons`, hold of any two: by reading).
A sub-protocol whose closing holds a masked block has to be defined as `(c₀.append c).link d`.
This file does not say that any chain has these properties.
On extractors: `PieceB`, `TailB` hold `GoodB R H A B ext P`, with its field `know`; `c.OkFrom c₀`
holds `l.GoodT` or `l.GoodM D`; `Spec.pieceB_seq`, `Spec.tailB_cons` conclude at the composed
extractor, `IOR.extSeq R₁ R₂ e₁ e₂ d`. Beyond these bundles this file says nothing on extractors:
`GoodB`'s rule (`Spec.goodB_seq`, Ior/Masked.lean) asks nothing of them beyond its two bundles.
The statements that end in pieces and tails over `GoodT` stand in the folder of these notions (the
statements: Cb/Ld/LdTowerKitChain.lean).
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesChain
import Ior.BearsProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- The budgets' half of a piece. -/
structure Side (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
    (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop) : Prop where
  noHid : ∀ w x, H.Hid w x = ∅
  noTie : ∀ ρ p, R.tie ρ p = ∅
  bears : R.Bears bud qi qo

/-- The budgets' half of a last piece. -/
structure SideT (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (qi : Finset Ei.Pos → Prop) : Prop where
  noHid : ∀ w x, H.Hid w x = ∅
  tied  : R.Tied
  bears : R.Bears bud qi fun _ => True

/-- A piece without zero knowledge of its own. -/
structure PieceB (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : Nums K R)
    (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop) : Prop where
  base : GoodB R H A B ext P
  side : Side R H P.bud qi qo

/-- A last piece without zero knowledge of its own. -/
structure TailB (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi)
    (P : Nums K R) (qi : Finset Ei.Pos → Prop) : Prop where
  base : GoodB R H A B ext P
  side : SideT R H P.bud qi

def Link.Side {A B : Joint K} (l : Link K A B)
    (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop) : Prop :=
  IOR.Side l.R l.H l.P.bud qa qb
def Link.SideT {A B : Joint K} (l : Link K A B) (qa : Finset A.E.Pos → Prop) : Prop :=
  IOR.SideT l.R l.H l.P.bud qa

namespace Chain

/-- Every link has the budgets' half, with some demands on positions at the joints between. -/
def Sides : {A B : Joint K} → Chain K A B → (Finset A.E.Pos → Prop) → (Finset B.E.Pos → Prop) → Prop
  | _, _, .one l, qa, qb => l.Side qa qb
  | _, _, .snoc (B := B) c l, qa, qc => ∃ qb : Finset B.E.Pos → Prop, c.Sides qa qb ∧ l.Side qb qc

/-- the same for a chain that ends a protocol -/
def SidesT : {A B : Joint K} → Chain K A B → (Finset A.E.Pos → Prop) → Prop
  | _, _, .one l, qa => l.SideT qa
  | _, _, .snoc (B := B) c l, qa => ∃ qb : Finset B.E.Pos → Prop, c.Sides qa qb ∧ l.SideT qb

/-- c stands behind c₀: every link of c is of one of the two kinds, and a masked link's masks are
fresh after all that comes before it, c₀ included. -/
def OkFrom : {Z A B : Joint K} → Chain K A B → Chain K Z A → Prop
  | _, _, _, .one l, c₀ => l.GoodT ∨ ∃ D : MaskData l.R _, l.GoodM D ∧ c₀.FreshFor D.kc D.Mk D.put
  | _, _, _, .snoc c l, c₀ =>
    OkFrom c c₀ ∧
    (l.GoodT ∨ ∃ D : MaskData l.R _, l.GoodM D ∧ (c₀.append c).FreshFor D.kc D.Mk D.put)

end Chain
end IOR

namespace Spec
open IOR

def side_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃)
      (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop) (qa : Finset E₁.Pos → Prop)
      (qb : Finset E₂.Pos → Prop) (qc : Finset E₃.Pos → Prop),
    Side R₁ H₁ b₁ qa qb → Side R₂ H₂ b₂ qb qc →
    Side (R₁.seq R₂) (H₁.seq H₂) (budSeq R₁ R₂ b₁ b₂) qa qc

def sideT_cons : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂)
      (H₂ : R₂.Honest W₂ W₃) (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop),
    Side R₁ H₁ b₁ qa qb → SideT R₂ H₂ b₂ qb → SideT (R₁.seq R₂) (H₁.seq H₂) (budSeq R₁ R₂ b₁ b₂) qa

def pieceB_seq : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop) (qc : Finset E₃.Pos → Prop),
    PieceB R₁ H₁ A B e₁ P₁ qa qb → PieceB R₂ H₂ B C e₂ P₂ qb qc →
    PieceB (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂) qa qc

def tailB_cons : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁)
      (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂) (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂)
      (qa : Finset E₁.Pos → Prop) (qb : Finset E₂.Pos → Prop),
    PieceB R₁ H₁ A B e₁ P₁ qa qb → TailB R₂ H₂ B C e₂ P₂ qb →
    TailB (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂) qa

/-- States, under the hypotheses below: a masked block has the budgets' half almost for nothing. -/
def side_of_mm : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (D : MaskData R Wi) (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    H.MM D → (∀ ρ, bud ρ ∅) → (∀ ρ U, qo U → qi (R.need ρ U)) → Side R H bud qi qo

/-- States: if `c.Sides qa qb`, the chain as one link has the budgets' half. -/
def chain_sides : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W)
      (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop),
    c.Sides qa qb → (c.link d).Side qa qb

def chain_sidesT : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W) (qa : Finset A.E.Pos → Prop),
    c.SidesT qa → (c.link d).SideT qa

def sides_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C) (qa : Finset A.E.Pos → Prop)
      (qb : Finset B.E.Pos → Prop) (qc : Finset C.E.Pos → Prop),
    c.Sides qa qb → c'.Sides qb qc → (c.append c').Sides qa qc

def sidesT_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C)
      (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop),
    c.Sides qa qb → c'.SidesT qb → (c.append c').SidesT qa

/-- States: two chains in a row are of the two kinds (`Ok`) if and only if the first is, and the
second is behind the first (`OkFrom`). -/
def ok_append : Prop :=
  ∀ (K : Type) (Z A B : Joint K) (c₀ : Chain K Z A) (c : Chain K A B),
    (c₀.append c).Ok ↔ c₀.Ok ∧ c.OkFrom c₀

/-- for a non-empty `Mk`: masks that are fresh after a chain are fresh after it behind every
chain -/
def freshFor_append : Prop :=
  ∀ (K : Type) (Z A B : Joint K) (c₀ : Chain K Z A) (c : Chain K A B) (Kc : Type) (kc : B.W → Kc)
      (Mk : Type) [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    c.FreshFor kc Mk put → (c₀.append c).FreshFor kc Mk put

/-- a chain that is of the two kinds (`Ok`) by itself is so behind every chain (`OkFrom`) -/
def okFrom_of_ok : Prop :=
  ∀ (K : Type) (Z A B : Joint K) (c₀ : Chain K Z A) (c : Chain K A B), c.Ok → c.OkFrom c₀

end Spec

open IOR IOR.Chain

namespace IOR.Chain
variable {K : Type} {Z A B C : Joint K}

theorem sides_one (l : Link K A B) (qa : Finset A.E.Pos → Prop) (qb : Finset B.E.Pos → Prop) :
    (Chain.one l).Sides qa qb ↔ l.Side qa qb := by rw [Sides]
theorem sides_snoc (c : Chain K A B) (l : Link K B C)
    (qa : Finset A.E.Pos → Prop) (qc : Finset C.E.Pos → Prop) :
    (c.snoc l).Sides qa qc ↔ ∃ qb : Finset B.E.Pos → Prop, c.Sides qa qb ∧ l.Side qb qc := by
  rw [Sides]
theorem sidesT_one (l : Link K A B) (qa : Finset A.E.Pos → Prop) :
    (Chain.one l).SidesT qa ↔ l.SideT qa := by rw [SidesT]
theorem sidesT_snoc (c : Chain K A B) (l : Link K B C) (qa : Finset A.E.Pos → Prop) :
    (c.snoc l).SidesT qa ↔ ∃ qb : Finset B.E.Pos → Prop, c.Sides qa qb ∧ l.SideT qb := by
  rw [SidesT]
theorem okFrom_one (c₀ : Chain K Z A) (l : Link K A B) :
    (Chain.one l).OkFrom c₀ ↔
    (l.GoodT ∨ ∃ D : MaskData l.R A.W, l.GoodM D ∧ c₀.FreshFor D.kc D.Mk D.put) := by rw [OkFrom]
theorem okFrom_snoc (c₀ : Chain K Z A) (c : Chain K A B) (l : Link K B C) :
    (c.snoc l).OkFrom c₀ ↔
    c.OkFrom c₀ ∧
    (l.GoodT ∨ ∃ D : MaskData l.R B.W, l.GoodM D ∧ (c₀.append c).FreshFor D.kc D.Mk D.put) := by
  rw [OkFrom]

end IOR.Chain

theorem side_seq : Spec.side_seq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
  ⟨noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid h₂.noHid,
    noTie_seq _ _ _ _ _ _ _ _ h₁.noTie h₂.noTie,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears h₂.bears⟩

theorem sideT_cons : Spec.sideT_cons := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ =>
  ⟨noHid_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.noHid h₂.noHid,
    tied_seq _ _ _ _ _ _ _ _ h₁.noTie h₂.tied,
    bears_seq _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.bears h₂.bears⟩

theorem pieceB_seq :
    Spec.pieceB_seq := fun K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ _ _ _ h₁ h₂ =>
  ⟨goodB_seq K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ h₁.base h₂.base,
    side_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.side h₂.side⟩

theorem tailB_cons :
    Spec.tailB_cons := fun K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ _ _ h₁ h₂ =>
  ⟨goodB_seq K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ d _ _ h₁.base h₂.base,
    sideT_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁.side h₂.side⟩

open Classical in
theorem side_of_mm : Spec.side_of_mm := by
  intro Xi Xo Ei Eo R Wi Wo H D bud qi qo m hb hq
  haveI := m.noOrc
  refine ⟨fun w x => ?_, fun _ p => (m.noOrc.false p).elim, fun ρ U hU => ⟨?_, hq ρ U hU⟩⟩
  · exact Set.eq_empty_of_subset_empty fun ρ hρ => (m.free w x).subset (Or.inr hρ)
  · rw [Finset.eq_empty_of_isEmpty (U.biUnion (R.srcO ρ))]
    exact hb ρ

theorem chain_sides : Spec.chain_sides := by
  intro K A B c d
  induction c with
  | one l =>
      intro qa qb h
      rw [link_one]
      exact (sides_one l qa qb).1 h
  | snoc c l ih =>
      intro qa qc h
      obtain ⟨qb, h1, h2⟩ := (sides_snoc c l qa qc).1 h
      rw [link_snoc]
      exact side_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ih qa qb h1) h2

theorem chain_sidesT : Spec.chain_sidesT := by
  intro K A B c d qa h
  cases c with
  | one l =>
      rw [link_one]
      exact (sidesT_one l qa).1 h
  | snoc c l =>
      obtain ⟨qb, h1, h2⟩ := (sidesT_snoc c l qa).1 h
      rw [link_snoc]
      exact sideT_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (chain_sides K _ _ c d qa qb h1) h2

theorem sides_append : Spec.sides_append := by
  intro K A B C c c'
  induction c' with
  | one l =>
      intro qa qb qc h h'
      rw [append_one]
      exact (sides_snoc c l qa qc).2 ⟨qb, h, (sides_one l qb qc).1 h'⟩
  | snoc c' l ih =>
      intro qa qb qc h h'
      obtain ⟨q, h1, h2⟩ := (sides_snoc c' l qb qc).1 h'
      rw [append_snoc]
      exact (sides_snoc _ l qa qc).2 ⟨q, ih qa qb q h h1, h2⟩

theorem sidesT_append : Spec.sidesT_append := by
  intro K A B C c c' qa qb h h'
  cases c' with
  | one l =>
      rw [append_one]
      exact (sidesT_snoc c l qa).2 ⟨qb, h, (sidesT_one l qb).1 h'⟩
  | snoc c' l =>
      obtain ⟨q, h1, h2⟩ := (sidesT_snoc c' l qb).1 h'
      rw [append_snoc]
      exact (sidesT_snoc _ l qa).2 ⟨q, sides_append K _ _ _ c c' qa qb q h h1, h2⟩

theorem ok_append : Spec.ok_append := by
  intro K Z A B c₀ c
  induction c with
  | one l => rw [append_one, ok_snoc, okFrom_one]
  | snoc c l ih => rw [append_snoc, ok_snoc, okFrom_snoc, ih, and_assoc]

theorem freshFor_append : Spec.freshFor_append := by
  intro K Z A B c₀ c
  induction c with
  | one l =>
      intro Kc kc Mk _ _ put h
      rw [append_one]
      exact (freshFor_snoc c₀ l kc Mk put).2 (Or.inl ((freshFor_one l kc Mk put).1 h))
  | snoc c l ih =>
      intro Kc kc Mk _ _ put h
      rw [append_snoc]
      refine (freshFor_snoc _ l kc Mk put).2 ?_
      rcases (freshFor_snoc c l kc Mk put).1 h with h | ⟨Kc', kc', put', h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨Kc', kc', put', ih Kc' kc' Mk put' h1, h2⟩

theorem okFrom_of_ok : Spec.okFrom_of_ok := by
  intro K Z A B c₀ c
  induction c with
  | one l =>
      intro h
      exact (okFrom_one c₀ l).2 (Or.inl ((ok_one l).1 h))
  | snoc c l ih =>
      intro h
      obtain ⟨h1, h2⟩ := (ok_snoc c l).1 h
      refine (okFrom_snoc c₀ c l).2 ⟨ih h1, ?_⟩
      rcases h2 with h2 | ⟨D, h2, hF⟩
      · exact Or.inl h2
      · exact Or.inr ⟨D, h2, freshFor_append K Z _ _ c₀ c _ D.kc D.Mk D.put hF⟩

end Iop
