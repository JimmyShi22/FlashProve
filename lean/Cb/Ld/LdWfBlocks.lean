-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfBlocks.lean: the lookup arguments inside the sub-protocol for the claim that the encoded
index is well-formed, each defined as the assembled lookup on the keys of the index (all parameters
stay variables).
These are the lookups of the preamble of weights-formedness.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdWfBlocksProofs.lean.
Cb/Ld/LdWf.lean takes each lookup as a parameter, with hypotheses (`Blk.Hyp`). Here the lookups are
given: for each forest the assembled lookup of Cb/Ld/LdLkpAsm2.lean, on tuples (message of the
index, messages), with rows and mask form on the messages' entries alone (Cb/Ld/LdLkpAsm2Pull.lean).
Six of the hypotheses become theorems, each under the hypotheses of its statement: the
sub-protocol's own statement (`lkp`), the three formats (`lkpI`, `lkpP`, `lkpH`), the number of rows
(`lkpN`), the public supports (`lkpS`).

Main names:
  `P.Lks`: the further data of the lookups, forest by forest: the number of keys as 2^(v' + 1); 2^w
    bit positions of which the first n + 1 count; where the bits are and where all own masks are
    among the entries `P.N` of the messages.
  `K.OK p`: the conditions, all on data:
    `v`: the numbers of keys agree;
    `adm`: the conditions on numbers of each lookup;
    `mult`: "the vector held is the multiplicities" (the parameter `P.mult`) gives the wide
      predicate `ValidMu` (Cb/Ld/LdLkpAsm2Pull.lean: `Valid` of Cb/Ld/LdLkpMult.lean) for the bits
      at their places;
    `rows`: the state's room for rows is the number of rows of each lookup;
    `supC`: the public support of a forest's claim's mask form contains the two inner masks of the
      last level of its keys' tree (the mask form reads nothing else: no bit, no other mask);
    `supR`: the public support of each of its rows contains all places of its lookup but the two
      inner masks of the last level of its keys' tree (`LkAsm2.PlacesInR`, Cb/Ld/LdBldWfSupp.lean:
      `cK l b` for l < v' only).
  `Spec.ldWfB_lkp`: under `CharP E p`, the laws of the data and `K.OK`: for every forest, `K.sub f`
    meets the sub-protocol's own statement, word for word as Cb/Ld/LdWf.lean asks it (field `lkp`).

Why `supR` leaves these two masks out. The coarse clause is `LkAsm2.PlacesIn`
(Cb/Ld/LdLkpAsm2Pull.lean): it asks for all places; it gives `LkAsm2.PlacesInR`
(`LkAsm2.PlacesIn.toR`). No row needs these two masks in its support (`Cb.ldBldWf_suppRows`). Under
the coarse clause the message that holds them had to stand in two groups of the offline linear
test's plan (Cb/Obj/LdObjectPpRows.lean: `plR` with `plC`), where this protocol's technical report
(lean/CREDITS.md) has it in one: the report's own placement was no instance of the hypothesis.
It was confirmed by reading, on both sides.

Limits: this file says nothing on the other fields of `Blk.Hyp`: the sending's seven; the item
"masked messages" of a lookup and its claim (`lkpM`, `lkpC`); masks sent in advance (`fresh`,
`freshB`); the batching's three. That `K.OK` can be met is not shown here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWf
import Cb.Ld.LdLkpAsm2Pull
import Cb.Ld.LdBldWfSupp

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

noncomputable section
namespace LdWfP
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} (P : LdWfP E C)

/-- The corner of the keys' cube with the number b, listed as Cb/Ld/LdLkpTree.lean lists points. -/
def cz (_ : LdWfP E C) (v b : ℕ) : ℕ → E := Blocks.nat (Alg.corner (Alg.bits v b))

/-- A key as a function of the entries μ of the index's matrix: the public constant plus the tensor
form at the corner with the number b. A key map is linear (`LdWfP.Laws.keyLin`), so this is the key,
under the hypotheses of `Spec.ldWfB_key`. -/
def keyE (f : ℕ) (μ : P.Rw × (Fin P.k → Bool) → E) (b : ℕ) : E :=
  P.off f (P.cz (P.v f) b) +
    Alg.mle (fun c => ∑ r, P.gOf f (P.cz (P.v f) b) r * μ (r, c)) (P.cOf f (P.cz (P.v f) b))

/-- The further data of the lookups. -/
structure Lks where
  v' : ℕ → ℕ
  w : ℕ → ℕ
  n : ℕ → ℕ
  bAt : ℕ → ℕ → ℕ → P.N
  wS  : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 1]) → P.N
  cS  : ℕ → Bool → P.N
  wAt : ℕ → ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → P.N
  cAt : ℕ → ℕ → Bool → P.N
  wK : (f l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → P.N
  cK : ℕ → ℕ → Bool → P.N
  wT : (f l : ℕ) → PIdx (List.replicate (w f + l) (pfCube E 2) ++ [pDummy E 2]) → P.N
  cT : ℕ → ℕ → Bool → P.N
  wE : (f : ℕ) → PIdx (List.replicate (w f + P.d f) (pfCube E 2)) → P.N
  wB : (f : ℕ) → PIdx (List.replicate (w f + P.d f) (pfCube E 2) ++ [pDummy E 2]) → P.N
  cB : ℕ → P.N

namespace Lks
variable {P} (K : P.Lks)

/-- The data of the assembled lookup of forest f: entries = (entries of the index's matrix) beside
(entries of the messages); keys read the first, all places lie in the second. -/
def asm (f : ℕ) : LkAsm2 E where
  St := P.WSt
  J := P.bt.J
  v' := K.v' f
  d := P.d f
  w := K.w f
  n := K.n f
  key := fun _ m => P.keyE f fun rc => m (Sum.inl rc)
  tab := fun _ => P.tab f
  bAt := fun u j => Sum.inr (K.bAt f u j)
  wS := fun i => Sum.inr (K.wS f i)
  cS := fun b => Sum.inr (K.cS f b)
  wAt := fun l i => Sum.inr (K.wAt f l i)
  cAt := fun l b => Sum.inr (K.cAt f l b)
  wK := fun l i => Sum.inr (K.wK f l i)
  cK := fun l b => Sum.inr (K.cK f l b)
  wT := fun l i => Sum.inr (K.wT f l i)
  cT := fun l b => Sum.inr (K.cT f l b)
  wE := fun i => Sum.inr (K.wE f i)
  wB := fun i => Sum.inr (K.wB f i)
  cB := Sum.inr (K.cB f)

/-- The lookup of forest f. -/
def sub (f : ℕ) : Sub P.S P.S C.E0 P.WSt P.N P.Wp := (K.asm f).subIN (N := P.N) Sum.inr C P.S P.msg

/-- The conditions. -/
structure OK (p : ℕ) : Prop where
  v    : ∀ f, f ≤ P.n → P.v f = K.v' f + 1
  adm  : ∀ f, f ≤ P.n → (K.asm f).H.lkb.Adm p
  mult : ∀ f, f ≤ P.n →
    ∀ (st : P.WSt) (U : C.Msg) (m : P.S.Msg),
      P.mult f U (P.body m) → (K.asm f).ValidMu st (P.msg (U, m))
  rows : ∀ f, f ≤ P.n → P.nR f = (K.asm f).nRows
  supC : ∀ f, f ≤ P.n → ∀ b, P.gC f (K.cK f (K.v' f) b)
  supR : ∀ f, f ≤ P.n → ∀ b, (K.asm f).PlacesInR fun j => ∃ n', j = Sum.inr n' ∧ P.gR f b n'

end Lks
end LdWfP
end
end Cb

namespace Cb.Spec
open Iop Prob Hiop IOR Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- States: under `P.Laws`, for f ≤ P.n and b < 2 ^ P.v f, a key is the public constant plus the
tensor form at its corner. -/
def ldWfB_key : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C), P.Laws →
    ∀ f, f ≤ P.n → ∀ (U : C.Msg) (b : ℕ), b < 2 ^ P.v f → P.key f U b = P.keyE f (P.mat U) b

/-- States the field `lkp` of `LdWfP.Blk.Hyp` (Cb/Ld/LdWf.lean) for the lookups `K.sub l`, under the
hypotheses below. -/
def ldWfB_lkp : Prop :=
  ∀ (p : ℕ) [CharP E p] (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks),
    P.Laws → K.OK p → ∀ l, l ≤ P.n → (K.sub l).OK (P.lk l) (P.multAt l) P.onW (P.honAt l) id P.entM

/-- The fields `lkpI`, `lkpP`, `lkpH`: this statement, `ldWfB_passes` and `ldWfB_same`. -/
def ldWfB_idx : Prop := ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (l : ℕ), (K.sub l).R.IdxStep
def ldWfB_passes : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (l : ℕ),
    (K.sub l).R.Passes (fun x => x) (fun x => (x.1.1, x.2))
/-- The field `lkpN`, under `K.OK p`, for l ≤ P.n: every explicit part that a lookup's verifier puts
out lists the number of rows that the preamble's state has room for. -/
def ldWfB_len : Prop :=
  ∀ (p : ℕ) (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks),
    K.OK p → ∀ l, l ≤ P.n → ∀ x y τ x', (K.sub l).R.out x y τ = some x' → x'.1.2.2.length = P.nR l
/-- The field `lkpS`, under `K.OK p`, for l ≤ P.n: mask form and rows are 0 outside their public
supports. -/
def ldWfB_supp : Prop :=
  ∀ (p : ℕ) (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks), K.OK p →
    ∀ l, l ≤ P.n →
      ∀ x y τ x', (K.sub l).R.out x y τ = some x' →
        (∀ n, ¬ P.gC l n → x'.1.2.1.mf n = 0) ∧
        ∀ (b : Fin (P.nR l)) n, ¬ P.gR l b n → (x'.1.2.2.getD b ⟨fun _ => 0, 0⟩).cf n = 0
def ldWfB_same : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (P : LdWfP E C) (K : P.Lks) (l : ℕ) w x c ρ,
    (((K.sub l).H.strat w x c).run ρ).2.2 = w

end
end Cb.Spec
