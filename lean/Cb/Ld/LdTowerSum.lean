-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdTowerSum.lean: "fold, then code switch" at the two blocks themselves: the zero-knowledge
sumcheck that folds (Cb/Ld/LdSum.lean) as a block of a tower, and one stage made of it and of the
code switch (Cb/Ld/LdSwitch.lean).

In standard terms: one recursion step of a proximity test beyond unique decoding: a sumcheck that
folds the word, then a switch to a new code. Cb/Ld/LdTower.lean has the fold as a parameter. Here
the parameter is filled.

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs (an assembly, but for `ldTower_sum`:
read off the term). The sets P, P' of long positions are not empty (`[Nonempty P]`) in all
statements.
The file follows the paper that this protocol builds on (lean/CREDITS.md).

Main names:
  `Y.jIn e`, `Y.jOut e`: the two joints of the fold `Y : SumPar E P`, at one radius e: in: main
    table and carried mask, rows on the cubes, a pair of forms; out: the three folded words side by
    side, the three forms side by side.
  `SumGood Y e ext t ..`: the one hypothesis on the fold: its bundle `IOR.GoodT` between these two
    joints. (Its own theorem, with the extractor named and the conditions on codes, radius and
    degree, belongs to the fold's files; it is not used here in any other way.)
    `IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with
    its honest side, between two joints, at given numbers; among its clauses: completeness between
    the honest relations, outside sets of verifier randomness whose probabilities further clauses
    bound by the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations,
    on the input joint's set of statements, with a given extractor, at the numbers' list of errors;
    and one on honest-verifier zero knowledge. Here it stands inside the definition `SumGood`, a
    hypothesis of this file's statements.
  `Spec.ldTower_sum`: under `SumGood`, the block `ldSumBlock` is OK t t: if what follows needs at
    most t long positions of the three folded words, then the budget of the fresh mask oracle bears
    the native positions behind them, and exactly these long positions of the input are needed: one
    query to the input for each query to the folded word (`SumPar.ior`: `srcE`, Cb/Ld/LdSum.lean).
    Read off the term: the verifier reads no oracle, nothing is tied, nothing is withheld.
  `ldSwAfter Y ..`: the data of a code switch that starts where the fold Y ends: its input code is
    `Y.Cout`, its old form `Y.slOut`; the new code, the pad, the naming of coordinates, the sample,
    the number of positions, the batching are free.
  `ldStageSum G ..` (G : `SumSw E P P'`: a fold Y = G.Y and the free data of a switch after it): the
    stage.
    `Spec.ldTower_stage_sum`: under `SumGood` at t = the switch's number of positions and the
    switch's hypotheses, of the stage, in the order of the statement's four conjuncts:
    (1) the stage is OK at that number and t', from `Y.jIn e` to the switch's `jOut e'`;
    (2) k + 3 rounds (k = Y.h + Y.g variables);
    (3) the errors in a row: the list of the whole complex (round 0); for j = 1 .. k: agreement of
    the main table after j rounds
    + [j ≤ h] (agreement of the two mask tables after j rounds)
    + (list of the complex before round j) · n; then the switch's two;
    (4) nothing is withheld, in this sense: `pBad` = 0 (`IOR.Nums`, Ior/Chain.lean), with
        `PieceTr.noHid` (Cb/Ld/LdTowerKit.lean; it lies inside (1)).
  `Y.reform sl`, `ldSumAfter`: the fold that starts where a switch ends. A switch leaves one batched
    form sl on the message coordinates of its new code. If that code is a main table and a mask
    table side by side (`Y.Cin`), `Y.reform sl` is the fold Y with the two parts of sl as its two
    forms, both with the states of sl; `ldSumAfter` is "cut the form (Cb/Ld/LdTower.lean:
    `ldSplit`), then that fold": a block from the joint (`Y.Cin`, sl, e). `Spec.ldTower_sum_after`:
    under `SumGood` of `Y.reform sl`, it is OK t t, has k + 1 rounds and the fold's errors.

Notation:
  `B.OK t t'`: the block is a piece of a chain: from at most t' long positions of the output word to
    at most t of the input word (`LdBlock.OK`, Cb/Ld/LdTower.lean; `PieceTr`,
    Cb/Ld/LdTowerKit.lean);
  `e`, `e'`: the field `LdJoint.e` (Cb/Ld/LdTower.lean) of the joints `Y.jIn e` and `jOut e'`: the
    radius of the relaxation: a count of long positions;
  `ext`: an extractor;
  `h`, `g`: the mask tables have rows on the cube of the first h variables; g further variables;
  `n`: the largest degree of a round polynomial
  (`h`, `g`, `n`: fields of `SumPar`, Cb/Ld/LdSum.lean);
  `L`, `t'`: numbers that enter the switch's hypotheses `(G.D e).Hyp e' L t'` (`LdSw.Hyp`,
    Cb/Ld/LdTower.lean).

Limits: what the heads of Cb/Ld/LdTower.lean, Cb/Ld/LdSum.lean and Cb/Ld/LdSwitch.lean list as not
said is not said here either.
The radius of the middle joint is the input's, as in the paper that this protocol builds on. The
numbers Lst, mC, mS, mW of the fold's errors are functions of the round (Cb/Ld/LdSum.lean: `ErrOK`
says what they bound); whether they bound it is not asked here: it is a hypothesis of the theorem
that proves `SumGood` (`SumPar.Hyp.errs`, Cb/Ld/LdTowerSumMain.lean) (`SumGood` itself has them only
as numbers: `Y.nums t Lst mC mS mW`).
`SumGood` is a hypothesis here. (Cb/Ld/LdTowerSumMain.lean proves it, at the extractor `Y.ext d`,
from `SumPar.Hyp`: `sumGood_of_hyp`.)
This file says nothing on sizes of errors.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerMain
import Cb.Ld.LdSum

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

noncomputable section
variable {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P]

namespace SumPar
variable (Y : SumPar E P)

/-- the joints of the fold, at one radius -/
def jIn (e : ℕ) : LdJoint E := ⟨P, Y.Cin, Y.St × Y.StS, Y.slIn, e⟩
def jOut (e : ℕ) : LdJoint E := ⟨P, Y.Cout, _, Y.slOut, e⟩

end SumPar

variable (Y : SumPar E P) (e : ℕ)
  (ext : (Y.jIn e).X × Y.Cin.ext.Str → Tr Y.ior.shape → (Y.jOut e).W → (Y.jIn e).W)
  (t : ℕ) (Lst mC mS mW : ℕ → ℕ)

/-- The fold as a block. -/
def ldSumBlock : LdBlock (Y.jIn e) (Y.jOut e) := ⟨Y.ior, Y.hon, ext, Y.nums t Lst mC mS mW⟩

/-- The one hypothesis on the fold: its bundle. -/
def SumGood : Prop := GoodT Y.ior Y.hon (Y.jIn e).rels (Y.jOut e).rels ext (Y.nums t Lst mC mS mW)

/-- the fold Y with the two parts of one form on all message coordinates of its input code as its
forms -/
def SumPar.reform {St : Type} (sl : Slf E St Y.Cin.J) : SumPar E P :=
  { Y with St := St, StS := St, sl := Slf.left sl, slS := Slf.right sl }

/-- A code switch that starts where the fold ends. -/
def ldSwAfter {P' : Type} [Fintype Y.Cout.Aa] (Cnew : LdCode E P') (Qo : Type) [Fintype Qo]
    [DecidableEq Qo] (place : (Y.Cout.J ⊕ Y.Cout.Q) ⊕ Qo ≃ Cnew.J)
    (Zo : Ood.Sample E ((Y.Cout.J ⊕ Y.Cout.Q) ⊕ Qo)) (ts : ℕ)
    (Zb : Evader E (LdRow Zo.S ts Y.Cout.Aa)) : LdSw E P P' (Y.jOut e).St :=
  ⟨Y.Cout, Cnew, Qo, place, Y.slOut, Zo, ts, Zb⟩

/-- Cut the form, then fold. -/
def ldSumAfter {St : Type} (sl : Slf E St Y.Cin.J)
    (ext' : ((Y.reform sl).jIn e).X × (Y.reform sl).Cin.ext.Str → Tr (Y.reform sl).ior.shape →
      ((Y.reform sl).jOut e).W → ((Y.reform sl).jIn e).W) :
    LdBlock (ldWhole (Y.C.il (Fin Y.k → Bool)) (Y.Z.il (Fin Y.h → Bool)) sl e)
      ((Y.reform sl).jOut e) :=
  ldCutThen (C₁ := Y.C.il (Fin Y.k → Bool)) (C₂ := Y.Z.il (Fin Y.h → Bool)) (sl := sl) (e := e)
    (ldSumBlock (Y.reform sl) e ext' t Lst mC mS mW)

end

/-- The data of a stage: the fold Y, and what is free in a switch that starts where Y ends
(`ldSwAfter`): new code, pad, naming of coordinates, sample, number of positions, batching. -/
structure SumSw (E P P' : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] where
  Y  : SumPar E P
  [finAa : Fintype Y.Cout.Aa]
  Cnew : LdCode E P'
  Qo : Type
  [finQo : Fintype Qo]
  [decQo : DecidableEq Qo]
  place : (Y.Cout.J ⊕ Y.Cout.Q) ⊕ Qo ≃ Cnew.J
  Zo : Ood.Sample E ((Y.Cout.J ⊕ Y.Cout.Q) ⊕ Qo)
  ts : ℕ
  Zb : Evader E (LdRow Zo.S ts Y.Cout.Aa)

attribute [instance] SumSw.finAa SumSw.finQo SumSw.decQo

noncomputable section
variable {E P P' : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']

/-- the switch of a stage -/
def SumSw.D (G : SumSw E P P') (e : ℕ) : LdSw E P P' (G.Y.jOut e).St :=
  ldSwAfter G.Y e G.Cnew G.Qo G.place G.Zo G.ts G.Zb

/-- One stage: the fold, then the code switch. -/
def ldStageSum (G : SumSw E P P') (e : ℕ)
    (ext : (G.Y.jIn e).X × G.Y.Cin.ext.Str → Tr G.Y.ior.shape → (G.Y.jOut e).W → (G.Y.jIn e).W)
    (Lst mC mS mW : ℕ → ℕ) (e' L t' : ℕ) :
    LdBlock (G.Y.jIn e) ((G.D e).jOut e') :=
  ldStage (a := G.Y.jIn e) (G.D e) (ldSumBlock G.Y e ext G.ts Lst mC mS mW) e' L t'

end

namespace Spec

/-- Under `SumGood`, P not empty, the fold is a piece: one long position of the input for each long
position of the folded words. -/
def ldTower_sum : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P) (e : ℕ)
      (ext : (Y.jIn e).X × Y.Cin.ext.Str → Tr Y.ior.shape → (Y.jOut e).W → (Y.jIn e).W)
      (t : ℕ) (Lst mC mS mW : ℕ → ℕ),
    SumGood Y e ext t Lst mC mS mW → (ldSumBlock Y e ext t Lst mC mS mW).OK t t

/-- Cut, then fold, under `SumGood` of `Y.reform sl`, P not empty: a piece from the joint with one
form. -/
def ldTower_sum_after : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (Y : SumPar E P) (e : ℕ) (t : ℕ)
      (Lst mC mS mW : ℕ → ℕ) (St : Type) (sl : Slf E St Y.Cin.J)
      (ext' : ((Y.reform sl).jIn e).X × (Y.reform sl).Cin.ext.Str → Tr (Y.reform sl).ior.shape →
        ((Y.reform sl).jOut e).W → ((Y.reform sl).jIn e).W),
    SumGood (Y.reform sl) e ext' t Lst mC mS mW →
    (ldSumAfter Y e t Lst mC mS mW sl ext').OK t t ∧
    (ldSumAfter Y e t Lst mC mS mW sl ext').R.shape.length = Y.k + 1 ∧
    HEq (ldSumAfter Y e t Lst mC mS mW sl ext').N.err ((Y.reform sl).err Lst mC mS mW)

/-- Fold, then code switch, at the two blocks. -/
def ldTower_stage_sum : Prop :=
  ∀ (E P P' : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] [Fintype P'] [Nonempty P']
      (G : SumSw E P P') (e : ℕ)
      (ext : (G.Y.jIn e).X × G.Y.Cin.ext.Str → Tr G.Y.ior.shape → (G.Y.jOut e).W → (G.Y.jIn e).W)
      (Lst mC mS mW : ℕ → ℕ) (e' L t' : ℕ),
    SumGood G.Y e ext G.ts Lst mC mS mW → (G.D e).Hyp e' L t' →
    (ldStageSum G e ext Lst mC mS mW e' L t').OK G.ts t' ∧
    (ldStageSum G e ext Lst mC mS mW e' L t').R.shape.length = G.Y.k + 3 ∧
    (ldStageSum G e ext Lst mC mS mW e' L t').N.err =
      Err.app (t := (G.D e).sh) (G.Y.err Lst mC mS mW)
        ((G.D e).W.err1 L, ((G.D e).W.err2 e L, ())) ∧
    (ldStageSum G e ext Lst mC mS mW e' L t').N.pBad = 0

end Spec

open Classical in
theorem ldTower_sum : Spec.ldTower_sum := by
  intro E P _ _ _ _ Y e ext t Lst mC mS mW hG
  refine ⟨hG, fun _ _ => rfl, fun _ _ => rfl, fun ρ U hU => ⟨⟨U, hU, ?_⟩, ?_⟩⟩
  · intro p hp
    obtain ⟨x, hx, hpx⟩ := (mem_biUnion_at _).1 hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 hpx
    exact ⟨q, Finset.mem_biUnion.2 ⟨x, hx, hq⟩, rfl⟩
  · have hsub : Y.ior.need ρ U ⊆ U := by
      intro q hq
      rcases mem_need.1 hq with h1 | ⟨u, hu, h2⟩
      · rcases mem_given.1 h1 with h3 | ⟨p, _, h4⟩
        · exact absurd h3 (Finset.notMem_empty _)
        · exact absurd h4 (Finset.notMem_empty _)
      · obtain rfl := Finset.mem_singleton.1 h2
        exact hu
    exact (Finset.card_le_card hsub).trans hU

theorem ldTower_sum_after : Spec.ldTower_sum_after := by
  intro E P _ _ _ _ Y e t Lst mC mS mW St sl ext' hG
  obtain ⟨h1, h2, h3, -⟩ := ldTower_cutThen E P St (Y.C.il (Fin Y.k → Bool))
    (Y.Z.il (Fin Y.h → Bool)) sl e ((Y.reform sl).jOut e)
    (ldSumBlock (Y.reform sl) e ext' t Lst mC mS mW) t t
    (ldTower_sum E P (Y.reform sl) e ext' t Lst mC mS mW hG)
  refine ⟨h1, ?_, h3⟩
  rw [show (ldSumAfter Y e t Lst mC mS mW sl ext').R.shape =
        (ldSumBlock (Y.reform sl) e ext' t Lst mC mS mW).R.shape from h2]
  show ((Y.reform sl).round0 :: List.replicate Y.k _).length = Y.k + 1
  rw [List.length_cons, List.length_replicate]

theorem ldTower_stage_sum : Spec.ldTower_stage_sum := by
  intro E P P' _ _ _ _ _ _ G e ext Lst mC mS mW e' L t' hG hD
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    ldTower_stage E (G.Y.jIn e) P' _ (G.D e) (ldSumBlock G.Y e ext G.ts Lst mC mS mW) e' L t'
      (ldTower_sum E P G.Y e ext G.ts Lst mC mS mW hG) hD
  refine ⟨h1, ?_, h3, h4⟩
  refine h2.trans ?_
  show (G.Y.round0 :: List.replicate G.Y.k _).length + 2 = G.Y.k + 3
  rw [List.length_cons, List.length_replicate]

end Cb
