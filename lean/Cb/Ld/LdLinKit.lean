-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinKit.lean: a round in which the prover sends nothing: the verifier draws a value, reads
the implicit instance at positions that the value names, and the statement changes with what it
drew and read.

The definition `IOR.peek`, its honest side, and one statement (`Iop.Spec.piece_peek`), proved here.
No protocol, no code occurs here.
In standard terms: a public-coin round (`Reduction`, Iop/Compose.lean) with an empty prover message,
in which the verifier queries the input oracles at positions fixed by its coins; err is the round's
error in round-by-round knowledge soundness, as a count of the verifier's values.

Ior/Draw.lean has the simplest such round (nothing is read; oracles and witness stay). The tests on
an encoded index need three things more:
  Reads: the verifier reads the implicit instance at the positions `V.rd c`, a function of the
    drawn value c alone; the new explicit part `V.out x c` (answers) may hold what was read (or a
    function of it, say a fold of a column).
  Oracles: the new implicit instance is `V.g` of the old one (`ExtMap`, Ior/Frame.lean): copies, or
    fewer oracles (one that has been read for the last time is dropped).
  Witness: the witness may change: the honest prover passes from w to `hw x w c` (say, it computes
    a vector that it will send next); the extractor `back` goes from a witness of the new statement
    to one of the old; it may read the old statement and the drawn value.

A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of statement and of
witness: the honest relation; a second relation, called relaxed, of which round-by-round knowledge
soundness speaks; the set of statements of which that soundness speaks; and a map from a witness to
its core.

Main names:
  `Spec.piece_peek`: `IOR.peek V` is a piece of a chain (Cb/Ld/LdTowerKit.lean: `PieceTr`, so
    `IOR.GoodT`) from the joint A to the joint B, perfectly complete, with nothing to simulate, if
    local: `V.g` is local;
    forward: for a witness in `A.rel`: the honest prover computes the new explicit part (`hx x w c`
      is what the verifier outputs), and `hw x w c` is a witness in `B.rel` of the new statement,
      for every c; the condition on statements is handed on; the cores agree;
    backward: for every statement with `A.on`, at most err values c are such that some witness w'
      is in `B.relR` for the new statement while `back .. w'` is not in `A.relR` for the old one;
    positions: for every set U of positions of the new oracles that is within qo (what follows needs
      them), every set S whose members are exactly the sources of U and the positions read is within
      qi (what they cost of the old oracles).
Here `PieceTr` is the conclusion. `PieceTr`, a piece of a chain, asks of a reduction between two
joints the bundle `IOR.GoodT` and three further clauses, `noHid`, `noTie` and `bears`, which
Cb/Ld/LdTowerKit.lean states (`bears` through `IOR.Bears`, Ior/Bears.lean); `IOR.Piece`
(Ior/Tail.lean) asks the same over `IOR.Good`.
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Limits: this file says nothing on how err compares with the number of values. The simulator is
given the symbols at the positions read and does not use them: they enter the new explicit part,
which is no part of a view.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdTowerKit
import Ior.Draw
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR

/-- The verifier of such a round: the data. -/
structure PeekV (Xi : Type) (Ei : ExtSpec) (Xo : Type) (Eo : ExtSpec) where
  /-- the values that the verifier draws -/
  D : Type
  [finD : Fintype D]
  [neD : Nonempty D]
  /-- the positions that it reads -/
  rd : D → Finset Ei.Pos
  /-- the new explicit part, from the old one, the value drawn and the symbols read -/
  out : Xi → D → (Ei.Pos → Option Ei.Sym) → Xo
  /-- the new implicit instance -/
  g : ExtMap Ei Eo

attribute [instance] PeekV.finD PeekV.neD

variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- the new explicit part at the oracles y -/
def PeekV.nx (V : PeekV Xi Ei Xo Eo) (x : Xi) (y : Ei.Str) (c : V.D) : Xo :=
  V.out x c (Ei.ans (V.rd c) y)

/-- The round. -/
def peek (V : PeekV Xi Ei Xo Eo) : IOR Xi Ei Xo Eo where
  shape := [drawRound V.D]
  blinded _ := true
  extReads ρ := V.rd (show V.D × Unit from ρ).1
  reads _ := ∅
  out x y τ := some (V.nx x y (drawn τ))
  imp y _ := V.g.map y
  srcE _ q := V.g.src q
  srcO _ _ := ∅
  tie _ _ := ∅

/-- Its honest side: nothing is sent, no coins, nothing is withheld. hx: the new explicit part, as
the honest prover computes it from its witness; hw: the new witness. -/
def Honest.peek (V : PeekV Xi Ei Xo Eo) (hx : Xi → Wi → V.D → Xo) (hw : Xi → Wi → V.D → Wo) :
    (IOR.peek V).Honest Wi Wo where
  Coin := Unit
  strat w x _ := ((((), ()), fun c => (hx x w c, hw x w c)) : Strat [drawRound V.D] (Xo × Wo))
  Bad := ∅
  Hid _ _ := ∅

/-- Its numbers (`Nums`, Ior/Chain.lean): one error; nothing is withheld; every budget. -/
def Nums.peek (K : Type) (V : PeekV Xi Ei Xo Eo) (err : ℕ) : Nums K (IOR.peek V) :=
  ⟨((err, ()) : ℕ × Unit), 0, 0, fun _ _ => True, fun _ => ∅⟩

end IOR

namespace Spec
open IOR

/-- States: under the hypotheses below, such a round is a piece of a chain. -/
def piece_peek : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (V : PeekV Xi Ei Xo Eo)
      (hx : Xi → Wi → V.D → Xo) (hw : Xi → Wi → V.D → Wo)
      (back : Xi × Ei.Str → V.D → Wo → Wi) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (err : ℕ) (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    V.g.IsLocal →
    (∀ x y w c, A.rel x y w → V.nx x y c = hx x w c ∧ B.rel (V.nx x y c) (V.g.map y) (hw x w c)) →
    (∀ x y c, A.on (x, y) → B.on (V.nx x y c, V.g.map y)) →
    (∀ x w c, B.core (hw x w c) = A.core w) →
    (∀ x y, A.on (x, y) →
      cnt (fun c => ∃ w', B.relR (V.nx x y c, V.g.map y) w' ∧ ¬ A.relR (x, y) (back (x, y) c w')) ≤
        err) →
    (∀ c U S, qo U → (∀ p, p ∈ S ↔ p ∈ V.rd c ∨ ∃ u ∈ U, p ∈ V.g.src u) → qi S) →
    PieceTr (IOR.peek V) (Honest.peek V hx hw) A B (fun a τ w' => back a (drawn τ) w')
      (Nums.peek K V err) qi qo

end Spec

open IOR

theorem piece_peek : Spec.piece_peek := by
  classical
  intro K Xi Xo Ei Eo Wi Wo V hx hw back A B err qi qo hloc hfw hon hcore hbw hq
  have hout : ∀ (a : Xi × Ei.Str) (τ : Tr [drawRound V.D]) b,
      (IOR.peek V).red.out a τ = some b → b = (V.nx a.1 a.2 (drawn τ), V.g.map a.2) := by
    intro a τ b hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    exact Prod.ext (Option.some.inj h1).symm h2
  refine ⟨⟨⟨((Blocks.plainPoint Unit V.D (), ()) : (drawRound V.D).IsPoint × Unit)⟩,
      ⟨fun x y y' τ τ' hρ _ hE _ => ?_, fun y y' τ τ' q _ _ hE _ => hloc y y' q hE⟩,
      fun x y w c ρ hR _ => ?_,
      ?_,
      fun w x c ρ => hcore x w _,
      prRho_empty _ fun _ h => h,
      fun _ _ => le_refl _,
      fun _ => prRho_empty _ fun _ h => h,
      ?_, ?_⟩,
    fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  · have e : drawn τ = drawn τ' :=
      congrArg (fun r : Rho [drawRound V.D] => (show V.D × Unit from r).1) hρ
    show some (V.nx x y (drawn τ)) = some (V.nx x y' (drawn τ'))
    rw [← e]
    have hE' : ∀ p ∈ V.rd (drawn τ), Ei.rd y p = Ei.rd y' p := hE
    unfold PeekV.nx
    rw [ExtSpec.ans_congr Ei hE']
  · obtain ⟨e, h2⟩ := hfw x y w (show V.D × Unit from ρ).1 hR
    refine ⟨congrArg some e, ?_⟩
    show B.rel (hx x w (show V.D × Unit from ρ).1) (V.g.map y) (hw x w (show V.D × Unit from ρ).1)
    rw [← e]
    exact h2
  · intro a τ b ha hb
    rw [hout a τ b hb]
    exact hon a.1 a.2 _ ha
  · refine Reduction.Know.of_badFam
      (fun a =>
        ((fun _ => {c | ∃ w', B.relR (V.nx a.1 a.2 c, V.g.map a.2) w' ∧ ¬ A.relR a (back a c w')},
          fun _ _ => ()) : BadFam [drawRound V.D]))
      (fun a ha => ⟨fun _ => hbw a.1 a.2 ha, fun _ _ => trivial⟩) ?_
    intro a τ b w' _ hc hb hw'
    rw [hout a τ b hb] at hw'
    by_contra hn
    exact hc.1 ⟨w', hw', hn⟩
  · refine ⟨fun _ ρ T _ =>
        PMF.pure (some
            ((IOR.peek V).view T
              ((((), ()), (show V.D × Unit from ρ).1, ()) : Tr [drawRound V.D]))),
      fun x y w _ ρ _ T _ => ?_⟩
    rw [(Honest.peek V hx hw).output_of_not_mem T (fun h => h.elim id id)]
    exact PMF.map_const (unif Unit)
      (some ((IOR.peek V).view T ((((), ()), (show V.D × Unit from ρ).1, ()) : Tr [drawRound V.D])))
  · intro ρ U hU
    refine ⟨trivial, ?_⟩
    refine hq (show V.D × Unit from ρ).1 U _ hU fun p => ?_
    rw [mem_need, mem_given]
    constructor
    · rintro ((h | ⟨r, _, h⟩) | ⟨u, hu, h⟩)
      · exact Or.inl h
      · exact absurd h (Finset.notMem_empty _)
      · exact Or.inr ⟨u, hu, h⟩
    · rintro (h | ⟨u, hu, h⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨u, hu, h⟩

end Iop
