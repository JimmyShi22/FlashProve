-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Draw.lean: a one-round reduction in which the verifier draws a value and the explicit part of
the statement changes with it: the simplest piece of a chain.

The definition `IOR.draw`, its honest side, and one statement (`Spec.piece_draw`), proved here.

One round. The prover sends nothing; the verifier sends β, uniform in a finite non-empty set D; it
reads nothing and never rejects. The oracles, and the witness, stay as they are. (Batching of many
claims into one by random coefficients is of this kind.)

Main names:
  `Spec.piece_draw`: it is a piece of a chain (`Piece`, Ior/Tail.lean) from the joint A to the joint
    B, with the identity as extractor, perfectly complete, with nothing to simulate, if
    forward: a witness in `A.rel` stays a witness in `B.rel`, for every β; the condition on
      statements is handed on; the cores agree;
    backward: for every statement with `A.on`, at most err values β are such that some witness is in
      `B.relR` for the new statement and not in `A.relR` for the old one.
  What follows needs of the old oracles exactly what it needs of the new ones, so the predicate on
    sets of positions is the same on both sides.

Limits: this file says nothing on how err compares with the number of values of β.
Terms: lean/GLOSSARY.md.
-/
import Ior.TailProofs
import Blocks.Basic

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K X X' : Type} {E : ExtSpec} {W : Type}

/-- The one round. -/
abbrev drawRound (D : Type) [Fintype D] [Nonempty D] : Round := Blocks.plainRound Unit D ()

/-- The value drawn. -/
def drawn {D : Type} [Fintype D] [Nonempty D] (τ : Tr [drawRound D]) : D :=
  (show (Unit × Unit) × D × Unit from τ).2.1

/-- The verifier draws β; the explicit part becomes nx x β. -/
def draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec) : IOR X E X' E where
  shape := [drawRound D]
  blinded _ := true
  extReads _ := ∅
  reads _ := ∅
  out x _ τ := some (nx x (drawn τ))
  imp y _ := y
  srcE _ q := {q}
  srcO _ _ := ∅
  tie _ _ := ∅

/-- Its honest side: nothing is sent, nothing is withheld, the witness stays. -/
def Honest.draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec) (W : Type) :
    (IOR.draw D nx E).Honest W W where
  Coin := Unit
  strat w x _ := ((((), ()), fun β => (nx x β, w)) : Strat [drawRound D] (X' × W))
  Bad := ∅
  Hid _ _ := ∅

/-- Its numbers: one error; nothing is withheld; every budget. -/
def Nums.draw (K : Type) (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X')
    (E : ExtSpec) (err : ℕ) : Nums K (IOR.draw D nx E) :=
  ⟨((err, ()) : ℕ × Unit), 0, 0, fun _ _ => True, fun _ => ∅⟩

end IOR

namespace Spec
open IOR

/-- Under the hypotheses below, drawing a value is a piece of a chain. -/
def piece_draw : Prop :=
  ∀ (K X X' : Type) (E : ExtSpec) (W D : Type) [Fintype D] [Nonempty D] (nx : X → D → X')
      (A : Rels K X E W) (B : Rels K X' E W) (err : ℕ) (q : Finset E.Pos → Prop),
    (∀ x y w β, A.rel x y w → B.rel (nx x β) y w) → (∀ x y β, A.on (x, y) → B.on (nx x β, y)) →
    (∀ w, B.core w = A.core w) →
    (∀ x y, A.on (x, y) → cnt (fun β => ∃ w, B.relR (nx x β, y) w ∧ ¬ A.relR (x, y) w) ≤ err) →
    Piece (IOR.draw D nx E) (Honest.draw D nx E W) A B (fun _ _ w => w) (Nums.draw K D nx E err) q q

end Spec

open IOR

theorem piece_draw : Spec.piece_draw := by
  classical
  intro K X X' E W D _ _ nx A B err q hfw hon hcore hbw
  refine ⟨⟨⟨((Blocks.plainPoint Unit D (), ()) : (drawRound D).IsPoint × Unit)⟩,
      ⟨fun x y y' τ τ' hρ _ _ _ => ?_,
        fun y y' τ τ' p _ _ hE _ => hE p (Finset.mem_singleton_self p)⟩,
      fun x y w c ρ hR _ => ⟨rfl, hfw x y w _ hR⟩,
      ?_,
      fun w x c ρ => hcore w,
      prRho_empty _ fun _ h => h,
      fun _ _ => le_refl _,
      fun _ => prRho_empty _ fun _ h => h,
      ?_, ?_⟩,
    fun _ _ => rfl, fun _ _ => rfl, ?_⟩
  · have e : drawn τ = drawn τ' :=
      congrArg (fun r : Rho [drawRound D] => (show D × Unit from r).1) hρ
    show some (nx x (drawn τ)) = some (nx x (drawn τ'))
    rw [e]
  · intro a τ b ha hb
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = (nx a.1 (drawn τ), a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e]
    exact hon a.1 a.2 _ ha
  · intro a ha m
    refine le_trans (cnt_mono fun β hβ => ?_) (hbw a.1 a.2 ha)
    by_contra hn
    refine hβ fun b w hb hw => ?_
    by_contra hA
    obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
    have e : b = (nx a.1 β, a.2) := Prod.ext (Option.some.inj h1).symm h2
    rw [e] at hw
    exact hn ⟨w, hw, hA⟩
  · refine ⟨fun _ ρ T _ =>
        PMF.pure (some
            ((IOR.draw D nx E).view T
              ((((), ()), (show D × Unit from ρ).1, ()) : Tr [drawRound D]))),
      fun x y w _ ρ _ T _ => ?_⟩
    rw [(Honest.draw D nx E W).output_of_not_mem T (fun h => h.elim id id)]
    exact PMF.map_const (unif Unit)
      (some
        ((IOR.draw D nx E).view T ((((), ()), (show D × Unit from ρ).1, ()) : Tr [drawRound D])))
  · intro ρ U hU
    refine ⟨trivial, ?_⟩
    have e : (IOR.draw D nx E).need ρ U = U := by
      ext p
      rw [mem_need, mem_given]
      constructor
      · rintro ((h | ⟨r, _, h⟩) | ⟨u, hu, h⟩)
        · exact absurd h (Finset.notMem_empty _)
        · exact absurd h (Finset.notMem_empty _)
        · rw [Finset.mem_singleton.1 h]
          exact hu
      · exact fun h => Or.inr ⟨p, h, Finset.mem_singleton_self p⟩
    rw [e]
    exact hU

end Iop
