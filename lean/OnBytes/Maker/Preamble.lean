-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Preamble.lean: from the rounds' data of a chain and a run on the chain's view to an
interactive oracle reduction that leaves oracles: the form of the two preambles of
Hiop/RecSubs.lean's `SubsR` (`wf`, `req`).

A first chain of a key file or of a proof file sends trees that a later chain of the same file
opens. As a reduction (Ior/Ior.lean) that is: the verifier returns claims, and the new implicit
instance is the old one together with the oracles left. This file makes such a reduction from data:
the choice of challenge types, the rounds' data (Run/PlanQTypes.lean: `RD`), the list of the trees
that are left, and a function that runs on the untyped view and returns the claims or nothing.
Shape, reads, view and the test of the proofs of work are Run/PlanQS.lean's own.

Main definitions.
  `LeftT`: a tree that is left: its number among the chain's own trees, and its depth.
  `EjOf L`: the oracle kind of the trees left: a position is (which tree, which leaf), a symbol a
    column.
  `preIOR`: the reduction.
Main theorems, each by unfolding: `preIOR_noReads`, `preIOR_noTie`, `preIOR_copy`,
`preIOR_srcIdx`, `preIOR_srcAux`: five of the conditions of form of `Hiop.PreListR`;
`preIOR_passes`: what the run hands on is handed on.

What is not said. Nothing on soundness or on an honest side. That the verifier is local. That a
tree of `L` is a tree of `ds` of that depth: at another number or depth the oracle left holds
empty columns there.


-/
import Run.PlanQS
import Ior.Ior

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ

/-- A tree that a chain leaves to later chains. -/
structure LeftT where
  /-- its number: among the chain's own trees in `preIOR`; over the whole file in Stage.lean,
  StageOf.lean, RowFit.lean -/
  no : ℕ
  /-- its depth -/
  a : ℕ

/-- A position in the trees left: which tree, which leaf. -/
abbrev PosL (L : List LeftT) : Type := Σ i : Fin L.length, Fin (2 ^ (L.get i).a)

/-- The oracle kind of the trees left. -/
abbrev EjOf (L : List LeftT) : ExtSpec :=
  ⟨PosL L → List UInt64, PosL L, List UInt64, fun y p => y p⟩

/-- **The reduction of a chain that leaves oracles.** `E`: the oracle kind of the implicit instance,
of which the chain reads nothing. `run`: from the explicit instance and the view to the claims. -/
def preIOR {Xi Xo : Type} (E : ExtSpec) (C : CK) (ds : List RD) (L : List LeftT)
    (run : Xi → View → Option Xo) : IOR Xi E Xo (E.prod (EjOf L)) where
  shape := Twin.up (SOf C ds)
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun ρ =>
    (((wanted ds (drawnSL C ds ρ.2)).filterMap fun nx =>
      (posAtS C ds nx.1 nx.2).map fun p => (Sum.inr p : OPos (Twin.up (SOf C ds))))).toFinset
  out := fun x _ τ =>
    if passSL C ds (rhoSL C ds τ.2.2) then run x (viewSL C ds τ.2.2) else none
  imp := fun y τ => (y, fun p => (colAtS C ds τ.2.2 (L.get p.1).no p.2.val).getD [])
  srcE := fun _ q => match q with
    | .inl p => {p}
    | .inr _ => ∅
  srcO := fun _ q => match q with
    | .inl _ => ∅
    | .inr p => ((posAtS C ds (L.get p.1).no p.2.val).map fun z =>
        (Sum.inr z : OPos (Twin.up (SOf C ds)))).toFinset
  tie := fun _ _ => ∅

section
variable {Xi Xo : Type} (E : ExtSpec) (C : CK) (ds : List RD) (L : List LeftT)
  (run : Xi → View → Option Xo)

theorem preIOR_noReads (ρ) : (preIOR E C ds L run).extReads ρ = ∅ := rfl

theorem preIOR_noTie (ρ p) : (preIOR E C ds L run).tie ρ p = ∅ := rfl

theorem preIOR_copy (y τ) : ((preIOR E C ds L run).imp y τ).1 = y := rfl

theorem preIOR_srcIdx (ρ) (p : E.Pos) :
    (preIOR E C ds L run).srcE ρ (Sum.inl p) = {p} ∧ (preIOR E C ds L run).srcO ρ (Sum.inl p) = ∅ :=
  ⟨rfl, rfl⟩

theorem preIOR_srcAux (ρ) (q : PosL L) : (preIOR E C ds L run).srcE ρ (Sum.inr q) = ∅ := rfl

/-- What every value of the run has, every output of the verifier has. -/
theorem preIOR_passes (good : Xi → Xo → Prop) (h : ∀ x v b, run x v = some b → good x b) (x y τ b)
    (hb : (preIOR E C ds L run).out x y τ = some b) : good x b := by
  have hb' :
      (if passSL C ds (rhoSL C ds τ.2.2) then run x (viewSL C ds τ.2.2) else none) = some b := hb
  split at hb'
  · exact h x _ b hb'
  · cases hb'

end

end OnBytes.Maker
