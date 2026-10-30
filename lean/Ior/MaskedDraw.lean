-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/MaskedDraw.lean: the verifier draws a value, then a masked block: a masked block, for a claim
Cl' as asked below.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean): a round
in which the verifier only draws a value, then a further reduction.
Definitions, a statement, its proof. No protocol, no code occurs here (the one reduction that is
named: `IOR.draw`, Ior/Draw.lean).
A masked block is a block with the item "masked messages" (`Honest.MM`, over parameters `MaskData`:
Ior/Masked.lean).

Ior/Draw.lean: in `IOR.draw` the prover sends nothing, the verifier sends β, the explicit part x
becomes nx x β; oracles and witness stay. If a block with the item "masked messages"
(Ior/Masked.lean: `H.MM D`) follows, the two together have the item (`Spec.mm_draw_seq`): same own
masks, same reading of the witness; the simulator reads x and the verifier's messages: it runs the
block's simulator at nx x β. The claim Cl' with which the whole starts is a parameter. Asked: it
gives the block's claim at every β, and it does not read the own masks in this sense:
`∀ x k M, Cl' x k → Cl' x (D.put M k)`.

Why: many claims are first joined by random coefficients, then reduced by a masked sumcheck: the
whole is one masked block.
Terms: lean/GLOSSARY.md.
-/
import Ior.Masked
import Ior.Draw
import Ior.SeqProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

namespace IOR
variable {X X₂ X₃ : Type} {E E₃ : ExtSpec} {W W₃ : Type}

/-- the value drawn, and the verifier's messages of the block -/
def drawnOf {Dd : Type} [Fintype Dd] [Nonempty Dd] {s : Shape} (ρ : Rho ([drawRound Dd] ++ s)) :
    Dd := ρ.1
def restOf {Dd : Type} [Fintype Dd] [Nonempty Dd] {s : Shape} (ρ : Rho ([drawRound Dd] ++ s)) :
    Rho s := ρ.2

/-- the plain parts of the whole: nothing, then those of the block -/
def afterNone {Dd : Type} [Fintype Dd] [Nonempty Dd] {s : Shape} (pl : Plains s) :
    Plains ([drawRound Dd] ++ s) := ((), pl)

/-- The parameters of the whole. -/
def MaskData.afterDraw {R₂ : IOR X₂ E X₃ E₃} (D : MaskData R₂ W) (Dd : Type)
    [Fintype Dd] [Nonempty Dd] (nx : X → Dd → X₂) (Cl' : X → D.Kc → Prop) :
    MaskData ((IOR.draw Dd nx E).seq R₂) W :=
  { Kc := D.Kc, kc := D.kc, Xp := X, pub := fun x => x, Mk := D.Mk, put := D.put, Cl := Cl'
    msg := fun k x ρ =>
      afterNone (Dd := Dd)
        (D.msg k (D.pub (nx x (drawnOf (Dd := Dd) (s := R₂.shape) ρ)))
          (restOf (Dd := Dd) (s := R₂.shape) ρ))
    sim := fun x ρ =>
      (D.sim (D.pub (nx x (drawnOf (Dd := Dd) (s := R₂.shape) ρ)))
          (restOf (Dd := Dd) (s := R₂.shape) ρ)).map
        (afterNone (Dd := Dd)) }

end IOR

namespace Spec
open IOR

/-- States, under the hypotheses below: a draw, then a masked block, is a masked block. -/
def mm_draw_seq : Prop :=
  ∀ (X X₂ X₃ : Type) (E E₃ : ExtSpec) (W W₃ : Type) (R₂ : IOR X₂ E X₃ E₃)
      (H₂ : R₂.Honest W W₃) (D : MaskData R₂ W) (Dd : Type) [Fintype Dd] [Nonempty Dd]
      (nx : X → Dd → X₂) (Cl' : X → D.Kc → Prop),
    H₂.MM D → (∀ x k β, Cl' x k → D.Cl (D.pub (nx x β)) k) →
    (∀ x k M, Cl' x k → Cl' x (D.put M k)) →
    ((Honest.draw Dd nx E W).seq H₂).MM (D.afterDraw Dd nx Cl')

end Spec

open IOR

theorem mm_draw_seq : Spec.mm_draw_seq := by
  intro X X₂ X₃ E E₃ W W₃ R₂ H₂ D Dd _ _ nx Cl' h hcl hst
  refine
    { noOrc := ⟨fun p => match p with
        | .inl e => e.elim
        | .inr p => h.noOrc.false p⟩
      free := fun w x => Set.eq_empty_iff_forall_notMem.2 fun ρ =>
        (IOR.Honest.not_mem_withheld_seq (Honest.draw Dd nx E W) H₂ w x ρ).2
          ⟨fun hh => hh.elim (fun a => a) fun a => a, fun c hh => by rw [h.free] at hh; exact hh⟩
      run := fun w x c ρ => ?_
      stable := hst
      law := fun k x ρ hk => ?_ }
  · have hs := IOR.Honest.run_seq (Honest.draw Dd nx E W) H₂ w x c ρ
    rw [hs]
    refine (Tr.plains_app _ _).trans ?_
    exact congrArg (afterNone (Dd := Dd))
      (h.run w (nx x (drawnOf (Dd := Dd) (s := R₂.shape) ρ))
        c.2 (restOf (Dd := Dd) (s := R₂.shape) ρ))
  · show (unif D.Mk).map
        (afterNone (Dd := Dd) ∘
          fun M =>
            D.msg (D.put M k) (D.pub (nx x (drawnOf (Dd := Dd) (s := R₂.shape) ρ)))
              (restOf (Dd := Dd) (s := R₂.shape) ρ)) = _
    rw [← PMF.map_comp, h.law _ _ _ (hcl x k _ hk)]
    rfl

end Iop
