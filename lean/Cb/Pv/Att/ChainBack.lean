-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/ChainBack.lean: what the verifier of a chain (Cb/Pv/Att/Chain.lean) hands on: the first
statement, inside the last one, and the oracles.

Statements and proofs.

Main names:
  `Ch.out_back`: whatever the chain's verifier puts out, the first statement inside it (`c.back`) is
    the statement that it was given. No condition on the chain.
  `Ch.imp_eq`: the oracles behind the chain are the oracles before it.
Limits: nothing on soundness.
-/
import Cb.Pv.Att.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole Johnson.L5.Layers Johnson.L5.Door Cb.Pv.Lay

variable {E : Type} [Field E] [Fintype E] {M : Type}

namespace Ch

theorem imp_eq (Ex : ExtSpec) : ∀ {X : Type} (c : Ch E M X) (y : Ex.Str) (τ : Tr (c.R Ex).shape),
    (c.R Ex).imp y τ = y
  | _, .done _, _, _ => rfl
  | _, .ride Y n F cl _ _ _ next, y, τ =>
    imp_eq Ex next y (Tr.snd (s := (rideNR Y n F cl Ex).shape) τ)
  | _, .draw D _ _ next, y, τ =>
    imp_eq Ex next y (Tr.snd (s := (IOR.draw D.D (fun x β => (x, β)) Ex).shape) τ)
  | _, .send n D _ _ _ next, y, τ =>
    imp_eq Ex next y (Tr.snd (s := (Lay.send E (Fin n) D.D _ Ex).shape) τ)

theorem out_back (Ex : ExtSpec) : ∀ {X : Type} (c : Ch E M X) (x : X) (y : Ex.Str)
    (τ : Tr (c.R Ex).shape) (e : c.End), (c.R Ex).out x y τ = some e → c.back e = x
  | _, .done _, _, _, _, _, h => (Option.some.inj h).symm
  | _, .ride Y n F cl _ _ _ next, x, y, τ, e, h => by
    obtain ⟨x₂, h1, h2⟩ := Option.bind_eq_some_iff.1
      (show ((rideNR Y n F cl Ex).out x y (Tr.fst τ)).bind (fun x₂ => (next.R Ex).out x₂
        ((rideNR Y n F cl Ex).imp y (Tr.fst τ))
        (Tr.snd (s := (rideNR Y n F cl Ex).shape) τ)) = some e from h)
    obtain ⟨o, -, rfl⟩ := Option.map_eq_some_iff.1 h1
    show (next.back e).1.1 = x
    rw [out_back Ex next _ _ _ e h2]
  | _, .draw D _ _ next, x, y, τ, e, h => by
    have h2 : (next.R Ex).out (x, drawn (Tr.fst τ)) y
        (Tr.snd (s := (IOR.draw D.D (fun x β => (x, β)) Ex).shape) τ) = some e := h
    show (next.back e).1 = x
    rw [out_back Ex next _ _ _ e h2]
  | _, .send n D _ _ _ next, x, y, τ, e, h => by
    have h2 : (next.R Ex).out ((x, sent (Tr.fst τ)), drawnS (Tr.fst τ)) y
        (Tr.snd (s := (Lay.send E (Fin n) D.D _ Ex).shape) τ) = some e := h
    show (next.back e).1.1 = x
    rw [out_back Ex next _ _ _ e h2]

end Ch
end Cb.Pv.Att

#print axioms Cb.Pv.Att.Ch.imp_eq
#print axioms Cb.Pv.Att.Ch.out_back
