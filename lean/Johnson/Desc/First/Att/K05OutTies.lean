-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05OutTies.lean: the four ties of the typed out-statement (`OutTies`,
Johnson/Desc/First/Att/K05Left.lean) hold of the lookup's written out-statement `lookOutE`
(OnBytes/Tie/Pv/Lookup/Forest/FoOutD.lean), at every record of end values, by definition.

Statements and proofs.
Main names:
  `outTies_lookOutE`: `OutTies` (Fo.lookOutE h lm jLK ι st En) En ι.
  `outTies_of_eq`: the same of every statement that equals the written one.
Limits: that a statement in front of the kind K5 is `lookOutE` at the rounds of the lookup's yes is
for the law of the lookup's kind to say; it is not shown in this file or in what it imports. Nothing
is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoOutD
import Johnson.Desc.First.Att.K05Left

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb Cb.LdLkp OnBytes OnBytes.Model

/-- **The written out-statement has the four ties**, by definition. -/
theorem outTies_lookOutE {St₀ J₀ : Type} [DecidableEq J₀] (h : Forest.Shape) (lm jLK : ℕ) (ι : Fo.Pl → Option J₀)
    (st : St₀) (En : Fo.Ends Cb.Gl.E) : OutTies (Fo.lookOutE h lm jLK ι st En) En ι :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, rfl⟩

/-- The same, at a statement that is the written one. -/
theorem outTies_of_eq {St₀ J₀ : Type} [DecidableEq J₀] {h : Forest.Shape} {lm jLK : ℕ} {ι : Fo.Pl → Option J₀}
    {st : St₀} {En : Fo.Ends Cb.Gl.E} {x0 : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)}
    (e : x0 = Fo.lookOutE h lm jLK ι st En) : OutTies x0 En ι := e ▸ outTies_lookOutE h lm jLK ι st En

end VerifiableInference.Desc.First.Att.P
