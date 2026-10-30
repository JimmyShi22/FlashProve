-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/FrontOn.lean: WHAT THE PROVED BLOCK's OWN PROMISE IN FRONT OF THE
BATCHING ASKS. A statement and its proof.

K10's law asks (hon) that a statement with `on` meets the promise of the joint in front of the
batching (`Cb.Pv.Bat.inJ`, kept beside a further oracle).
  `front_on`: that promise is: no oracle message has a collision at the seed of its sample
    (`Sig.CF`, Cb/Ld/LdSig.lean), and the promise of the joint A₀ on the kept messages. By
    definition.
So it names neither the typed rows' states nor their forms: whichever forms a caller chooses for the
rows of the claim (OrderedOf.lean chooses them), this premise asks the same.
Limits. Nothing on whether the promise can be kept. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice Iop IOR KObj Cb Cb.Pv Johnson.Top.H

variable {K : Type} [Field K] [Fintype K] (s : Cb.Pv.Bat.Size K) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)) (F : ExtSpec)

theorem front_on
    (x : ((((s.B → K) × (∀ b, s.Sb b)) × St₀) × s.S.Smp) × ((E₀.prod s.S.ext).prod F).Str) :
    ((Cb.Pv.Bat.inJ s A₀).keepE F).on x ↔
      s.S.CF x.1.2 x.2.1.2 ∧ A₀.on (x.1.1.2, x.2.1.1) := Iff.rfl

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.front_on
