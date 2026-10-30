-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwFill.lean.
The lookup's verifier with the short sumcheck filled by `V₀`, `V₀C` never refuses; its
out-statement, for all inputs.

Definitions, and theorems with their proofs. `V₀`, `V₀C`, `F₀`, `Eq0` are of Cb/G6/Pick.lean (in
each round the constant coefficient is left out); `shortV` is of Cb/G6/Value.lean, `shortVC` of
Cb/G6/Core.lean.
Main names:
  `SK₀ E Ex`: the verifiers and errors of `V₀`, `V₀C`. `sk₀_eq`: it is `PscLtK.ofShort V₀ V₀C Ex`,
    by rfl.
  `SV₀ E Ex`: their values `shortV Y (F₀ Y)`, `shortVC Y (F₀ Y)`. `fullV₀`, `coreV₀`: under `Eq0 Y`
    the verifier is total with that value.
  `ltV₀`: `LtV (SV₀ E Ex) A` for every assembly A, from `asmK_eq0` (Cb/Pv/Lookup/Know/AsmKV0.lean):
    no premise is left.
  `chnK₀_out`, `baseK₀_out`: for every A, statement and transcript: the out of the chain and of the
    lookup's verifier.
Limits: at this one filling. The verifier's side alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwOut
import Cb.Pv.Lookup.Know.AsmKV0

set_option autoImplicit false

namespace Tw
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole

noncomputable section
variable (E : Type) [Field E] [Fintype E]

/-- The letter at the filling `V₀`, `V₀C`. -/
def SK₀ (Ex : ExtSpec) : PscLtK E Ex :=
  ⟨fun Y => ⟨(V₀ Y Ex).R, (V₀ Y Ex).ε⟩, fun Y => ⟨(V₀C Y Ex).R, (V₀C Y Ex).ε⟩⟩

/-- Its value: `shortV`, `shortVC` at the pick `F₀`. -/
def SV₀ (Ex : ExtSpec) : PscLtV (SK₀ E Ex) :=
  ⟨fun Y => shortV Y (F₀ Y), fun Y => shortVC Y (F₀ Y)⟩

variable {E}

theorem fullV₀ (Ex : ExtSpec) (Y : PscPar E) (h : Eq0 Y) : (SV₀ E Ex).FullV Y :=
  ⟨fun x y τ => short_out Y (F₀ Y) Ex (F₀_ok Y h) x y τ, fun _ _ => rfl⟩

theorem coreV₀ (Ex : ExtSpec) (Y : PscPar E) (h : Eq0 Y) : (SV₀ E Ex).CoreV Y :=
  ⟨fun x y τ => short_outC Y (F₀ Y) Ex (F₀_ok Y h) x y τ, fun _ _ => rfl⟩

/-- `SK₀` is the letter over which `LkAsmH.baseK V₀ V₀C` (Cb/Pv/Lookup/Know/AsmKV.lean) is built. -/
theorem sk₀_eq (Ex : ExtSpec) : SK₀ E Ex = PscLtK.ofShort V₀ V₀C Ex := rfl

/-- `LtV` holds at this filling, for every assembly: no premise is left on the letter's value. -/
theorem ltV₀ (Ex : ExtSpec) (A : LkAsmH E) : LtV (SV₀ E Ex) A :=
  { tie := fun l _ => fullV₀ Ex _ ((asmK_eq0 E A).1 l)
    keys := fun l _ => fullV₀ Ex _ ((asmK_eq0 E A).2.1 l)
    tab := fun l _ => fullV₀ Ex _ ((asmK_eq0 E A).2.2.1 l)
    clo := coreV₀ Ex _ (asmK_eq0 E A).2.2.2.1
    bit := fullV₀ Ex _ (asmK_eq0 E A).2.2.2.2 }

/-- The chain's last state at the filling, for all inputs. -/
theorem chnK₀_out (Ex : ExtSpec) (A : LkAsmH E) (a : A.St × Ex.Str)
    (τ : Tr (A.chnK (SK₀ E Ex)).R.shape) :
    (A.chnK (SK₀ E Ex)).R.red.out a τ = some (chnV (SV₀ E Ex) A a.1 τ, a.2) :=
  chnK_out (SV₀ E Ex) A (ltV₀ Ex A) a τ

/-- The lookup's verifier at the filling never refuses; its value, for all inputs. -/
theorem baseK₀_out (Ex : ExtSpec) (A : LkAsmH E) (a : A.St × Ex.Str)
    (τ : Tr (A.baseKS (SK₀ E Ex)).R.shape) :
    (A.baseKS (SK₀ E Ex)).R.red.out a τ = some (A.rd (chnV (SV₀ E Ex) A a.1 τ), a.2) :=
  baseKS_out (SV₀ E Ex) A (ltV₀ Ex A) a τ

end
end Tw
#print axioms Tw.sk₀_eq
#print axioms Tw.ltV₀
#print axioms Tw.chnK₀_out
#print axioms Tw.baseK₀_out
