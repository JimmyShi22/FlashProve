-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/NeedRelErase.lean: from token programs to oracle algorithms, up to a relation on what they
return.

Generic; it relates Compile/NeedRel.lean to Rom/OverOneNRel.lean. `erase` (Compile/Star.lean) puts
secret strings in the place of the tokens of a program (`Step`, Rom/Defer.lean); it returns the
program's value together with the store of strings.

  `ERel R`         The relation on (value, store): the values are related by R, the stores are
                   equal.
  `Alike.erase`    Programs that are alike up to R (`Alike R`, Compile/NeedRel.lean: "The same
                   program but for the values at its ends, which are related by R.") are, erased
                   from the same store, alike up to `ERel R` (`OComp.AlikeO`, Rom/OverOneNRel.lean).
  `SFacR.erase`    A program that goes on in the same way up to R after related answers (related by
                   ag: `SFacR ag R`, Compile/NeedRel.lean) is, erased, an algorithm that does so up
                   to `ERel R` (`OComp.FactorsByR ag`, Rom/OverOneNRel.lean).

So a prover that is split in two after `erase`, and passes whole answers from the first part to the
second, can still be shown to read only a part of them.

Limits: nothing on any scheme.
-/
import Compile.NeedRel
import Rom.OverOneNRel

open Rom Iop

namespace Compile
namespace Need

variable {S : OSpec} {sp : Split S} {α : Type}
  {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop} {R : α → α → Prop}

/-- values related by R, equal stores -/
def ERel (R : α → α → Prop) (x y : α × List Bits) : Prop := R x.1 y.1 ∧ x.2 = y.2

theorem Alike.erase {c c' : Step S sp α} (h : Alike R c c') :
    ∀ vs, OComp.AlikeO (ERel R) (Compile.erase c vs) (Compile.erase c' vs) := by
  induction h with
  | pure h => exact fun _ => .pure ⟨h, rfl⟩
  | sample m _ ih => exact fun vs => .sample m fun r => ih r vs
  | plain o q _ ih => exact fun vs => .query o q fun r => ih r vs
  | fresh ℓ _ ih => exact fun vs => .sample _ fun r => ih _ _
  | marked o t us pt inj _ ih => exact fun vs => .query o _ fun r => ih _ _ _
  | reveal ts _ ih => exact fun vs => ih _ vs

theorem SFacR.erase {c : Step S sp α} (h : SFacR ag R c) :
    ∀ vs, OComp.FactorsByR ag (ERel R) (Compile.erase c vs) := by
  induction h with
  | pure h => exact fun _ => .pure ⟨h, rfl⟩
  | sample m _ ih => exact fun vs => .sample m fun r => ih r vs
  | plain o q he _ ih => exact fun vs => .query o q (fun r r' e => (he r r' e).erase vs) fun r => ih r vs
  | fresh ℓ _ ih => exact fun vs => .sample _ fun r => ih _ _
  | marked o t us pt inj he _ ih =>
    refine fun vs => .query o _ (fun r r' e => ?_) fun r => ih _ _ _
    obtain ⟨h1, h2⟩ := he _ _ r r' e
    show OComp.AlikeO _ (Compile.erase _ (vs ++ [List.ofFn (sp.split o r).2]))
      (Compile.erase _ (vs ++ [List.ofFn (sp.split o r').2]))
    rw [h1]
    exact (h2 _).erase _
  | reveal ts _ ih => exact fun vs => ih _ vs

end Need
end Compile
