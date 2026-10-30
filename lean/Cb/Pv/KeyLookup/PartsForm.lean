-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/PartsForm.lean: the parts' steps hand the caller's state on unchanged and only copy
their oracles.

Statements and proofs: the line of this stretch in the bundle Bks.Form of
Cb/Pv/KeyLookup/AsmForm.lean.
After the pattern of pass_tie (Cb/Ld/LdLkpFormatAsm.lean). Nothing on an honest side.

Main names:
  D.FormK SK k: what is asked of the letter of the sumcheck at the steps below k: its verifier
    passes
    its state on (Passes Prod.snd Out.st) and only copies its oracles.
  partsK_passes, partsK_copies: the first state is passed on through b and k steps; they only copy.
  partsXK_form: D.FormK SK (m - 1) gives Bks.FormX (A.partsXK wP cP SK).
  partsXK_form_lib: at the sumcheck of Cb/Ld/LdPsc.lean there is no premise (psc_passes,
    psc_onlyCopies: Cb/Ld/LdLkpFormat.lean).

Limits: this file says nothing on soundness.

-/
import Cb.Pv.KeyLookup.AsmForm
import Cb.Pv.KeyLookup.PartsK
import Cb.Ld.LdLkpFormatAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.LdLkp.Kn

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

/-- What is asked of the letter, at the steps below k. -/
def PartsP.FormK (D : PartsP E) (SK : PscLtK E Ex) (k : ℕ) : Prop :=
  ∀ l < k, (SK.full (D.lv l).T.par).R.Passes Prod.snd PscPar.Out.st ∧
    (SK.full (D.lv l).T.par).R.OnlyCopies

theorem mapK_passes {X X' Rc : Type} (φ : X → X') (r : X → Rc) (r' : X' → Rc)
    (h : ∀ x, r' (φ x) = r x) : (mapK Ex φ).R.Passes r r' := fun x _ _ x' e => by
  obtain rfl := Option.some.inj e
  exact h x

theorem mapK_copies {X X' : Type} (φ : X → X') : (mapK Ex φ).R.OnlyCopies :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

variable (D : PartsP E) (SK : PscLtK E Ex)

theorem partsK_passes {X : Type} (b : BkK X (E × (D.lv 0).T.St) Ex) (r : X → D.St0)
    (hb : b.R.Passes r fun x => (D.lv 0).base x.2) :
    ∀ k, D.FormK SK k → (D.afterK SK b k).R.Passes r fun x => (D.lv k).base x.2
  | 0, _ => hb
  | k + 1, h =>
    (partsK_passes b r hb k fun l hl => h l (Nat.lt_succ_of_lt hl)).seq
      ((passes_map (h k (Nat.lt_succ_self k)).1 (D.lv k).base).post _ _ fun o x' e => by
        obtain rfl := Option.some.inj e
        rfl)

theorem partsK_copies {X : Type} (b : BkK X (E × (D.lv 0).T.St) Ex) (hb : b.R.OnlyCopies) :
    ∀ k, D.FormK SK k → (D.afterK SK b k).R.OnlyCopies
  | 0, _ => hb
  | k + 1, h =>
    (partsK_copies b hb k fun l hl => h l (Nat.lt_succ_of_lt hl)).seq
      (onlyCopies_post (h k (Nat.lt_succ_self k)).2 _)

theorem partsK_form_lib (k : ℕ) : D.FormK (PscLtK.lib E Ex) k := fun l _ =>
  ⟨psc_passes (D.lv l).T.par Ex, psc_onlyCopies (D.lv l).T.par Ex⟩

end

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (A : Dat E)
variable (wP : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → A.J) (cP : ℕ → Bool → A.J)
variable (SK : PscLtK E Ex)

theorem partsXK_form (h : (A.partsD wP cP).FormK SK (A.m - 1)) : Bks.FormX (A.partsXK wP cP SK) :=
  ⟨(passes_map
      (partsK_passes (A.partsD wP cP) SK (mapK Ex (A.partsIn wP cP)) (fun x : A.XS => x)
        (mapK_passes _ _ _ fun _ => rfl) (A.partsD wP cP).n h) (fun x : A.XS => x.st)).post _ _
      fun y x' e => by
        obtain rfl := Option.some.inj e
        rfl,
    onlyCopies_post (partsK_copies (A.partsD wP cP) SK _ (mapK_copies _) (A.partsD wP cP).n h) _⟩

theorem partsXK_form_lib : Bks.FormX (A.partsXK wP cP (PscLtK.lib E Ex)) :=
  partsXK_form A wP cP _ (partsK_form_lib (A.partsD wP cP) _)

end
end Lk6

#print axioms Lk6.partsXK_form
#print axioms Lk6.partsXK_form_lib
