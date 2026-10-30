-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/TieForm.lean: two properties of form of the draw and the fused tie
(Cb/Pv/KeyLookup/TieM.lean), if the sumcheck, which is a parameter, has them: the caller's state is
handed on unchanged, and the oracles are only copied. The draw and the tie together are called the
head.

A link above the lookup wants both (Cb/Pv/KeyLookup/AsmForm.lean). It imports no file of the program
(OnBytes/Iop, OnBytes/Params, ...). Terms: lean/GLOSSARY.md.

Main names:
  `Tie.passes_chainK`, `Tie.copies_chainK`: the library's rules for blocks in a row (`passes_chain`,
  `OnlyCopies.seq`), for blocks without an honest side.
  `Tie.LtForm D SK n`: what is asked of the sumcheck: at each of the steps 0, .., n its verifier
  hands its state on and only copies its oracles.
  `Tie.ltForm_lib`: the library's own sumcheck does (`psc_passes`, `psc_onlyCopies`).
  `Tie.tie_passes`: the tie hands on the state from before the tie, which `base` reads off the
  nested state.
  `head_form`: LtForm ⇒ `(A.headK L SK n).R.Passes id (·.st)` and `(A.headK L SK n).R.OnlyCopies`.
  `head_form_lib`: at the library's sumcheck, with no condition.
Limits: the one condition is `LtForm`. Nothing on an honest side; nothing on relations.

-/
import Cb.Pv.KeyLookup.TieM
import Cb.Pv.KeyLookup.AsmForm
import Cb.Ld.LdLkpFormatAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn

namespace Tie

section
variable {Ex : ExtSpec} {Rc : Type}

theorem passes_chainK (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) (r : ∀ l, X l → Rc) :
    ∀ n, (∀ l ≤ n, (b l).R.Passes (r l) (r (l + 1))) →
      (BkK.chain X b n).R.Passes (r 0) (r (n + 1))
  | 0, h => h 0 (Nat.le_refl 0)
  | n + 1, h =>
    (passes_chainK X b r n fun l hl => h l (Nat.le_succ_of_le hl)).seq (h (n + 1) (Nat.le_refl _))

theorem copies_chainK (X : ℕ → Type) (b : ∀ l, BkK (X l) (X (l + 1)) Ex) :
    ∀ n, (∀ l ≤ n, (b l).R.OnlyCopies) → (BkK.chain X b n).R.OnlyCopies
  | 0, h => h 0 (Nat.le_refl 0)
  | n + 1, h =>
    (copies_chainK X b n fun l hl => h l (Nat.le_succ_of_le hl)).seq (h (n + 1) (Nat.le_refl _))

end

variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

/-- What is asked of the sumcheck, a parameter, at the steps 0, .., n. -/
def LtForm (D : TieF E) (SK : PscLtK E Ex) (n : ℕ) : Prop :=
  ∀ l ≤ n, (SK.full (D.lv l).T.par).R.Passes Prod.snd PscPar.Out.st ∧
    (SK.full (D.lv l).T.par).R.OnlyCopies

theorem ltForm_lib (D : TieF E) (Ex : ExtSpec) (n : ℕ) : LtForm D (PscLtK.lib E Ex) n := fun l _ =>
  ⟨psc_passes (D.lv l).T.par Ex, psc_onlyCopies (D.lv l).T.par Ex⟩

theorem step_passes (D : TieF E) (SK : PscLtK E Ex) (l : ℕ)
    (h : (SK.full (D.lv l).T.par).R.Passes Prod.snd PscPar.Out.st) :
    (D.stepK SK l).R.Passes (fun x => (D.lv l).base x.2) (fun x => (D.lv (l + 1)).base x.2) :=
  (passes_map h (D.lv l).base).post _ _ fun _ _ e => by
    obtain rfl := Option.some.inj e
    rfl

/-- The tie hands on the state from before it. -/
theorem tie_passes (D : TieF E) (SK : PscLtK E Ex) (n : ℕ) (h : LtForm D SK n) :
    (D.tieK SK n).R.Passes (fun x => (D.lv 0).base x.2) (fun x => (D.lv (n + 1)).base x.2) :=
  passes_chainK (fun l => E × (D.lv l).T.St) (D.stepK SK) (fun l x => (D.lv l).base x.2) n
    fun l hl => step_passes D SK l (h l hl).1

theorem tie_copies (D : TieF E) (SK : PscLtK E Ex) (n : ℕ) (h : LtForm D SK n) :
    (D.tieK SK n).R.OnlyCopies :=
  copies_chainK (fun l => E × (D.lv l).T.St) (D.stepK SK) n fun l hl =>
    onlyCopies_post (h l hl).2 _

end Tie

variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

/-- The head hands the caller's state on and only copies its oracles. -/
theorem head_form (A : Dat E) (L : TiePl E A.J) (SK : PscLtK E Ex) (n : ℕ)
    (h : Tie.LtForm (A.tie L) SK n) :
    (A.headK L SK n).R.Passes id (fun x => x.st) ∧ (A.headK L SK n).R.OnlyCopies := by
  have hd : (A.drawK Ex).R.Passes id (fun x : A.XS => x.st) :=
    Passes.draw E A.ini Ex id (fun x : A.XS => x.st) fun _ _ => rfl
  have h1 := passes_map (Tie.tie_passes (A.tie L) SK n h) (fun x : A.XS => x.st)
  have h2 : (A.tieK L SK n).R.Passes (fun x : A.XS => x.st) (fun x : A.XS => x.st) :=
    (h1.pre (fun x : A.XS => some ((0 : E), x)) (ExtMap.id Ex) (r₁ := fun x : A.XS => x.st)
      fun _ _ e => by
        obtain rfl := Option.some.inj e
        rfl).post (fun x => some (A.back L n x)) (ExtMap.id Ex) fun _ _ e => by
          obtain rfl := Option.some.inj e
          rfl
  exact ⟨hd.seq h2,
    (OnlyCopies.draw E A.ini Ex).seq
      (onlyCopies_post (onlyCopies_pre (Tie.tie_copies (A.tie L) SK n h) _) _)⟩

theorem head_form_lib (A : Dat E) (L : TiePl E A.J) (Ex : ExtSpec) (n : ℕ) :
    (A.headK L (PscLtK.lib E Ex) n).R.Passes id (fun x => x.st) ∧
      (A.headK L (PscLtK.lib E Ex) n).R.OnlyCopies :=
  head_form A L _ n (Tie.ltForm_lib (A.tie L) Ex n)

end Lk6

#print axioms Lk6.head_form
#print axioms Lk6.head_form_lib
