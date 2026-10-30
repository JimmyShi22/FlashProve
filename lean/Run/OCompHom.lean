-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OCompHom.lean: the monad of trees of queries: "run at f" as a morphism of monads into the
identity monad; "asks at most t" and "tosses no coin" as counts.

Four definitions: the instances, at ZKCP/Defs.lean's `OComp lam` (oracle computations), of the two
generic notions of Run/Hom.lean; and what each says, by definition.

Main names:
  `detHom f`: a tree ↦ its result at the oracle f, every coin toss yielding 0 (Run/OCompM.lean:
    `det`, `det_pure'`, `det_bind'`).
  `qbCost`: `Cost (OComp lam)`: le x t := ZKCP/Defs.lean's bound "at most t queries on every path"
    (`QueryBound`).
  `ncCost`: le x t := "no path of x has a coin toss", whatever t is: pure and bind keep it, so
    every statement on counts that is generic in the count gives it too.
  `qc`: both at once.
  `detHom_on_HM`: the hash over the tree monad, read through detHom f, is the hash over the
    function oB f.
  `qc_HM`: on the hash over the tree monad.

Limits: this file says nothing on any rule of the format but the hash (`detHom_on_HM`, `qc_HM`):
the morphism and the counts at the format's functions are in Run/HomFmt.lean and Run/CostFmt.lean
(the latter over `CostP`, Run/CostP.lean).

Terms: lean/GLOSSARY.md.
-/
import Run.Hom
import Run.OCompM

set_option autoImplicit false

namespace Run
open ZKCP

/-- "Run at f" as a morphism of monads. -/
def detHom {lam : ℕ} (f : Oracle lam) : Hom (OComp lam) Id where
  app := fun c => c.det f
  app_pure := fun _ => rfl
  app_bind := fun x g => OComp.det_bind f x g

/-- "Asks at most t". -/
def qbCost (lam : ℕ) : Cost (OComp lam) where
  le := fun x t => x.QueryBound t
  le_pure := fun _ => trivial
  le_bind := fun x g s t hx hg => OComp.QueryBound.bind g t hg x s hx
  le_mono := fun x s t hx hst => OComp.QueryBound.mono x s t hst hx

/-- "Tosses no coin", whatever the number. -/
def ncCost (lam : ℕ) : Cost (OComp lam) where
  le := fun x _ => x.NoCoin
  le_pure := fun _ => trivial
  le_bind := fun _ _ _ _ hx hg => OComp.NoCoin.bind hx hg
  le_mono := fun _ _ _ hx _ => hx

/-- Both at once: tosses no coin and asks at most t. -/
def qc (lam : ℕ) : Cost (OComp lam) where
  le := fun x t => x.NoCoin ∧ x.QueryBound t
  le_pure := fun _ => ⟨trivial, trivial⟩
  le_bind := fun x g s t hx hg =>
    ⟨OComp.NoCoin.bind hx.1 fun a => (hg a).1,
      OComp.QueryBound.bind g t (fun a => (hg a).2) x s hx.2⟩
  le_mono := fun x s t hx hst => ⟨hx.1, OComp.QueryBound.mono x s t hst hx.2⟩

theorem detHom_app {lam : ℕ} {α : Type} (f : Oracle lam) (c : OComp lam α) :
    (detHom f).app c = c.det f := rfl

theorem qbCost_le {lam : ℕ} {α : Type} (x : OComp lam α) (t : ℕ) :
    (qbCost lam).le x t ↔ x.QueryBound t := Iff.rfl

theorem ncCost_le {lam : ℕ} {α : Type} (x : OComp lam α) (t : ℕ) : (ncCost lam).le x t ↔ x.NoCoin :=
  Iff.rfl

theorem qc_le {lam : ℕ} {α : Type} (x : OComp lam α) (t : ℕ) :
    (qc lam).le x t ↔ x.NoCoin ∧ x.QueryBound t := Iff.rfl

/-- The hash over the tree monad tosses no coin and asks at most twice. -/
theorem qc_HM (number tree index : Nat) (start bytes : ByteArray) :
    (qc 256).le (_root_.Fmt.HM askB number tree index start bytes) 2 :=
  ⟨noCoin_HM number tree index start bytes, asks_HM number tree index start bytes⟩

/-- The hash over the tree monad, read through "run at f", is the hash over the function `oB f`. -/
theorem detHom_on_HM (f : Oracle 256) :
    (detHom f).on (_root_.Fmt.HM askB) = _root_.Fmt.HO (oB f) := by
  funext number tree index start bytes
  exact det_HM f number tree index start bytes

end Run
