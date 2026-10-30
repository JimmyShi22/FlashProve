-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SeedRoot.lean: a last part of a derived algorithm (Rom/SpecDerive.lean) whose result is
thrown away does not change the distribution of the output (words of this library:
lean/GLOSSARY.md).

  `Rom.OComp.runEager_derive_drop`
            the statement, for fixed oracle functions, if after that part only a function of earlier
            results is returned; `runEager_derive_cong`, `derive_bind_pure`: lemmas (see their
            statements)

Limits: this file does not define a committer that builds only the first encoding and Test's proof,
and proves nothing on one.
-/
import Compile.SeedShape
import Compile.Spec

noncomputable section

open Rom Iop

namespace Rom
namespace OComp

variable {S : OSpec} {α β γ : Type} (σ : SeedOracle S) (s : Fin (σ.sd + 1)) (g : Fam S)

/-- a derived algorithm whose result is thrown away -/
theorem runEager_derive_const (b : β) :
    ∀ (y : OComp S α) (j : ℕ),
      ((y.bind fun _ => (pure b : OComp S β)).derive σ s j).runEager g = PMF.pure b
  | .pure _, _ => rfl
  | .query o q k, j => runEager_derive_const b (k (g o q)) j
  | .sample n k, j => runEager_derive_const b (k (σ.ψ n (g σ.o (σ.pt s j)))) (j + 1)

/-- after a common first part, two continuations with the same distribution for every counter may be
exchanged -/
theorem runEager_derive_cong {f f' : α → OComp S β}
    (h : ∀ a j, ((f a).derive σ s j).runEager g = ((f' a).derive σ s j).runEager g) :
    ∀ (c : OComp S α) (j : ℕ),
      ((c.bind f).derive σ s j).runEager g = ((c.bind f').derive σ s j).runEager g
  | .pure a, j => h a j
  | .query o q k, j => runEager_derive_cong h (k (g o q)) j
  | .sample n k, j => runEager_derive_cong h (k (σ.ψ n (g σ.o (σ.pt s j)))) (j + 1)

/-- A last part whose result is thrown away may be dropped. -/
theorem runEager_derive_drop (c : OComp S α) (y : α → OComp S β) (h : α → γ) (j : ℕ) :
    ((c.bind fun a => (y a).bind fun _ => (pure (h a) : OComp S γ)).derive σ s j).runEager g =
      ((c.bind fun a => (pure (h a) : OComp S γ)).derive σ s j).runEager g :=
  runEager_derive_cong σ s g (fun a j => runEager_derive_const σ s g (h a) (y a) j) c j

/-- a last step without coins and queries may be inside or outside `derive` -/
theorem derive_bind_pure (h : α → β) :
    ∀ (c : OComp S α) (j : ℕ), (c.bind fun a => (pure (h a) : OComp S β)).derive σ s j =
      (c.derive σ s j).bind fun a => pure (h a)
  | .pure _, _ => rfl
  | .query o q k, j => congrArg (OComp.query o q) (funext fun r => derive_bind_pure h (k r) j)
  | .sample n k, j =>
    congrArg (OComp.query σ.o (σ.pt s j)) (funext fun d => derive_bind_pure h (k (σ.ψ n d)) (j + 1))

end OComp
end Rom

