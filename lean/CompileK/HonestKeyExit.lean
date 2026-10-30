-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyExit.lean: "under an honest key no false instance is accepted" is carried from the
compiler's typed oracles to one random oracle and to the literal syntax (`wrongExp`,
ZKCP/HonestKey.lean), with the honest committer kept typed.


This file is about soundness of the compiled argument where the key is made honestly: it carries the
bound from several oracles with long answers to one random oracle.
Statements and proofs.
`honestExp A i Pt` (CompileK/HonestKeySound.lean): an honest key for i, any prover Pt handed both
keys, then V.



Main names:
  `Rom.Spec.honest_overOne`: for every scheme A over a family of oracles, every coding m, every
    prover Pt over the one oracle, every event E on (bit, instance), Pr [ E | honestExp (A over the
    one oracle) i Pt ] = Pr [ E | honestExp A i (Pt brought down) ] (an equation). The prover's
    query at a string becomes one query at that string's point (`down`, Rom/ExitDown.lean), so its
    number of queries does not grow.
  `Rom.Spec.honest_oneOf`: Pr [ E | ZKCP.wrongExp (the scheme of ZKCP/Defs.lean that G gives) i Pt ]
    = Pr [ E | honestExp G i Pt ] (an equation).








Why the committer is kept typed: the proof by which index binding goes to one oracle brings both
adversaries down, a string a query. An honest committer over the one oracle asks every block of
every long answer: brought down, each block would be an entry of the typed trace, and the hash term
would be squared in that larger number. Here the honest parties are never brought up and down: under
the glued oracle (`glue`, Rom/ExitDown.lean) they are the typed ones (`honestExp_glue`).

Limits: what the head of CompileK/HonestKeySound.lean lists as not said is not said here either. No
number is evaluated here.





Terms: lean/GLOSSARY.md.
-/
import CompileK.HonestKeySound
import CompileK.GrindOpt
import Rom.ExitBind
import ZKCP.HonestKey
import ZKCP.SpecialAny

set_option autoImplicit false

noncomputable section

namespace Rom
open ZKCP MeasureTheory
open scoped ENNReal

namespace Spec

/-- From the family of oracles to the one oracle: an equation; the honest parties stay typed. -/
def honest_overOne : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (I X W IVK ISK Pf : Type) (m : OracleCoding S lam)
      (A : Gen.Arg S I X W IVK ISK Pf) (i : I)
      (Pt : IVK × ISK → OComp (rom lam) (X × Pf)) (E : Set (Bool × X)),
    Rom.Pr (Gen.honestExp (schemeOverOneHashFunction m A) i Pt) (fun _ => E) =
      Rom.Pr (Gen.honestExp A i fun k => down m (Pt k)) (fun _ => E)

/-- To the syntax of ZKCP/Defs.lean: an equation. -/
def honest_oneOf : Prop :=
  ∀ (lam : ℕ) (I X W IVK ISK Pf : Type) (G : Gen.Arg (rom lam) I X W IVK ISK Pf) (i : I)
      (Pt : IVK × ISK → ZKCP.OComp lam (X × Pf)) (E : Set (Bool × X)),
    ZKCP.Pr (ZKCP.wrongExp (SpecialAny.oneOf G) i Pt) (fun _ => E) =
      Rom.Pr (Gen.honestExp G i fun k => toRom (Pt k)) (fun _ => E)

end Spec

theorem honestExp_glue {S : OSpec} {lam : ℕ} {I X W IVK ISK Pf : Type} (m : OracleCoding S lam)
    (A : Gen.Arg S I X W IVK ISK Pf) (i : I)
    (Pt : IVK × ISK → OComp (rom lam) (X × Pf)) (F : Fam S) :
    (Gen.honestExp (schemeOverOneHashFunction m A) i Pt).runEager (glue m F) =
      (Gen.honestExp A i fun k => down m (Pt k)).runEager F := by
  have e1 : Gen.honestExp (schemeOverOneHashFunction m A) i Pt =
      ((A.C i).overOne m).bind fun k =>
        (Pt k).bind fun o => ((A.V k.1 o.1 o.2).overOne m).bind fun b => .pure (b, o.1) := rfl
  have e2 : (Gen.honestExp A i fun k => down m (Pt k)) =
      (A.C i).bind fun k =>
        (down m (Pt k)).bind fun o => (A.V k.1 o.1 o.2).bind fun b => .pure (b, o.1) := rfl
  rw [e1, e2]
  simp only [OComp.runEager_bind, runEager_overOne, readBlocks_glue, runEager_down, OComp.runEager]

theorem honest_overOne : Spec.honest_overOne := by
  intro S lam I X W IVK ISK Pf m A i Pt E
  unfold Pr
  rw [lintegral_glue m (fun g => PrCoins g (Gen.honestExp (schemeOverOneHashFunction m A) i Pt) E)]
  · simp only [PrCoins, honestExp_glue m A]
  · simp only [PrCoins, honestExp_glue m A]
    exact measurable_PrCoins _ _

theorem honest_oneOf : Spec.honest_oneOf := by
  intro lam I X W IVK ISK Pf G i Pt E
  rw [← Rom.Pr_toRom (ZKCP.wrongExp (SpecialAny.oneOf G) i Pt) (fun _ => E)]
  congr 1
  unfold ZKCP.wrongExp Gen.honestExp
  simp only [toRom_bind, toRom_pure]
  show ((toRom (ofRom (G.C i))).bind fun k =>
      (toRom (Pt k)).bind fun o =>
        (toRom (ofRom (G.V k.1 o.1 o.2))).bind fun b => OComp.pure (b, o.1)) = _
  simp only [toRom_ofRom]

end Rom
