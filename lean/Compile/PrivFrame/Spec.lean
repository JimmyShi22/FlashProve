-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/PrivFrame/Spec.lean: THE FRAME of a proof of index privacy by a reduction around a game.
A DEFINITION AND ONE STATEMENT; the proof is in Compile/PrivFrame/Proof.lean. General in the family
of oracles, in the scheme, in the reduction and in the game.

A general statement. This file states no goal of the release.

The library's proofs of index privacy for compiled schemes have one shape. A REDUCTION (a Wrap,
Compile/Step1_defc_Gen.lean) stands between the adversary and a GAME without hashing; the game has a
real side, which knows the index, and a simulated side, which does not. The simulator of the
definition is the reduction around the game's simulated side. This file says once, for any scheme,
what has to be shown:

  hop    the real experiment at the index i is within h t n of the reduction around the game's real
         side at i;
  adm    the adversary with the reduction inside is one that the game admits;
  game   for the adversaries that the game admits, its two sides are within z t n;
  cons   the reduction around the simulated side never answers one query in two ways.

Then the scheme has index privacy in the library's form (Gen.HasIndexPrivacyWith, ZKCP/Gen.lean: the
environment that names the instances sees the adversary's whole view), with the simulator
simOf PP (Wp.world Gs) (Compile/Batch/SpecGlue.lean) and the error h t n + z t n.

The reduction is blind by type: its calls are SCall ("setup", and "prove xs" with the instances of
the adversary's own slots), on the real side too. t: the adversary's queries in all; n: its batches.

  Wrap.pre    a reduction whose calls are first translated by a function.
  Spec.frame  the statement.
Follows the pattern of closePubUTOf and privacyPubGrWithUOf (Compile/Batch/PubProgMainBGr.lean).
Terms: lean/GLOSSARY.md.

-/
import Compile.Batch.SpecGlue
import Compile.Step1_defc_Gen

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Rom

/-- A reduction whose calls are first translated by f. -/
def Wrap.pre {S : OSpec} {Out Out₂ In Out' In' : Type} (Wp : Wrap S Out In Out' In')
    (f : Out₂ → Out) : Wrap S Out₂ In Out' In' where
  τ := Wp.τ
  ans := Wp.ans
  rep := fun w m => Wp.rep w (f m)

end Rom

namespace Compile
namespace PrivFrame
open Rom Prob ZKCP
open Compile.GlueB (GCall SCall GIn GAdm asW realW simOf forget)

/-- **The frame.** Wp: the reduction, w₀ its first state. Gr i, gr i: the game's real side at the
index i and its first state. Gs, gs: the simulated side. Adm i α E t n: the game admits the
adversary E, at the index i and the outer adversary's counts t, n. -/
def Spec.frame : Prop :=
  ∀ (S : OSpec) (I X Wn PP IVK ISK Pf : Type) [Inhabited IVK] [Inhabited Pf] (Out' In' : Type)
      (R : Gen.RelPair I X Wn PP) (A : Gen.Arg S I X Wn IVK ISK Pf) (B : ℕ)
      (Wp : Wrap S (SCall X) (GIn IVK Pf) Out' In') (w₀ : Wp.τ)
      (Gr : I → World S Out' In') (gr : ∀ i, (Gr i).σ) (Gs : World S Out' In') (gs : Gs.σ)
      (Adm : I → (α : Type) → Adv S Out' In' α → ℕ → ℕ → Prop) (h z : ℕ → ℕ → ℝ≥0∞),
    (∀ (i : I) (α : Type) (D : Adv S (GCall X Wn) (GIn IVK Pf) α) (t n : ℕ),
      D.TotalBound t (n + 1) → GAdm (fun b => Gen.ValidBatch R B i b.pairs) D false n →
      tv ((interact (realW A i) D (none, Table.empty _)).map Prod.fst)
        ((interact (asW Wn (Wp.world (Gr i))) D (w₀, gr i)).map Prod.fst) ≤ h t n) →
    (∀ (i : I) (α : Type) (D : Adv S (GCall X Wn) (GIn IVK Pf) α) (t n : ℕ),
      D.TotalBound t (n + 1) → GAdm (fun b => Gen.ValidBatch R B i b.pairs) D false n →
      Adm i α ((Wp.pre forget).adv D w₀) t n) →
    (∀ (i : I) (α : Type) (E : Adv S Out' In' α) (t n : ℕ), Adm i α E t n →
      tv ((interact (Gr i) E (gr i)).map Prod.fst) ((interact Gs E gs).map Prod.fst) ≤ z t n) →
    (Wp.world Gs).Consistent →
    Gen.HasIndexPrivacyWith R A B (simOf PP (Wp.world Gs) (w₀, gs)) fun t n => h t n + z t n

end PrivFrame
end Compile
