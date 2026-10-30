-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/DueHead.lean: at the proof file's description some list of
challenges passes `Draws.due` (Honest/Frame.lean), and so does the list that the frame reads off any
typed verifier's message. Many hypotheses of the frame's rules begin "at every list ρ with ρ.due F =
true". They would be idle if no list were due. Here one is shown to exist, where the public files
are in scope and `P5J.LaidAt` holds.

  1  `due_laid`   at the kit `ckP .two`: what `drawsAt` reads off any verifier's message of the
    file's rounds is due
  2  `due_exists_laid`   so some list is due

How. `due_at_two` (Honest/Law/DueData.lean) at the file's data, with its hypothesis on the declared
rounds paid by `draws_decl` (Honest/Law/CoverDrawsAll.lean). The type of verifier's messages has an
element by the library's instance `Iop.instNonemptyRho` (Iop/Shape.lean).

Limits.
  * That the public files are in scope, and `LaidAt`, are hypotheses.
  * `Draws.due` is a test of form on a list of challenges. Nothing is said on how a list is drawn,
    on a run, or on whether a run goes through at a due list.
  * The list of `due_exists_laid` is taken by choice. Nothing computes it.
  * The full size alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverDrawsAll
import Johnson.Desc.ProofFile.Honest.Law.DueData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD chainsOf)
open _root_.Run (ckP)
open P5J (TS)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- What the frame reads off any typed verifier's message of the file's rounds is due. -/
theorem due_laid {TF TJ T3 : Type} (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) (tF : TF) (tJ : TJ) (t3 : T3)
    (ρ : Iop.Rho (chainsOf (ckP .two) D tF tJ t3).sh) :
    (drawsAt (ckP .two) D tF tJ t3 ρ).due (P5J.F0T o Zp Np cF) = true :=
  due_at_two tF tJ t3 L.data (draws_decl hZ L) ρ

/-- **Some list of challenges is due at the proof file's description.** -/
theorem due_exists_laid (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ ρ : Draws, ρ.due (P5J.F0T o Zp Np cF) = true :=
  ⟨_, due_laid hZ L () () () (Classical.arbitrary _)⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.due_laid
#print axioms ProofFile.Honest.due_exists_laid
