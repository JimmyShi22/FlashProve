-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/YesOfWhole.lean: THE RUN ON SHAPES RETURNS AT ANY Z UNDER THE HEAD, FROM ONE FACT AT THE STORED FILES: that the
steps on shapes run from the start through all 358 members there (RunsAll 0 358 startShA c, at some end c). A joining:
yes_of_pieces_in_scope at one piece; the run's value by the premise's own text.

  yes_of_whole   RunsAll 0 358 startShA c ⊢ the table's run on shapes says yes at 358, at any Z under the head
  run_of_whole   RunsAll 0 358 startShA c ⊢ at a record of the stored files the run to 358 returns c

Limits. THE WHOLE RUN AT THE STORED FILES (hW) IS A PREMISE: closed lines of the kernel, in a library of their own. On shapes alone:
no member's acceptance, no value. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.YesAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- The whole run as one piece. -/
theorem one_piece {c : ShA} (hW : RunsAll 0 358 startShA c) :
    ∀ k, k < 1 → RunsAll (ProofFile.Honest.border (fun _ => 358) k) ((fun _ : Nat => 358) k)
      ((fun k : Nat => if k = 0 then startShA else c) k)
      ((fun k : Nat => if k = 0 then startShA else c) (k + 1)) := by
  intro k hk
  obtain rfl : k = 0 := by omega
  exact hW

/-- **hyes AT ANY Z UNDER THE HEAD, FROM THE WHOLE RUN AT THE STORED FILES.** -/
theorem yes_of_whole (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {c : ShA}
    (hW : RunsAll 0 358 startShA c) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true :=
  yes_of_pieces_in_scope h hB (fun _ => 358) (fun k => if k = 0 then startShA else c) 1
    (one_piece hW) rfl rfl

/-- The run over the first n members is the run of n members from 0 on. -/
theorem run_is_from {S' : Type} (Y : ProofFile.Honest.Shape S') (n : Nat) (a : Y.Sh) :
    Y.run n a = Y.runFrom 0 n a := by
  have k := ProofFile.Honest.run_add Y 0 n a
  rw [Nat.zero_add] at k
  exact k

/-- **The run's value at the end, at a record of the stored files.** -/
theorem run_of_whole {c : ShA} (hW : RunsAll 0 358 startShA c) (X₀ : Verify.Public)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀) :
    (shapeL (LWn X₀)).run 358 startShA = .ok c :=
  (run_is_from (shapeL (LWn X₀)) 358 startShA).trans (hW X₀ hX)

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.yes_of_whole
#print axioms Johnson.AtFull.Shape.Scope.run_of_whole
