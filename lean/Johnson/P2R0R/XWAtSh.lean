-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2R0R/XWAtSh.lean: THE SHARED TABLE's CONSTANT's Sh.xW
(Johnson/Desc/K14/Law/SharedConst.lean) IS P2R0R/XWAtPlan.lean's seatedFirst AT THE CONSTANT's
LETTERS (rfl); so that file's two equations hold of it. STATED AND PROVED: each proof is one call.
Limits: that file's. Nothing on soundness.

-/
import Johnson.P2R0R.XWAtPlan
import Johnson.Desc.K14.Law.SharedConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace P2R0
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.Sound (Mem)
open VerifiableInference.Desc.Shared (NumbersS)
open VerifiableInference.Desc.First (S ModelPart)
open ProofFile (SecondHashFunctionArgument LinksBy Cl)
open Desc.K14.Law (ShPlan ShOpen)
open ToldDesc (p14At)
open LLT25

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-- **Sh.xW is the first member of the first chain's list at W's seat.** -/
theorem xW_is : ∃ d, Desc.K14.Law.Sh.xW A O = seatedFirst O.ms₁ O.N₁.w d := ⟨_, rfl⟩

variable {o : SecondHashFunctionArgument} {mk : LinksBy} {Z : ProofFile.Pub} {N : H2U.Places4} {c : Chain S Cl}
  {D : WholeD} {Xi' : Type} {G : FileDescription Xi'} {arr : ℕ → ℕ → ℕ} {dB : RDT} {dt : List RDT}
  {ms₂ : List Mem} {Ns : NumbersS} {links : List ModelPart}
  {ps : List VerifiableInference.Desc.Place} {r : Fmt.M1.Stage → ℕ} {n₁ ft nΩ : ℕ}
  {Ld : VerifiableInference.Desc.K12.Door.Laid}

/-- **hseat's form, and the shape, at Sh.xW.** -/
theorem xW_at_plan
    (hP : PlanOk₃ o mk Z N c D G arr dB dt O.ms₁ ms₂ O.N₁ Ns links ps r n₁ ft nΩ (vAt Z O.N₁) Ld) :
    (Desc.K14.Law.Sh.xW A O).1.seat (Desc.K14.Law.Sh.xW A O).2 = O.N₁.w ∧
      ((Desc.K14.Law.Sh.xW A O).1.l.get (Desc.K14.Law.Sh.xW A O).2).1 = (p14At Z).S.w := by
  obtain ⟨d, e⟩ := xW_is A O
  rw [e]
  exact seatedFirst_at_plan hP d

/-- **hsh's form, at Sh.xW.** -/
theorem hsh_at_sh
    (hP : PlanOk₃ o mk Z N c D G arr dB dt O.ms₁ ms₂ O.N₁ Ns links ps r n₁ ft nΩ (vAt Z O.N₁) Ld)
    (Pw : VerifiableInference.Desc.K13.Where) (hPw : Pw.lin.w = (p14At Z).S.w) :
    Pw.lin.w = ((Desc.K14.Law.Sh.xW A O).1.l.get (Desc.K14.Law.Sh.xW A O).2).1 :=
  hPw.trans (xW_at_plan A O hP).2.symm

end P2R0

#print axioms P2R0.xW_is
#print axioms P2R0.xW_at_plan
#print axioms P2R0.hsh_at_sh
