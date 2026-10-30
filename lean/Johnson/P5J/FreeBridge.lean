-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FreeBridge.lean: THE SHARED TABLE's OPEN LETTERS AT THE VALUE (`AtMg.shOpen`,
FreeShared.lean) ARE, UNDER ONE EQUATION ON THE CODES, THE SAME LETTERS IN ANOTHER WRITING:
the first table's meaning as the constant `mgAt` (here: the tower's spelling h.mq), and the first
table's reader of samples carried over the codes' equation (here: the same text at the other codes).
Why: other files' closed theorems on the shared chain stand at the second writing; the tower's fields
at the first. The two are not one term.
  `smpNamed_cast`  the reader of samples, carried over an equation of codes, is the reader at the
                   other codes.
  `shFirst_is`     the five letters in the second writing.
  **`shOpen_is`**  `Sh.openAt` at the two writings: ONE VALUE.
hcs: At.cs Zp = h.shPlan.Q.codes: `Sh.hcs_in_scope` | `Sh.hcs_of_made`, under their
premises: a premise here.
Limits. Equations between letters: no law. No soundness follows. Nothing on hiding. It holds no
coding theory.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.FreeShared

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open Desc.K14.Law.Fence (numbersSh)
open Desc.K14.Law (ShPlan ShOpen Sh.planAt Sh.openAt Sh.Open₁ Sh.nums Sh.mg Sh.pm Sh.own Sh.ex)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The reader of samples, carried over an equation of codes. -/
theorem smpNamed_cast {P : Type} {c c' : OnBytes.Codes} (e : c = c') (seats : List (ℕ × ℕ)) :
    (e ▸ (smpNamed (P := P) c seats) : (a : P × VerifiableInference.Desc.First.S) → (s : Sending) →
      (i : Fin s.l.length) → Option ((Johnson.Pack.sigOf c' s.l).om i).Smp) =
      smpNamed (P := P) c' seats := by
  subst e
  rfl

variable (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
  (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))

/-- **The first table's five letters, in the second writing.** -/
theorem shFirst_is (hcs : At.cs Zp = h.shPlan.Q.codes) :
    h.shFirst 𝔇₀ =
      { N₁ := At.N Zp cF, links := At.links, Mg₁ := mgAt h 𝔇₀, smp₁ := hcs ▸ At.smp Zp,
        ms₁ := At.ms Zp Z.lay } := by
  have e1 : h.mq 𝔇₀ = mgAt h 𝔇₀ := (mgAt_is_mq h 𝔇₀).symm
  have e2 : smpNamed (P := ProofFile.InstPub) h.shPlan.Q.codes (At.seats Zp) = hcs ▸ At.smp Zp :=
    (smpNamed_cast hcs (At.seats Zp)).symm
  unfold AtMg.shFirst
  rw [e1, e2]
  rfl

/-- **The shared table's open letters at the value are `Sh.openAt` at the second writing.** -/
theorem shOpen_is (hcs : At.cs Zp = h.shPlan.Q.codes) :
    h.shOpen 𝔇₀ =
      Sh.openAt o Zp Np (Desc.K14.Law.secondAt Zp Np) cF h.plan.shape (ppAtFiles Z.pol Z.KL)
        (At.EAt Z)
        { N₁ := At.N Zp cF, links := At.links, Mg₁ := mgAt h 𝔇₀, smp₁ := hcs ▸ At.smp Zp,
          ms₁ := At.ms Zp Z.lay } :=
  congrArg (Sh.openAt o Zp Np (Desc.K14.Law.secondAt Zp Np) cF h.plan.shape (ppAtFiles Z.pol Z.KL)
    (At.EAt Z)) (shFirst_is h 𝔇₀ hcs)

end P5J

#print axioms P5J.smpNamed_cast
#print axioms P5J.shFirst_is
#print axioms P5J.shOpen_is
