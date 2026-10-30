-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StartInScope.lean: IN SCOPE, OF THE FOUR CLAUSES OF `StartHeld` (E2E/StartAtFiles.lean) ONE IS
LEFT: the clause on the request's item. For every public part that `P5J.LaidAt` ties to the public
files: its numbers of tokens and of the vocabulary's entries are the instance's type's, and the
segments' data are made. Statements and proofs; nothing is evaluated.

What is shown.
  **`numbers_of_laid`**: in scope: `Zp.p.X.T = ppref.T` and `Zp.p.X.P.h.V = ppref.V`. By the
    library's `reads_of_scope`, `scan_of_scope` (in scope the scan of the parameter file is a closed
    form), `public_parts`, `polLayout_T`, `publicOfO_older`.
  **`startHeld_of_laid`**: in scope: the clause on the item gives `StartHeld`.
  **`okStart_of_item`**: so, in scope: the clause on the item gives that the proof file's first test
    accepts what is written for every instance of the type, at every OOD sample.
  **`okStart_of_one`**: ALL OR NONE, in scope: an accept at ONE instance of the type gives an accept
    at every one.

Limits.
- The clause on the item stays a premise: it is shown at no public files here.
- All limits of E2E/StartAtFiles.lean stand.


-/
import E2E.StartAtFiles
import Johnson.P5J.LaidOpens
import Johnson.IMR.MemberOfGate
import Johnson.Goal.Meaning.ScopeScanTies
import Johnson.Road.HeadPub
import OnBytes.Tie.Pv.Lookup.Ends.FoMadePub
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false

namespace AtPublicFiles.Start
open OnBytes OnBytes.Model Inst.Model
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord XF)
open OnBytes.Flat (RecFull)
open VerifiableInference.Desc (Chain)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl}

/-- **In scope the public part's two numbers are the instance's type's.** -/
theorem numbers_of_laid (scope : VerifierAndGoals.InScope Z = true)
    (Ld : LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    Zp.p.X.T = ppref.T ∧ Zp.p.X.P.h.V = ppref.V := by
  obtain ⟨pp, hR⟩ := IM.reads_of_scope scope
  have h : Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact Ld.publicO
  obtain ⟨P, y, hpl, eP, ey, -⟩ := OnBytes.Road.Hd.public_parts h
  have hs := OnBytes.Road.Hd.scan_of_scope scope hR h
  constructor
  · show Zp.p.X.y.T = 1024
    rw [ey, Fo.Pub.polLayout_T _ _ _ hpl, ← eP, hs]
    rfl
  · rw [hs]
    rfl

/-- **In scope the clause on the item is all that is left.** -/
theorem startHeld_of_laid (scope : VerifierAndGoals.InScope Z = true)
    (Ld : LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (item : ∀ req : ByteArray, req.size = 4 * (Zp.p.X.T + 2) →
      ∃ it, Fmt.requestItem secondHashFunction Zp.pol Zp.KL req = some it ∧
        Verify.statementHeld Zp.p.X it = .ok ()) :
    StartHeld secondHashFunction ProofFile.pureRoad.links Zp :=
  ⟨(numbers_of_laid scope Ld).1, (numbers_of_laid scope Ld).2, item, links_of_pub Ld.pub⟩

/-- So, in scope, under `LaidAt` and where the clause on the item holds: the first test accepts what
is written for every instance of the type, at every OOD sample. -/
theorem okStart_of_item (scope : VerifierAndGoals.InScope Z = true)
    (Ld : LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (item : ∀ req : ByteArray, req.size = 4 * (Zp.p.X.T + 2) →
      ∃ it, Fmt.requestItem secondHashFunction Zp.pol Zp.KL req = some it ∧
        Verify.statementHeld Zp.p.X it = .ok ())
    (z : XF × RecFull) : (F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true :=
  okStart_of_public Np cF (startHeld_of_laid scope Ld item) z

/-- **All or none, in scope.** -/
theorem okStart_of_one (scope : VerifierAndGoals.InScope Z = true)
    (Ld : LaidAt secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {z₀ : XF × RecFull}
    (h₀ : (F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z₀) = true) (z : XF × RecFull) :
    (F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true :=
  okStart_all_of_one Np cF Ld.pub (numbers_of_laid scope Ld).1 (numbers_of_laid scope Ld).2 h₀ z

end AtPublicFiles.Start

#print axioms AtPublicFiles.Start.numbers_of_laid
#print axioms AtPublicFiles.Start.startHeld_of_laid
#print axioms AtPublicFiles.Start.okStart_of_item
#print axioms AtPublicFiles.Start.okStart_of_one
