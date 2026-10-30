-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/HinAtConst.lean: AT THE CLOSED CONSTANT: THE PREMISE hin OF
hitems' THREE PAYERS, AT EVERY ENTRY OF THE SORT's ORDER OF CLAIMS BUT "K8.equations", FROM THE
CONDITION IN FRONT OF THE BATCHING ALONE. One statement and its proof: a call of
LPFE1R/HinOfPromise.lean's two.

  hin_at             (h : AtMgA secondHashFunction …) (hm : m < 25) (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase)
                     fullLinks At.ps (fun s => (z, s)) Rz (batchAt fullLinks At.ps m) a) (he : e ∈
                     orderOf (subAt m)) (h8 : (e.2 == "K8.equations") = false) : K9.formsIn (h.𝔇.Rd
                     m) (h.𝔇.N.group m) e.1 e.2 a.1 = true. General in z and Rz.

Limits. AT "K8.equations" NOTHING IS SAID: there the promise holds the weaker test formsInA. The
head is a premise. The full size alone. No soundness statement.

-/
import Johnson.LPFE1R.HinOfPromise
import Johnson.Desc.Sound.MgAt.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item orderOf runsOf)
open IM (subAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **hin at the closed constant, at every entry of the order but "K8.equations".** -/
theorem hin_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : ℕ} (hm : m < 25) {F : Frame}
    (z : ProofFile.InstPub) (Rz : ℕ → S × F.E.Str → Prop) (a : S × F.E.Str)
    (ho : onTR h.𝔇.N (mgAll h.𝔇 mgBase) P5J.fullLinks P5J.At.ps (fun s : S => (z, s)) Rz
      (batchAt P5J.fullLinks P5J.At.ps m) a)
    {e : ℕ × String} (he : e ∈ orderOf (subAt m)) (h8 : (e.2 == "K8.equations") = false) :
    K9.formsIn (h.𝔇.Rd m) (h.𝔇.N.group m) e.1 e.2 a.1 = true := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 named_full m (List.mem_range.2 hm)) e he
  rw [h8, Bool.false_or] at h1
  obtain ⟨i, hi, h2⟩ := List.any_eq_true.1 h1
  cases i with
  | forms m' kk r =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h2
    obtain ⟨rfl, h3⟩ := h2
    have er : e ∈ h.𝔇.runs m' kk r :=
      mem_runsAt P5J.fullLinks m' (subAt m') (LPFK9.fullLinks_sub m' hm) kk r e h3
    exact formsIn_of_promise h.𝔇 mgBase P5J.fullLinks P5J.At.ps (fun s : S => (z, s))
      (batchAt P5J.fullLinks P5J.At.ps m') a ho.1.1
      (Classical.not_not.1 ho.1.2) hi er h8
  | _ => exact absurd h2 (by simp)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hin_at
