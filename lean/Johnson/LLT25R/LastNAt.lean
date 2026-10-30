-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastNAt.lean: THE PREMISE hN OF `LLT25.own3_at_top` (Johnson/LLT25R/LastTop.lean; the
same text in `own3_at_top_unpulled`, Johnson/LLT25R/LastUnpulled.lean) AT THE ONE X AND THE SHARED
TABLE's
OWN NUMBERING: X := `Sh.X A 12` · oNo := `Sh.oNo A` · ms₂ := `Sh.ms A`, A any plan of the shared
table's constant. A JOIN OF FILES OF Johnson/LLT25R/ AND OF Johnson/Desc/K14/Law/.
  `omegaNo_at`: **whoever of mine sits at the seat t bears, by `Sh.oNo A`, the number that a state
    inside `Sh.X A 12` notes as o_omega's**, FROM FOUR PREMISES: hT (`Sh.Tests A`: "all the named
    tests say true") · hNs (the letter Ns has Omega's tenant where the constant has it) · hw · hi
    (no elder seat is t). By `Sh.oNo_omega_of` and `Sh.omega_number_of`
    (Johnson/Desc/K14/Law/SharedConstOmegaNo.lean) and `mem_mineOf`.
  `tenant_sh`: hNs at Ns := `numbersSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) a b`: by unfolding.
  `hN_of_plan`: **hN, letter for letter as own3_at_top has it**, at that Ns, from hT and that law's
    OWN premise hP (its field seatsApart pays hw and hi, since `vAt Z N₁` has N₁'s two seats).
Limits. The seat's coordinates (D.t₁ + 1, 0) are tied to Omega's tenant by nothing here and need not
be: if nobody of mine sits there the sentence says nothing of x (hP's field omegaSeat says that one
does); and it says nothing of a d outside `Sh.X A 12`: no state is shown inside it here. hT is paid
by nobody here. hP IS OWED AT ms₂ := `Sh.ms A` AND THIS Ns: its evaluations at other letters do not
count for these. (Where this and lean/THEOREM.md
differ, the page holds.) Nothing on soundness.
-/
import Johnson.LLT25R.LastAt
import Johnson.Desc.K14.Law.SharedConstOmegaNo

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (S ModelPart Numbers)
open ProofFile (SecondHashFunctionArgument LinksBy Cl)
open ToldDesc (p14At)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open _root_.Desc.K14.Law.Fence

variable {Xi : Type} (A : ShPlan Xi)

/-- **Whoever of mine sits at t bears o_omega's number.** -/
theorem omegaNo_at (hT : Sh.Tests A) (ms₁ : List Mem) (N₁ : Numbers) (Ns : NumbersS) (t : ℕ × ℕ)
    (hNs : Ns.tenant .oOmega = tenantSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) .oOmega)
    (hw : N₁.w ≠ t) (hi : N₁.index ≠ t) :
    ∀ x ∈ mineOf ms₁ (Sh.ms A) N₁ Ns, seatOf x = t → ∀ d, Sh.X A 12 d = true →
      Sh.oNo A x = d.loc.oOmega := by
  intro x hx hs d hd
  rcases mem_mineOf.1 hx with ⟨-, h | h⟩ | ⟨hm, h⟩
  · exact absurd (h.symm.trans hs) hw
  · exact absurd (h.symm.trans hs) hi
  · exact (Sh.oNo_omega_of A hT x hm (h.trans hNs)).trans (Sh.omega_number_of A hT d hd).symm

/-- **The constant's own numbers have Omega's tenant where the constant has it.** -/
theorem tenant_sh (a b : ℕ × ℕ) :
    (numbersSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) a b).tenant .oOmega =
      tenantSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) .oOmega := rfl

/-- **hN as own3_at_top has it, from the named tests and that law's own premise hP.** -/
theorem hN_of_plan (hT : Sh.Tests A) (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain S Cl) (D : WholeD) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ) (dB : RDT)
    (dt : List RDT) (ms₁ : List Mem) (N₁ : Numbers) (a b : ℕ × ℕ) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (r : Fmt.M1.Stage → ℕ) (n₁ ft : ℕ)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ (Sh.ms A) N₁
      (numbersSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) a b) links ps r n₁ ft 1 (vAt Z N₁) Ld) :
    ∀ x ∈ (mineOf ms₁ (Sh.ms A) N₁ (numbersSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) a b)),
      seatOf x = (D.t₁ + 1, 0) → ∀ d, Sh.X A 12 d = true → Sh.oNo A x = d.loc.oOmega :=
  omegaNo_at A hT ms₁ N₁ _ _ (tenant_sh A a b) hP.seatsApart.2.2 hP.seatsApart.2.1

end LLT25

#print axioms LLT25.omegaNo_at
#print axioms LLT25.tenant_sh
#print axioms LLT25.hN_of_plan
