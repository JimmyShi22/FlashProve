-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/PlanAtOmega.lean: THE FIELD planAt OF `LLT25.PlanOk₃` (hP) AT OMEGA's MEMBER OF THE SHARED
TABLE's CONSTANT's OWN LIST `Sh.ms A`, A := `Sh.planAt Z N G`, AT r := `rWFull`.
  `xOmega A`: the member, written out: o_omega's sending's first, with the shape A.Q.S.omega and the
    radius A.rad5 0.
  `eq_xOmega`: under the named tests, whoever of `Sh.ms A` sits at Omega's tenant IS `xOmega A`.
  `rWFull_le`: `rWFull` is at most 3131972 at every stage (by its text).
  `rad_omega`: **PlanAt's CLAUSE ON THE RADIUS AT `xOmega`, AT EVERY STAGE AND EVERY cs**, from the
    equations on the public part (`Written Z x`) and the places: there A.rad5 0 = 3131972 is a
    theorem of another file (`seat_radii_terms`, Johnson/Goal/Numbers/K14RadiiTerms.lean).
  `fits_omega`: PlanAt's fifth clause at `xOmega`, from the named tests (`Sh.tests_fO10`).
  `tie_omega`: PlanAt's first clause at `xOmega`: a closed fact by the kernel at the typed shape.
  **`planAt_omega`**: `PlanAt (p14At Z).codes G' Fr rWFull st (xOmega A)` at every stage st, FROM
    `Written Z x`, the places, the named tests AND TWO THAT STAY: hF (the field seats at this member:
    clause three; clause four follows from it) · hD (clause six: no column of the frame at that tree
    is deeper: the test `noDeeperB`, Johnson/P2LawR/PlanLeftAt.lean, says true).
Limits. Omega's member alone: W's and the index masks' members are not here. `Written` costs the
door's pins. hF and hD are premises. No value is evaluated. Nothing on soundness.
-/
import Johnson.P2LawR.PlanLeftAt
import Johnson.Desc.K14.Law.SharedConstAt
import Johnson.Desc.K14.Law.SharedConstLastAt
import Johnson.Desc.K14.Law.SharedConstFull
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25.PlanB
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K12.Coin (ShapeFits)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open _root_.Desc.K14.Law _root_.Desc.K14.Law.Fence
open P2Law.PlanLeft
open ToldDesc (p14At tieB tie_iff)

variable {Xi : Type}

/-- **Omega's member of the constant's list.** -/
def xOmega (A : ShPlan Xi) : Mem :=
  ⟨sendingO A.Q.S (A.rad5 0) (A.rad5 1) (Sh.t₁ A) (Sh.layU A) (Sh.layO A), ⟨0, Nat.two_pos⟩⟩

/-- **Whoever of the constant's list sits at Omega's tenant is that member.** -/
theorem eq_xOmega (A : ShPlan Xi) (hT : Sh.Tests A) (x : Mem) (hx : x ∈ Sh.ms A)
    (hs : x.1.seat x.2 = tenantSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) .oOmega) : x = xOmega A := by
  have hx' : x ∈ msSh A.Q.S (A.rad2 0) (A.rad5 0) (A.rad5 1) (Sh.t₁ A) (Sh.layU A) (Sh.layO A) := hx
  rw [msSh_all] at hx'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
  have ap := tenants_apart A.Q.codes (Sh.sentU A) (_root_.Desc.K14.withOmega A.Q.S) (Sh.layU A)
    (Sh.layO A) (Sh.tests_hlU A hT) (Sh.tests_hlO A hT) (by rw [Sh.tests_hsU A hT]; decide)
    (by rw [Sh.tests_hsO A hT]; decide) (Sh.t₁ A)
  rcases hx' with rfl | rfl | rfl
  · exact Msg2.noConfusion (ap .oU .oOmega hs)
  · rfl
  · exact Msg2.noConfusion (ap .oSp .oOmega hs)

/-- K12's files' radii for W at the full size are at most the first stage's. -/
theorem rWFull_le (s : Fmt.M1.Stage) : H2K.Member.rWFull s ≤ 3131972 := by
  unfold H2K.Member.rWFull
  split_ifs <;> omega

variable (Z : ProofFile.Pub) (N : H2U.Places4) (G : FileDescription Xi)

/-- **The clause on the radius at Omega's member, at every stage.** -/
theorem rad_omega {x : LinSized} (hx : realSized = some (x, codesFull2)) (h : Written Z x)
    (hN : H2U.placesOfMade Z.made = .ok N) (cs : Codes) (st : Fmt.M1.Stage) :
    radB cs H2K.Member.rWFull st (xOmega (Sh.planAt Z N G)) = true := by
  rw [radB_iff]
  have e : ((xOmega (Sh.planAt Z N G)).1.l.get (xOmega (Sh.planAt Z N G)).2).2 = 3131972 :=
    (seat_radii_terms hx h hN).hrO
  rw [e]
  calc H2K.Member.rWFull _ ≤ 3131972 := rWFull_le _
    _ < (3131972 + 1) * 1 := by omega
    _ ≤ (3131972 + 1) * 2 ^ _ := Nat.mul_le_mul_left _ Nat.one_le_two_pow

/-- **The fifth clause at Omega's member.** -/
theorem fits_omega (A : ShPlan Xi) (hT : Sh.Tests A) (st : Fmt.M1.Stage) (lg : ℕ) :
    ShapeFits A.Q.codes st ((xOmega A).1.l.get (xOmega A).2).1 lg :=
  Or.inl (Sh.tests_fO10 A hT)

/-- A closed fact: K1's tie at the typed shape's Omega. -/
theorem tie_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    tieB codesFull2 x.shape.omega = true := by
  obtain ⟨x, a1, -⟩ := full_real
  have h : (realSized.any fun p => tieB p.2 p.1.shape.omega) = true := by decide +kernel
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, h⟩

/-- **The first clause at Omega's member.** -/
theorem tie_omega {x : LinSized} (hx : realSized = some (x, codesFull2)) (h : Written Z x) :
    tieB (p14At Z).codes ((xOmega (Sh.planAt Z N G)).1.l.get (xOmega (Sh.planAt Z N G)).2).1 =
      true := by
  obtain ⟨x', a1, a2⟩ := tie_real
  obtain rfl := sized_one hx a1
  have ec : (p14At Z).codes = codesFull2 := h.codes
  have es : ((xOmega (Sh.planAt Z N G)).1.l.get (xOmega (Sh.planAt Z N G)).2).1 = x.shape.omega :=
    congrArg (·.omega) h.shape
  rw [ec, es]
  exact a2

/-- **PlanAt at Omega's member, at every stage: four clauses paid, two stay.** -/
theorem planAt_omega {Xi' : Type} (G' : FileDescription Xi') {x : LinSized}
    (hx : realSized = some (x, codesFull2)) (h : Written Z x)
    (hN : H2U.placesOfMade Z.made = .ok N) (hT : Sh.Tests (Sh.planAt Z N G)) (Fr : Frame)
    (st : Fmt.M1.Stage)
    (hF : SeatFits G' (p14At Z).codes (xOmega (Sh.planAt Z N G)).1.l
      (xOmega (Sh.planAt Z N G)).1.seat)
    (hD : noDeeperB G' Fr (xOmega (Sh.planAt Z N G)) = true) :
    LLT25.PlanAt (p14At Z).codes G' Fr H2K.Member.rWFull st (xOmega (Sh.planAt Z N G)) := by
  refine (planAt_iff G' (p14At Z).codes Fr _ st _ hF).1 ?_
  unfold planAt5B
  rw [tie_omega Z N G hx h, rad_omega Z N G hx h hN,
    (toldB_iff G' _).2 (told_of_seatFits G' _ _ hF),
    (fitsAtB_iff G' (p14At Z).codes st _).2 (fun o _ => fits_omega (Sh.planAt Z N G) hT st _), hD]
  rfl

end LLT25.PlanB

#print axioms LLT25.PlanB.eq_xOmega
#print axioms LLT25.PlanB.rWFull_le
#print axioms LLT25.PlanB.rad_omega
#print axioms LLT25.PlanB.fits_omega
#print axioms LLT25.PlanB.tie_real
#print axioms LLT25.PlanB.tie_omega
#print axioms LLT25.PlanB.planAt_omega
