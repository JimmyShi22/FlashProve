-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/LinkShift.lean: under premises on sizes and on the honest run, the link
prover's algorithm and the simulator's algorithm disclose the same, up to a shift of the coins
that can be undone.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Fix parameters P and S, the number t of positions of the first stage (97 at
the full-size parameters), data X and verifier challenges D, and assume the public premises on
sizes (Sizes, Johnson/LinkSim/AtText/SpecShift.lean).
  linkShiftIn   proves Spec.linkShiftIn (Johnson/LinkSim/AtText/SpecShiftIn.lean), the form used
      in the proof of homeExact. InPlaces C says that C is 0 outside the places that a finite
      type of coins holds (Johnson/LinkSim/AtText/Places.lean). Assume also the premise on the
      honest run: for every C with InPlaces C, the element sampled in the base case's first round
      is 0 (LamZero) or the claim left at the base case is true (ClaimTrue). Then there are two
      maps s and s' on coins such that, for every C with InPlaces C: InPlaces (s C); linkAll at
      (X, C) and simAll at (X, C + s C) disclose the same rounds and groups (shownOf,
      SpecShift.lean); and s' (C + s C) = s C, so the shift can be recovered from the shifted
      coins.
  linkShift     proves Spec.linkShift (SpecShift.lean), the plain form: the same at all coins, with
      ClaimTrue asked at all coins, and with nothing said of the places.
  frontShift    proves Spec.frontShift (Johnson/LinkSim/AtText/SpecStage.lean). With the shifted
      coins C' = C + shC, the run at the data 0 has the same five front rounds (lFront,
      Johnson/Prover/Link/LinkAll.lean) and the same verifier state after the batching (lT,
      same file) as the honest run. AtStage holds in front of the first stage, with the
      difference d0.
  frontWalk     proves Spec.frontWalk (SpecStage.lean): the shift shC computed along the run at the
      data 0 and coins C' equals the one computed along the honest run.
In both forms s is shC computed along the honest run, and s' is shC computed along the run at the
data 0.

How it fits. linkShiftIn rests on frontShift and frontWalk here, on bodyShiftOr and walkSame
(Johnson/LinkSim/AtText/Induct.lean), and on shiftInPlaces (PlacesProof.lean). In
Johnson/LinkSim/AtHome/Home.lean, homeExact calls home_upTo at linkShiftIn, and linkFieldsHome calls
roadCloses at linkShiftIn (both in Johnson/LinkSim/AtHome/RoadCloses.lean). Under Johnson/LinkSim/
no file uses linkShift.

The other names.
  link_core      at one value of the coins C, under Sizes and the premise at C, linkAll at C and
                 simAll at C + shC disclose the same rounds and groups.
  shC_eq         the shift shC, written out when the plan's list of stages is first :: rest.
  shC_fr, shC_new, shC_W   the stages' part of shC is shB's.
  atFront_of     under Sizes, the coins C and C + shC satisfy the premises of the front's lemmas
                 (AtFront, Johnson/LinkSim/AtText/FrontStep.lean).
  linkAll_rs_at, linkAll_gs_at, simAll_rs, simAll_gs'   the two algorithms' rounds and groups,
                 written out.

Limits. Those of Spec.linkShift and Spec.linkShiftIn stand once, in the heads of SpecShift.lean
and SpecShiftIn.lean (among them: the coins are functions on all natural numbers, and the claim
left at the base case is a premise).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Induct
import Johnson.LinkSim.AtText.FrontStep

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open Johnson.Prover.Link

variable {P : P15} {S : Sz} {t : ℕ} {D : ℕ → Fmt.Drawn} {first : Fmt.M1.Stage}
  {rest : List Fmt.M1.Stage}

theorem shC_eq (hst : (p12Of P).nums.stages = first :: rest) (Xd Xr : LIn S) (C : LCoins) :
    shC P S t Xd Xr C D =
      { pad := shPad S t Xd D
        tN := shTN P S t Xd D
        ψN := shPsi P S t Xd Xr C D
        body :=
          { W := fun σ i => if i = 0 then shW0 P S t Xd Xr C D σ
              else (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
                (lT P S t Xr C D) (lPS P S Xr C D) (lCol P S Xr C D)
                (d0 P S t Xd Xr C D)).W σ i
            new := (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
              (lT P S t Xr C D) (lPS P S Xr C D) (lCol P S Xr C D) (d0 P S t Xd Xr C D)).new
            fr := (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
              (lT P S t Xr C D) (lPS P S Xr C D) (lCol P S Xr C D)
              (d0 P S t Xd Xr C D)).fr } } := by
  unfold shC
  rw [hst]

theorem shC_fr (hst : (p12Of P).nums.stages = first :: rest) (Xd Xr : LIn S) (C : LCoins) :
    (shC P S t Xd Xr C D).body.fr =
      (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t Xr C D)
        (lPS P S Xr C D) (lCol P S Xr C D) (d0 P S t Xd Xr C D)).fr := by
  rw [shC_eq hst]

theorem shC_new (hst : (p12Of P).nums.stages = first :: rest) (Xd Xr : LIn S) (C : LCoins) :
    (shC P S t Xd Xr C D).body.new =
      (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t Xr C D)
        (lPS P S Xr C D) (lCol P S Xr C D) (d0 P S t Xd Xr C D)).new := by
  rw [shC_eq hst]

theorem shC_W (hst : (p12Of P).nums.stages = first :: rest) (Xd Xr : LIn S) (C : LCoins) (σ : Sg)
    {i : ℕ} (hi : 0 < i) :
    (shC P S t Xd Xr C D).body.W σ i =
      (shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t Xr C D)
        (lPS P S Xr C D) (lCol P S Xr C D) (d0 P S t Xd Xr C D)).W σ i := by
  rw [shC_eq hst]
  exact if_neg (by omega : ¬ i = 0)

theorem atFront_of (hS : Sizes P S t D) (hst : (p12Of P).nums.stages = first :: rest)
    (hF : FitsBody D rest first 6) (X : LIn S) (C : LCoins) :
    AtFront P S t X C (addC C (shC P S t X X C D)) D := by
  have hq := q0_le hS hst hF
  rw [shC_eq hst]
  exact ⟨fun _ => rfl, fun _ _ => rfl, rfl, rfl, padRoom_of S hS.pad, hq.1, hq.2⟩

/-- Proves Spec.frontShift: with the shifted coins, the run at the data 0 has the honest run's
front rounds and verifier state, and AtStage holds before the first stage. -/
theorem frontShift : Spec.frontShift := by
  intro P S t X C D hS first rest hst
  obtain ⟨f', r', hst', hF⟩ := hS.body
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hst'.symm.trans hst)
  have hA := atFront_of hS hst hF X C
  have hne := rest_ne hS hst hF
  refine ⟨lFront_same hA, lT_same hA, lPS_add hA, fun x hx => lCol_same hA ?_, fun _ => ?_,
    fun h => absurd h hne, fun i _ => ?_, fun i _ => ?_, fun σ i hi => ?_⟩
  · have e : openedAt D r' f' 6 = q0 P D := by
      unfold openedAt q0
      rw [sg0_first hst]
      cases r' with
      | nil => exact absurd rfl hne
      | cons _ _ => rfl
    rw [← e]
    exact hx
  · have e : μOf (sgOf f') (d0 P S t X X C D) = μOf (sgOf f') (dTab0 S t X D) := by
      funext x
      cases x <;> rfl
    rw [e, ← sg0_first hst, hA.W]
    congr 1
    unfold shW0
    rw [if_pos rfl]
  · rw [← shC_fr hst X X C]
    rfl
  · rw [← shC_new hst X X C]
    rfl
  · rw [← shC_W hst X X C σ hi]
    rfl

/-- Proves Spec.frontWalk: the shift shC computed along the run at the data 0 equals the one
computed along the honest run. -/
theorem frontWalk : Spec.frontWalk := by
  intro P S t X C D hS
  obtain ⟨first, rest, hst, hF⟩ := hS.body
  obtain ⟨_, hT, hA⟩ := frontShift P S t X C D hS first rest hst
  have hW := walkSame (p12Of P) D rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D) C.body
    (addC C (shC P S t X X C D)).body _ _ _ _ _ hF hA
  generalize addC C (shC P S t X X C D) = C' at hT hW ⊢
  have e0 : ∀ σ, shW0 P S t X (zeroIn X) C' D σ = shW0 P S t X X C D σ := by
    intro σ
    unfold shW0
    rw [← hT]
  have e1 : dPhi P S t X (zeroIn X) C' D = dPhi P S t X X C D := by
    funext i
    unfold dPhi
    rw [e0]
  have e2 : shPsi P S t X (zeroIn X) C' D = shPsi P S t X X C D := by
    unfold shPsi
    rw [e1]
  have e3 : d0 P S t X (zeroIn X) C' D = d0 P S t X X C D := by
    unfold d0
    rw [e1, e2]
  rw [shC_eq hst X (zeroIn X) C', shC_eq hst X X C, e2, e3, ← hT, hW]
  simp only [e0]

theorem linkAll_rs_at (hst : (p12Of P).nums.stages = first :: rest) (X : LIn S) (C : LCoins) :
    (linkAll P S t X C D).rs = lFront S t X C D ++ [(⟨[], D 5⟩ : Fmt.RoundView)] ++
      (bodyAll (p12Of P) C.body rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D)
        (lPS P S X C D) (lCol P S X C D) D).rs := by
  unfold linkAll
  rw [hst]

theorem linkAll_gs_at (hst : (p12Of P).nums.stages = first :: rest) (X : LIn S) (C : LCoins) :
    (linkAll P S t X C D).gs = lStored P S X D ++
      (bodyAll (p12Of P) C.body rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D)
        (lPS P S X C D) (lCol P S X C D) D).gs := by
  unfold linkAll
  rw [hst]

theorem simAll_gs' (X : LIn S) (C : LCoins) :
    (simAll P S t X C D).gs = (linkAll P S t (zeroIn X) C D).gs := by
  unfold simAll
  split <;> rfl

theorem simAll_rs (hst : (p12Of P).nums.stages = first :: rest) (X : LIn S) (C : LCoins) :
    (simAll P S t X C D).rs = (linkAll P S t (zeroIn X) C D).rs.set
      (bodyEnd (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
        (lT P S t (zeroIn X) C D) (lPS P S (zeroIn X) C D) (lCol P S (zeroIn X) C D)).o
      ⟨[.e (tauStar (p12Of P) (bodyEnd (p12Of P) C.body D rest 0 first
          ((laidOf (p12Of P)).drop 1) 6 (lT P S t (zeroIn X) C D) (lPS P S (zeroIn X) C D)
          (lCol P S (zeroIn X) C D)) D)],
        D (bodyEnd (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
          (lT P S t (zeroIn X) C D) (lPS P S (zeroIn X) C D) (lCol P S (zeroIn X) C D)).o⟩ := by
  have hE : linkEnd P S t (zeroIn X) C D = some (bodyEnd (p12Of P) C.body D rest 0 first
      ((laidOf (p12Of P)).drop 1) 6 (lT P S t (zeroIn X) C D) (lPS P S (zeroIn X) C D)
      (lCol P S (zeroIn X) C D)) := by
    unfold linkEnd
    rw [hst]
  unfold simAll
  rw [hE]

/-- Under Sizes and the premise on the honest run at C: linkAll at C and simAll at C + shC disclose
the same rounds and groups (shownOf). -/
theorem link_core {X : LIn S} (hS : Sizes P S t D) (C : LCoins)
    (hcl : ∀ e, linkEnd P S t X C D = some e → LamZero D e ∨ ClaimTrue (p12Of P) e) :
    shownOf (linkAll P S t X C D) = shownOf (simAll P S t X (addC C (shC P S t X X C D)) D) := by
  obtain ⟨first, rest, hst, hF⟩ := hS.body
  obtain ⟨hFr, hT, hA⟩ := frontShift P S t X C D hS first rest hst
  have hE : linkEnd P S t X C D = some (bodyEnd (p12Of P) C.body D rest 0 first
      ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D) (lPS P S X C D) (lCol P S X C D)) := by
    unfold linkEnd
    rw [hst]
  obtain ⟨hg, hr⟩ := bodyShiftOr (p12Of P) D rest 0 first ((laidOf (p12Of P)).drop 1) 6
    (lT P S t X C D) C.body (addC C (shC P S t X X C D)).body _ _ _ _ _ hF hA (hcl _ hE)
  have hge := bodyEnd_o (p12Of P) (addC C (shC P S t X X C D)).body D rest 0 first
    ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D)
    (lPS P S (zeroIn X) (addC C (shC P S t X X C D)) D)
    (lCol P S (zeroIn X) (addC C (shC P S t X X C D)) D)
  generalize addC C (shC P S t X X C D) = C' at hFr hT hg hr hge ⊢
  have hlen : (lFront S t X C D ++ [(⟨[], D 5⟩ : Fmt.RoundView)]).length = 6 := rfl
  refine Prod.ext ?_ ?_
  · show (linkAll P S t X C D).rs = (simAll P S t X C' D).rs
    rw [simAll_rs hst X C', linkAll_rs_at hst X C, linkAll_rs_at hst (zeroIn X) C', ← hFr, ← hT,
      List.set_append_right _ _ (by rw [hlen]; exact hge), hlen, hr]
  · show (linkAll P S t X C D).gs = (simAll P S t X C' D).gs
    rw [simAll_gs', linkAll_gs_at hst X C, linkAll_gs_at hst (zeroIn X) C', ← hT, hg]
    rfl

/-- Proves Spec.linkShiftIn, the form used in the proof of homeExact. -/
theorem linkShiftIn : Spec.linkShiftIn := fun P S t X D hS hcl =>
  ⟨fun C => shC P S t X X C D, fun C' => shC P S t X (zeroIn X) C' D, fun C hC =>
    ⟨shiftInPlaces P S t X X C D hS, link_core hS C (hcl C hC), frontWalk P S t X C D hS⟩⟩

/-- Proves Spec.linkShift, the plain form. -/
theorem linkShift : Spec.linkShift := fun P S t X D hS hcl =>
  ⟨fun C => shC P S t X X C D, fun C' => shC P S t X (zeroIn X) C' D, fun C =>
    ⟨link_core hS C fun e he => Or.inr (hcl C e he), frontWalk P S t X C D hS⟩⟩

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.frontShift
#print axioms OnBytes.LinkSim.AtText.frontWalk
#print axioms OnBytes.LinkSim.AtText.linkShiftIn
#print axioms OnBytes.LinkSim.AtText.linkShift
