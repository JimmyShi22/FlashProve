-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.OmegaIsSome
import Johnson.Loose.H2K12.SitsAtDescPure
import Johnson.Desc.Laid.ProofFullScope
/-
Johnson/Loose/H2K12/FirstTieAtSeats.lean: THE TIE BETWEEN A PROXIMITY TEST's FIRST WRITTEN STAGE AND THE
PLANNER's FIRST STAGE, AT THE SHARED CHAIN's TWO TESTS (on G_u; on G_omega), IN SCOPE AND AT
LPFD.Full.proofDataAndDecisionOfPublicFiles's RETURN. Johnson/Goal/Numbers/K12FitTop.lean asks for FirstTie σ st π r,
the one new premise of its hfit9_of | hfit10_of, at σ := setAt · st := szUFull |
szOFull. THAT FILE IS NOT IMPORTED: FirstTieSays IS FirstTie's BODY, WRITTEN OUT BY
HAND, sign for sign by reading: THAT THE TWO ARE ONE IS HELD BY NO COMPILER HERE. CALLS ALONE.
FACTS ON THE LIST OF ROUNDS' NUMBERS. NO SOUNDNESS IS CLAIMED.
NOTHING ON HIDING.
  FirstTieSays σ st π r   ∀ a₀ rest, π.nums.stages = a₀ :: rest → ∃ y rest', st = y :: rest' ∧
      sgOf a₀ = stageOf y.g y.t ∧ r (sgOf a₀).st = radBy σ st (sgOf a₀)
  firstTie_of       general: π.nums.stages = st.map stageNums · r is radBy σ st at each written stage ·
      r reads of a stage what sgOf keeps: by stages_tie (Johnson/Desc/K12/Law/CondAtMade.lean)
  firstTie_U_of | firstTie_O_of   at every place whose written stages are the closed place's: by
      stages_UFull | _OFull · radBy_UFull | _OFull (Johnson/Desc/K12/Law/Sizes/); rUFull | rOFull read
      the code's number a alone: rfl
  firstTie_in_scope_U | _O   VerifierAndGoals.InScope S · pubPlain's and placesOfMade's returns · the
      description's test on the plan (at G_omega: N.O = some nO) ⇒ FirstTieSays setAt szUFull (pGu N)
      rUFull | setAt szOFull (pGomega nO) rOFull
  firstTie_laid     VerifierAndGoals.InScope S · proofDataAndDecisionOfPublicFiles … = .ok (D, r) ⇒ ∃ Z N nO c, the returns ∧ both
NO EXAMPLE: at no files is proofDataAndDecisionOfPublicFiles's return shown in Lean. IS IT EMPTY ELSE? FirstTieSays is «for all a₀
rest»: where the place has no written stage it says nothing: at the closed places the list has a head
(szUFull | szOFull are closed lists; not said by a theorem here).
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's
end.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (radBy sgOf stages_tie)
open H2K.Member (setAt szUFull szOFull rUFull rOFull piUFull piOFull)

/-- What FirstTie σ st π r says (Johnson/Goal/Numbers/K12FitTop.lean), written out. -/
def FirstTieSays (σ : OnBytes.Params.Setting) (st : List OnBytes.Params.StageSize) (π : P12)
    (r : Fmt.M1.Stage → ℕ) : Prop :=
  ∀ a₀ rest, π.nums.stages = a₀ :: rest → ∃ y rest', st = y :: rest' ∧
    sgOf a₀ = Johnson.Top.H.stageOf y.g y.t ∧ r (sgOf a₀).st = radBy σ st (sgOf a₀)

/-- General: the place's written stages are the planner's list's numbers · r is radBy at each written
stage · r reads of a stage what sgOf keeps. -/
theorem firstTie_of {σ : OnBytes.Params.Setting} {st : List OnBytes.Params.StageSize} {π : P12}
    {r : Fmt.M1.Stage → ℕ} (hs : π.nums.stages = st.map H2U.stageNums)
    (hr : ∀ a ∈ π.nums.stages, radBy σ st (sgOf a) = r a) (hn : ∀ a, r (sgOf a).st = r a) :
    FirstTieSays σ st π r := by
  intro a₀ rest ha
  have hm : a₀ ∈ π.nums.stages := by rw [ha]; exact List.mem_cons_self
  cases st with
  | nil => rw [hs] at ha; cases ha
  | cons y rest' =>
    rw [hs, List.map_cons] at ha
    obtain ⟨e, _⟩ := List.cons.inj ha
    refine ⟨y, rest', rfl, ?_, (hn a₀).trans (hr a₀ hm).symm⟩
    have t := stages_tie [y]
    rw [← e]
    exact (List.cons.inj t).1

/-- At every place whose written stages are the closed place's on G_u. -/
theorem firstTie_U_of {π : P12} (h : π.nums.stages = piUFull.nums.stages) :
    FirstTieSays setAt szUFull π rUFull :=
  firstTie_of (h.trans H2K.Sizes.stages_UFull) (fun a ha => H2K.Sizes.radBy_UFull a (h ▸ ha))
    fun _ => rfl

/-- The like on G_omega. -/
theorem firstTie_O_of {π : P12} (h : π.nums.stages = piOFull.nums.stages) :
    FirstTieSays setAt szOFull π rOFull :=
  firstTie_of (h.trans H2K.Sizes.stages_OFull) (fun a ha => H2K.Sizes.radBy_OFull a (h ▸ ha))
    fun _ => rfl

/-- In the goals' scope, at the test on G_u. -/
theorem firstTie_in_scope_U {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (mk : ProofFile.LinksBy)
    (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) (hN : H2U.placesOfMade Z.made = .ok N)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    FirstTieSays setAt szUFull (pGu N) rUFull := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ N.U (plan_at_seat_U o Z mk N c hp)
  exact firstTie_U_of ((congrArg (·.stages) hn).trans (H2K.Sizes.place_U_of_full A hN).1)

/-- In the goals' scope, at the test on G_omega. -/
theorem firstTie_in_scope_O {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (mk : ProofFile.LinksBy)
    (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO) (c : Chain First.S ProofFile.Cl)
    (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    FirstTieSays setAt szOFull (pGomega nO) rOFull := by
  have A := H2K.Sizes.atFull_of_pubPlain hS hZ
  have hn := H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO (plan_at_seat_O o Z mk N nO hO c hp)
  exact firstTie_O_of ((congrArg (·.stages) hn).trans (H2K.Sizes.place_O_of_full A hN nO hO).1)

/-- At proofDataAndDecisionOfPublicFiles's return: the letters are ten_facts_laid's. -/
theorem firstTie_laid (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true) (o : ProofFile.SecondHashFunctionArgument)
    (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N nO c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      N.O = some nO ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      FirstTieSays setAt szUFull (pGu N) rUFull ∧ FirstTieSays setAt szOFull (pGomega nO) rOFull := by
  obtain ⟨F, hF, hp, _, hs, _⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z _ N c hp hpin
  exact ⟨Z, N, nO, c, hZ, hN, hO, hF, firstTie_in_scope_U hS Z hZ _ N c hN hp,
    firstTie_in_scope_O hS Z hZ _ N nO hO c hN hp⟩

end H2K.JointK

#print axioms H2K.JointK.firstTie_of
#print axioms H2K.JointK.firstTie_U_of
#print axioms H2K.JointK.firstTie_O_of
#print axioms H2K.JointK.firstTie_in_scope_U
#print axioms H2K.JointK.firstTie_in_scope_O
#print axioms H2K.JointK.firstTie_laid
