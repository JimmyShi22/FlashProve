-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Top.Fire.Code.KeyBasesAtSix
import Johnson.Top.Fire.Code.BasesOk
import Johnson.RunOne.Law.KeyInScope
import Johnson.RunOne.Law.K12Facts15Z
import Johnson.Desc.K12.Law.Sizes.KeyClosedAtScope
import Johnson.Desc.K12.Law.BatOneMade
import Johnson.Desc.Key.KeyFillAtSizes
import Johnson.Loose.H2K12.RoundsAtKeySeats
import Johnson.Desc.Key.AsksBothTests
import Johnson.Goal.Numbers.PlanWrittenDescScope
import OnBytes.Model.VerifyDerives
import Johnson.Top.Fire.Code.KeyPublicAtSeat
import Johnson.RunOne.KeyScopeNums
import Johnson.Top.Fire.Code.RowCut
import Johnson.RunOne.Law.K12AtPlaceRow
import Johnson.Desc.K12.Coin.LawAtTile
import Johnson.Desc.K12.Coin.LawAtTileOwn
import Johnson.Desc.K12.Coin.LawAtTileThird
import Johnson.Desc.K12.Coin.GameAt
import Johnson.Desc.K12.Coin.LabelsAtKeyW
import Johnson.Desc.K12.Law.KeyTileFacts
import Johnson.Desc.K12.Law.FirstNe
import Iop.ErrCap
/-
Johnson/RunOne/Law/K12PlaceAtName.lean:
AT THE KEY FILE's THREE LATER PROXIMITY TESTS (the kind K12; the
tables' rows 2.9, 2.10, 3.2): PUBLIC FACTS ON THE MADE PLACES AND ON THE PIECES' BASES, IN SCOPE, AT
ANY DIGEST. §§ 1-5: those that need NOTHING ON THE DECLARED ROUNDS: the stages are the closed
places' · the test on the Johnson radii · the test on "BAT"'s written round · the first tree's
number · the members' «fit» at the first stage · the tree of every pin that is open lies below the
piece's base. § 6: WITH THE YES OF EVERY TEST OF THE KEY FILE's DOOR (what the seat hands its
payer): written out, the declared rounds are the written lists; so the made places' seven numbers
are the closed places', whole, and ClosedL holds there. §§ 7-9: AT THE MAKER's OWN PIECES AT THE
THREE SEATS, in the form in which the tables' rows name them: the stretch · the base · AtPlace |
AtPlaceOwn at the Johnson letters, the closed radii and the place's own errors · the labels' premise
· the whole entry is at most the cap at 128 · at 2.10 the three premises on "BAT"'s round and four
small tests. Calls and kernel lines: NO NEW MATHEMATICS.
WHAT IT IS NOT, FIRST. NO EXAMPLE: that the premises can be met together is shown nowhere here: no
public files, no m, no P are exhibited, and no theorem shows that the door's tests say yes at any
files. NOT HERE: that a row's piece has nothing put behind its rounds (other files'); the game;
anything on the verifier's state. «At most the cap» compares counts with the number of a round's
written verifier messages divided by 2 ^ 128. Tests with code and comparisons of numbers alone:
nothing on what a count is worth. The round "BAT" stands in front of the place's chain and is not in
the chain's condition: its number is priced by ClosedL's field bat; the law that this number bounds
the round's bad verifier messages is the game's. The full size alone. No soundness is claimed.
Nothing on hiding.
PREMISES. The scope's three (the public files are in scope · the parameter file read · the chains
made, at any digest) · hL: the later places are made of the same m · hp: the description's test on
the plan. For the pins besides: the source of m · the test on the places · «DK at the frame's depth
is the written data» · the three chains' heads. For § 6 besides: hasks: every test of Key.lawsAsk at
m and the description says yes (its other three letters are free). THE LETTERS THAT ARE FIXED
HERE. The radii: every line on joh and «fit» stands at rKUFull | rKOFull | rKWFull: whoever calls a
row's join with these facts lays THAT r; no general fit is here. The data: pins₂ | pins₃ speak of
the pieces at DK.at frS.P.T.a and write Fk X N P, which is Key.descriptionFromSource X N P by unfolding: a join whose
pieces stand at a letter D meets them by its premise D = DK.at frS.P.T.a.
CALLED. key_in_scope (Johnson/RunOne/Law/KeyInScope.lean) · set_in_scope (…/K12Facts15Z.lean) ·
set_eq (Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean) · later_of_full, key_later_more
(…/Sizes/KeyAtScope.lean) · johOk_reads (…/Sizes/ClosedAtScope.lean) · the closed places
(Johnson/Desc/K12/Law/PlacesKeyFull.lean) with held_KU | _KO | _KW and pi…Full_johOk
(…/RoundsAtKeyPlaces.lean) · keyPlan_U | _O | _W (H2K12/RoundsAtKeySeats.lean) · nums_of_planOk
(…/Law/PlacesNums.lean) · batOneOk_of_planOk (…/Law/BatOneMade.lean) · six
(Johnson/Desc/Key/KeyFillAtSizes.lean) · bases_of_all, basesAll_at_six
(Johnson/Top/Fire/Code/BasesOk.lean, KeyBasesAtSix.lean). The pattern of «fit»:
Johnson/RunOne/Law/K12Facts15P.lean's hfit_full.
  stages_29 | stages_210 | stages_32     the made place's stages are the closed place's.
  joh_29 | joh_210 | joh_32 · batOne_29 | batOne_32 · ft_29 | ft_210
  fit0_29 | fit3_29 · fit2_210 | fit3_210 · fitI_32 | fitV_32 | fitO_32     seven kernel lines,
      each with a negative test (…_no): four of the seven hold by ONE (the two radii are equal).
  stageZ_29 | _210 | _32     the split's masks' (at 3.2: I's) code is no deeper than the first
      stage's mask code: three kernel lines, each with a negative test. · ranges_four
  pins₂ | pins₃     at EVERY piece of the shared and of the last chain.
  hW_of_asks     Key.gives_at2 (Johnson/Desc/Key/AsksBothTests.lean) with scan_key_in_scope
      (Johnson/Goal/Numbers/PlanWrittenDescScope.lean), polLayout_scan, madeAt_parts.
  t1_six | t2_eleven | lo_six     the numbers of trees that the first two chains send.
  nums_29 | _210 | _32 · closed_29 | _210 | _32     over nums_K… (…/Sizes/KeyClosedAtScope.lean),
      rounds_at_key_… and closedL_at_key_… (H2K12/RoundsAtKeySeats.lean).
  row_cut₂ | row_cut₃     general in the description: rowAt₂ | ₃, cutDs_inner, cutBase_eq,
      cutPut_inner (Johnson/Top/Fire/Code/RowCut.lean), before_held
      (Johnson/RunOne/Law/K12AtPlaceRow.lean).
  free_29 | _210 | _32 · rds_… · small_210 · firstNe_KO (firstNe_KO_no beside it: no control)
  place_29 | place_210 | place_32     over atPlace_tile₂ | atPlaceOwn_tile₂ | atPlace_tile₃ and
      pays_at_tile (Johnson/Desc/K12/Coin/LawAtTile.lean, LawAtTileOwn.lean, LawAtTileThird.lean),
      labelsPub_own (…/Coin/GameAt.lean), labels_KW (…/Coin/LabelsAtKeyW.lean),
      Err.le_cap_of_below_inv (Iop/ErrCap.lean), the cuts of Johnson/Desc/K12/Law/KeyTileFacts.lean.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Johnson.RunOne.Law.K12PlaceAtName
open OnBytes.Maker (RDT WholeD uLT)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.K12
open VerifiableInference.Desc.Sound (Piece held pieceOf Rest atDesc piecesAt frameAt allOf nTrees)
open _root_.Run (ckP bsRound)
open _root_.Iop (Err)
open OnBytes.Slice (Sg)
open Johnson.G.OfPlan (rootsOf)
open Johnson.RunOne.Law.K12AtPlaceRow (before_held)
open H2K.JointK (keySharedPre keyGu keyOmega keySharedEnd secondPre ownEntry secondEnd pOwnK pGomega
  Blk')
open Johnson.RunOne.KeyRows23 (Fk atSix open₂ open₃)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.Pack (aOf)
open Johnson.Top.H (csKey)
open VerifiableInference.Desc.Key.Fill (six)
open H2K.Pub (johOk sgOf batV0)
open H2K.First (batOneOk)
open H2K.Member (piKUFull piKOFull piKWFull rKUFull rKOFull rKWFull)

/-! ## 1. Off the description's test on the plan alone -/

theorem batOne_29 (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (hp : (Fk X N P).planOk = true) : batOneOk (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) = true :=
  H2K.Made.batOneOk_of_planOk guardedProximityTestParts _ (H2K.JointK.keyPlan_U X N P hp)

theorem batOne_32 (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (hp : (Fk X N P).planOk = true) : batOneOk (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) = true :=
  H2K.Made.batOneOk_of_planOk guardedProximityTestParts _ (H2K.JointK.keyPlan_W X N P hp)

/-! ## 2. With «the later places are made of m» -/

theorem ft_29 {m : Johnson.G.OfPlan.Made} {P : LaterPlaces} (hL : laterPlaces m = .ok P)
    (X : Source) (N : H2U.PlaceNums) (hp : (Fk X N P).planOk = true) :
    (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums.firstTree = 0 := by
  rw [H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ P.U (H2K.JointK.keyPlan_U X N P hp)]
  exact (H2K.Sizes.key_later_more hL).1.2.1

theorem ft_210 {m : Johnson.G.OfPlan.Made} {P : LaterPlaces} (hL : laterPlaces m = .ok P)
    (X : Source) (N : H2U.PlaceNums) (hp : (Fk X N P).planOk = true) (nO : H2U.PlaceNums)
    (hO : P.O = some nO) : (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.firstTree = 0 := by
  rw [H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO (H2K.JointK.keyPlan_O X N P hp nO hO)]
  exact ((H2K.Sizes.key_later_more hL).2.2 nO hO).2

/-! ## 3. The kernel lines at the closed places -/

/-- «The fit» at a stage s and the i-th of the six members: the test's radius at s lies below the
member's own radius and one, times two to the difference of the two codes' depths. Spelled as the
rows' joins spell it. -/
abbrev FitAt (r : Fmt.M1.Stage → ℕ) (i : Fin six.length) (s : Fmt.M1.Stage) : Prop :=
  r (sgOf s).st < ((six.get i).2 + 1) * 2 ^ ((sgOf s).C.a - aOf csKey (six.get i).1)

/-- The folded row's test's first radius against U's own. By the kernel. -/
theorem fit_KU_U :
    (piKUFull.nums.stages.head?.all fun s => decide (FitAt rKUFull ⟨3, by decide⟩ s)) = true := by
  decide +kernel

/-- … against the shared split's masks' own. By the kernel. -/
theorem fit_KU_Sp :
    (piKUFull.nums.stages.head?.all fun s => decide (FitAt rKUFull ⟨5, by decide⟩ s)) = true := by
  decide +kernel

/-- Omega's test's first radius against Omega's own. By the kernel. -/
theorem fit_KO_O :
    (piKOFull.nums.stages.head?.all fun s => decide (FitAt rKOFull ⟨4, by decide⟩ s)) = true := by
  decide +kernel

/-- … against the shared split's masks' own. By the kernel. -/
theorem fit_KO_Sp :
    (piKOFull.nums.stages.head?.all fun s => decide (FitAt rKOFull ⟨5, by decide⟩ s)) = true := by
  decide +kernel

/-- The own test's first radius against I's own. By the kernel. -/
theorem fit_KW_I :
    (piKWFull.nums.stages.head?.all fun s => decide (FitAt rKWFull ⟨0, by decide⟩ s)) = true := by
  decide +kernel

/-- … against V's own. By the kernel. -/
theorem fit_KW_V :
    (piKWFull.nums.stages.head?.all fun s => decide (FitAt rKWFull ⟨2, by decide⟩ s)) = true := by
  decide +kernel

/-- … against Omega's own. By the kernel. -/
theorem fit_KW_O :
    (piKWFull.nums.stages.head?.all fun s => decide (FitAt rKWFull ⟨4, by decide⟩ s)) = true := by
  decide +kernel

/-- The split's masks' code is no deeper than the first stage's mask code. By the kernel. -/
theorem stageZ_KU : (piKUFull.nums.stages.head?.all fun s =>
    decide (aOf csKey (six.get ⟨5, by decide⟩).1 ≤ s.Z.a)) = true := by
  decide +kernel

/-- The like under Omega's test. By the kernel. -/
theorem stageZ_KO : (piKOFull.nums.stages.head?.all fun s =>
    decide (aOf csKey (six.get ⟨5, by decide⟩).1 ≤ s.Z.a)) = true := by
  decide +kernel

/-- I's code is no deeper than the own test's first stage's mask code. By the kernel. -/
theorem stageZ_KW : (piKWFull.nums.stages.head?.all fun s =>
    decide (aOf csKey (six.get ⟨0, by decide⟩).1 ≤ s.Z.a)) = true := by
  decide +kernel

/-! Negative tests: with the member's radius itself in the place of the radius and one (at the
split's masks under the folded row's test: with one depth less); and the mask code's depth less
one. -/

theorem fit_KU_U_no :
    (piKUFull.nums.stages.head?.all fun s => decide (rKUFull (sgOf s).st <
      (six.get ⟨3, by decide⟩).2 * 2 ^ ((sgOf s).C.a - aOf csKey (six.get ⟨3, by decide⟩).1))) =
    false := by
  decide +kernel

theorem fit_KU_Sp_no :
    (piKUFull.nums.stages.head?.all fun s => decide (rKUFull (sgOf s).st <
      ((six.get ⟨5, by decide⟩).2 + 1) *
        2 ^ ((sgOf s).C.a - aOf csKey (six.get ⟨5, by decide⟩).1 - 1))) = false := by
  decide +kernel

theorem fit_KO_O_no :
    (piKOFull.nums.stages.head?.all fun s => decide (rKOFull (sgOf s).st <
      (six.get ⟨4, by decide⟩).2 * 2 ^ ((sgOf s).C.a - aOf csKey (six.get ⟨4, by decide⟩).1))) =
    false := by
  decide +kernel

theorem fit_KO_Sp_no :
    (piKOFull.nums.stages.head?.all fun s => decide (rKOFull (sgOf s).st <
      (six.get ⟨5, by decide⟩).2 * 2 ^ ((sgOf s).C.a - aOf csKey (six.get ⟨5, by decide⟩).1))) =
    false := by
  decide +kernel

theorem fit_KW_I_no :
    (piKWFull.nums.stages.head?.all fun s => decide (rKWFull (sgOf s).st <
      (six.get ⟨0, by decide⟩).2 * 2 ^ ((sgOf s).C.a - aOf csKey (six.get ⟨0, by decide⟩).1))) =
    false := by
  decide +kernel

theorem fit_KW_V_no :
    (piKWFull.nums.stages.head?.all fun s => decide (rKWFull (sgOf s).st <
      (six.get ⟨2, by decide⟩).2 * 2 ^ ((sgOf s).C.a - aOf csKey (six.get ⟨2, by decide⟩).1))) =
    false := by
  decide +kernel

theorem fit_KW_O_no :
    (piKWFull.nums.stages.head?.all fun s => decide (rKWFull (sgOf s).st <
      (six.get ⟨4, by decide⟩).2 * 2 ^ ((sgOf s).C.a - aOf csKey (six.get ⟨4, by decide⟩).1))) =
    false := by
  decide +kernel

theorem stageZ_KU_no : (piKUFull.nums.stages.head?.all fun s =>
    decide (aOf csKey (six.get ⟨5, by decide⟩).1 + 1 ≤ s.Z.a)) = false := by
  decide +kernel

theorem stageZ_KO_no : (piKOFull.nums.stages.head?.all fun s =>
    decide (aOf csKey (six.get ⟨5, by decide⟩).1 + 1 ≤ s.Z.a)) = false := by
  decide +kernel

theorem stageZ_KW_no : (piKWFull.nums.stages.head?.all fun s =>
    decide (aOf csKey (six.get ⟨0, by decide⟩).1 + 1 ≤ s.Z.a)) = false := by
  decide +kernel

/-! ## 4. In scope, at any digest -/

section
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
  (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
  (hm : madeAt Z Zp.lay cfg = .ok m) {P : LaterPlaces} (hL : laterPlaces m = .ok P) (X : Source)
  (N : H2U.PlaceNums) (hp : (Fk X N P).planOk = true)
include hZ hP hm hL hp

theorem stages_29 : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums.stages = piKUFull.nums.stages := by
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm
  have hset := (Johnson.RunOne.Law.K12Facts15.set_in_scope hZ hP hm).trans H2K.Sizes.set_eq
  rw [H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ P.U (H2K.JointK.keyPlan_U X N P hp)]
  exact (H2K.Sizes.later_of_full hk hset hL).1.1.trans H2K.Pub.held_KU.1.symm

theorem stages_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.stages = piKOFull.nums.stages := by
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm
  have hset := (Johnson.RunOne.Law.K12Facts15.set_in_scope hZ hP hm).trans H2K.Sizes.set_eq
  rw [H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO (H2K.JointK.keyPlan_O X N P hp nO hO)]
  exact ((H2K.Sizes.later_of_full hk hset hL).2.2 nO hO).1.trans H2K.Pub.held_KO.1.symm

theorem stages_32 : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).nums.stages = piKWFull.nums.stages := by
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm
  have hset := (Johnson.RunOne.Law.K12Facts15.set_in_scope hZ hP hm).trans H2K.Sizes.set_eq
  rw [H2K.Made.nums_of_planOk ⟨3, none, 2, .K12⟩ P.W (H2K.JointK.keyPlan_W X N P hp)]
  exact (H2K.Sizes.later_of_full hk hset hL).2.1.1.trans H2K.Pub.held_KW.1.symm

theorem joh_29 : johOk (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) rKUFull = true := by
  rw [H2K.Sizes.johOk_reads rKUFull (stages_29 hZ hP hm hL X N hp)]
  exact H2K.Pub.piKUFull_johOk

theorem joh_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    johOk (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) rKOFull = true := by
  rw [H2K.Sizes.johOk_reads rKOFull (stages_210 hZ hP hm hL X N hp nO hO)]
  exact H2K.Pub.piKOFull_johOk

theorem joh_32 : johOk (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) rKWFull = true := by
  rw [H2K.Sizes.johOk_reads rKWFull (stages_32 hZ hP hm hL X N hp)]
  exact H2K.Pub.piKWFull_johOk

/-- Row 2.9: the fit at the place's first stage, at U. -/
theorem fit0_29 :
    ∀ s rest, (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums.stages = s :: rest →
      FitAt rKUFull ⟨3, by decide⟩ s := by
  intro s rest hs
  have h1 := fit_KU_U
  rw [← stages_29 hZ hP hm hL X N hp, hs] at h1
  exact of_decide_eq_true h1

/-- … and at the shared split's masks. -/
theorem fit3_29 :
    ∀ s rest, (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums.stages = s :: rest →
      FitAt rKUFull ⟨5, by decide⟩ s := by
  intro s rest hs
  have h1 := fit_KU_Sp
  rw [← stages_29 hZ hP hm hL X N hp, hs] at h1
  exact of_decide_eq_true h1

/-- Row 2.10: at Omega. -/
theorem fit2_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    ∀ s rest, (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.stages = s :: rest →
      FitAt rKOFull ⟨4, by decide⟩ s := by
  intro s rest hs
  have h1 := fit_KO_O
  rw [← stages_210 hZ hP hm hL X N hp nO hO, hs] at h1
  exact of_decide_eq_true h1

/-- … and at the shared split's masks. -/
theorem fit3_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    ∀ s rest, (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.stages = s :: rest →
      FitAt rKOFull ⟨5, by decide⟩ s := by
  intro s rest hs
  have h1 := fit_KO_Sp
  rw [← stages_210 hZ hP hm hL X N hp nO hO, hs] at h1
  exact of_decide_eq_true h1

/-- Row 3.2: at I. -/
theorem fitI_32 :
    ∀ s rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).nums.stages = s :: rest →
      FitAt rKWFull ⟨0, by decide⟩ s := by
  intro s rest hs
  have h1 := fit_KW_I
  rw [← stages_32 hZ hP hm hL X N hp, hs] at h1
  exact of_decide_eq_true h1

/-- … at V. -/
theorem fitV_32 :
    ∀ s rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).nums.stages = s :: rest →
      FitAt rKWFull ⟨2, by decide⟩ s := by
  intro s rest hs
  have h1 := fit_KW_V
  rw [← stages_32 hZ hP hm hL X N hp, hs] at h1
  exact of_decide_eq_true h1

/-- … at Omega. -/
theorem fitO_32 :
    ∀ s rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).nums.stages = s :: rest →
      FitAt rKWFull ⟨4, by decide⟩ s := by
  intro s rest hs
  have h1 := fit_KW_O
  rw [← stages_32 hZ hP hm hL X N hp, hs] at h1
  exact of_decide_eq_true h1

theorem stageZ_29 : ∀ s rest, (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums.stages = s :: rest →
    aOf csKey (six.get ⟨5, by decide⟩).1 ≤ s.Z.a := by
  intro s rest hs
  have h1 := stageZ_KU
  rw [← stages_29 hZ hP hm hL X N hp, hs] at h1
  exact of_decide_eq_true h1

theorem stageZ_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    ∀ s rest, (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.stages = s :: rest →
      aOf csKey (six.get ⟨5, by decide⟩).1 ≤ s.Z.a := by
  intro s rest hs
  have h1 := stageZ_KO
  rw [← stages_210 hZ hP hm hL X N hp nO hO, hs] at h1
  exact of_decide_eq_true h1

theorem stageZ_32 : ∀ s rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).nums.stages = s :: rest →
    aOf csKey (six.get ⟨0, by decide⟩).1 ≤ s.Z.a := by
  intro s rest hs
  have h1 := stageZ_KW
  rw [← stages_32 hZ hP hm hL X N hp, hs] at h1
  exact of_decide_eq_true h1

/-- The key's ranges have four stages: so the number «stages + 2» of the rows' letters is 6. -/
theorem ranges_four (hX : sourceOf m = .ok X) :
    (Johnson.RunOne.KeyRows23.oneAt X).ranges.stages.length = 4 := by
  rw [(LPFD.one_full hZ hP hm hX hp).1]
  exact Johnson.RunOne.KeyLetters.stages_full

end

/-! ## 5. The pins -/

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) {W : Type}
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt (DK.at OnBytes.Slice.frS.P.T.a) (allOf (DK.at OnBytes.Slice.frS.P.T.a))
      (DK.at OnBytes.Slice.frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt (DK.at OnBytes.Slice.frS.P.T.a) (allOf (DK.at OnBytes.Slice.frS.P.T.a))
      (DK.at OnBytes.Slice.frS.P.T.a).key₂ 0)
      (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt (DK.at OnBytes.Slice.frS.P.T.a) (allOf (DK.at OnBytes.Slice.frS.P.T.a))
      (DK.at OnBytes.Slice.frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
  (dW wEnd : W)
  {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
  (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
  (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
  (hw : (Fk X N P).wantedOk = true)
  (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
  (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
  (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)
include hZ hP hm hX hp hw hDK q₁ q₂ q₃

/-- **At every piece of the shared chain every open pin's tree lies below the piece's base.** Two
calls of other files' theorems. -/
theorem pins₂ (n : ℕ) (p) (h : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
      (DK.at OnBytes.Slice.frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
      (DK.at OnBytes.Slice.frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? =
      some p) : ∀ j ∈ pinned (open₂ n), (atSix j).1 < p.base :=
  (LPFD.bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd atSix
    (LPFD.basesAll_at_six hZ hP hm hX hp hw hDK) q₁ q₂ q₃).2.1 n p h

/-- **The like at the last chain.** -/
theorem pins₃ (n : ℕ) (p) (h : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
      (DK.at OnBytes.Slice.frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ ::
    (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P)
      (DK.at OnBytes.Slice.frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[n]? =
      some p) : ∀ j ∈ pinned (open₃ n), (atSix j).1 < p.base :=
  (LPFD.bases_of_all X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd atSix
    (LPFD.basesAll_at_six hZ hP hm hX hp hw hDK) q₁ q₂ q₃).2.2 n p h

end

/-! ## 6. With the yes of every test of the key file's door -/

/-- The number over the file of the shared chain's own tree number n. -/
theorem numAt_own₁ (t₁ t₂ n : ℕ) : numAt t₁ t₂ 1 (.own n) = t₁ + n := rfl

/-- **In scope, where every test of the key file's door says yes, the description's declared
rounds, written out, are the written lists.** The door's second test, by `Key.gives_at2`; the key's
three numbers by `scan_key_in_scope` at what was read of the parameter file. X₀, lay, F, D: free. -/
theorem hW_of_asks {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol Z) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt Z Zp.lay cfg = .ok m)
    {X₀ : OnBytes.Model.Verify.Public} {lay : ByteArray} {F : FileDescription Xi} {D : WholeD}
    (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m F D, t.2 = true) :
    Johnson.G.OfPlan.writtenOf "key file" F.roundsDeclaredByBlocks = .ok Johnson.G.dryKeyFull := by
  obtain ⟨y, hy, _⟩ := hP
  have hs := VerifiableInference.PlanWritten.scan_key_in_scope hZ
    (OnBytes.Model.Verify.polLayout_scan hy)
  refine (Key.gives_at2 hasks ?_).1
  rw [(Johnson.RunOne.Law.SourceIs.madeAt_parts hm).1]
  exact hs

section
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
  (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
  (hm : madeAt Z Zp.lay cfg = .ok m) {P : LaterPlaces} (hL : laterPlaces m = .ok P) (X : Source)
  (N : H2U.PlaceNums) (hp : (Fk X N P).planOk = true) {X₀ : OnBytes.Model.Verify.Public}
  {lay : ByteArray} {DA : WholeD} (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
include hZ hP hm hL hp hasks

/-- The made place's seven numbers are the closed place's, whole: row 2.9. -/
theorem nums_29 : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums = piKUFull.nums := by
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm
  have hset := (Johnson.RunOne.Law.K12Facts15.set_in_scope hZ hP hm).trans H2K.Sizes.set_eq
  rw [H2K.Made.nums_of_planOk ⟨2, none, 9, .K12⟩ P.U (H2K.JointK.keyPlan_U X N P hp)]
  exact H2K.Sizes.nums_KU hk hset hL
    (H2K.JointK.rounds_at_key_U hk hset hL X N hp (hW_of_asks hZ hP hm hasks))

/-- Row 2.10. -/
theorem nums_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums = piKOFull.nums := by
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm
  have hset := (Johnson.RunOne.Law.K12Facts15.set_in_scope hZ hP hm).trans H2K.Sizes.set_eq
  rw [H2K.Made.nums_of_planOk ⟨2, none, 10, .K12⟩ nO (H2K.JointK.keyPlan_O X N P hp nO hO)]
  exact H2K.Sizes.nums_KO hk hset hL nO hO
    (H2K.JointK.rounds_at_key_O hk hset hL X N hp (hW_of_asks hZ hP hm hasks) nO hO)

/-- Row 3.2. -/
theorem nums_32 : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).nums = piKWFull.nums := by
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm
  have hset := (Johnson.RunOne.Law.K12Facts15.set_in_scope hZ hP hm).trans H2K.Sizes.set_eq
  rw [H2K.Made.nums_of_planOk ⟨3, none, 2, .K12⟩ P.W (H2K.JointK.keyPlan_W X N P hp)]
  exact H2K.Sizes.nums_KW hk hset hL
    (H2K.JointK.rounds_at_key_W hk hset hL X N hp (hW_of_asks hZ hP hm hasks))

/-- **The first chain sends six trees.** Off the written lists. -/
theorem t1_six : (Fk X N P).t₁ = 6 :=
  (H2K.JointK.roots_whole (H2K.Pub.chains_of_written (hW_of_asks hZ hP hm hasks)).1).trans
    H2K.Member.rootsK_first

/-- The shared chain sends eleven. -/
theorem t2_eleven : (Fk X N P).t₂ = 11 :=
  (H2K.JointK.roots_whole (H2K.Pub.chains_of_written (hW_of_asks hZ hP hm hasks)).2.1).trans
    H2K.Member.rootsK_shared

/-- In the letters of row 2.10's join: the number over the file of the shared chain's first own
tree. -/
theorem lo_six : numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own 0) = 6 := by
  rw [numAt_own₁, Nat.add_zero]
  exact t1_six hZ hP hm hL X N hp hasks

/-- `ClosedL` (four tests with code and the place's chain at 2⁻¹ ^ 128) at the made place: row
2.9. -/
theorem closed_29 : Coin.ClosedL (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) rKUFull 1 0 0 H2K.Pub.TKUFull :=
  H2K.JointK.closedL_at_key_U (Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm)
    ((Johnson.RunOne.Law.K12Facts15.set_in_scope hZ hP hm).trans H2K.Sizes.set_eq) hL X N hp
    (hW_of_asks hZ hP hm hasks)

/-- Row 2.10. -/
theorem closed_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    Coin.ClosedL (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) rKOFull 1 0 0 H2K.Pub.TKOFull :=
  H2K.JointK.closedL_at_key_O (Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm)
    ((Johnson.RunOne.Law.K12Facts15.set_in_scope hZ hP hm).trans H2K.Sizes.set_eq) hL X N hp
    (hW_of_asks hZ hP hm hasks) nO hO

/-- Row 3.2. -/
theorem closed_32 : Coin.ClosedL (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) rKWFull 2 6 2 H2K.Pub.TKWFull :=
  H2K.JointK.closedL_at_key_W (Johnson.RunOne.Law.KeyInScope.key_in_scope hZ hP hm)
    ((Johnson.RunOne.Law.K12Facts15.set_in_scope hZ hP hm).trans H2K.Sizes.set_eq) hL X N hp
    (hW_of_asks hZ hP hm hasks)

end

/-! ## 7. The maker's piece in front of which given blocks stand: general in the description -/

section
variable {Xi W : Type} (F : FileDescription Xi) (D : WholeD)
  (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl)) (c₂ : Block F.S₂ F.Cl)
  (k₂ : List (Block F.S₂ F.Cl)) (c₃ : Block F.S₃ F.Cl) (k₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
      ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (dW wEnd : W)

/-- **The shared chain's piece in front of which the blocks `pre` stand, its fields in hand**, in
the form in which the tables' rows name their pieces. B is not the chain's last block. -/
theorem row_cut₂ (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl)
    (post : List (Block F.S₂ F.Cl)) (hcut : c₂ :: k₂ = pre ++ B :: b' :: post) (p)
    (h : ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ ::
      (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
        wEnd)).l₂)[pre.length]? = some p) :
    p.b = held B ∧ p.back = [] ∧
      p.base = D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧
      p.ds = (D.ds₂.drop (pre.flatMap (·.rounds)).length).take B.rounds.length := by
  obtain ⟨b, hb, rfl⟩ := LPFD.rowAt₂ (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
    pre.length p h
  have hbB : b = B := by
    rw [hcut, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hb
    exact (Option.some.inj hb).symm
  subst hbB
  have hlen : pre.length < k₂.length := by
    have e := congrArg List.length hcut
    simp only [List.length_cons, List.length_append] at e
    omega
  have htake : (c₂ :: k₂).take pre.length = pre := by
    rw [hcut, List.take_left']
    rfl
  have hbef : LPFD.before (held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (k₂.map held)
      pre.length = (pre.flatMap (·.rounds)).length := by
    rw [before_held, htake]
  have hget : ((held c₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) :: k₂.map held)[pre.length]? =
      some (held b) := by
    rw [← List.map_cons, List.getElem?_map, hb]
    rfl
  have hlen' : pre.length < (k₂.map (held (P := (F.XiPub × F.S₁)))).length := by
    rw [List.length_map]
    exact hlen
  refine ⟨rfl, LPFD.cutPut_inner [] _ _ hlen', ?_, ?_⟩
  · exact (LPFD.cutBase_eq _ _ _ _ _ (Nat.le_of_lt hlen')).trans (by rw [hbef])
  · exact (LPFD.cutDs_inner _ _ _ _ _ hlen' hget).trans (by rw [hbef]; rfl)

/-- **The last chain's piece in front of which the blocks `pre` stand, its fields in hand**, in the
form in which the tables' rows name their pieces. B is not the chain's last block. -/
theorem row_cut₃ (pre : List (Block F.S₃ F.Cl)) (B b' : Block F.S₃ F.Cl)
    (post : List (Block F.S₃ F.Cl)) (hcut : c₃ :: k₃ = pre ++ B :: b' :: post) (p)
    (h : ((atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ ::
      (atDesc F (piecesAt (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW
        wEnd)).l₃)[pre.length]? = some p) :
    p.b = held B ∧ p.back = [] ∧
      p.base = D.t₁ + D.t₂ + nTrees (D.ds₃.take (pre.flatMap (·.rounds)).length) ∧
      p.ds = (D.ds₃.drop (pre.flatMap (·.rounds)).length).take B.rounds.length := by
  obtain ⟨b, hb, rfl⟩ := LPFD.rowAt₃ (ckP .two) F D c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd
    pre.length p h
  have hbB : b = B := by
    rw [hcut, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hb
    exact (Option.some.inj hb).symm
  subst hbB
  have hlen : pre.length < k₃.length := by
    have e := congrArg List.length hcut
    simp only [List.length_cons, List.length_append] at e
    omega
  have htake : (c₃ :: k₃).take pre.length = pre := by
    rw [hcut, List.take_left']
    rfl
  have hbef : LPFD.before (held c₃ : Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl) (k₃.map held)
      pre.length = (pre.flatMap (·.rounds)).length := by
    rw [before_held, htake]
  have hget : ((held c₃ : Block ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl) ::
      k₃.map held)[pre.length]? = some (held b) := by
    rw [← List.map_cons, List.getElem?_map, hb]
    rfl
  have hlen' : pre.length < (k₃.map (held (P := (F.XiPub × F.S₁ × F.S₂)))).length := by
    rw [List.length_map]
    exact hlen
  refine ⟨rfl, LPFD.cutPut_inner [] _ _ hlen', ?_, ?_⟩
  · exact (LPFD.cutBase_eq _ _ _ _ _ (Nat.le_of_lt hlen')).trans (by rw [hbef])
  · exact (LPFD.cutDs_inner _ _ _ _ _ hlen' hget).trans (by rw [hbef]; rfl)

end

/-! ## 8. The first free own number is the number of roots declared in front; small tests -/

/-- No tree of Omega's group is the first fold's own mask's. By the kernel. -/
theorem firstNe_KO : H2K.Made.firstNe piKOFull = true := by decide +kernel

/-- A closed fact; no control: it cannot fail (`spoilFirst` lays the tree that `firstNe` bars). -/
theorem firstNe_KO_no : H2K.Made.firstNe (H2K.Made.spoilFirst piKOFull) = false := by
  decide +kernel

section
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
  (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
  (hm : madeAt Z Zp.lay cfg = .ok m) {P : LaterPlaces} (hL : laterPlaces m = .ok P) (X : Source)
  (N : H2U.PlaceNums) (hp : (Fk X N P).planOk = true) {X₀ : OnBytes.Model.Verify.Public}
  {lay : ByteArray} {DA : WholeD} (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
include hZ hP hm hL hp hasks

theorem free_29 : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums.free =
    rootsOf ((keySharedPre X.chains P).flatMap (·.rounds)) := by
  have hW : Johnson.G.OfPlan.writtenOf "key file" (Key.descriptionFromSource X N P).roundsDeclaredByBlocks =
      .ok Johnson.G.dryKeyFull := hW_of_asks hZ hP hm hasks
  obtain ⟨_, r, R', er, hr⟩ := H2K.JointK.seat_rounds ⟨2, none, 9, .K12⟩ P.U
    (H2K.JointK.keyPlan_U X N P hp)
  have hx := (H2K.Pub.chains_of_written hW).2.1
  rw [H2K.JointK.keyDecl_atU] at hx
  have hl : ((keySharedPre X.chains P).flatMap (·.rounds)).length = 8 := by
    have hx' := hx
    rw [er] at hx'
    exact H2K.JointK.pre_length_closed hx' hr (H2K.JointK.keySharedPre_bats X.chains P)
      H2K.Member.bat_KUFull
  rw [nums_29 hZ hP hm hL X N hp hasks, H2K.JointK.roots_closed hx, hl]
  exact H2K.Member.roots_KUFull.symm

theorem free_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.free =
      rootsOf ((keySharedPre X.chains P ++ [keyGu P]).flatMap (·.rounds)) := by
  have hW : Johnson.G.OfPlan.writtenOf "key file" (Key.descriptionFromSource X N P).roundsDeclaredByBlocks =
      .ok Johnson.G.dryKeyFull := hW_of_asks hZ hP hm hasks
  obtain ⟨_, r, R', er, hr⟩ := H2K.JointK.seat_rounds ⟨2, none, 10, .K12⟩ nO
    (H2K.JointK.keyPlan_O X N P hp nO hO)
  have hx := (H2K.Pub.chains_of_written hW).2.1
  rw [H2K.JointK.keyDecl_atO X N P nO hO] at hx
  have hl : ((keySharedPre X.chains P ++ [keyGu P]).flatMap (·.rounds)).length = 43 := by
    have hx' := hx
    rw [show (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').rounds = r :: R' from er] at hx'
    exact H2K.JointK.pre_length_closed hx' hr (H2K.JointK.keySharedPreO_bats X N P hp)
      H2K.Member.bat_KOFull
  rw [nums_210 hZ hP hm hL X N hp hasks nO hO, H2K.JointK.roots_closed hx, hl]
  exact H2K.Member.roots_KOFull.symm

theorem free_32 : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W).nums.free =
    rootsOf ((secondPre Key.Claim (Key.thirdPar X.chains)
      (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')).flatMap (·.rounds)) := by
  rw [nums_32 hZ hP hm hL X N hp hasks, H2K.JointK.secondPre_rounds]
  rfl

/-- The blocks at the made and at the closed place declare the same rounds: row 2.9. -/
theorem rds_29 : H2K.Member.rdsAt (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) = H2K.Member.rdsAt piKUFull :=
  H2K.Sizes.rdsAt_reads (H2K.JointK.keyPlan_U X N P hp) H2K.Pub.piKUFull_planOk
    (by rw [nums_29 hZ hP hm hL X N hp hasks])

theorem rds_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    H2K.Member.rdsAt (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) = H2K.Member.rdsAt piKOFull :=
  H2K.Sizes.rdsAt_reads (H2K.JointK.keyPlan_O X N P hp nO hO) H2K.Pub.piKOFull_planOk
    (by rw [nums_210 hZ hP hm hL X N hp hasks nO hO])

theorem rds_32 : H2K.Member.rdsAt (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) = H2K.Member.rdsAt piKWFull :=
  H2K.Sizes.rdsAt_reads (H2K.JointK.keyPlan_W X N P hp) H2K.Pub.piKWFull_planOk
    (by rw [nums_32 hZ hP hm hL X N hp hasks])

/-- Row 2.10's small fields: the first fold sends its own mask · the labels · no tree of the group
is that mask's · a tree stands in front. -/
theorem small_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.ownMask = true ∧
      Coin.ownLabelsB (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) = true ∧
      H2K.Made.firstNe (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) = true ∧
      0 < (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.free := by
  have e := nums_210 hZ hP hm hL X N hp hasks nO hO
  refine ⟨by rw [e]; rfl, ?_, ?_, by rw [e]; decide⟩
  · rw [H2K.Sizes.ownLabelsB_reads (π := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) (q := piKOFull)
      (H2K.JointK.keyPlan_O X N P hp nO hO) H2K.Pub.piKOFull_planOk
      (by rw [e]) (rds_210 hZ hP hm hL X N hp hasks nO hO) (by rw [e])]
    exact H2K.Pub.labelTests_KO.2
  · rw [H2K.Sizes.firstNe_reads (q := piKOFull) (by rw [e]) (by rw [e])]
    exact firstNe_KO

end

/-! ## 9. At the pieces -/

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) {W : Type}
  (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
  (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl) (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl))
  (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt (DK.at OnBytes.Slice.frS.P.T.a) (allOf (DK.at OnBytes.Slice.frS.P.T.a))
      (DK.at OnBytes.Slice.frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt (DK.at OnBytes.Slice.frS.P.T.a) (allOf (DK.at OnBytes.Slice.frS.P.T.a))
      (DK.at OnBytes.Slice.frS.P.T.a).key₂ 0)
      (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) →
    Rest (ckP .two) (frameAt (DK.at OnBytes.Slice.frS.P.T.a) (allOf (DK.at OnBytes.Slice.frS.P.T.a))
      (DK.at OnBytes.Slice.frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
  (dW wEnd : W)
  {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : OnBytes.Model.Verify.Public}
  (hP : ReadOf Zp.pol Z) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}
  (hm : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hL : laterPlaces m = .ok P)
  (hp : (Fk X N P).planOk = true) (hw : (Fk X N P).wantedOk = true)
  (hdata : (Fk X N P).data "key file" = .ok (DK.at OnBytes.Slice.frS.P.T.a))
  (hDK : DK.at OnBytes.Slice.frS.P.T.a = Johnson.G.writtenKFull)
  {X₀ : OnBytes.Model.Verify.Public} {lay : ByteArray} {DA : WholeD}
  (hasks : ∀ t ∈ Key.lawsAsk X₀ lay m (Fk X N P) DA, t.2 = true)
  (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (q₂ : (Fk X N P).shared.blocksInOrder = c₂ :: k₂)
  (q₃ : (Fk X N P).second.blocksInOrder = c₃ :: k₃)

include hZ hP hm hL hp hdata hasks q₂ in
/-- **Row 2.9: at the maker's own piece at the seat of the test on G_u**: its stretch is dB ::
dt; `AtPlace` there, at the Johnson letters, the closed radii and the place's own errors; the
labels' premise; the whole entry is at most the cap at 128. -/
theorem place_29 (n : ℕ) (hn : n = (keySharedPre X.chains P).length) (p)
    (h : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ ::
      (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some p) :
    ∃ dB dt, p.ds = dB :: dt ∧
      p.base = numAt (Fk X N P).t₁ (Fk X N P).t₂ 1
        (.own (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums.free) ∧
      Coin.AtPlace (frameAt (DK.at OnBytes.Slice.frS.P.T.a) (allOf (DK.at OnBytes.Slice.frS.P.T.a))
          (DK.at OnBytes.Slice.frS.P.T.a).key₂ 0) (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U)
        (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
        (fun s => rKUFull s.st) p.base dB dt
        (Coin.errJ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) rKUFull dt) ∧
      Coin.LabelsPub (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1)
        (Coin.nlAt (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U)
          (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1 (.own 0))) p.base ∧
      Err.le ((batV0 (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) rKUFull * (bsRound .two dB.entry dB.kind).w,
          Coin.errJ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) rKUFull dt) :
          Err (uLT (ckP .two) (dB :: dt)))
        (Err.cap 128 (uLT (ckP .two) (dB :: dt))) := by
  subst hn
  have C := closed_29 hZ hP hm hL X N hp hasks
  have e := nums_29 hZ hP hm hL X N hp hasks
  obtain ⟨b', post', eb⟩ := H2K.JointK.key_shared_behind X.chains P
  have hfl : (Fk X N P).shared.blocksInOrder = keySharedPre X.chains P ++ keyGu P :: b' :: post' := by
    rw [← eb]
    exact H2K.JointK.key_shared_flat X N P
  obtain ⟨dB, dt, hst, hAt, hsm⟩ := Coin.atPlace_tile₂ (Fk X N P) "key file"
    (DK.at OnBytes.Slice.frS.P.T.a) hdata (DK.at OnBytes.Slice.frS.P.T.a).key₂ 0
    (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) rKUFull 128 (keySharedPre X.chains P) (keyGu P)
    (b' :: post') hfl
    (H2K.JointK.keyGu_alike P).rounds (free_29 hZ hP hm hL X N hp hasks) C.plan C.chain C.joh C.bat
    (by rw [e]; rfl)
  obtain ⟨_, _, hbase, hds⟩ := row_cut₂ (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
    rest₁ rest₂ rest₃ dW wEnd (keySharedPre X.chains P) (keyGu P) b' post' (q₂.symm.trans hfl) p h
  have hb0 : numAt (Fk X N P).t₁ (Fk X N P).t₂ 1
      (.own (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).nums.free) = p.base := by
    have h0 := hAt.numOwn 0
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [hbase]
    exact h0
  refine ⟨dB, dt, ?_, hb0.symm, ?_, ?_, Err.le_cap_of_below_inv 128 _ hsm⟩
  · rw [hds, (H2K.JointK.keyGu_alike P).rounds]
    exact hst
  · rw [hbase]
    exact hAt
  · rw [← hb0]
    refine Coin.labelsPub_own _ 1 _ _ ?_
    rw [H2K.Sizes.ownLabelsFreeB_reads C.plan H2K.Pub.piKUFull_planOk (by rw [e])
      (rds_29 hZ hP hm hL X N hp hasks) (by rw [e]) (by rw [e])]
    exact H2K.Pub.labelTests_KU.1

include hZ hP hm hL hp hdata hasks q₂ in
/-- **Row 2.10: at the maker's own piece at the seat of the test on G_omega**: the second arm:
`AtPlaceOwn`; the three premises on "BAT"'s round; the cap. -/
theorem place_210 (nO : H2U.PlaceNums) (hO : P.O = some nO) (n : ℕ)
    (hn : n = (keySharedPre X.chains P ++ [keyGu P]).length) (p)
    (h : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ ::
      (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[n]? = some p) :
    ∃ dB dt, p.ds = dB :: dt ∧
      p.base = numAt (Fk X N P).t₁ (Fk X N P).t₂ 1
        (.own (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.free) ∧
      Coin.AtPlaceOwn (frameAt (DK.at OnBytes.Slice.frS.P.T.a)
          (allOf (DK.at OnBytes.Slice.frS.P.T.a))
          (DK.at OnBytes.Slice.frS.P.T.a).key₂ 0) (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
        (numAt (Fk X N P).t₁ (Fk X N P).t₂ 1) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
        (fun s => rKOFull s.st) p.base dB dt
        (Coin.errJ (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) rKOFull dt) ∧
      (H2K.Pub.PayPub (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) (fun s => rKOFull s.st) dB.entry.rows
          (batV0 (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) rKOFull) ∧
        Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0] ∧ dB.entry.logN ≤ 64) ∧
      Err.le ((batV0 (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) rKOFull * (bsRound .two dB.entry dB.kind).w,
          Coin.errJ (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) rKOFull dt) :
          Err (uLT (ckP .two) (dB :: dt)))
        (Err.cap 128 (uLT (ckP .two) (dB :: dt))) := by
  subst hn
  have C := closed_210 hZ hP hm hL X N hp hasks nO hO
  have hfl : (Fk X N P).shared.blocksInOrder =
      (keySharedPre X.chains P ++ [keyGu P]) ++ keyOmega nO :: keySharedEnd X.chains P :: [] :=
    H2K.JointK.key_shared_flat_omega X N P nO hO
  obtain ⟨dB, dt, hst, hT⟩ := Coin.atPlaceOwn_tile₂ (Fk X N P) "key file"
    (DK.at OnBytes.Slice.frS.P.T.a) hdata (DK.at OnBytes.Slice.frS.P.T.a).key₂ 0
    (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) rKOFull 128 (keySharedPre X.chains P ++ [keyGu P])
    (keyOmega nO)
    [keySharedEnd X.chains P] hfl (H2K.JointK.keyOmega_alike nO).rounds
    (free_210 hZ hP hm hL X N hp hasks nO hO) C.plan C.chain C.joh C.bat
    (small_210 hZ hP hm hL X N hp hasks nO hO).1
  have hpay := Coin.pays_at_tile hT C.joh
  obtain ⟨hAt, hsm⟩ := hT
  obtain ⟨_, _, hbase, hds⟩ := row_cut₂ (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
    rest₁ rest₂ rest₃ dW wEnd (keySharedPre X.chains P ++ [keyGu P]) (keyOmega nO)
    (keySharedEnd X.chains P) [] (q₂.symm.trans hfl) p h
  have hb0 : numAt (Fk X N P).t₁ (Fk X N P).t₂ 1
      (.own (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.free) = p.base := by
    have h0 := hAt.numOwn 0
    rw [Nat.add_zero, Nat.add_zero] at h0
    rw [hbase]
    exact h0
  refine ⟨dB, dt, ?_, hb0.symm, ?_, hpay, Err.le_cap_of_below_inv 128 _ hsm⟩
  · rw [hds, (H2K.JointK.keyOmega_alike nO).rounds]
    exact hst
  · rw [hbase]
    exact hAt

include hZ hP hm hX hL hp hw hdata hDK hasks q₁ q₂ q₃ in
/-- **Row 3.2: at the maker's own piece at the seat of the last chain's own test.** The labels'
premise stands at nlKW t₁: the trees are taken over from the two chains in front. -/
theorem place_32 (p)
    (h : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ ::
      (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a)
        c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[2]? = some p) :
    ∃ dB dt, p.ds = dB :: dt ∧
      Coin.AtPlace (frameAt (DK.at OnBytes.Slice.frS.P.T.a) (allOf (DK.at OnBytes.Slice.frS.P.T.a))
          (DK.at OnBytes.Slice.frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
        (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W)
        (numAt (Fk X N P).t₁ (Fk X N P).t₂ 2) Sg.lstJ Sg.flC Sg.flZ Sg.flZ
        (fun s => rKWFull s.st) p.base dB dt
        (Coin.errJ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) rKWFull dt) ∧
      Coin.LabelsPub (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) (numAt (Fk X N P).t₁ (Fk X N P).t₂ 2)
        (Coin.nlKW (Fk X N P).t₁) p.base ∧
      Err.le ((batV0 (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) rKWFull * (bsRound .two dB.entry dB.kind).w,
          Coin.errJ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) rKWFull dt) :
          Err (uLT (ckP .two) (dB :: dt)))
        (Err.cap 128 (uLT (ckP .two) (dB :: dt))) := by
  have C := closed_32 hZ hP hm hL X N hp hasks
  have e := nums_32 hZ hP hm hL X N hp hasks
  have hfl := H2K.JointK.key_second_flat X N P
  obtain ⟨dB, dt, hst, hAt, hsm⟩ := Coin.atPlace_tile₃ (Fk X N P) "key file"
    (DK.at OnBytes.Slice.frS.P.T.a) hdata (DK.at OnBytes.Slice.frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber
    (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) rKWFull 128
    (secondPre Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk'))
    (ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk'))
    [secondEnd Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')] hfl
    (H2K.JointK.ownEntry_keeps Key.Claim _).2 (free_32 hZ hP hm hL X N hp hasks) C.plan C.chain
    C.joh C.bat (by rw [e]; rfl)
  obtain ⟨_, _, hbase, hds⟩ := row_cut₃ (Fk X N P) (DK.at OnBytes.Slice.frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
    rest₁ rest₂ rest₃ dW wEnd
    (secondPre Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk'))
    (ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk'))
    (secondEnd Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')) []
    (q₃.symm.trans hfl) p h
  have h7 : 7 < p.base := pins₃ X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd hZ hP hm hX hp
    hw hDK q₁ q₂ q₃ 2 p h 4 (by decide)
  refine ⟨dB, dt, ?_, ?_, ?_, Err.le_cap_of_below_inv 128 _ hsm⟩
  · rw [hds, (H2K.JointK.ownEntry_keeps Key.Claim _).2]
    exact hst
  · rw [hbase]
    exact hAt
  · intro a rest hs o ho
    rw [H2K.Sizes.opensOf_rds _ _ C.plan, rds_32 hZ hP hm hL X N hp hasks,
      ← H2K.Sizes.opensOf_rds _ _ H2K.Pub.piKWFull_planOk] at ho
    exact Coin.labels_KW (Fk X N P).t₁ (Fk X N P).t₂ p.base (by omega)
      (by rw [t1_six hZ hP hm hL X N hp hasks]; exact h7) a rest
      ((stages_32 hZ hP hm hL X N hp).symm.trans hs) o ho

end

end Johnson.RunOne.Law.K12PlaceAtName

#print axioms Johnson.RunOne.Law.K12PlaceAtName.batOne_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.batOne_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.ft_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.ft_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KU_U
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KU_Sp
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KO_O
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KO_Sp
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KW_I
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KW_V
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KW_O
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stageZ_KU
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stageZ_KO
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stageZ_KW
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KU_U_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KU_Sp_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KO_O_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KO_Sp_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KW_I_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KW_V_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit_KW_O_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stageZ_KU_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stageZ_KO_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stageZ_KW_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stages_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stages_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stages_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.joh_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.joh_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.joh_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit0_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit3_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit2_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fit3_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fitI_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fitV_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.fitO_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stageZ_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stageZ_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.stageZ_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.ranges_four
#print axioms Johnson.RunOne.Law.K12PlaceAtName.pins₂
#print axioms Johnson.RunOne.Law.K12PlaceAtName.pins₃
#print axioms Johnson.RunOne.Law.K12PlaceAtName.numAt_own₁
#print axioms Johnson.RunOne.Law.K12PlaceAtName.hW_of_asks
#print axioms Johnson.RunOne.Law.K12PlaceAtName.nums_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.nums_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.nums_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.t1_six
#print axioms Johnson.RunOne.Law.K12PlaceAtName.t2_eleven
#print axioms Johnson.RunOne.Law.K12PlaceAtName.lo_six
#print axioms Johnson.RunOne.Law.K12PlaceAtName.closed_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.closed_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.closed_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.row_cut₂
#print axioms Johnson.RunOne.Law.K12PlaceAtName.row_cut₃
#print axioms Johnson.RunOne.Law.K12PlaceAtName.firstNe_KO
#print axioms Johnson.RunOne.Law.K12PlaceAtName.firstNe_KO_no
#print axioms Johnson.RunOne.Law.K12PlaceAtName.free_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.free_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.free_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.rds_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.rds_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.rds_32
#print axioms Johnson.RunOne.Law.K12PlaceAtName.small_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.place_29
#print axioms Johnson.RunOne.Law.K12PlaceAtName.place_210
#print axioms Johnson.RunOne.Law.K12PlaceAtName.place_32
