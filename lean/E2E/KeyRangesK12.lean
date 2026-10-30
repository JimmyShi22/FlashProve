-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesK12.lean: THE KEY FILE's TEST ON THE RANGES AS A SEATED PROXIMITY TEST OF THE FIRST
CHAIN's THREAD (`laid₁`, E2E/KeyRest.lean, with any halves and any tables): what of the premises of
`playsS_k12` and `accepted_every` (Johnson/Desc/ProofFile/Honest/K12/SeatedPlaysS.lean,
EveryAt.lean) reads the description and the plan alone, paid there, in scope. Statements and proofs.

  **`member15`**   in scope the first chain's sub-protocol number 15 (from 0) is the ranges' test as
                 the chain's flat list lays it (`rngEntry`, Johnson/Desc/K12/Law/SitsKeyChains.lean)
  `seatOf_rngEntry`   that sub-protocol seats the proximity test (`SeatOf`) at every job at its
                 place
  **`member_laid`**   THE CLAUSE "member" of `K12PlayedS`, `K12Played`, `K12Seated` and `K12SeatedF`
                 at `laid₁`, whatever halves and tables are laid
  **`place_sourced`**   in scope `rangesParams N`, of which the seat's laws speak, is the written
                 place `piKRFull`, of which the closed facts speak
  `stages_KRJ`, **`stages_plays`**   THE CLAUSES "stages": at a job at the written place `piKRFull`
                 whose fresh table has come earlier: two stages or more, k = h + g at the first; and
                 `PlanPlays` at two trees sent in front
  **`fixed_laid`**   THE CLAUSE "fixed": an own tree's table is fixed by the challenges in front of
                 the round that sends it
  **`listed_laid`**   THE CLAUSE "listed": every sub-protocol of the chain states one oracle message
                 for each root

By `places_named`, `lengths` (E2E/KeyPlacesNamed.lean, KeyThreadFits.lean), `key_sits_row`
(Johnson/Loose/H2K12/SitsRowKey.lean), `seatOf_ranges`, `planPlays_KR`
(…/Honest/K12/SeatRanges.lean, PlanPlaysAt.lean), `planOk_all`
(Johnson/Desc/ProofFile/Honest/Thread/File.lean), `lists_of_shaped`
(…/Honest/Small/FixedSent.lean).

Limits. THE OTHER CLAUSES ARE NOT TOUCHED: the half, what is asked where the thread holds, the
tables, the whole chain's steps. J is a letter here: the job at that place is `rangesTestJob`
(E2E/KeyRangesJob.lean). That two trees are sent in front of the member: E2E/KeyRangesTrees.lean.
`piKRFull` was typed off a print; in scope it is held against the description's own numbers by
`place_sourced`. Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyRest
import E2E.KeyThreadFits
import E2E.KeyPlacesNamed
import E2E.KeyShapeFullSourced
import Johnson.Loose.H2K12.SitsRowKey
import Johnson.Desc.ProofFile.Honest.K12.SeatRanges
import Johnson.Desc.ProofFile.Honest.K12.PlanPlaysAt
import Johnson.Desc.ProofFile.Honest.K12.SeatedPlaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12 P12)
open VerifiableInference.Desc.Key (Xi FirstState Claim enterRanges leaveRanges enterAndAsk
  rangesParams)
open H2K.JointK (rngEntry key_sits_row)
open H2K.Member (piKRFull nKRFull)
open H2K.Pub (sgOf)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open AtPublicFiles.KeyBook (places_named fullFirst rngPlace)
open Johnson.RunOne.Sound (rowsOf)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K12 (TestJob SeatOf seatOf_ranges PlanPlays planPlays_KR)

/-! ## 1 The member -/

section Member
variable {Z : PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

/-- **The first chain's sub-protocol number 15 is the ranges' test.** -/
theorem member15 (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl) :
    (keyFileDescription Xs N Pl).first.blocksInOrder[15]? = some (rngEntry Xs.Y.k.oneTime N) := by
  have r := (places_named scope h).1
  have l := (lengths scope h).1
  have h15 : 15 < (keyFileDescription Xs N Pl).first.blocksInOrder.length := by
    rw [l]
    decide
  have hE := List.getElem?_eq_getElem h15
  have q := congrArg (·[15]?) r
  unfold rowsOf at q
  have q' : ((keyFileDescription Xs N Pl).first.blocksInOrder[15]?).map (fun b => (b.place, b.rounds.length)) =
      fullFirst[15]? := by
    rw [← List.getElem?_map]
    exact q
  rw [hE] at q'
  have e15 : fullFirst[15]? = some (rngPlace, 23) := by decide
  rw [e15] at q'
  have hp : ((keyFileDescription Xs N Pl).first.blocksInOrder[15]).place = rngPlace :=
    congrArg Prod.fst (Option.some.inj q')
  exact hE.trans (congrArg some
    ((key_sits_row Xs N Pl).ranges.2.2 _ (List.getElem_mem h15) (by rw [hp]; rfl)))

end Member

/-- The ranges' test, as the flat list lays it, seats the proximity test. -/
theorem seatOf_rngEntry {W X : Type} (one : OnBytes.Params.OneTime) (N : H2U.PlaceNums)
    (J : TestJob W X) (hJ : J.p = rangesParams N) :
    SeatOf (rngEntry one N) J (enterAndAsk (enterRanges one) (rangesParams N)) leaveRanges := by
  have h := seatOf_ranges (Cl := Claim) (enterRanges one) leaveRanges N J hJ
  exact ⟨h.place, h.rounds, h.oracles, h.decide⟩

/-! ## 2 At the thread -/

section Laid
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀)
  (rc : Rc) (x : Xi) (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **The clause "member".** -/
theorem member_laid (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl)
    (J : TestJob (Local W₀ Rc Xi Unit) X') (hJ : J.p = rangesParams N) :
    ∃ blk, (laid₁ Xs N Pl L w₀ rc x hs tb).bs[15]? = some blk ∧
      SeatOf blk J (enterAndAsk (enterRanges Xs.Y.k.oneTime) (rangesParams N)) leaveRanges :=
  ⟨_, member15 scope h, seatOf_rngEntry _ N J hJ⟩

/-- **The clause "fixed".** -/
theorem fixed_laid (j : Nat) :
    (laid₁ Xs N Pl L w₀ rc x hs tb).fixed (.own j) =
      (laid₁ Xs N Pl L w₀ rc x hs tb).front +
        Small.sentIn ((laid₁ Xs N Pl L w₀ rc x hs tb).bs.flatMap (·.rounds)) j :=
  (Nat.zero_add _).symm

/-- **The clause "listed".** -/
theorem listed_laid (h : KeyNamed Z Xs N Pl) :
    ∀ b ∈ (laid₁ Xs N Pl L w₀ rc x hs tb).bs, Small.Listed b :=
  fun b hb => Small.lists_of_shaped ((planOk_all h.plan).1 b hb).2

end Laid

/-! ## 3 At the written place -/

/-- **In scope the place of the description's test on the ranges is the written one**: the seat's
laws speak of `rangesParams N`, the closed facts of `piKRFull`. -/
theorem place_sourced {Z : PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
    {Pl : VerifiableInference.Desc.Key.LaterPlaces} (hs : AtPublicFiles.AtFiles.KeySourced Z Xs N Pl)
    (scope : InScope Z = true) : rangesParams N = piKRFull := by
  rw [AtPublicFiles.AtFiles.Full.nums_sourced hs scope]
  exact H2K.Member.params_KR

section Place
variable {W X : Type}

/-- Two stages or more; k = h + g at the first. -/
theorem stages_KRJ (J : TestJob W X) (hJ : J.p = piKRFull) :
    ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g := by
  rw [hJ]
  have h2 : 2 ≤ piKRFull.nums.stages.length := by decide +kernel
  have hk : (piKRFull.nums.stages.headD default).k =
      (sgOf (piKRFull.nums.stages.headD default)).h +
        (sgOf (piKRFull.nums.stages.headD default)).g := by decide +kernel
  cases h : piKRFull.nums.stages with
  | nil =>
    rw [h] at h2
    exact absurd h2 (by decide)
  | cons s l =>
    cases l with
    | nil =>
      rw [h] at h2
      exact absurd h2 (by simp)
    | cons t rest =>
      rw [h] at hk
      exact ⟨s, t, rest, rfl, hk⟩

/-- **The clause "stages" of `K12PlayedS`**, at two trees sent in front. -/
theorem stages_plays (J : TestJob W X) (hJ : J.p = piKRFull) (hfr : J.fresh.isNone = false) :
    ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g ∧
      PlanPlays J s (t :: rest) 2 := by
  obtain ⟨s, t, rest, hst, hk⟩ := stages_KRJ J hJ
  exact ⟨s, t, rest, hst, hk, planPlays_KR J hJ hfr s (t :: rest) hst⟩

end Place

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.member15
#print axioms AtPublicFiles.KeyThread.seatOf_rngEntry
#print axioms AtPublicFiles.KeyThread.member_laid
#print axioms AtPublicFiles.KeyThread.fixed_laid
#print axioms AtPublicFiles.KeyThread.listed_laid
#print axioms AtPublicFiles.KeyThread.place_sourced
#print axioms AtPublicFiles.KeyThread.stages_KRJ
#print axioms AtPublicFiles.KeyThread.stages_plays
