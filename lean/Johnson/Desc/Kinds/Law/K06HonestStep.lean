--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
RE-BASED over Block.lean's ninth and State.lean's tenth issue, and over the seats that go with
them (Stored/HeadSeatAt.lean, Stored/ReplySeatAt.lean). WHAT TURNED: the proof that the lookup's
hearing is there in front: the seat's lookup reads S.lookHeard? itself now, so K6On's lost clause
is not spent any more. The statements are as they were.
Johnson/Desc/Kinds/Law/K06HonestStep.lean: **THE FIVE PREMISES OF mean1's rowStep (Law/RowPins.lean: RowStepStatement: the out-law FROM THE FOLD's OWN CALL Block.step) ARE MET TOGETHER AT AN HONEST RUN, GENERAL IN W, UNDER ONE NAMED PREMISE: JoinAtTruth.** One step along the road from rowRides'
 member to the line in the one coin: (A)(i) Block.step's yes, (ii) no bad draw at ruleStep, (iii) K6On's two further clauses: JOINED HERE; (iv) JoinOpened: THE NAMED PREMISE; (B) k6Own's premises on the piece: NOT HERE.
EVERY LETTER UNDER "THERE IS" IN k06HonestStep, AND WHAT PINS IT: s': THE STEP's OWN RETURN (b.step firstTree s rs cols = .ok (s', 0): an equation; the count of columns taken is the numeral 0) · H: heard s' = some H (an equation) · rs: NO EQUATION: HeardAre (in order: pts · gam · om · the four lists but their last
members), ShapedAs (membership for the rest): THE SENDER IS A "THERE IS". UNDER "FOR ALL": cols: ANY: the block is owed no column and takes none · firstTree: read by the step alone, idle here (no tree is opened) · l: read by blockOf alone · epsS · down · epsP · epsN · epsL: tied to rs by membership alone.
WHAT IT IS NOT, FIRST. (1) **JoinAtTruth IS NOT SHOWN, AT NO VALUE, NOT EVEN AT THE TOY**: "behind every honest run of K6's rounds from s, the form of «join» at the head's key vectors and at what the lookup has heard is worth 0": it wants that WHAT THE LOOKUP HEARD IS HONEST OF THE SAME CELLS: the lookups' house's
 UNTIL SOMEBODY PAYS IT AT SOME VALUE THIS THEOREM MAY BE EMPTY. It is asked at honest runs alone. (2) not a member of k6Own. (3) ALL FOURTEEN FENCES OF Law/K06Honest.lean | K06HonestWhole.lean's heads: honest by what the rounds say · the cells' honesty a premise · the record in front a premise · no W pinned ·
reads as the stated sums · c | mask tied to nothing · no probability · 8 is met by empty lists · no order of play. (4) the rounds bear no digest (the sender's rounds): a real round's sealed digest is struck by the step itself; none of K6's rounds is sealed. Nothing on soundness.
  JoinAtTruth · decide_any_groups · blockAt_rounds · step_of_shaped (from a yes of the seated decision at rounds of the table's shape to a yes of Block.step, which takes no column) · WholeWithRun | wholeWithRun (Law/K06HonestWhole.lean's top with one clause more: the rounds are an honest run: the same proof) ·
  K06HonestStepStatement | k06HonestStep: … ⇒ ∀ cols, ∃ rs s' H: heard · HeardAre · ShapedAs · K6On W s · NoBad (ruleStep W s (c, mask)) rs · Canonical rs · b.step firstTree s rs cols = .ok (s', 0) · K6Out W s' (c, mask) · AND rowStep's CONCLUSION K6In W s (c, mask) (Came.rowStep itself applies).
IMPORTED, NOT MINE: mean1's rowStep, K6Out | K6In, lookHeard_leaves (Law/RowPins.lean), decide_step | noBad_ruleStep (Law/StepBack.lean).

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K06HonestWhole
import Johnson.Desc.Kinds.Law.StepFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE zeroE oneE)
open OnBytes.Model (Aff Fork World)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First (S)

/-- **THE ONE NAMED PREMISE: "join" AT THE TRUTH.** Behind every HONEST run of K6's rounds from s (Law/K06Honest.lean: HonestRunK6), the 36th form, "join"'s, at the head's key vectors and at what the lookup has heard, is worth 0. It is asked at honest runs alone. -/
def JoinAtTruth (W : OnBytes.Model.Verify.Public) (b : Block S Unit) (s : S) (c : NCells)
    (mask : Nat → E) : Prop :=
  ∀ (rs : List Fmt.RoundView) (s' : S) (gk : OnBytes.Model.Forest.Heard),
    HonestRunK6 W.hS (readsOf W) (workOf W) s c mask rs → b.decide s rs [] = .ok s' →
    s'.lookHeard? = some gk →
    JoinOpened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' c mask gk

/-- The seated block's decision never reads the groups of columns. -/
theorem decide_any_groups (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s : S)
    (rs : List Fmt.RoundView) (g1 g2 : List (List (Nat × List UInt64))) :
    (blockAt h iU3 work l).decide s rs g1 = (blockAt h iU3 work l).decide s rs g2 := rfl

/-- The seated block's declared rounds. -/
theorem blockAt_rounds (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) :
    (blockAt h iU3 work l).rounds = (@rounds (parOf h work).sizes).map fun R =>
      ({ entry := R.entry (parOf h work).work } : Fmt.DeclaredRound) := rfl

/-- **From a yes of the seated block's decision at rounds of the table's shape to a yes of Block.step**, which takes no column. -/
theorem step_of_shaped (h : OnBytes.Model.Head.Shape) (iU3 work l firstTree : Nat) (s s' : S)
    (D : List E) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (cols : List OpenedColumn)
    (hz : ∀ x ∈ D, OnBytes.isZeroE x = false)
    (hs : ShapedAs D rs (@rounds (parOf h work).sizes))
    (hd : (blockAt h iU3 work l).decide s rs gs = .ok s') :
    (blockAt h iU3 work l).step firstTree s rs cols = .ok (s', 0) := by
  have hg : groupsOf firstTree (blockAt h iU3 work l).rounds (rs.map (·.drawn)) = [] := by
    rw [blockAt_rounds]
    exact groups_none firstTree _ _ _
  have hw : wantOf firstTree (blockAt h iU3 work l) rs = [] := by
    unfold wantOf
    rw [hg]
    rfl
  have hfit : roundsFit (blockAt h iU3 work l).rounds rs = true := by
    rw [blockAt_rounds]
    exact roundsFit_shaped _ D hz rs _ hs (@rounds_known (parOf h work).sizes)
  have key := Came.decide_step firstTree (blockAt h iU3 work l) s rs cols s' hfit
    (by rw [hw]; rfl)
    (by rw [noDigest_shaped D rs _ hs]; exact hd)
  rw [hw] at key
  exact key

/-- Law/K06HonestWhole.lean's top, with one clause more: the rounds are an honest run. (The same proof; that file's bytes do not turn.) -/
def WholeWithRun : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit), blockOf W l = some b →
    ∀ (s : S) (c : NCells) (mask : Nat → E), K6On W s → K6MoreB s = true → K6RoomB W s = true →
    (∀ g : Given, given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g →
      (dataOf c).Holds ∧ HonestHead c.toCells) →
    ∀ (pts : List E) (gam epsS down om epsP epsN epsL : E) (rsS rsP rsN rsL : List E),
    (letI : Sizes := (parOf W.hS (workOf W)).sizes
     DrawsOk pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) →
    ∃ (rs : List Fmt.RoundView) (s' : S) (gs : List (List (Nat × List UInt64))) (H : HeardAll),
    HonestRunK6 W.hS (readsOf W) (workOf W) s c mask rs ∧
    (seatAt W.hS (readsOf W)).heard s' = some H ∧
    (letI : Sizes := (parOf W.hS (workOf W)).sizes
     HeardAre pts gam om rsS rsP rsN rsL H) ∧
    ShapedAs (drawsOf pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) rs
      (@rounds (parOf W.hS (workOf W)).sizes) ∧
    ClosedWhole (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' c mask ∧
    b.decide s rs gs = .ok s' ∧ WellLaid ((seatAt W.hS (readsOf W)).ledger s) ∧
    (parOf W.hS (workOf W)).ok = true ∧ hasFeatures (parOf W.hS (workOf W)) ∧
    (parOf W.hS (workOf W)).okStart ((seatAt W.hS (readsOf W)).request s) = true ∧
    (∀ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y →
      y < (parOf W.hS (workOf W)).sizes.V) ∧
    Canonical rs ∧
    Sound.NoBad (ruleK6T (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c mask) rs ∧
    Opened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' c mask

theorem wholeWithRun : WholeWithRun := by
  intro W l b hb s c mask hOn hMore hRoom hc pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL hD
  have hOn' := hOn
  obtain ⟨a1, a2, a3, a4, a5, _⟩ := hOn'
  have hRoom' := hRoom
  unfold K6RoomB at hRoom'
  rw [Bool.and_eq_true] at hRoom'
  have hgiven := hRoom'.1
  cases hg : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s with
  | error e => rw [hg] at hgiven; cases hgiven
  | ok g =>
    obtain ⟨hH, hC⟩ := hc g hg
    obtain ⟨z, y, hz, hty, hP, rfl⟩ :=
      Came.given_ok (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s g hg
    letI : Sizes := (parOf W.hS (workOf W)).sizes
    letI : Policy := (parOf W.hS (workOf W)).policy
    letI : Request := (seatAt W.hS (readsOf W)).request s
    letI : Token := ⟨y⟩
    obtain ⟨_, hzt, _⟩ := letters_of_lookup (parOf W.hS (workOf W)).sT
      (parOf W.hS (workOf W)).floor z.1 z.2 a2 hP
    letI : FinalNorm.In := (fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).norm
    letI : In := (fromLookup (parOf W.hS (workOf W)).floor z.1 z.2).head
    obtain ⟨rs, H, G, R, hE⟩ := honestRun_exists_eq c mask a1 hH hzt pts gam epsS down om epsP epsN
      epsL rsS rsP rsN rsL hD ((roomB_iff _ _).mp hRoom'.2)
    have RK : HonestRunK6 W.hS (readsOf W) (workOf W) s c mask rs := ⟨_, _, H, G, hg, hH, hC, R⟩
    obtain ⟨s', gs, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := k06Honest W l b hb s c mask rs hOn hMore RK
    -- what the seat reads back at s' is H
    have hat : (blockAt W.hS (readsOf W) (workOf W) l).decide s rs gs = .ok s' := by
      obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp hb
      have hr : readsOf W = iU3 := by
        unfold readsOf
        rw [hu]
        rfl
      rw [hr]
      rw [← hbb] at h1
      exact h1
    obtain ⟨g2, H2, F2, w2, s1, s2, hg2, hhear2, e1, e2, hs'⟩ :=
      decide_hears_at W.hS (readsOf W) (workOf W) l s s' rs gs hat
    rw [hg] at hg2
    have hgg := (Except.ok.inj hg2).symm
    subst hgg
    have hsame : some (H2, F2, ([] : List Fmt.RoundView)) = some (H, G, []) := hhear2.symm.trans R.hears
    have hH2 : H2 = H := congrArg Prod.fst (Option.some.inj hsame)
    obtain ⟨_, bH, _, _⟩ := seatBack_at W.hS (readsOf W) (workOf W) s _ rs [] F2 H2 w2 s1 s2 hg a1
      R.can hhear2 e1 e2
    refine ⟨rs, s', gs, H, RK, by rw [hs', ← hH2]; exact bH, hE, R.shaped,
      Came.rowRides W l _ hb s c mask s' rs gs h1 h2 h3 h4 h5 h6 h7 h8 h9,
      h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- **rowStep's FIVE PREMISES ARE MET TOGETHER, UNDER THE ONE NAMED PREMISE.** -/
def K06HonestStepStatement : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit), blockOf W l = some b →
    ∀ (firstTree : Nat) (s : S) (c : NCells) (mask : Nat → E), K6On W s → K6MoreB s = true →
    K6RoomB W s = true →
    (∀ g : Given, given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s = .ok g →
      (dataOf c).Holds ∧ HonestHead c.toCells) →
    JoinAtTruth W b s c mask →
    ∀ (pts : List E) (gam epsS down om epsP epsN epsL : E) (rsS rsP rsN rsL : List E),
    (letI : Sizes := (parOf W.hS (workOf W)).sizes
     DrawsOk pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) →
    ∀ (cols : List OpenedColumn), ∃ (rs : List Fmt.RoundView) (s' : S) (H : HeardAll),
    (seatAt W.hS (readsOf W)).heard s' = some H ∧
    (letI : Sizes := (parOf W.hS (workOf W)).sizes
     HeardAre pts gam om rsS rsP rsN rsL H) ∧
    ShapedAs (drawsOf pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL) rs
      (@rounds (parOf W.hS (workOf W)).sizes) ∧
    K6On W s ∧ Sound.NoBad (ruleStep W s (c, mask)) rs ∧ Canonical rs ∧
    b.step firstTree s rs cols = .ok (s', 0) ∧ K6Out W s' (c, mask) ∧
    K6In W s (c, mask)

theorem k06HonestStep : K06HonestStepStatement := by
  intro W l b hb firstTree s c mask hOn hMore hRoom hc hJ pts gam epsS down om epsP epsN epsL rsS rsP
    rsN rsL hD cols
  obtain ⟨rs, s', gs, H, RK, hH, hE, hS, _, h1, _, _, _, _, _, h7, h8, h9⟩ :=
    wholeWithRun W l b hb s c mask hOn hMore hRoom hc pts gam epsS down om epsP epsN epsL rsS rsP rsN
      rsL hD
  obtain ⟨iU3, hu, hbb⟩ := Option.map_eq_some_iff.mp hb
  subst hbb
  have hz : ∀ x ∈ drawsOf pts gam epsS down om epsP epsN epsL rsS rsP rsN rsL,
      OnBytes.isZeroE x = false := fun x hx =>
    ((@DrawsOk.ok (parOf W.hS (workOf W)).sizes _ _ _ _ _ _ _ _ _ _ _ _ hD) x hx).2
  have hstep := step_of_shaped W.hS iU3 (workOf W) l firstTree s s' _ rs gs cols hz hS h1
  have hnd := noDigest_shaped _ rs _ hS
  have hnb : Sound.NoBad (ruleStep W s (c, mask)) rs :=
    Came.noBad_ruleStep W s (c, mask) rs (by rw [hnd]; exact h8)
  -- what the lookup has heard is there, in front and behind
  have hlk : s'.lookHeard? = s.lookHeard? := Came.lookHeard_leaves W.hS iU3 (workOf W) l s rs gs s' h1
  have hsome : ∃ gk, s.lookHeard? = some gk := by
    obtain ⟨g, _, _, _, hg, _⟩ := RK
    obtain ⟨z, _, hz', _⟩ := Came.given_ok _ _ s g hg
    have : (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = some z := hz'
    cases hq : s.lookHeard? with
    | some gk => exact ⟨gk, rfl⟩
    | none => rw [hq] at this; cases this
  obtain ⟨gk, hgk⟩ := hsome
  have hout : K6Out W s' (c, mask) :=
    ⟨h9, gk, hlk.trans hgk, hJ rs s' gk RK h1 (hlk.trans hgk)⟩
  exact ⟨rs, s', H, hH, hE, hS, hOn, hnb, h7, hstep, hout,
    Came.rowStep W l _ hb firstTree s (c, mask) rs cols s' 0 hOn hnb h7 hstep hout⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.step_of_shaped
#print axioms VerifiableInference.Desc.Kinds.Head.Law.wholeWithRun
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k06HonestStep
