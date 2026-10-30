-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySmpStay.lean: THEOREMS. **EVERY BLOCK OF Key.descriptionFromSource's THREE CHAINS LEAVES THE CODES AND THE SAMPLED MESSAGES: a message that is sampled stands behind the block at its number, with its shape, its mark and ITS SAMPLE ROWS** («RowsStay»).
The seam from chain 1's end to chain 3's start is laid (start₃_same | start₃_smp).
THE RELATION: K1.SmpStay (Johnson/Desc/K1/Law/SmpStay.lean) over SampleKept (Johnson/Desc/Ground/Begin.lean), with groundKeeps_smpStay | groundKeeps_kept (the ground's ten routines keep them), kept_begun, kept_modOracle, smpStay_of. WHAT IS NEW HERE IS ONE LAW AND ITS USE:
OBJECT. (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide · the four seats of the proximity test in Key.descriptionFromSource · Key.firstChain | sharedChain | thirdChain. USER. SeedIs.stays | Sealed.stays | held_block (Johnson/Desc/K1/Law/SealStays.lean · SmpHeldAt.lean) at a member at a later border. LETTERS. p · t0 tE; one · N; X · N · P.
  spend_unsampled     a yes of the ground's spendAsMaskP at o: the message o is NOT sampled (its own clause)
  stages_kept         a yes of the stages from a stage on: SampleKept: every elder message but the record's mask to the letter (K12's files' stages_st, field oraclesOld); the mask: at the base case the mark alone turns (BaseSt); at a fold it is spent by the ground's routine: so it is not sampled: outside the relation
  k12_kept            **a yes of the proximity test's decision: SampleKept t0.st tE.st** (K12's files' k12_ok · batJ_ok · bat_st; kept_begun; stages_kept): given early and one answer, which K12's files' stage_st asks
  k12_smpStay         **… SmpStay t0.st tE.st** := smpStay_of (K12's files' k12_grows) k12_kept
  ranges_smpStay · onGu | onGomega | onOwn _smp      the four seats (yes_unit · plan_unit, Johnson/RunOne/Law/RngAnyCl.lean · decide_ok, RngAsked.lean; Johnson/Desc/K12/Seat/Core.lean)
  first_smpStay · shared_smpStay · second_smpStay · three_smpStay     **(Key.descriptionFromSource X N P).planOk = true → ChainKeeps (By SmpStay ·) of each chain**
  flat_smpStay₁ | ₂ | ₃     **planOk → every block of the flat list Decides (By SmpStay ·)**
  start₃_same | start₃_smp  THE SEAM: a yes of the last chain's start at s₁ s₂: the statement that chain 3 starts with IS chain 1's end's (start₃E_inv · start₃_inv · firstOutFrom_inv): so a message that chain 1 has sent and sampled (W, at 1.17) comes to its test at 3.2 with its sample rows
What is not claimed. WHY planOk HERE AND NOT AT «A STATEMENT ONLY GROWS» (KeyCodesLater.lean: no premise): H2K.Out.k12_grows asks nothing but the yes; stage_st | stages_st (Johnson/Desc/K12/Law/OutK2.lean), by which the sample rows are held, ask early and one answer. Omega's message comes into chain 3 anew (adoptP · elsewhereP at 3.0): it is no elder message there: its sample rows are COPIED under the new number (Row.renamed): of that copy nothing is said. Nothing on a message that is not sampled (a mask; a message between its receiving and its admitting), on groups, open rows, pads or ledgers. early | one answer come off planOk: without it nothing is said of the tests' seats. Nothing on soundness.

-/
import Johnson.RunOne.KeyCodesLater
import Johnson.Desc.K1.Law.SmpStay
import Johnson.Desc.K12.Law.Top
import Johnson.RunOne.KeySendFlat
import Johnson.Desc.RunLaws

set_option autoImplicit false

namespace Johnson.RunOne.KeySmp

section TheTest
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open H2K.FoldLaw (bind_ok)
open VerifiableInference.Desc.Ground (kept_begun)
open VerifiableInference.Desc.K1 (SmpStay smpStay_of)

/-- A message that the ground's routine spends as a mask is not sampled: the routine's own clause. -/
theorem spend_unsampled {d d' : _root_.Desc.Plain.DState Unit} {o : ℕ} (h : Ground.spendAsMaskP d o = some d') (x : OnBytes.Oracle) (hx : d.st.oracles[o]? = some x) :
    x.sampled = false := by
  unfold Ground.spendAsMaskP at h
  split at h
  · rename_i hok
    simp only [Ground.ok, Ground.spendAsMaskL, List.all_cons, Bool.and_eq_true] at hok
    have h2 := hok.2.1
    rw [hx] at h2
    simpa [Ground.has] using h2
  · cases h

/-- **The stages leave every sampled message's mark and sample rows.** -/
theorem stages_kept (p : P12) (he : p.early = true) (ha : p.answers = 1) (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (stagesFrom guardedProximityTestParts p j cur rest l : Blk').decide t rs gs = .ok tE) : SampleKept t.st tE.st := by
  have hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12) (rs : List Fmt.RoundView) (gs : Gs), (guardedProximityTestParts.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t' :=
    fun j cur cut t t' rs gs h => baseJ5_st p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1
  have k := stages_st guardedProximityTestParts p (like_P5 p) hB he ha rest j cur l t tE rs gs h
  intro o x hx hs
  have ho : o < t.st.oracles.size := by
    rcases Nat.lt_or_ge o t.st.oracles.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hx
      cases hx
  by_cases hm : t.mask = some o
  · cases rest with
    | nil =>
      rw [stagesFrom_last] at h
      obtain ⟨star, _, _, h3⟩ := hB _ _ _ _ _ _ _ h
      rw [h3]
      exact kept_modOracle t.st star (fun y => { y with spentAsMask := true }) (fun y _ sy => ⟨sy, rfl⟩) o x hx hs
    | cons nxt rest =>
      obtain ⟨t1, t2, t3, f1, _⟩ := (stagesFrom_ok guardedProximityTestParts p j cur nxt rest l t tE rs gs).1 h
      obtain ⟨_, _, _, _, id, d1, d', _, _, _, hcase, hsp, _⟩ := foldJ_form p j cur _ t t1 _ _ ((like_P5 p).fold _ _ _ _ _ _ _ f1)
      rcases hcase with ⟨hmk, rfl⟩ | ⟨hmk, _⟩
      · have e : id = o := Option.some.inj (hmk.symm.trans hm)
        subst e
        have hu := spend_unsampled hsp x hx
        rw [hs] at hu
        cases hu
      · rw [hmk] at hm
        cases hm
  · exact ⟨x, (k.oraclesOld o ho hm).trans hx, hs, rfl⟩

/-- **A yes of the proximity test's decision leaves every sampled message's mark and sample rows.** -/
theorem k12_kept (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    SampleKept t0.st tE.st := by
  obtain ⟨first, rest, ds, tF, t1, hs, _, hfr, hbat, _, hst⟩ := k12_ok guardedProximityTestParts p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := (like_P5 p).front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ ((like_P5 p).bat _ _ _ _ _ hbat)
  obtain ⟨G, _, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  exact (kept_begun tF.st tF.g G).trans (stages_kept p he ha rest 0 first _ _ tE _ _ hst)

/-- **… and the codes and shapes: SmpStay.** -/
theorem k12_smpStay (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    SmpStay t0.st tE.st := smpStay_of (H2K.Out.k12_grows p t0 tE rs gs h) (k12_kept p he ha t0 tE rs gs h)

end TheTest

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.Ground (By)
open VerifiableInference.Desc.Keeps (Decides ChainKeeps chain_flat_keeps)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay)
open Johnson.RunOne.KeySendGood (bareOf flat_eq)

/-- The proximity test's own block, from its own test on the plan. -/
theorem k12_decides_smp (p : P12) (hp : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) : Decides (By SmpStay fun t : T12 => t.st) (proximityTestKind guardedProximityTestParts p : Block T12 Unit) :=
  fun t rs gs t' h => k12_smpStay p (H2K.JointK.early_of_planOk p hp) (H2K.JointK.answers_of_planOk p hp) t t' rs gs h

/-- SmpStay, read at the three (statement · book · roots) of Johnson/Desc/CoreKeeps.lean. -/
abbrev SmpC : VerifiableInference.Desc.Ground.Core → VerifiableInference.Desc.Ground.Core → Prop := fun a b => SmpStay a.st b.st

theorem onGu_smp (b : Block T12 Unit) (hb : Decides (By SmpStay fun t : T12 => t.st) b) : Decides (By SmpStay st₂) (VerifiableInference.Desc.K12.Seat.onGu b) :=
  VerifiableInference.Desc.K12.Seat.onGu_keeps (R := SmpC) b hb

theorem onGomega_smp (b : Block T12 Unit) (hb : Decides (By SmpStay fun t : T12 => t.st) b) : Decides (By SmpStay st₂) (VerifiableInference.Desc.K12.Seat.onGomega b) :=
  VerifiableInference.Desc.K12.Seat.onGomega_keeps (R := SmpC) b hb

theorem onOwn_smp (b : Block T12 Unit) (hb : Decides (By SmpStay fun t : T12 => t.st) b) : Decides (By SmpStay st₃) (VerifiableInference.Desc.K12.Seat.onOwn b) :=
  VerifiableInference.Desc.K12.Seat.onOwn_keeps (R := SmpC) b hb

/-- **The ranges' seat.** As seat_grows_yes (Johnson/RunOne/Law/K12GrowsYes.lean) goes, at SmpStay; early | one answer off the block's own test on the plan. -/
theorem ranges_smpStay (one : OneTime) (N : H2U.PlaceNums) (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true) :
    Decides (By SmpStay st₁) (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim) := by
  intro s rs gs s' h
  obtain ⟨_, he, ha, _, _⟩ := Johnson.RunOne.Law.RngAsked.planOk_ok (Johnson.RunOne.Law.RngAnyCl.plan_unit hp)
  obtain ⟨t0, tE, h1, _, hd, hbk⟩ := Johnson.RunOne.Law.RngAsked.decide_ok (Johnson.RunOne.Law.RngAnyCl.yes_unit h)
  unfold rangesRecord at h1
  obtain ⟨l, hl, rfl⟩ := Johnson.RunOne.Law.RngAsked.mapE_ok h1
  have g := k12_smpStay (rangesParams N) he ha _ tE rs gs hd
  show SmpStay s.d.st s'.d.st
  rw [Johnson.RunOne.Law.RngAtKeyD.hout s tE s' hbk, ← Johnson.RunOne.Law.RngAtKeyD.hin s l hl]
  exact g

/-- The tests on the plan of the proximity test's own blocks at the three later places. -/
def LaterPlans (N : LaterPlaces) : Prop :=
  (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) : Block T12 Unit).planOk = true ∧
  (∀ nO ∈ N.O.toList, (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit).planOk = true) ∧
  (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).planOk = true


/-- The shared chain. -/
theorem shared_smp (c : Model.Verify.Chains) (N : LaterPlaces) (hN : LaterPlans N) : ChainKeeps (By SmpStay st₂) (sharedChain c N) := by
  refine ⟨fun d _ _ d' hd => ?_, fun b hb => (by cases hb), fun L hL => (by cases hL), fun b hb => ?_, end_keeps' SmpStay.refl _ _ _ _ _ _⟩
  · cases hd
    exact SmpStay.refl _
  · rcases List.mem_append.1 hb with hb | hb
    · exact blocksOr_keep groundKeeps_smpStay _ b hb
    · rcases List.mem_append.1 hb with hb | hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact onGu_smp _ (k12_decides_smp _ hN.1)
        · cases hb
      · obtain ⟨nO, hO, rfl⟩ := List.mem_map.1 hb
        exact onGomega_smp _ (k12_decides_smp _ (hN.2.1 nO hO))

/-- The last chain. -/
theorem third_smp (c : Model.Verify.Chains) (N : LaterPlaces) (hN : LaterPlans N) : ChainKeeps (By SmpStay st₃) (thirdChain c N) := by
  refine ⟨k14Second_keeps groundKeeps_smpStay _, fun b hb => (by cases hb), fun L hL => (by cases hL), fun b hb => ?_, end_keeps' SmpStay.refl _ _ _ _ _ _⟩
  rcases List.mem_cons.1 hb with rfl | hb
  · intro s rs gs s' h
    rw [VerifiableInference.Desc.Third.Law.takenSources_same _ s s' rs gs h]
    exact SmpStay.refl _
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact onOwn_smp _ (k12_decides_smp _ hN.2.2)
    · cases hb

/-- A block of a chain's back stands, bared, in the flat list. -/
theorem back_flat {S Cl : Type} (c : Chain S Cl) (b : Block S Cl) (h : b ∈ c.back) : bareOf b ∈ c.blocksInOrder := by
  rw [flat_eq]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem h)))

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-- A seated test's planOk, bared and at another type of claims, holds the kind's own block's. -/
theorem inner_plan {S : Type} (k : Block T12 Unit) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (h : (bareOf ((k.inside enter leave).retype (Cl' := Claim))).planOk = true) : k.planOk = true := by
  have h' : (((k.planOk && k.claims.isEmpty && k.after.isEmpty) && (k.inside enter leave).claims.isEmpty) && ((k.inside enter leave).retype (Cl' := Claim)).hasNoClaimsAndNothingAfter) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1.1.1.1

/-- **The three later places' plans, off the description's test on the plan.** -/
theorem later_plans (hp : (descriptionFromSource X N P).planOk = true) : LaterPlans P := by
  have Q := ((descriptionFromSource X N P).planOk_ok).1 hp
  refine ⟨?_, fun nO hO => ?_, ?_⟩
  · have h2 := (Q.blocks₂ _ (back_flat (descriptionFromSource X N P).shared
      ((VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U))).retype (Cl' := Claim))
      (List.mem_map_of_mem (List.mem_append_right _ (List.mem_append_left _ (List.mem_cons_self)))))).1
    exact inner_plan _ _ _ h2
  · have h2 := (Q.blocks₂ _ (back_flat (descriptionFromSource X N P).shared
      ((VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO))).retype (Cl' := Claim))
      (List.mem_map_of_mem (List.mem_append_right _ (List.mem_append_right _
        (List.mem_map_of_mem (f := fun nO => VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO))) hO)))))).1
    exact inner_plan _ _ _ h2
  · have h3 := (Q.blocks₃ _ (back_flat (descriptionFromSource X N P).second ((VerifiableInference.Desc.Third.ownAt (ownTest P)).retype (Cl' := Claim))
      (List.mem_map_of_mem (List.mem_cons_of_mem _ (List.mem_cons_self))))).1
    -- ownAt turns the place alone: the test on the plan, the claims and the runs behind are the seated block's
    exact inner_plan (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W)) VerifiableInference.Desc.K12.Seat.enterOwn VerifiableInference.Desc.K12.Seat.leaveOwn h3


/-- The description's test on the plan holds the ranges' test's own. -/
theorem rng_planOk (hp : (descriptionFromSource X N P).planOk = true) : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Claim).planOk = true := by
  have hb := Johnson.RunOne.KeySendGood.flat_back (descriptionFromSource X N P).first 1 (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N) rfl
  have h1 := ((((descriptionFromSource X N P).planOk_ok).1 hp).blocks₁ _ (List.mem_of_getElem? hb)).1
  have h2 : ((rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Claim).planOk && (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Claim).hasNoClaimsAndNothingAfter) = true := h1
  exact (Bool.and_eq_true _ _ ▸ h2).1


/-- **Chain 1 of the description leaves the codes and the sampled messages.** -/
theorem first_smpStay (hp : (descriptionFromSource X N P).planOk = true) : ChainKeeps (By SmpStay (st₁ (β := LookupRecord))) (descriptionFromSource X N P).first :=
  chain1_keeps groundKeeps_smpStay _ _ _ _ _ (ranges_smpStay _ N (rng_planOk hp))

theorem shared_smpStay (hp : (descriptionFromSource X N P).planOk = true) : ChainKeeps (By SmpStay st₂) (descriptionFromSource X N P).shared :=
  retype_keeps (shared_smp X.chains P (later_plans hp))

theorem second_smpStay (hp : (descriptionFromSource X N P).planOk = true) : ChainKeeps (By SmpStay st₃) (descriptionFromSource X N P).second :=
  retype_keeps (third_smp X.chains P (later_plans hp))

/-- **All three chains.** -/
theorem three_smpStay (hp : (descriptionFromSource X N P).planOk = true) :
    ChainKeeps (By SmpStay (st₁ (β := LookupRecord))) (descriptionFromSource X N P).first ∧ ChainKeeps (By SmpStay st₂) (descriptionFromSource X N P).shared ∧ ChainKeeps (By SmpStay st₃) (descriptionFromSource X N P).second :=
  ⟨first_smpStay hp, shared_smpStay hp, second_smpStay hp⟩

/-- **Every block of the flat lists.** -/
theorem flat_smpStay₁ (hp : (descriptionFromSource X N P).planOk = true) : ∀ b ∈ (descriptionFromSource X N P).first.blocksInOrder, Decides (By SmpStay (st₁ (β := LookupRecord))) b :=
  chain_flat_keeps (By SmpStay (st₁ (β := LookupRecord))) (fun _ => SmpStay.refl _) (fun _ _ _ x y => SmpStay.trans x y) _ (first_smpStay hp)

theorem flat_smpStay₂ (hp : (descriptionFromSource X N P).planOk = true) : ∀ b ∈ (descriptionFromSource X N P).shared.blocksInOrder, Decides (By SmpStay st₂) b :=
  chain_flat_keeps (By SmpStay st₂) (fun _ => SmpStay.refl _) (fun _ _ _ x y => SmpStay.trans x y) _ (shared_smpStay hp)

theorem flat_smpStay₃ (hp : (descriptionFromSource X N P).planOk = true) : ∀ b ∈ (descriptionFromSource X N P).second.blocksInOrder, Decides (By SmpStay st₃) b :=
  chain_flat_keeps (By SmpStay st₃) (fun _ => SmpStay.refl _) (fun _ _ _ x y => SmpStay.trans x y) _ (second_smpStay hp)

/-- **The seam: the statement that the last chain starts with is the first chain's end's.** -/
theorem start₃_same {x : (descriptionFromSource X N P).XiPub} {s₁ : (descriptionFromSource X N P).S₁} {s₂ : (descriptionFromSource X N P).S₂} {s₃ : (descriptionFromSource X N P).S₃} (h : (descriptionFromSource X N P).start₃ x s₁ s₂ = .ok s₃) :
    st₃ (show S₃ from s₃) = st₁ (show FirstState from s₁) := by
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.ChainEnd.bind_ok h
  obtain ⟨f, hf, hs⟩ := VerifiableInference.Desc.Third.Law.start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨_, _, rfl⟩ := VerifiableInference.Desc.Third.Law.start₃_inv _ _ _ _ hs
  obtain ⟨_, hst, _⟩ := VerifiableInference.Desc.Third.Law.firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  exact hst

theorem start₃_smp {x : (descriptionFromSource X N P).XiPub} {s₁ : (descriptionFromSource X N P).S₁} {s₂ : (descriptionFromSource X N P).S₂} {s₃ : (descriptionFromSource X N P).S₃} (h : (descriptionFromSource X N P).start₃ x s₁ s₂ = .ok s₃) :
    SmpStay (st₁ (show FirstState from s₁)) (st₃ (show S₃ from s₃)) := by
  rw [start₃_same h]
  exact SmpStay.refl _

end Johnson.RunOne.KeySmp
