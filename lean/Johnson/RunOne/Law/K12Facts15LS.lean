-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Facts15LS.lean: THE ERRORS OF THE PROXIMITY TEST's LAW AT ROW 1.15 OF THE KEY FILE's TABLES LIE AT OR BELOW THE CAP AT 128 (the premise Le15 of Johnson/RunOne/Law/K12Facts15M.lean): general under two tests on the plan; and at the full size from scope's equations. Statements with proofs; evaluations in the kernel, with controls. IT PAYS NO FIELD OF THE TABLES: Gives15 HOLDS ALL THE WEIGHT AND IS SHOWN OF NOTHING. (Where this and lean/THEOREM.md differ, the page holds.)
OBJECT. Le15 at a frame's letter rest₁ whose errors at the 15th piece are the cap at 128 (hcap). By report: the rests on the tables' main road are all such.
USER. The21's filler in the goals' scope.
WHAT IT SAYS AND DOES NOT SAY OF BITS. Each of the 23 rounds' count is at most 2⁻¹²⁸ of ITS OWN round's written verifier messages (bits of work among them), by exact numbers in the kernel; one round at a time, no sum.
THE DEFAULT ARM. The errors behind the batching's round (errJ) are the list of zeros where the place's stages and written rounds make no chain; there Le15 would be won for nothing. Whether the chain is there is a fact on the place alone (chainFrom reads its stages and written rounds, no codes). It wants the test that holds the written rounds against a state's codes (pubOk) at some codes: cond_scope: under it the kind's whole condition holds, whose first consequence is that the chain is there. The seat asks that test on the test's own state in front of every run (Key.asksOnRecord): so wherever the block says yes the chain is there. Of a place at which the block never says yes nothing is shown here.

  le15_of: GENERAL: Le15 from hcap, the facts, and two tests on the plan: the chain's counts (smallOk) and the batching's count (batPriceOk at 128).
  numbers_more: two more lines of the routine that makes the place's numbers: the bits of work, the rows.
  sgOf_of_st, rad_fun: the radii by stage are the written test's own radii.
  workFull, rowsFull, work_full: the bits of work and the rows at the written values.
  trial_eq, trial_rng, and three controls: THE FIRST OF THE NINE WRITTEN TESTS IS THIS PLACE's OWN TEST: at the written stages and bits of work. With one position more at the second stage, with one bit of work more, and at the neighbouring test the trial says no.
  small_scope: the chain's counts: from the kernel theorem that every written test says yes (tests_ok).
  batAs, price_eq, price_full, price_edge: the batching's count: by the kernel at 128; and the edge: the greatest k at which the comparison holds.
  price_scope, le15_scope, cond_scope.
  r1_15_scope_cap: the field r1_15 ⇐ scope's equations · hcap · q₁ · hl · Gives15.
Limits. That scope's equations hold is not shown here (hset: Johnson/RunOne/Law/K12Facts15Z.lean). As empty as Gives15. One size. It stands over files of Johnson/Bridge/ (see their heads on what they rest). Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Facts15S
import Johnson.RunOne.Law.K12Facts15L
import Johnson.Desc.K12.Law.SmallOfPlaces
import Johnson.Desc.K12.Law.BatPriceLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Facts15
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key
open Johnson.G.OfPlan (Made)
open Lk6.AtPlan (keyFull)
open Johnson.Bridge (Br TestAt testsFull)
open H2K.Pub (sgOf stN writtenOf WR radOf brOfT testAtStages testOf_eq Trial trialB bump ok_full smallOk batPriceOk batAtB priceOn)
open scoped ENNReal

/-- Two more lines of the routine that makes the place's numbers. -/
theorem numbers_more {m : Made} {N : H2U.PlaceNums} (hN : rangesNumbers m = .ok N) :
    N.nums.work = m.p.chains.made.sized.set.workOf .query .once ∧
      N.nums.rows = Wf.rowsBatched m.p.chains.made.sized.key.ranges.x m.p.chains.made.sized.key.ranges.matrix := by
  unfold rangesNumbers at hN
  dsimp only at hN
  obtain ⟨ts, _, hN⟩ := exc_bind hN
  obtain ⟨first, _, hN⟩ := exc_bind hN
  cases hb : (H2U.batPlaces m.p.chains.key.oneTime.given.plan.rounds).head? with
  | none =>
    try rw [hb] at hN
    obtain ⟨_, e', _⟩ := exc_bind hN
    cases e'
  | some i =>
    try rw [hb] at hN
    obtain ⟨y, _, hN⟩ := exc_bind hN
    split at hN
    · obtain ⟨_, _, hN⟩ := exc_bind hN
      obtain rfl : _ = N := Except.ok.inj hN
      exact ⟨rfl, rfl⟩
    · obtain ⟨_, e', _⟩ := exc_bind hN
      cases e'

theorem sgOf_of_st (s : Sg) : sgOf s.st = s := by
  cases s with
  | mk C Z h g t =>
    show (⟨C, Z, h, h + g - h, t⟩ : Sg) = ⟨C, Z, h, g, t⟩
    rw [Nat.add_sub_cancel_left]

/-- The radii by stage are the written test's own. -/
theorem rad_fun : (fun s : Sg => radRng s.st) = radOf testRng := by
  funext s
  show radOf testRng (sgOf s.st) = radOf testRng s
  rw [sgOf_of_st]

/-- The bits of work of a round of positions, at the written setting, at the scope of the key's first chain. -/
def workFull : ℕ := recordSet.workOf .query .once

/-- The rows that the test batches, at the written value. -/
def rowsFull : ℕ := Wf.rowsBatched keyFull.ranges.x keyFull.ranges.matrix

theorem work_full : workFull = 32 := by decide +kernel

/-- **The first of the nine written tests is this place's own test.** -/
theorem trial_eq : testAtStages (radOf testRng) (brOfT testRng) stagesFull workFull = some testRng := rfl

theorem trial_rng : Trial testsFull 0 stagesFull workFull := ⟨testRng, testRng_at, trial_eq⟩

theorem trial_yes : trialB testsFull 0 stagesFull workFull = true := by decide +kernel
/-- Controls: one position more at the second stage; one bit of work more; the neighbouring test. -/
theorem trial_no_stage : trialB testsFull 0 (bump stagesFull) workFull = false := by decide +kernel
theorem trial_no_work : trialB testsFull 0 stagesFull (workFull + 1) = false := by decide +kernel
theorem trial_no_next : trialB testsFull 1 stagesFull workFull = false := by decide +kernel

/-- "BAT" as the maker lays it, at a number of rows. -/
def batAs (rows : ℕ) : WR := H2K.Made.wr ⟨{ Fmt.M1.rBat.entry with rows := rows }, [], []⟩ .elems none

/-- The test on the batching's count reads the place's first stage and its rows alone. -/
theorem price_eq (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : π.nums.stages = a :: rest) (w0 : WR) (l : List WR) (hw : writtenOf π.nums = some (w0 :: l)) :
    batPriceOk π r k = priceOn (stN a) (batAs π.nums.rows) (r (stN a)) π.nums.rows k := by
  have e : w0 = batAs π.nums.rows := H2K.Made.written_bat_eq π.nums w0 l hw
  have hat : batAtB π = some (stN a, w0) := by
    unfold batAtB
    rw [hs, hw]
    rfl
  have hr : (batAs π.nums.rows).entry.rows = π.nums.rows := rfl
  unfold batPriceOk
  rw [hat, Option.any_some, e]
  dsimp only
  rw [hr]

theorem stages_ne : stagesFull ≠ [] := by decide +kernel

/-- The first stage at the written value. -/
def aFull : Fmt.M1.Stage := stagesFull.head stages_ne

theorem stages_cons : stagesFull = aFull :: stagesFull.tail := by
  first
    | exact (List.cons_head_tail stages_ne).symm
    | exact (List.head_cons_tail stagesFull stages_ne).symm

/-- The comparison at the written values. -/
def priceFull (k : ℕ) : Bool := priceOn (stN aFull) (batAs rowsFull) (radRng (stN aFull)) rowsFull k

theorem price_full : priceFull 128 = true := by decide +kernel

/-- The edge. -/
theorem price_edge : priceFull 174 = true ∧ priceFull 175 = false := by decide +kernel

section
variable {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ}
  {m : Made} {N : H2U.PlaceNums}

theorem stages_scope (hN : rangesNumbers m = .ok N) (h : (rangesTest laid back N : Block σ Cl).planOk = true)
    (hk : m.p.chains.made.sized.key = keyFull) : (rangesParams N).nums.stages = stagesFull := by
  obtain ⟨hn, _⟩ := nums_of_early N (PlanPays.rng_pays h).1
  rw [hn, (numbers_parts hN).2.2.2.2.2, hk]
  rfl

/-- The chain's counts. -/
theorem small_scope (hN : rangesNumbers m = .ok N) (h : (rangesTest laid back N : Block σ Cl).planOk = true)
    (hk : m.p.chains.made.sized.key = keyFull) (hset : m.p.chains.made.sized.set = recordSet) :
    smallOk (fun s => radRng s.st) (brOfT testRng) (rangesParams N) = true := by
  obtain ⟨hn, _⟩ := nums_of_early N (PlanPays.rng_pays h).1
  have hw : (rangesParams N).nums.work = workFull := by
    rw [hn, (numbers_more hN).1, hset]
    rfl
  rw [rad_fun]
  refine smallOk_of_test (Cl := Unit) _ _ _ testRng ?_ (ok_full (List.mem_of_getElem? testRng_at))
    (PlanPays.rng_pays h).2.2.1
  rw [testOf_eq, stages_scope hN h hk, hw]
  exact trial_eq

/-- The batching's count. -/
theorem price_scope (hN : rangesNumbers m = .ok N) (h : (rangesTest laid back N : Block σ Cl).planOk = true)
    (hk : m.p.chains.made.sized.key = keyFull) : batPriceOk (rangesParams N) radRng 128 = true := by
  obtain ⟨hn, _⟩ := nums_of_early N (PlanPays.rng_pays h).1
  have hr : (rangesParams N).nums.rows = rowsFull := by
    rw [hn, (numbers_more hN).2, hk]
    rfl
  obtain ⟨w0, l, hw⟩ := written_of_plan h
  have hs : (rangesParams N).nums.stages = aFull :: stagesFull.tail := (stages_scope hN h hk).trans stages_cons
  rw [price_eq _ radRng 128 aFull _ hs w0 l hw, hr]
  exact price_full

/-- **The kind's whole condition, wherever the written rounds fit a state's codes**: its first consequence is that the place's chain is there. -/
theorem cond_scope (hN : rangesNumbers m = .ok N) (h : (rangesTest laid back N : Block σ Cl).planOk = true)
    (hk : m.p.chains.made.sized.key = keyFull) (hset : m.p.chains.made.sized.set = recordSet)
    (K : Codes) (hpub : H2K.Pub.pubOk (rangesParams N) K = true) :
    H2K.Pub.K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => radRng s.st) (rangesParams N) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  H2K.Pub.k12Condition_of_four radRng (brOfT testRng) (rangesParams N) K hpub (PlanPays.rng_pays h).2.2.2.1
    (joh_scope hN h hk) (small_scope hN h hk hset)

end

end Johnson.RunOne.Law.K12Facts15

set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace Johnson.RunOne.Law.K12AtThe21
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open OnBytes.Slice (Sg)
open H2K.Pin (NTuple)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt johOk batV0 codes_of_johOk)
open H2K.First (batOneOk)
open Johnson.G.OfPlan (rootsOf)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ R₁ open₁)
open LPFD

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (notBad : List OnBytes.E → Strs → Prop) (off₂ off₃ : ℕ → ℕ)
    (on : ℕ → (Xi × FirstState) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str → Prop)


/-- **The law's errors lie at or below the cap**, from two tests on the plan. -/
theorem le15_of (file : String) (stageRad : _root_.Fmt.M1.Stage → ℕ) (Bk : Sg → Johnson.Bridge.Br × Johnson.Bridge.Br)
    (m : Johnson.G.OfPlan.Made)
    (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (data : (Fk X N P).data file = .ok (DK.at frS.P.T.a))
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hno : ∀ d ∈ (DK.at frS.P.T.a).ds₁.take (((c₁ :: k₁).take 15).flatMap (·.rounds)).length, (d.entry.name == "BAT") = false)
    (joh : johOk (rangesParams N) stageRad = true)
    (hcap : ∀ ds, (rest₁ 15 ds).err = Err.cap 128 (uLT (ckP .two) ds))
    (hsm : H2K.Pub.smallOk (fun s => stageRad s.st) Bk (rangesParams N) = true)
    (hpr : H2K.Pub.batPriceOk (rangesParams N) stageRad 128 = true) :
    Le15 X N P DK c₁ k₁ rest₁ stageRad := by
  intro dB dt hcut
  have plan := K12Facts15.plan_of X N P hp
  obtain ⟨w0, l, hw⟩ := K12Facts15.written_of_plan plan
  have hbe := K12Facts15.behind_ne X N P c₁ k₁ hp q₁ hl
  have hbeh : ((c₁ :: k₁).drop (15 + 1)).flatMap (·.rounds) =
      (((c₁ :: k₁).drop 16).flatMap (·.rounds)).dropLast ++ [(((c₁ :: k₁).drop 16).flatMap (·.rounds)).getLast hbe] := by
    first
      | exact (List.dropLast_concat_getLast hbe).symm
      | exact (List.dropLast_append_getLast hbe).symm
  have hfree := K12Facts15.free_of c₁ k₁ file _ hX hN hp data q₁ hl hno
  have A := K12AtPlaceRow.atPlace_row₁J (Fk X N P) file (DK.at frS.P.T.a) data c₁ k₁ q₁ 15 _
    (K12AtField.rng_at_15 X N P c₁ k₁ q₁ hl) (K12Facts15.not_last X N P c₁ k₁ q₁ hl) (rangesParams N)
    (RngAnyCl.same_k12 (A := Key.Claim) (B := Unit) guardedProximityTestParts (rangesParams N)).rounds _ _ hbeh stageRad dB dt
    hcut hfree (PlanPays.rng_pays plan).1 (PlanPays.rng_pays plan).2.1 (PlanPays.rng_pays plan).2.2.1
    (PlanPays.rng_pays plan).2.2.2.1 joh (K12Facts15.arm_of hN plan) w0 l hw
  rw [hcap]
  exact K12Facts15.pair_le_cap (rangesParams N) stageRad Bk dB dt (PlanPays.rng_pays plan).2.2.1 hsm hpr A.like

/-- At the full size. -/
theorem le15_scope (file : String) (m : Johnson.G.OfPlan.Made)
    (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (data : (Fk X N P).data file = .ok (DK.at frS.P.T.a)) (hDK : DK = Johnson.G.writtenKFull)
    (hk : m.p.chains.made.sized.key = Lk6.AtPlan.keyFull) (hset : m.p.chains.made.sized.set = OnBytes.Params.recordSet)
    (hL : (Fk X N P).first.blocksInOrder.map (·.rounds.length) = K12Facts15.roundsFull)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hcap : ∀ ds, (rest₁ 15 ds).err = Err.cap 128 (uLT (ckP .two) ds)) :
    Le15 X N P DK c₁ k₁ rest₁ K12Facts15.radRng := by
  have plan := K12Facts15.plan_of X N P hp
  refine le15_of X N P DK c₁ k₁ rest₁ file K12Facts15.radRng (H2K.Pub.brOfT K12Facts15.testRng) m hX hN hp data q₁ hl ?_
    (K12Facts15.joh_scope hN plan hk) hcap (K12Facts15.small_scope hN plan hk hset) (K12Facts15.price_scope hN plan hk)
  rw [hDK]
  exact K12Facts15.hno_scope (c₁ :: k₁) (q₁ ▸ hL) _

/-- **THE FIELD r1_15 OF The21, AT THE FULL SIZE, AT RESTS AT THE CAP, FROM SCOPE's EQUATIONS AND THE ONE PREMISE THAT HOLDS THE WEIGHT.** -/
theorem r1_15_scope_cap (file : String) (rd : ℕ → ℕ) (m : Johnson.G.OfPlan.Made)
    (hX : sourceOf m = .ok X) (hN : rangesNumbers m = .ok N) (hp : (Fk X N P).planOk = true)
    (data : (Fk X N P).data file = .ok (DK.at frS.P.T.a)) (hDK : DK = Johnson.G.writtenKFull)
    (hk : m.p.chains.made.sized.key = Lk6.AtPlan.keyFull) (hset : m.p.chains.made.sized.set = OnBytes.Params.recordSet)
    (hL : (Fk X N P).first.blocksInOrder.map (·.rounds.length) = K12Facts15.roundsFull)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hcap : ∀ ds, (rest₁ 15 ds).err = Err.cap 128 (uLT (ckP .two) ds))
    (gives : Gives15 X N P DK c₁ k₁ rest₁ B at_ R (OnH X N P DK B at_ R coll) K12Facts15.radRng rd) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 15 :=
  r1_15_scope X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll file rd m hX hN hp data hDK hk hL q₁ hl
    (le15_scope X N P DK c₁ k₁ rest₁ file m hX hN hp data hDK hk hset hL q₁ hl hcap) gives

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12Facts15.numbers_more
#print axioms Johnson.RunOne.Law.K12Facts15.sgOf_of_st
#print axioms Johnson.RunOne.Law.K12Facts15.rad_fun
#print axioms Johnson.RunOne.Law.K12Facts15.work_full
#print axioms Johnson.RunOne.Law.K12Facts15.trial_eq
#print axioms Johnson.RunOne.Law.K12Facts15.trial_rng
#print axioms Johnson.RunOne.Law.K12Facts15.trial_yes
#print axioms Johnson.RunOne.Law.K12Facts15.trial_no_stage
#print axioms Johnson.RunOne.Law.K12Facts15.trial_no_work
#print axioms Johnson.RunOne.Law.K12Facts15.trial_no_next
#print axioms Johnson.RunOne.Law.K12Facts15.price_eq
#print axioms Johnson.RunOne.Law.K12Facts15.stages_ne
#print axioms Johnson.RunOne.Law.K12Facts15.stages_cons
#print axioms Johnson.RunOne.Law.K12Facts15.price_full
#print axioms Johnson.RunOne.Law.K12Facts15.price_edge
#print axioms Johnson.RunOne.Law.K12Facts15.stages_scope
#print axioms Johnson.RunOne.Law.K12Facts15.small_scope
#print axioms Johnson.RunOne.Law.K12Facts15.price_scope
#print axioms Johnson.RunOne.Law.K12Facts15.cond_scope
#print axioms Johnson.RunOne.Law.K12AtThe21.le15_of
#print axioms Johnson.RunOne.Law.K12AtThe21.le15_scope
#print axioms Johnson.RunOne.Law.K12AtThe21.r1_15_scope_cap
