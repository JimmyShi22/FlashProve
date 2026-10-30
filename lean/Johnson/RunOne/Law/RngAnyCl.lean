-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngAnyCl.lean: THE PROXIMITY TEST's BLOCK, AND THE BLOCK AT A KEY FILE's RANGES' TEST, DECIDE THE SAME AT EVERY TYPE OF CLAIMS: so the laws on them in Johnson/RunOne/Law/, stated at blocks without claims' type (Cl := Unit) as the kind's files' are, speak of the block at whichever Cl it is seated. Statements and
proofs.
OBJECT. `proximityTestKind X p` and `rangesTest laid back N` at two types of claims.
USER. Johnson/RunOne/Law/RngAtKeyD.lean, RngOver.lean, PlanPays.lean, PlanPays8.lean.
LETTERS. The two types, the parts X, the place, the state and the two halves are free.

Why. A block's type has a letter Cl, the type of a claim. The kind K12 makes no claim, and its files' laws are stated at Cl := Unit. A description seats the block at its own Cl: that is another term. By reading: as stated no theorem of these files applies to the term that rides.

What is said.
  `Same a b`: a block at claims' type A and one at B have the same test on the plan, the same declared rounds, the same decide, no claims' run either, and the same runs behind the batching.
  `same_at`, `same_asks`, `same_andThen`, `same_stages`, `same_k12`: the frame's makers keep it; so proximityTestKind X p at A and at B are `Same`, for all parts X and all places.
  `decide_cl`, `planOk_cl`: of the block rangesTest: decide and the test on the plan are the same at A and at B.
  `cond_of_yes_cl`, `out_of_yes_cl`, `seat_grows_cl`, `rng_lemma_cl`: THE FOUR TOP LAWS AT ANY Cl: the premises speak of the block at Cl; the conclusions are those of Johnson/RunOne/Law/RngSized.lean, K12Grows.lean and RngLemma.lean to the letter (where a conclusion names the variant's own decide, it
    names it at Unit: the same function by `same_k12`).
Limits. Of the block as rangesTest makes it: a description that lays something over it (another decide under a knob) is another term. Those of the four laws. Nothing on soundness.

-/
import Johnson.RunOne.Law.RngLemma
import Johnson.RunOne.Law.RngSized
import Johnson.RunOne.Law.K12Grows

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace Johnson.RunOne.Law.RngAnyCl
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc (Block Grows noDigest)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts Parts stagesFrom asks firstFits)
open VerifiableInference.Desc.First.Close (bat)
open H2K.Pub (sgOf writtenOf WR chainFrom CodesAt)
open H2K.First (gpL Good Plain gpG gpOf sg)
open H2K.JointK (FrontK DeepK accK wAt yOf WO)
open VerifiableInference.Desc.Key Johnson.RunOne.Law.RngHolds

/-- Two blocks at two types of claims that are the same in all that a run's verdict hangs on. (Left out: name, which a run reads for a refusal's words; place, oracles and «before», which a description's test on the plan reads: whoever carries a law through that test to another type of claims wants these too.) -/
structure Same {T A B : Type} (a : Block T A) (b : Block T B) : Prop where
  planOk : a.planOk = b.planOk
  rounds : a.rounds = b.rounds
  decide : a.decide = b.decide
  claims : a.claims = [] ∧ b.claims = []
  after : a.after = b.after

section
variable {T A B : Type}

theorem same_at (x : VerifiableInference.Desc.K12.Part T) (name : String) (place : VerifiableInference.Desc.Place) (l : VerifiableInference.Desc.K12.Laid) :
    Same (x.at name place l : Block T A) (x.at name place l : Block T B) :=
  ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl⟩

theorem same_asks (name : String) (place : VerifiableInference.Desc.Place) (ok : T → Bool) :
    Same (asks name place ok : Block T A) (asks name place ok : Block T B) :=
  ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl⟩

theorem same_andThen (name : String) {a a' : Block T A} {b b' : Block T B} (h : Same a b)
    (k : Same a' b') : Same (a.andThen name a') (b.andThen name b') where
  planOk := by
    show (a.planOk && a'.planOk) = (b.planOk && b'.planOk)
    rw [h.planOk, k.planOk]
  rounds := by
    show a.rounds ++ a'.rounds = b.rounds ++ b'.rounds
    rw [h.rounds, k.rounds]
  decide := by
    have ho : a.openings = b.openings := by
      unfold Block.openings
      rw [h.rounds]
    funext s rs gs
    show (a.decide s (rs.take a.rounds.length) (gs.take a.openings)).bind (fun s' =>
        a'.decide s' (rs.drop a.rounds.length) (gs.drop a.openings)) =
      (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind fun s' =>
        b'.decide s' (rs.drop b.rounds.length) (gs.drop b.openings)
    rw [h.decide, k.decide, h.rounds, ho]
  claims := by
    constructor
    · show a.claims ++ a'.claims = []
      rw [h.claims.1, k.claims.1]
      rfl
    · show b.claims ++ b'.claims = []
      rw [h.claims.2, k.claims.2]
      rfl
  after := by
    show a.after ++ a'.after = b.after ++ b'.after
    rw [h.after, k.after]

theorem same_stages (X : Parts T) (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j : Nat)
    (cur : Fmt.M1.Stage) (l : VerifiableInference.Desc.K12.Laid),
    Same (stagesFrom X p j cur rest l : Block T A) (stagesFrom X p j cur rest l : Block T B)
  | [], j, cur, l => by
    simp only [stagesFrom]
    exact same_at _ _ _ _
  | next :: rest, j, cur, l => by
    simp only [stagesFrom]
    exact same_andThen _ (same_andThen _ (same_andThen _ (same_andThen _ (same_at _ _ _ _)
      (same_at _ _ _ _)) (same_at _ _ _ _)) (same_asks _ _ _)) (same_stages X p rest _ _ _)

/-- **The proximity test's block is the same at every type of claims.** -/
theorem same_k12 (X : Parts T) (p : P12) : Same (proximityTestKind X p : Block T A) (proximityTestKind X p : Block T B) := by
  unfold proximityTestKind
  cases p.nums.stages with
  | nil => exact ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
  | cons first rest =>
    cases H2U.roundsOfNums p.nums with
    | none => exact ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
    | some rs =>
      cases H2U.testOracles p.nums with
      | none => exact ⟨rfl, rfl, rfl, ⟨rfl, rfl⟩, rfl⟩
      | some os =>
        have hb : Same (A := A) (B := B) _ _ := same_andThen "the test" (same_andThen "the batching"
          (same_andThen "the front" (same_at (X.front p) "the front" p.place [])
            (same_at (X.bat p (((rs.zip p.oracles).take 1).map (·.1))) "the batching" p.place
              ((rs.zip p.oracles).take 1)))
          (same_asks "the group is not the first stage's" p.place fun t =>
            (X.group t).any (firstFits first)))
          (same_stages X p rest 0 first ((rs.zip p.oracles).drop 1))
        exact ⟨congrArg (fun z => _ && z) hb.planOk, hb.rounds, hb.decide, hb.claims, hb.after⟩

end

section
variable {σ A B : Type} (laid : σ → Except String RangesLaid) (back : σ → T12 → Except String σ)
  (N : H2U.PlaceNums)

/-- The block rangesTest decides the same at every type of claims. -/
theorem decide_cl :
    (rangesTest (Cl := A) laid back N).decide = (rangesTest (Cl := B) laid back N).decide := by
  funext s rs gs
  show (enterAndAsk laid (rangesParams N) s).bind (fun t =>
      ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 A).decide t rs gs).bind (back s)) =
    (enterAndAsk laid (rangesParams N) s).bind fun t =>
      ((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 B).decide t rs gs).bind (back s)
  rw [(same_k12 (A := A) (B := B) guardedProximityTestParts (rangesParams N)).decide]

/-- And its test on the plan is the same. -/
theorem planOk_cl :
    (rangesTest (Cl := A) laid back N).planOk = (rangesTest (Cl := B) laid back N).planOk := by
  have S := same_k12 (A := A) (B := B) guardedProximityTestParts (rangesParams N)
  show (((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 A).planOk &&
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 A).claims.isEmpty &&
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 A).after.isEmpty) && asksOnPlan (rangesParams N)) =
    (((proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 B).planOk &&
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 B).claims.isEmpty &&
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 B).after.isEmpty) && asksOnPlan (rangesParams N))
  rw [S.planOk, S.claims.1, S.claims.2, S.after]
  rfl

end

/-! ## The four top laws at any type of claims -/

section
variable {σ Cl : Type} {laid : σ → Except String RangesLaid} {back : σ → T12 → Except String σ}
  {N : H2U.PlaceNums}

theorem plan_unit (hp : (rangesTest (Cl := Cl) laid back N).planOk = true) :
    (rangesTest (Cl := Unit) laid back N).planOk = true := by
  rw [planOk_cl (A := Unit) (B := Cl)]
  exact hp

theorem yes_unit {s s' : σ} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (rangesTest (Cl := Cl) laid back N).decide s rs gs = .ok s') :
    (rangesTest (Cl := Unit) laid back N).decide s rs gs = .ok s' := by
  rw [decide_cl (A := Unit) (B := Cl)]
  exact h

/-- Johnson/RunOne/Law/RngSized.lean's cond_of_yes, of the block at any Cl. -/
theorem cond_of_yes_cl {s s' : σ} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : (rangesTest (Cl := Cl) laid back N).planOk = true)
    (h : (rangesTest (Cl := Cl) laid back N).decide s rs gs = .ok s') :
    ∃ t0 tE, rangesRecord laid s = .ok t0 ∧ asksOnRecord (rangesParams N) t0 = .ok () ∧
      (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide t0 rs gs = .ok tE ∧ back s tE = .ok s' ∧
      (∃ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
        rs.head? = some r ∧ bat t0.st t0.g e r = .ok (row, L, S') ∧ row.kept = #[]) ∧
      ∀ (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (S' : Statement),
        bat t0.st t0.g e r = .ok (row, L, S') → row.kept = #[] →
        ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (D : Plain)
          (hg : Good (rangesParams N).nums.firstTree a row D),
          (rangesParams N).nums.stages = a :: rest ∧
          gpOf (rangesParams N) { t0 with st := S', pass := .claim row L } a L = some D ∧ (sg a).Sized ∧
          ∀ (rd : ℕ), rd < (sg a).d → ∀ (rad : ℕ → ℕ) (yw : (gpG hg rad).Words),
            Cond (sg a) rd t0.st t0.g ((gpG hg rad).word yw) :=
  RngSized.cond_of_yes (plan_unit hp) (yes_unit h)

/-- Its out_of_yes, of the block at any Cl. -/
theorem out_of_yes_cl {s s' : σ} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : (rangesTest (Cl := Cl) laid back N).planOk = true)
    (h : (rangesTest (Cl := Cl) laid back N).decide s rs gs = .ok s') :
    ∃ t0 tE G, rangesRecord laid s = .ok t0 ∧ back s tE = .ok s' ∧
      H2K.Out.OutK2 t0 tE ((rangesParams N).nums.stages.length - 1) G :=
  RngSized.out_of_yes (plan_unit hp) (yes_unit h)

/-- Johnson/RunOne/Law/K12Grows.lean's seat_grows, of the block at any Cl. -/
theorem seat_grows_cl (st : σ → Statement) (hin : ∀ s l, laid s = .ok l → l.d.st = st s)
    (hout : ∀ s t s', back s t = .ok s' → st s' = t.st)
    (hp : (rangesTest (Cl := Cl) laid back N).planOk = true) :
    ∀ s rs gs s', (rangesTest (Cl := Cl) laid back N).decide s rs gs = .ok s' → Grows (st s) (st s') :=
  fun s rs gs s' h => K12Grows.seat_grows st hin hout (plan_unit hp) s rs gs s' (yes_unit h)

/-- Johnson/RunOne/Law/RngLemma.lean's rng_lemma, its premise on the plan at any Cl. -/
theorem rng_lemma_cl (hp : (rangesTest (Cl := Cl) laid back N).planOk = true) {t0 : T12}
    (ha : asksOnRecord (rangesParams N) t0 = .ok ()) {L mC mS mW : Sg → ℕ → ℕ} {rad : Sg → ℕ} {εs : ℝ≥0∞}
    (hcodes : CodesAt L mC mS mW rad (rangesParams N).nums.stages)
    (hsmall : ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      (rangesParams N).nums.stages = a :: rest → writtenOf (rangesParams N).nums = some (w0 :: l) →
      chainFrom (.at L mC mS mW rad) rest a l = some c → Err.Below c.err εs) :
    ∃ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (w0 : WR) (l : List WR) (c : Chain (sgOf a)),
      (rangesParams N).nums.stages = a :: rest ∧ writtenOf (rangesParams N).nums = some (w0 :: l) ∧
      c.rds = l.map WR.rd ∧ c.rad = rad (sgOf a) ∧ c.Holds ∧ Err.Below c.err εs ∧
      ∀ (F : ℕ) (r0 : Fmt.RoundView) (e : Fmt.Entry) (row : GroupRow) (Ly : GroupLayout) (S' : Statement),
        bat t0.st t0.g e (noDigest r0) = .ok (row, Ly, S') → row.kept = #[] →
        ∃ (D : Plain) (hok : H2K.First.ok (gpL (rangesParams N) a row D) = true),
          FrontK (rangesParams N) t0 a r0 e row Ly S' D ∧
          ∀ (rd : ℕ → ℕ) (W0 : ℕ → WO) (fM : H2K.Pub.Msg1 c → WO), DeepK D W0 fM →
            (∀ w, ¬ (sgOf a).RIn c.rad (stmG (sgOf a) row, yOf (rangesParams N) a row D hok rd W0) w) →
            Doomed (PQ.uL (ckP .two) c.rds) c.errL fun τ =>
              accK (rangesParams N) F t0 r0 c D.ts (wAt c W0 D.fresh.t fM) τ = false :=
  RngLemma.rng_lemma (plan_unit hp) ha hcodes hsmall

end

end Johnson.RunOne.Law.RngAnyCl

#print axioms Johnson.RunOne.Law.RngAnyCl.same_k12
#print axioms Johnson.RunOne.Law.RngAnyCl.decide_cl
#print axioms Johnson.RunOne.Law.RngAnyCl.planOk_cl
#print axioms Johnson.RunOne.Law.RngAnyCl.cond_of_yes_cl
#print axioms Johnson.RunOne.Law.RngAnyCl.out_of_yes_cl
#print axioms Johnson.RunOne.Law.RngAnyCl.seat_grows_cl
#print axioms Johnson.RunOne.Law.RngAnyCl.rng_lemma_cl
