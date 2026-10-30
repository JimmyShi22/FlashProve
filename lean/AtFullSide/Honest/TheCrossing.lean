-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheCrossing.lean: the one object at the rows' prover at the committer's columns.

TheOneObject.lean stands at the base prover A.H. The prover that runs is the rows' prover at the
committer's columns, over A.H read through the table's coins. Here a value of the object gives, at
every tied input and coin, at that prover: ready returns, the plan serves, and a value of ThreadsCJ
with the sides' own falls, whose invariants are the three threads with what is said at each, at the
state as the base prover's side reads it. The four premises: the dummy's range, the rows,
the key and the committed columns.

threadsAtRelation gives ThreadsP at the base prover from the first half alone, at any relation inside
the tied inputs, at every coin; threadsAtRelation_I names its invariants, in HEq.
-/
import AtFullSide.Honest.TheOneObject
import Johnson.Desc.ProofFile.Honest.ThruThreadsJ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed
open VerifierAndGoals (PublicFiles readFiles)

local instance (priority := high) nonemptyPadZ_theCrossing : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A}
  {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp}

/-- **The crossing.** -/
theorem theCrossing
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheOneObject h hr)
    (hd : A.H.inRange (id matrixInput.dummy) = A.H.inRange A.H.dummy)
    (hrows : (theSides h).prover (A.H.thru id (tableCoins Z) matrixInput.dummy) =
      A.H.thru id (tableCoins Z) matrixInput.dummy)
    (hk : (cmAlong (AZ Z) PadZ (holdZ Z)).key = A.H.key)
    (hcols : ∀ n w x, TiedRequest h hr n w x →
      CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H id (tableCoins Z) w.1 w.2.1) :
    ∀ n w x (c : CoinG A.B RunValue RunValue), TiedRequest h hr n w x →
      ∃ R, ProofFile.Honest.ready h.description A.B A.H w.1 (tableCoins Z w.2.1) x (pursesOf c) = .ok R ∧
      ∃ R', ProofFile.Honest.ready h.description A.B
          ((theSides h).prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0
            (A.H.thru id (tableCoins Z) matrixInput.dummy))) w.1 w.2.1 x (pursesOf c) = .ok R' ∧
        PlanServes ((theSides h).prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0
            (A.H.thru id (tableCoins Z) matrixInput.dummy))) w.1 w.2.1 R' ∧
        ∃ T : ThreadsCJ h.description A.B ((theSides h).prover
            ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0
              (A.H.thru id (tableCoins Z) matrixInput.dummy))) w.1 w.2.1 x (pursesOf c) R',
          T.f₁ = (theSides h).falls₁ ∧ T.f₂ = (theSides h).falls₂ ∧ T.f₃ = (theSides h).falls₃ ∧
          T.I₁ = (fun j k s m E => ThrS (TheLetters.thread₁ h R) (TheLetters.said₁ h R) j k s
            (Mid.narrow (Local.thru id (tableCoins Z)) m) E) ∧
          T.I₂ = (fun j k s m E => ThrS (TheLetters.thread₂ h R (O := O.open₂)) (TheLetters.said₂ h R (O := O.open₂)) j k s
            (Mid.narrow (Common.thru id (tableCoins Z)) m) E) ∧
          T.I₃ = (fun j k s m E => ThrS (TheLetters.thread₃ h O.open₃ R) (TheLetters.said₃ h O.open₃ R) j k s
            (Mid.narrow (Local.thru id (tableCoins Z)) m) E) := by
  intro n w x c hx
  obtain ⟨R, hR, hP, T, ⟨e₁, e₂, e₃⟩, i₁, i₂, i₃, -⟩ := atEveryTiedRunAtItsThreads made O n w x c hx
  obtain ⟨R', hR', hP', T', f₁, f₂, f₃, j₁, j₂, j₃⟩ := rows_of_thruJ_named id (tableCoins Z)
    matrixInput.dummy (theSides h) (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H w.1 w.2.1 x (pursesOf c)
    hd hrows hk (hcols n w x hx) hR hP T
  refine ⟨R, hR, R', hR', hP', T', f₁.trans e₁, f₂.trans e₂, f₃.trans e₃, ?_, ?_, ?_⟩
  · rw [j₁, i₁]
    rfl
  · rw [j₂, i₂]
    rfl
  · rw [j₃, i₃]
    rfl

/-- **ThreadsP at another description, prover, input, coins that are the same**: the cast that the
value at a run takes from the description by name to the return's field. -/
def threadsP_at {Xi W₀ Rc Ky Tr X₀ X : Type} {F F' : VerifiableInference.Desc.FileDescription Xi} {Bk : ProverCoinCounts}
    {H H' : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ w₀' : W₀} {rc rc' : Rc} {x : Xi} {k k' : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (eF : F = F') (eH : H = H') (ew : w₀ = w₀') (er : rc = rc')
    (ek : k = k') (T : ThreadsP F Bk H w₀ rc x k R) : ThreadsP F' Bk H' w₀' rc' x k' R := by
  subst eF eH ew er ek
  exact T

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The cast keeps the three invariants. -/
theorem threadsP_at_I {Xi W₀ Rc Ky Tr X₀ X : Type} {F F' : VerifiableInference.Desc.FileDescription Xi}
    {Bk : ProverCoinCounts} {H H' : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ w₀' : W₀} {rc rc' : Rc} {x : Xi}
    {k k' : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X} (eF : F = F') (eH : H = H') (ew : w₀ = w₀')
    (er : rc = rc') (ek : k = k') (T : ThreadsP F Bk H w₀ rc x k R) :
    HEq (threadsP_at eF eH ew er ek T).I₁ T.I₁ ∧ HEq (threadsP_at eF eH ew er ek T).I₂ T.I₂ ∧
      HEq (threadsP_at eF eH ew er ek T).I₃ T.I₃ := by
  subst eF eH ew er ek
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩

/-- **The invariants at every input of a relation that lies in the tied ones, and at every coin**, at
the return's own description and at a prover of rows that leave A.H as it is. This stands on the
first half alone. -/
noncomputable def TheThreadsHalf.threadsAtRelation
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr)
    (G : Sides A.F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit) (hP : G.prover A.H = A.H)
    {Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop}
    (hRel : ∀ w₀ rc x, Rel w₀ rc x → ∃ n w, w.1 = w₀ ∧ tableCoins Z w.2.1 = rc ∧
      TiedRequest h hr n w x) :
    ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ProofFile.Honest.ready A.F A.B (G.prover A.H) w₀ rc x k = .ok R →
      ThreadsP A.F A.B (G.prover A.H) w₀ rc x k R := fun w₀ rc x hx k R hR =>
  have hD : A.F = h.description := (atPure_at_laid h.head.laid made).2
  let n := Classical.choose (hRel w₀ rc x hx)
  let w := Classical.choose (Classical.choose_spec (hRel w₀ rc x hx))
  have hw := Classical.choose_spec (Classical.choose_spec (hRel w₀ rc x hx))
  let c := Classical.choose (pursesOf_onto k)
  have hc : pursesOf c = k := Classical.choose_spec (pursesOf_onto k)
  have hR' : ProofFile.Honest.ready h.description A.B A.H w.1 (tableCoins Z w.2.1) x (pursesOf c) = .ok R := by
    rw [hw.1, hw.2.1, hc, ← hD, ← hP]
    exact hR
  threadsP_at hD.symm hP.symm hw.1 hw.2.1 hc (O.threads made ⟨n, w, x, c, R, hw.2.2, hR'⟩)

/-- **What those invariants are**: the three threads with what is said at each, at the run's R. -/
theorem TheThreadsHalf.threadsAtRelation_I
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheThreadsHalf h hr)
    (G : Sides A.F A.B FullSizeMatrix IndexCommitterCoins OnBytes.TableKey Cells Unit Unit) (hP : G.prover A.H = A.H)
    {Rel : FullSizeMatrix → IndexCommitterCoins → ProofFile.Inst → Prop}
    (hRel : ∀ w₀ rc x, Rel w₀ rc x → ∃ n w, w.1 = w₀ ∧ tableCoins Z w.2.1 = rc ∧
      TiedRequest h hr n w x)
    (w₀ : FullSizeMatrix) (rc : IndexCommitterCoins) (x : ProofFile.Inst) (hx : Rel w₀ rc x) (k : Coins A.B)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit)
    (hR : ProofFile.Honest.ready A.F A.B (G.prover A.H) w₀ rc x k = .ok R) :
    HEq (O.threadsAtRelation made G hP hRel w₀ rc x hx k R hR).I₁
        (ThrS (TheLetters.thread₁ h R) (TheLetters.said₁ h R)) ∧
      HEq (O.threadsAtRelation made G hP hRel w₀ rc x hx k R hR).I₂
        (ThrS (TheLetters.thread₂ h R (O := O.open₂)) (TheLetters.said₂ h R (O := O.open₂))) ∧
      HEq (O.threadsAtRelation made G hP hRel w₀ rc x hx k R hR).I₃
        (ThrS (TheLetters.thread₃ h O.open₃ R) (TheLetters.said₃ h O.open₃ R)) :=
  threadsP_at_I _ _ _ _ _ _

end AtFullSide.Honest

#print axioms AtFullSide.Honest.theCrossing
#print axioms AtFullSide.Honest.threadsP_at
#print axioms AtFullSide.Honest.TheThreadsHalf.threadsAtRelation
#print axioms AtFullSide.Honest.TheThreadsHalf.threadsAtRelation_I
