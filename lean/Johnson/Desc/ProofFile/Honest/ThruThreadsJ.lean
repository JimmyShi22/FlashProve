-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruThreadsJ.lean: the hypotheses of the rule on a run with the third
family (ThreadsCJ, Honest/Law/ThreadStratCJ.lean) go over from a prover to the prover read through
and to the rows' prover, as ThreadsC does (Honest/ThruThreads.lean). The third family is on the
verifier's state alone, so it stays.

  SaysYesJ.thru, CarriesOn.thru   the two conditions with the third family
  ThreadsCJ.thru, ThreadsCJ.withStored   the invariants, the falls, the third family, the starts
  rows_of_thruJ   at the rows' prover: ready returns, the plan serves and there is a value of
                  ThreadsCJ with the same falls
-/
import Johnson.Desc.ProofFile.Honest.ThruThreads
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratCJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription)

variable {S Cl Xi V V' W W' Y Pb W₀ W₀' Rc Rc' Ky Tr X₀ X Sd Xc : Type}

section
variable (see : V' → V) (wit : W' → W) {φ : Face V W Pb} {φ' : Face V' W' Pb}
  (hφ : ∀ w : W', (φ'.sees w).map see = φ.sees (wit w)) {Bk : ProverCoinCounts} {chain ft : Nat}
  {hs : List (Placed V W Y)} {b : Block S Cl}
include hφ

/-- **The second condition with the third family, read through.** -/
theorem SaysYesJ.thru {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid W Y → Env → Prop} {J : S → Prop}
    (h : SaysYesJ φ Bk chain ft hs b fall A J) :
    SaysYesJ φ' Bk chain ft (hs.map (Placed.thru see wit)) b fall
      (fun k s m E => A k s (Mid.narrow wit m) E) J := by
  intro k s m E ds l y cols hA hJ hd hst hf hc hp hcols
  have hv := hφ m.st.input
  rw [chainStopAt_thru see wit _ _ hv] at hst
  obtain ⟨l₀, hb, rfl⟩ := chainSteps_ok_thru see wit hv hc
  have hq := play_thru wit l₀ ds [] m
  rw [hp] at hq
  exact h k s (Mid.narrow wit m) E ds l₀ (playedNarrow wit y) cols hA hJ hd hst hf hb hq.symm hcols

/-- **The third condition read through.** -/
theorem CarriesOn.thru {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid W Y → Env → Prop} {J J' : S → Prop}
    (h : CarriesOn φ Bk chain ft hs b fall A J J') :
    CarriesOn φ' Bk chain ft (hs.map (Placed.thru see wit)) b fall
      (fun k s m E => A k s (Mid.narrow wit m) E) J J' := by
  intro k s m E ds l y cols s' n hA hJ hd hst hf hc hp hcols hstep
  have hv := hφ m.st.input
  rw [chainStopAt_thru see wit _ _ hv] at hst
  obtain ⟨l₀, hb, rfl⟩ := chainSteps_ok_thru see wit hv hc
  have hq := play_thru wit l₀ ds [] m
  rw [hp] at hq
  exact h k s (Mid.narrow wit m) E ds l₀ (playedNarrow wit y) cols s' n hA hJ hd hst hf hb hq.symm
    hcols hstep

end

/-- **The hypotheses with the third family, read through.** Each invariant reads a state as the
prover's side reads it; the falls and the third family stay. -/
def ThreadsCJ.thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w : W₀'} {rc : Rc'} {x : Xi} {k : Coins Bk}
    {R' : Ready W₀' Rc' Xi Ky Tr X₀ X} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : Ready.ReadThrough g rd R' R) (T : ThreadsCJ F Bk H (g w) (rd rc) x k R) :
    ThreadsCJ F Bk (H.thru g rd d) w rc x k R' where
  I₁ := fun j k' s m E => T.I₁ j k' s (Mid.narrow (Local.thru g rd) m) E
  I₂ := fun j k' s m E => T.I₂ j k' s (Mid.narrow (Common.thru g rd) m) E
  I₃ := fun j k' s m E => T.I₃ j k' s (Mid.narrow (Local.thru g rd) m) E
  f₁ := T.f₁
  f₂ := T.f₂
  f₃ := T.f₃
  J₁ := T.J₁
  J₂ := T.J₂
  J₃ := T.J₃
  h₁ := fun j b hb => PlaysOn.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.h₁ j b hb)
  h₂ := fun j b hb => PlaysOn.thru (φ := .shared) (φ' := .shared) id (Common.thru g rd)
    (fun _ => rfl) (T.h₂ j b hb)
  h₃ := fun j b hb => PlaysOn.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.h₃ j b hb)
  y₁ := fun j b hb => SaysYesJ.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.y₁ j b hb)
  y₂ := fun j b hb => SaysYesJ.thru (φ := .shared) (φ' := .shared) id (Common.thru g rd)
    (fun _ => rfl) (T.y₂ j b hb)
  y₃ := fun j b hb => SaysYesJ.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.y₃ j b hb)
  c₁ := fun j b hb => CarriesOn.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.c₁ j b hb)
  c₂ := fun j b hb => CarriesOn.thru (φ := .shared) (φ' := .shared) id (Common.thru g rd)
    (fun _ => rfl) (T.c₂ j b hb)
  c₃ := fun j b hb => CarriesOn.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.c₃ j b hb)
  a₁ := by
    show T.I₁ 0 k (F.start₁ (F.pub x))
      { Mid.narrow (Local.thru g rd) (R'.start₁ (H.thru g rd d)) with opened := some [] }
      (envOf (H.storedWords (g w) (rd rc)) (fun _ _ => none) [])
    rw [Ready.start₁_narrow g rd d H h]
    exact T.a₁
  a₂ := by
    show T.I₂ 0 k (F.start₂ (F.pub x))
      { Mid.narrow (Common.thru g rd) (R'.start₂ (H.thru g rd d)) with opened := some [] }
      (envOf (H.storedWords (g w) (rd rc)) (fun _ _ => none) [])
    rw [Ready.start₂_narrow g rd d H h]
    exact T.a₂
  j₁ := T.j₁
  j₂ := T.j₂
  b₃ := fun e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ i₁ i₂ hs p₁ p₂ => by
    have hi := T.b₃ e₁ (Mid.narrow (Local.thru g rd) m₁) E₁ e₂
      (Mid.narrow (Common.thru g rd) m₂) E₂ s₃ o₁ o₂ i₁ i₂ hs p₁ p₂
    show T.I₃ 0 k s₃
      { Mid.narrow (Local.thru g rd) (R'.start₃ (H.thru g rd d) m₁ m₂) with
        opened := some (o₁ ++ o₂) } (envThird E₁ E₂)
    rw [Ready.start₃_narrow g rd d H h m₁ m₂]
    exact hi
  d₃ := fun e₁ m₁ E₁ e₂ m₂ E₂ i₁ i₂ j₁ j₂ => T.d₃ e₁ _ E₁ e₂ _ E₂ i₁ i₂ j₁ j₂
  j₃ := T.j₃
  fin := fun e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ i₁ i₂ i₃ j₁ j₂ j₃ =>
    T.fin e₁ _ E₁ e₂ _ E₂ e₃ _ E₃ i₁ i₂ i₃ j₁ j₂ j₃

/-- **The same at other columns that show the same words.** -/
def ThreadsCJ.withStored {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F))
    (hs : (H.withStored s).storedWords w rc = H.storedWords w rc)
    (T : ThreadsCJ F Bk H w rc x k R) : ThreadsCJ F Bk (H.withStored s) w rc x k R where
  I₁ := T.I₁
  I₂ := T.I₂
  I₃ := T.I₃
  f₁ := T.f₁
  f₂ := T.f₂
  f₃ := T.f₃
  J₁ := T.J₁
  J₂ := T.J₂
  J₃ := T.J₃
  h₁ := T.h₁
  h₂ := T.h₂
  h₃ := T.h₃
  y₁ := T.y₁
  y₂ := T.y₂
  y₃ := T.y₃
  c₁ := T.c₁
  c₂ := T.c₂
  c₃ := T.c₃
  a₁ := by
    rw [hs]
    exact T.a₁
  a₂ := by
    rw [hs]
    exact T.a₂
  j₁ := T.j₁
  j₂ := T.j₂
  b₃ := T.b₃
  d₃ := T.d₃
  j₃ := T.j₃
  fin := T.fin

/-- **At the rows' prover: ready returns, the plan serves, and there is a value of ThreadsCJ with
the same falls**, from the same at the prover that is read through. -/
theorem rows_of_thruJ (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀' Rc' Ky Tr X₀ X) (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (k : Coins Bk)
    (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
    (hs : CommittedColumns Cm item₀ H g rd w rc) {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H (g w) (rd rc) x k = .ok R) (P : PlanServes H (g w) (rd rc) R)
    (T : ThreadsCJ F Bk H (g w) (rd rc) x k R) :
    ∃ R', ready F Bk (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x k = .ok R' ∧
      PlanServes (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc R' ∧
      ∃ T' : ThreadsCJ F Bk (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x k R',
        T'.f₁ = T.f₁ ∧ T'.f₂ = T.f₂ ∧ T'.f₃ = T.f₃ := by
  have hw : ((H.thru g rd d).withStored (Cm.columnsAt item₀)).storedWords w rc =
      (H.thru g rd d).storedWords w rc := by
    funext it p
    exact hs it p
  have hr := Ready.reads_thru g rd hR
  have e := rows_prover_eq G Cm item₀ (H.thru g rd d) hrows hk
  have r₁ : ready F Bk ((H.thru g rd d).withStored (Cm.columnsAt item₀)) w rc x k =
      .ok (Ready.thru g rd w rc R) := by
    rw [ready_withStored, ready_thru g rd d F Bk H w rc x k hd, hR]
    rfl
  rw [e]
  exact ⟨_, r₁, (P.thru g rd d hr).withStored _ hw,
    (T.thru g rd d hr).withStored _ hw, rfl, rfl, rfl⟩

/-- **rows_of_thruJ with the value's invariants named**: they are the base's, read through. -/
theorem rows_of_thruJ_named (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀' Rc' Ky Tr X₀ X) (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (k : Coins Bk)
    (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
    (hs : CommittedColumns Cm item₀ H g rd w rc) {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H (g w) (rd rc) x k = .ok R) (P : PlanServes H (g w) (rd rc) R)
    (T : ThreadsCJ F Bk H (g w) (rd rc) x k R) :
    ∃ R', ready F Bk (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x k = .ok R' ∧
      PlanServes (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc R' ∧
      ∃ T' : ThreadsCJ F Bk (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x k R',
        T'.f₁ = T.f₁ ∧ T'.f₂ = T.f₂ ∧ T'.f₃ = T.f₃ ∧
        T'.I₁ = (fun j k' s m E => T.I₁ j k' s (Mid.narrow (Local.thru g rd) m) E) ∧
        T'.I₂ = (fun j k' s m E => T.I₂ j k' s (Mid.narrow (Common.thru g rd) m) E) ∧
        T'.I₃ = (fun j k' s m E => T.I₃ j k' s (Mid.narrow (Local.thru g rd) m) E) := by
  have hw : ((H.thru g rd d).withStored (Cm.columnsAt item₀)).storedWords w rc =
      (H.thru g rd d).storedWords w rc := by
    funext it p
    exact hs it p
  have hr := Ready.reads_thru g rd hR
  have e := rows_prover_eq G Cm item₀ (H.thru g rd d) hrows hk
  have r₁ : ready F Bk ((H.thru g rd d).withStored (Cm.columnsAt item₀)) w rc x k =
      .ok (Ready.thru g rd w rc R) := by
    rw [ready_withStored, ready_thru g rd d F Bk H w rc x k hd, hR]
    rfl
  rw [e]
  exact ⟨_, r₁, (P.thru g rd d hr).withStored _ hw,
    (T.thru g rd d hr).withStored _ hw, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.SaysYesJ.thru
#print axioms ProofFile.Honest.CarriesOn.thru
#print axioms ProofFile.Honest.ThreadsCJ.thru
#print axioms ProofFile.Honest.ThreadsCJ.withStored
#print axioms ProofFile.Honest.rows_of_thruJ
#print axioms ProofFile.Honest.rows_of_thruJ_named
