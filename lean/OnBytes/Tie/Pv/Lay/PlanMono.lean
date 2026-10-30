-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lay/PlanMono.lean: the planner's routines for a layers' sub-proof only add rounds,
and how many; the planner's routine for the sub-proof's own rounds, cut at the row products'
stretch.

Main names:
  `Good s n x`: from a state with no open message the routine x leaves such a state and adds n
    rounds.
  `Mono x`: the routine x keeps the rounds that were there.
  `mono_*`, `good_*`: these two of the planner's routines, one by one.
  `ownBefore`, `afterOwn`, `own_eq`: Params.planLayerOwn written as what comes before the row
    products' stretch, that stretch, and what comes after.
  `planLayerOwn_stretch`: in whatever planLayerOwn returns, the rounds from place ownBefore on are
    the stretch's list of OnBytes/Tie/Pv/Lay/PlanAt.lean.

Limits: as in OnBytes/Tie/Pv/Lay/PlanAt.lean.

-/
import OnBytes.Tie.Pv.Lay.PlanAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay

open OnBytes OnBytes.Params

/-- x, from a state at which no message is open, leaves such a state and adds just n rounds -/
def Good (s : Setting) (n : Nat) (x : Planning Unit) : Prop :=
  ∀ p q, At s 0 p → x p = .ok ((), q) →
    At s 0 q ∧ ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧ l.length = n

/-- x only adds rounds -/
def Mono {α : Type} (x : Planning α) : Prop :=
  ∀ p a q, x p = .ok (a, q) → ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray

theorem bind_ok' {α β : Type} {x : Planning α} {f : α → Planning β} {p q : PlanState} {b : β}
    (h : (x >>= f) p = .ok (b, q)) : ∃ a m, x p = .ok (a, m) ∧ f a m = .ok (b, q) := by
  have h' : (match x p with | .ok (a, m) => f a m | .error e => .error e) = .ok (b, q) := by
    rw [← h]
    show _ = (x p >>= fun y => f y.1 y.2)
    cases x p <;> rfl
  cases hx : x p with
  | error e => rw [hx] at h'; exact absurd h' (by simp)
  | ok y => rw [hx] at h'; exact ⟨y.1, y.2, rfl, h'⟩

theorem Good.bind {s : Setting} {n m : Nat} {x y : Planning Unit} (hx : Good s n x) (hy : Good s m
    y) :
    Good s (n + m) (x >>= fun _ => y) := fun p q hp h => by
  obtain ⟨_, r, h1, h2⟩ := bind_ok h
  obtain ⟨a1, l1, e1, c1⟩ := hx p r hp h1
  obtain ⟨a2, l2, e2, c2⟩ := hy r q a1 h2
  exact ⟨a2, l1 ++ l2, by rw [e2, e1]; simp, by rw [List.length_append, c1, c2]⟩

theorem Good.pure (s : Setting) : Good s 0 (pure ()) := fun p q hp h => by
  obtain rfl : p = q := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨hp, [], by simp, rfl⟩

theorem Mono.bind {α β : Type} {x : Planning α} {f : α → Planning β} (hx : Mono x) (hf : ∀ a, Mono
    (f a)) :
    Mono (x >>= f) := fun p b q h => by
  obtain ⟨a, r, h1, h2⟩ := bind_ok' h
  obtain ⟨l1, e1⟩ := hx p a r h1
  obtain ⟨l2, e2⟩ := hf a r b q h2
  exact ⟨l1 ++ l2, by rw [e2, e1]; simp⟩

theorem Mono.pure {α : Type} (a : α) : Mono (pure a : Planning α) := fun p b q h => by
  obtain rfl : p = q := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨[], by simp⟩

theorem Mono.ite {α : Type} {c : Prop} [Decidable c] {x y : Planning α} (hx : Mono x) (hy : Mono y)
    :
    Mono (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem mono_setting : Mono theSetting := fun p a q h => by
  obtain rfl : p = q := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨[], by simp⟩

theorem mono_scalars (n : Nat) : Mono (planScalars n) := fun p a q h => by
  obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
  exact ⟨[], by simp⟩

theorem push_app {α : Type} (a : Array α) (r : α) : a.push r = a ++ [r].toArray := by simp

theorem mono_close (name : String) (why : ErrorKind) (e : Bound) (d : Draws) : Mono (close name why
    e d) :=
  fun p a q h => by
    unfold close at h
    simp only at h
    split at h
    · split at h
      · cases h
      · obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
        exact ⟨_, push_app _ _⟩
    · split at h
      · cases h
      · obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
        exact ⟨_, push_app _ _⟩

theorem mono_none (name : String) : Mono (closeNone name) := fun p a q h => by
  unfold closeNone at h
  split at h
  · cases h
  · obtain rfl := (Prod.mk.inj (Except.ok.inj h)).2
    exact ⟨_, push_app _ _⟩

theorem mono_rounds (s : Setting) : ∀ g : List Nat, Mono (planPscRounds s g)
  | [] => Mono.pure ()
  | _ :: gs => Mono.bind (mono_scalars _) fun _ => Mono.bind (mono_close _ _ _ _) fun _ =>
      mono_rounds s gs

theorem mono_psc (x : PscSize) : Mono (planPsc x) :=
  Mono.bind mono_setting fun s => Mono.bind (mono_scalars _) fun _ => Mono.bind (mono_close _ _ _
      _) fun _ =>
    Mono.bind (mono_rounds s _) fun _ => Mono.ite
      (Mono.bind (mono_scalars _) fun _ => Mono.bind (mono_close _ _ _ _) fun _ =>
        Mono.bind (mono_scalars _) fun _ => mono_none _)
      (Mono.pure _)

theorem mono_bat (rows : Nat) : Mono (planBatSigma rows) :=
  Mono.bind mono_setting fun _ => mono_close _ _ _ _

theorem mono_line : Mono planLine := Mono.bind mono_setting fun _ => mono_close _ _ _ _
theorem mono_join (v : Nat) : Mono (planJoin v) := Mono.bind mono_setting fun _ => mono_close _ _ _
    _
theorem mono_layer (v : Nat) : Mono (planProductLayer v) := Mono.bind (mono_psc _) fun _ =>
    mono_line
theorem mono_token (lt dy sh : Nat) : Mono (planTokenSumcheck lt dy sh) :=
  Mono.bind (mono_scalars _) fun _ => mono_psc _

/-- a round that reads the setting and closes, with b bytes open -/
theorem good_close {s : Setting} (k : Nat) (name : String) (e : Setting → Bound) (d : Draws) :
    Good s 1 (planScalars k >>= fun _ => theSetting >>= fun s' => close name .field (e s') d) :=
  fun p q hp h => by
    obtain ⟨_, m1, h1, k1⟩ := bind_ok h
    obtain ⟨n1, e1, a1, r1⟩ := scalars_at hp k
    rw [e1] at h1
    obtain rfl : n1 = m1 := (Prod.mk.inj (Except.ok.inj h1)).2
    obtain ⟨s2, m2, g2, h2⟩ := bind_ok k1
    obtain ⟨rfl, rfl⟩ : n1.set = s2 ∧ n1 = m2 := Prod.mk.inj (Except.ok.inj g2)
    obtain ⟨a2, x2, er2, _⟩ := close_at a1 _ _ _ h2
    exact ⟨a2, [x2], by rw [er2, r1]; simp, rfl⟩

theorem good_close0 {s : Setting} (name : String) (e : Setting → Bound) (d : Draws) :
    Good s 1 (theSetting >>= fun s' => close name .field (e s') d) :=
  fun p q hp h => by
    obtain ⟨s2, m2, g2, h2⟩ := bind_ok h
    obtain ⟨rfl, rfl⟩ : p.set = s2 ∧ p = m2 := Prod.mk.inj (Except.ok.inj g2)
    obtain ⟨a2, x2, er2, _⟩ := close_at hp _ _ _ h2
    exact ⟨a2, [x2], by rw [er2]; simp, rfl⟩

/-- a product layer on v variables: v + 4 rounds -/
theorem good_layer {s : Setting} (v : Nat) : Good s (v + 4) (planProductLayer v) := fun p q hp h =>
    by
  obtain ⟨_, mA, hA, hB⟩ := bind_ok (x := planPsc
      { degree := List.replicate v 3, degreeY := 2, values := 2 })
    (f := fun _ => planLine) h
  have h' : (theSetting >>= fun s' =>
      planScalars 1 >>= fun _ =>
      close "PSC epsilon" .field (fieldError s' 1) { drawE := 1, priced := .settingAlone } >>= fun
          _ =>
      planPscRounds s' (List.replicate v 3) >>= fun _ =>
      planScalars 2 >>= fun _ =>
      close "PSC Y" .field (fieldErrorNonzero s' 2)
          { drawE := 1, drawNZ := 1, priced := .roundItself } >>= fun _ =>
      planScalars 2 >>= fun _ =>
      closeNone "PSC values") p = .ok ((), mA) := hA
  obtain ⟨s4, m4, g4, k4⟩ := bind_ok h'
  obtain ⟨rfl, rfl⟩ : p.set = s4 ∧ p = m4 := Prod.mk.inj (Except.ok.inj g4)
  obtain ⟨_, m5, h5, k5⟩ := bind_ok k4
  obtain ⟨n5, e5, a5, r5⟩ := scalars_at hp 1
  rw [e5] at h5
  obtain rfl : n5 = m5 := (Prod.mk.inj (Except.ok.inj h5)).2
  obtain ⟨_, m6, h6, k6⟩ := bind_ok k5
  obtain ⟨a6, x6, er6, _⟩ := close_at a5 _ _ _ h6
  obtain ⟨_, m7, h7, k7⟩ := bind_ok k6
  rw [hp.set] at h7
  obtain ⟨a7, l7, el7, sl7⟩ := rounds_at v a6 h7
  obtain ⟨_, m8, h8, k8⟩ := bind_ok k7
  obtain ⟨n8, e8, a8, r8⟩ := scalars_at a7 2
  rw [e8] at h8
  obtain rfl : n8 = m8 := (Prod.mk.inj (Except.ok.inj h8)).2
  obtain ⟨_, m9, h9, k9⟩ := bind_ok k8
  obtain ⟨a9, x9, er9, _⟩ := close_at a8 _ _ _ h9
  obtain ⟨_, m10, h10, k10⟩ := bind_ok k9
  obtain ⟨n10, e10, a10, r10⟩ := scalars_at a9 2
  rw [e10] at h10
  obtain rfl : n10 = m10 := (Prod.mk.inj (Except.ok.inj h10)).2
  obtain ⟨a11, x11, er11, _⟩ := none_at a10 _ k10
  obtain ⟨a12, l12, el12, c12⟩ := good_close0 (s := s) "LINE" (fun s' => fieldError s' 1)
    { drawE := 1, priced := .settingAlone } mA q a11 hB
  have c7 : l7.length = v := by
    have := congrArg List.length sl7
    simpa using this
  refine ⟨a12, [x6] ++ l7 ++ [x9, x11] ++ l12, ?_, ?_⟩
  · rw [el12, er11, r10, er9, r8, el7, er6, r5]
    simp
  · simp [c7, c12]

/-- the rounds of planLayerOwn before the stretch -/
def ownBefore (x : LayerRounds) : Nat :=
  1 + (if x.firstGroup then 2 else 0) + 1 + (if x.lNI != 0 then 1 else 0) + (x.lNI + x.lPd + x.lt +
      4)

/-- what follows the stretch in planLayerOwn: ITS TEXT (SubRounds.lean:151-162), copied; own_eq
below holds the copy to the planner's routine -/
def afterOwn (x : LayerRounds) : Planning Unit := do
  if x.withTerms then
    planTokenSumcheck x.lt 1 x.shownByTheTerms
    planBatSigma 2
  planPsc { degree := List.replicate x.lamS 3, degreeY := 2,
            values := 2 + x.neverSent + x.weightClaims }
  planProductLayer (x.ll + x.lPf + x.lt)
  if x.routed then
    if 1 < x.ll then planJoin (x.ll - 1)
    planProductLayer (x.ll - 1 + x.lfe + x.lt)
  if x.firstGroup then planScalars 1
  planBatSigma (x.weightClaims + (if x.firstGroup then 1 else 0))
  planPsc { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 }

theorem after_eq (x : LayerRounds) : afterOwn x =
    ((if x.withTerms then (planTokenSumcheck x.lt 1 x.shownByTheTerms >>= fun _ => planBatSigma 2)
        else pure ()) >>= fun _ =>
     planPsc { degree := List.replicate x.lamS 3, degreeY := 2,
               values := 2 + x.neverSent + x.weightClaims } >>= fun _ =>
     planProductLayer (x.ll + x.lPf + x.lt) >>= fun _ =>
     (if x.routed then ((if 1 < x.ll then planJoin (x.ll - 1) else pure ()) >>= fun _ =>
        planProductLayer (x.ll - 1 + x.lfe + x.lt)) else pure ()) >>= fun _ =>
     (if x.firstGroup then planScalars 1 else pure ()) >>= fun _ =>
     planBatSigma (x.weightClaims + (if x.firstGroup then 1 else 0)) >>= fun _ =>
     planPsc { degree := List.replicate x.lkW 3, degreeY := 1, values := 1 }) := by
  unfold afterOwn
  by_cases h1 : x.withTerms = true <;> by_cases h2 : x.routed = true <;> by_cases h3 : 1 < x.ll <;>
    by_cases h4 : x.firstGroup = true <;>
    simp only [h1, h2, h3, h4, ↓reduceIte, bind_assoc, pure_bind, Bool.false_eq_true]

theorem mono_after (x : LayerRounds) : Mono (afterOwn x) := by
  rw [after_eq]
  exact
    Mono.bind (Mono.ite (Mono.bind (mono_token _ _ _) fun _ => mono_bat _) (Mono.pure _)) fun _ =>
    Mono.bind (mono_psc _) fun _ => Mono.bind (mono_layer _) fun _ =>
    Mono.bind (Mono.ite (Mono.bind (Mono.ite (mono_join _) (Mono.pure _)) fun _ => mono_layer _)
        (Mono.pure _)) fun _ =>
    Mono.bind (Mono.ite (mono_scalars _) (Mono.pure _)) fun _ => Mono.bind (mono_bat _) fun _ =>
        mono_psc _

/-- planLayerOwn, with its two first conditions laid flat: THE PORT's OWN ROUTINE IS THIS CHAIN. -/
theorem own_eq (x : LayerRounds) : planLayerOwn x =
    (planZero x.lt >>= fun _ =>
     (if x.firstGroup then (planZero (x.ls + x.lt) >>= fun _ => planZero (x.lPd - x.ls)) else pure
         ()) >>= fun _ =>
     planScalars (x.NS * x.NI) >>= fun _ =>
     planBatSigma x.NS >>= fun _ =>
     (if x.lNI != 0 then planJoin x.lNI else pure ()) >>= fun _ =>
     planProductLayer (x.lNI + x.lPd + x.lt) >>= fun _ =>
     planScalars (x.NP * x.NI) >>= fun _ =>
     planBatSigma (x.NP * x.NI) >>= fun _ =>
     planTokenSumcheck x.lt 2 (x.NO * x.NI) >>= fun _ =>
     afterOwn x) := by
  unfold planLayerOwn afterOwn
  by_cases h1 : x.firstGroup = true <;> by_cases h2 : (x.lNI != 0) = true <;>
    simp only [h1, h2, ↓reduceIte, bind_assoc, pure_bind, Bool.false_eq_true]

/-- THE STRETCH STANDS IN THE PORT's OWN planLayerOwn, behind ownBefore x rounds. -/
theorem planLayerOwn_stretch (s : Setting) (x : LayerRounds) (p q : PlanState) (hp : At s 0 p)
    (h : planLayerOwn x p = .ok ((), q)) :
    ∃ before l after : List PlanRound, q.rounds = p.rounds ++ (before ++ l ++ after).toArray ∧
      before.length = ownBefore x ∧
      l.map shapeOf = stretch (s.workOf .field .request) x.lt x.NI x.NP x.NO := by
  rw [own_eq] at h
  -- the norms' token point
  obtain ⟨_, m1, h1, k1⟩ := bind_ok h
  obtain ⟨a1, l1, e1, c1⟩ := good_close0 (s := s) "ZERO" (fun s' => fieldError s' x.lt)
    { drawE := x.lt, priced := .roundItself } p m1 hp h1
  -- the first group's two points
  obtain ⟨_, m2, h2, k2⟩ := bind_ok k1
  have g2 : Good s (if x.firstGroup then 2 else 0)
      (if x.firstGroup then (planZero (x.ls + x.lt) >>= fun _ => planZero (x.lPd - x.ls)) else pure
          ()) := by
    split
    · exact Good.bind (good_close0 "ZERO" (fun s' => fieldError s' (x.ls + x.lt)) _)
        (good_close0 "ZERO" (fun s' => fieldError s' (x.lPd - x.ls)) _)
    · exact Good.pure s
  obtain ⟨a2, l2, e2, c2⟩ := g2 m1 m2 a1 h2
  -- the limbs' slots and batch
  obtain ⟨_, m3, h3, k3⟩ := bind_ok k2
  obtain ⟨_, m4, h4, k4⟩ := bind_ok k3
  have g4 : (planScalars (x.NS * x.NI) >>= fun _ => theSetting >>= fun s' =>
      close "BAT-sigma" .field (powersError s' x.NS)
          { drawE := 1, rows := x.NS, priced := .asSaid }) m2 =
      .ok ((), m4) := by
    show (planScalars (x.NS * x.NI) m2 >>= fun y => planBatSigma x.NS y.2) = _
    rw [h3]
    exact h4
  obtain ⟨a4, l4, e4, c4⟩ := good_close (s := s) _ _ (fun s' => powersError s' x.NS) _ m2 m4 a2 g4
  -- the join over the norm instances
  obtain ⟨_, m5, h5, k5⟩ := bind_ok k4
  have g5 : Good s (if x.lNI != 0 then 1 else 0) (if x.lNI != 0 then planJoin x.lNI else pure ())
      := by
    split
    · exact good_close0 "JOIN" (fun s' => fieldError s' x.lNI) _
    · exact Good.pure s
  obtain ⟨a5, l5, e5, c5⟩ := g5 m4 m5 a4 h5
  -- the product layer of the squares
  obtain ⟨_, m6, h6, k6⟩ := bind_ok k5
  obtain ⟨a6, l6, e6, c6⟩ := good_layer (s := s) _ m5 m6 a5 h6
  -- the stretch: its three lines, then the rest
  obtain ⟨_, m7, h7, k7⟩ := bind_ok k6
  obtain ⟨_, m8, h8, k8⟩ := bind_ok k7
  obtain ⟨_, m9, h9, k9⟩ := bind_ok k8
  have g9 : rowProductsL x.lt x.NI x.NP x.NO m6 = .ok ((), m9) := by
    show (planScalars (x.NP * x.NI) m6 >>= fun y =>
      (planBatSigma (x.NP * x.NI) y.2 >>= fun z => planTokenSumcheck x.lt 2 (x.NO * x.NI) z.2)) = _
    rw [h7]
    show (planBatSigma (x.NP * x.NI) m7 >>= fun z => planTokenSumcheck x.lt 2 (x.NO * x.NI) z.2) = _
    rw [h8]
    exact h9
  obtain ⟨_, l9, e9, s9⟩ := rowProducts_at x.lt x.NI x.NP x.NO a6 g9
  obtain ⟨l10, e10⟩ := mono_after x m9 () q k9
  refine ⟨l1 ++ l2 ++ l4 ++ l5 ++ l6, l9, l10, ?_, ?_, s9⟩
  · rw [e10, e9, e6, e5, e4, e2, e1]
    simp
  · simp only [List.length_append, c1, c2, c4, c5, c6, ownBefore]

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.own_eq
#print axioms OnBytes.Tie.Pv.Lay.planLayerOwn_stretch
