-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruThreads.lean: NOT IN FRONT OF A LAW OVER COINS.
The hypotheses of the rules on a run (PlaysOn, SaysYes, Honest/Law/ThreadC.lean; ThreadsC,
Honest/Law/ThreadStratC.lean; PlanServes, Honest/Law/RunsFile.lean) go over from a prover to the
prover read through (Honest/ThruRun.lean), and to the rows' prover with a committer's columns
(Honest/ThruRows.lean): an invariant at the prover read through is the invariant at the state as
the prover's side reads it. So what is stated at the filling's prover, with the index a letter, is
carried once for all kinds: assembled there, it crosses whole by ThreadsC.thru and rows_of_thru. A
Thread does not cross. At the term g is the identity: a law stated at fullIn is not carried.

  play_thru            a stretch of rounds read through; playedNarrow is how its result is read
  PlaysOn.thru, SaysYes.thru   the two conditions on a sub-protocol
  ChainServes.thru, PlanServes.thru   what the plan declares of the rounds
  ThreadsC.thru        the invariants, the falls and the starts
  ThreadsC.withStored, PlanServes.withStored   the like at other columns with the same words
  rows_of_thru         at the rows' prover: ready returns, the plan serves and there is a value of
                       ThreadsC with the same falls

By what. Step.tell_thru, Step.hear_thru, chainSteps_thru, chainStopAt_thru, Ready.start₁_narrow and
its two sisters (Honest/ThruRun.lean); rows_prover_eq, CommittedColumns (Honest/ThruRows.lean).

Limits.
  * Every statement here takes a ThreadsC or a PlaysOn as a premise or gives one as its end. None of
    them is a law over coins, and none may stand in front of one: a value of ThreadsC speaks of one
    run's coins and, through its invariants, of whatever they say.
  * The invariants are read through narrow: nothing is said on what they hold of a state that no
    run reaches.
  * rows_of_thru takes the rows' equation, the key's and CommittedColumns as premises.
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruRows
import Johnson.Desc.ProofFile.Honest.Law.ThreadStratC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription)

variable {S Cl Xi V V' W W' Y Pb W₀ W₀' Rc Rc' Ky Tr X₀ X Sd Xc : Type}

/-! ## 1 A stretch of rounds -/

/-- What a stretch of rounds returns, as the prover's side reads it. -/
def playedNarrow (wit : W' → W) (y : List Played × Mid W' Y) : List Played × Mid W Y :=
  (y.1, Mid.narrow wit y.2)

/-- **A stretch of rounds read through.** -/
theorem play_thru (wit : W' → W) (ss : List (Step W Y)) :
    ∀ (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W' Y),
      (play (ss.map (Step.thru wit)) ds back m).map (playedNarrow wit) =
        play ss ds back (Mid.narrow wit m) := by
  induction ss with
  | nil =>
    intro ds back m
    cases ds <;> rfl
  | cons s ss ih =>
    intro ds back m
    cases ds with
    | nil => rfl
    | cons d ds =>
      show Except.map (playedNarrow wit) (((s.thru wit).tell back.head? m).bind _) =
        (s.tell back.head? (Mid.narrow wit m)).bind _
      rw [Step.tell_thru]
      cases s.tell back.head? (Mid.narrow wit m) with
      | error e => rfl
      | ok x =>
        show Except.map (playedNarrow wit) (((s.thru wit).hear x d m).bind fun m' =>
            (play (ss.map (Step.thru wit)) ds back.tail m').map _) =
          (s.hear x d (Mid.narrow wit m)).bind fun m' => (play ss ds back.tail m').map _
        rw [← Step.hear_thru wit s x d m]
        cases (s.thru wit).hear x d m with
        | error e => rfl
        | ok m' =>
          show Except.map (playedNarrow wit)
              (Except.map _ (play (ss.map (Step.thru wit)) ds back.tail m')) =
            Except.map _ (play ss ds back.tail (Mid.narrow wit m'))
          rw [← ih ds back.tail m']
          cases play (ss.map (Step.thru wit)) ds back.tail m' with
          | error e => rfl
          | ok y => rfl

/-- Where a chain's rounds read through come back, the rounds do, and they are read through. -/
theorem chainSteps_ok_thru (see : V' → V) (wit : W' → W) {Bk : ProverCoinCounts} {rows : List (Addr × Due)}
    {look : Addr → (d : Due) × Cs d} {v : Option V} {v' : Option V'} (hv : v'.map see = v)
    {bs : List (Block S Cl)} {hs : List (Placed V W Y)} {l : List (Step W' Y)}
    (hc : chainSteps Bk rows look v' bs (hs.map (Placed.thru see wit)) = .ok l) :
    ∃ l₀, chainSteps Bk rows look v bs hs = .ok l₀ ∧ l₀.map (Step.thru wit) = l := by
  rw [chainSteps_thru see wit Bk rows look v v' hv bs hs] at hc
  cases hb : chainSteps Bk rows look v bs hs with
  | error e =>
    rw [hb] at hc
    have h' : (Except.error e : Except String (List (Step W' Y))) = .ok l := hc
    cases h'
  | ok l₀ =>
    rw [hb] at hc
    exact ⟨l₀, rfl, Except.ok.inj hc⟩

/-! ## 2 The two conditions on a sub-protocol -/

section
variable (see : V' → V) (wit : W' → W) {φ : Face V W Pb} {φ' : Face V' W' Pb}
  (hφ : ∀ w : W', (φ'.sees w).map see = φ.sees (wit w)) {Bk : ProverCoinCounts} {chain ft : Nat}
  {hs : List (Placed V W Y)} {b : Block S Cl}
include hφ

/-- **The first condition read through.** -/
theorem PlaysOn.thru {A B : Coins Bk → S → Mid W Y → Env → Prop}
    (h : PlaysOn φ Bk chain ft hs b A B) :
    PlaysOn φ' Bk chain ft (hs.map (Placed.thru see wit)) b
      (fun k s m E => A k s (Mid.narrow wit m) E)
      (fun k s m E => B k s (Mid.narrow wit m) E) := by
  intro k s m E ds l hA hd hst hc
  have hv := hφ m.st.input
  rw [chainStopAt_thru see wit _ _ hv] at hst
  obtain ⟨l₀, hb, rfl⟩ := chainSteps_ok_thru see wit hv hc
  obtain ⟨y, cols, hy, hcols, hB⟩ := h k s (Mid.narrow wit m) E ds l₀ hA hd hst hb
  have hp := play_thru wit l₀ ds [] m
  rw [hy] at hp
  cases hq : play (l₀.map (Step.thru wit)) ds [] m with
  | error e =>
    rw [hq] at hp
    have h' : (Except.error e : Except Refusal (List Played × Mid W Y)) = .ok y := hp
    cases h'
  | ok y' =>
    rw [hq] at hp
    have hyy : playedNarrow wit y' = y := Except.ok.inj hp
    subst hyy
    exact ⟨y', cols, rfl, hcols, fun s' n e => hB s' n e⟩

/-- **The second condition read through.** -/
theorem SaysYes.thru {fall : S → List Fmt.Drawn → Option String}
    {A : Coins Bk → S → Mid W Y → Env → Prop} (h : SaysYes φ Bk chain ft hs b fall A) :
    SaysYes φ' Bk chain ft (hs.map (Placed.thru see wit)) b fall
      (fun k s m E => A k s (Mid.narrow wit m) E) := by
  intro k s m E ds l y cols hA hd hst hf hc hp hcols
  have hv := hφ m.st.input
  rw [chainStopAt_thru see wit _ _ hv] at hst
  obtain ⟨l₀, hb, rfl⟩ := chainSteps_ok_thru see wit hv hc
  have hq := play_thru wit l₀ ds [] m
  rw [hp] at hq
  exact h k s (Mid.narrow wit m) E ds l₀ (playedNarrow wit y) cols hA hd hst hf hb hq.symm hcols

end

/-! ## 3 What the plan declares -/

section
variable (wit : W' → W)

/-- A round's move read through is there where the move is. -/
theorem move_thru_isSome (s : Step W Y) : (s.thru wit).move.isSome = s.move.isSome := by
  show (s.move.map _).isSome = s.move.isSome
  cases s.move <;> rfl

/-- The oracle messages of rounds read through. -/
theorem oracles_thru : ∀ l : List (Step W Y),
    (l.map (Step.thru wit)).flatMap (·.oracles) = l.flatMap (·.oracles)
  | [] => rfl
  | s :: l => by
    show s.oracles ++ (l.map (Step.thru wit)).flatMap (·.oracles) =
      s.oracles ++ l.flatMap (·.oracles)
    rw [oracles_thru l]

/-- The same of the first rounds. -/
theorem oracles_take_thru : ∀ (l : List (Step W Y)) (n : Nat),
    ((l.map (Step.thru wit)).take n).flatMap (·.oracles) = (l.take n).flatMap (·.oracles)
  | [], n => by cases n <;> rfl
  | _ :: _, 0 => rfl
  | s :: l, n + 1 => by
    show s.oracles ++ ((l.map (Step.thru wit)).take n).flatMap (·.oracles) =
      s.oracles ++ (l.take n).flatMap (·.oracles)
    rw [oracles_take_thru l n]

/-- **What the plan declares of a chain's rounds, read through.** -/
theorem ChainServes.thru {stored : Nat → Nat → Option (List UInt64)} {l : List (Step W Y)}
    (h : ChainServes stored l) : ChainServes stored (l.map (Step.thru wit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
    exact h.shaped s hs
  · intro u hu e
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
    rw [move_thru_isSome] at e
    exact h.noRoot s hs e
  · intro u hu e
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
    rw [move_thru_isSome] at e
    exact h.part0 s hs e
  · intro r u hr o ho n hn
    rw [List.getElem?_map] at hr
    cases hh : l[r]? with
    | none =>
      rw [hh] at hr
      have h' : (none : Option (Step W' Y)) = some u := hr
      cases h'
    | some s =>
      rw [hh] at hr
      have e : s.thru wit = u := Option.some.inj hr
      subst e
      obtain ⟨orc, h1, h2⟩ := h.inTime r s hh o ho n hn
      exact ⟨orc, by rw [oracles_take_thru]; exact h1, h2⟩
  · intro u hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
    exact h.stored s hs

end

/-- **What the plan declares of a prepared run, read through.** -/
theorem PlanServes.thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {w : W₀'} {rc : Rc'} {R' : Ready W₀' Rc' Xi Ky Tr X₀ X} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : Ready.ReadThrough g rd R' R) (P : PlanServes H (g w) (rd rc) R) :
    PlanServes (H.thru g rd d) w rc R' := by
  have e₁ := h.first
  have e₂ := h.shared
  have e₃ := h.second
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e₁]
    exact P.first.thru _
  · rw [e₂]
    exact P.shared.thru _
  · rw [e₃]
    exact P.second.thru _
  · intro u hu
    rw [e₁] at hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
    exact P.own₁ s hs
  · intro u hu
    rw [e₂] at hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
    exact P.own₂ s hs
  · intro u hu o ho ch j e
    rw [e₃] at hu
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hu
    rcases P.taken s hs o ho ch j e with ⟨c, orc, h1, h2⟩ | ⟨c, orc, h1, h2⟩
    · exact .inl ⟨c, orc, by rw [e₁, oracles_thru]; exact h1, h2⟩
    · exact .inr ⟨c, orc, by rw [e₂, oracles_thru]; exact h1, h2⟩

/-! ## 4 The invariants of a run -/

/-- **The hypotheses of the rules on a run, read through.** Each invariant reads a state as the
prover's side reads it; the falls stay. -/
def ThreadsC.thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w : W₀'} {rc : Rc'} {x : Xi} {k : Coins Bk}
    {R' : Ready W₀' Rc' Xi Ky Tr X₀ X} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (h : Ready.ReadThrough g rd R' R) (T : ThreadsC F Bk H (g w) (rd rc) x k R) :
    ThreadsC F Bk (H.thru g rd d) w rc x k R' where
  I₁ := fun j k' s m E => T.I₁ j k' s (Mid.narrow (Local.thru g rd) m) E
  I₂ := fun j k' s m E => T.I₂ j k' s (Mid.narrow (Common.thru g rd) m) E
  I₃ := fun j k' s m E => T.I₃ j k' s (Mid.narrow (Local.thru g rd) m) E
  f₁ := T.f₁
  f₂ := T.f₂
  f₃ := T.f₃
  h₁ := fun j b hb => PlaysOn.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.h₁ j b hb)
  h₂ := fun j b hb => PlaysOn.thru (φ := .shared) (φ' := .shared) id (Common.thru g rd)
    (fun _ => rfl) (T.h₂ j b hb)
  h₃ := fun j b hb => PlaysOn.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.h₃ j b hb)
  y₁ := fun j b hb => SaysYes.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.y₁ j b hb)
  y₂ := fun j b hb => SaysYes.thru (φ := .shared) (φ' := .shared) id (Common.thru g rd)
    (fun _ => rfl) (T.y₂ j b hb)
  y₃ := fun j b hb => SaysYes.thru (φ := .own) (φ' := .own) (Local.thru g rd) (Local.thru g rd)
    (fun _ => rfl) (T.y₃ j b hb)
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
  a₃ := fun e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ i₁ i₂ j₁ j₂ => by
    obtain ⟨s₃, hs, hi⟩ := T.a₃ e₁ (Mid.narrow (Local.thru g rd) m₁) E₁ e₂
      (Mid.narrow (Common.thru g rd) m₂) E₂ o₁ o₂ i₁ i₂ j₁ j₂
    refine ⟨s₃, hs, ?_⟩
    show T.I₃ 0 k s₃
      { Mid.narrow (Local.thru g rd) (R'.start₃ (H.thru g rd d) m₁ m₂) with
        opened := some (o₁ ++ o₂) } (envThird E₁ E₂)
    rw [Ready.start₃_narrow g rd d H h m₁ m₂]
    exact hi
  fin := fun e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃ i₁ i₂ i₃ =>
    T.fin e₁ _ E₁ e₂ _ E₂ e₃ _ E₃ i₁ i₂ i₃

/-- **The same at other columns that show the same words.** -/
def ThreadsC.withStored {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F))
    (hs : (H.withStored s).storedWords w rc = H.storedWords w rc)
    (T : ThreadsC F Bk H w rc x k R) : ThreadsC F Bk (H.withStored s) w rc x k R where
  I₁ := T.I₁
  I₂ := T.I₂
  I₃ := T.I₃
  f₁ := T.f₁
  f₂ := T.f₂
  f₃ := T.f₃
  h₁ := T.h₁
  h₂ := T.h₂
  h₃ := T.h₃
  y₁ := T.y₁
  y₂ := T.y₂
  y₃ := T.y₃
  a₁ := by
    rw [hs]
    exact T.a₁
  a₂ := by
    rw [hs]
    exact T.a₂
  a₃ := T.a₃
  fin := T.fin

/-- What the plan declares, at other columns that show the same words. -/
theorem PlanServes.withStored {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w : W₀} {rc : Rc}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} (s : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F))
    (hs : (H.withStored s).storedWords w rc = H.storedWords w rc) (P : PlanServes H w rc R) :
    PlanServes (H.withStored s) w rc R := by
  refine ⟨?_, ?_, ?_, P.own₁, P.own₂, P.taken⟩
  · rw [hs]
    exact P.first
  · rw [hs]
    exact P.shared
  · rw [hs]
    exact P.second

/-! ## 5 At the rows' prover -/

/-- **At the rows' prover: ready returns, the plan serves, and there is a value of ThreadsC with the
same falls**, from the same at the prover that is read through. -/
theorem rows_of_thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {F : FileDescription Xi} {Bk : ProverCoinCounts}
    (G : Sides F Bk W₀' Rc' Ky Tr X₀ X) (Cm : Committer W₀' Rc' Sd Xc Xi Ky) (item₀ : Nat)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w : W₀') (rc : Rc') (x : Xi) (k : Coins Bk)
    (hd : H.inRange (g d) = H.inRange H.dummy)
    (hrows : G.prover (H.thru g rd d) = H.thru g rd d) (hk : Cm.key = H.key)
    (hs : CommittedColumns Cm item₀ H g rd w rc) {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H (g w) (rd rc) x k = .ok R) (P : PlanServes H (g w) (rd rc) R)
    (T : ThreadsC F Bk H (g w) (rd rc) x k R) :
    ∃ R', ready F Bk (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x k = .ok R' ∧
      PlanServes (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc R' ∧
      ∃ T' : ThreadsC F Bk (G.prover (Cm.proverAt item₀ (H.thru g rd d))) w rc x k R',
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

end ProofFile.Honest

#print axioms ProofFile.Honest.playedNarrow
#print axioms ProofFile.Honest.play_thru
#print axioms ProofFile.Honest.chainSteps_ok_thru
#print axioms ProofFile.Honest.PlaysOn.thru
#print axioms ProofFile.Honest.SaysYes.thru
#print axioms ProofFile.Honest.move_thru_isSome
#print axioms ProofFile.Honest.oracles_thru
#print axioms ProofFile.Honest.oracles_take_thru
#print axioms ProofFile.Honest.ChainServes.thru
#print axioms ProofFile.Honest.PlanServes.thru
#print axioms ProofFile.Honest.ThreadsC.thru
#print axioms ProofFile.Honest.ThreadsC.withStored
#print axioms ProofFile.Honest.PlanServes.withStored
#print axioms ProofFile.Honest.rows_of_thru
