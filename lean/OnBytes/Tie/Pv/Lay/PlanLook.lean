-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/PlanLook.lean: in the plan of a layers' sub-proof the sub-proof's own rounds
stand behind the rounds of a lookup. The lookup's routine leaves the planner in a state from which
the theorems on the own rounds speak.

The planner runs `planLayerOwn x` only behind the lookup of all calls: `layerRounds look x small
claims 0` is `planForest look`, then `planLayerOwn x` (OnBytes/Params/SubRounds.lean). The
theorems of OnBytes/Tie/Pv/Lay/PlanList.lean and PlanBounds.lean start from a state `At s 0`: a
request's scope, no open byte, root or answer.

Main names:
  `KeepsB s b b' x`: from a state with b open bytes the routine x ends well only in a state with
    b' open bytes, and the rounds that stood stay, in front. `Keeps s x`: the same with no open
    byte before and behind.
  `keeps_psc`, `keeps_tree`, `keeps_lookup`, `keeps_forest`: the planner's routines for a masked
    sumcheck of any size, a product tree, a lookup, the lookup of a group of calls keep such a
    state.
  `layer0_rounds`: for every setting, sizes and states p, q with `At s 0 p` and `layerRounds look
    x small claims 0 p = .ok ((), q)`: `At s 0 q`, and q's rounds are p's, then some list f, then
    `ownRounds s x`, whole.

Limits: the lookup's rounds f are not listed here. That the routine of a whole request calls
`layerRounds` from a state `At s 0` is not shown. Nothing is said on the moments 1 and 2.
-/
import OnBytes.Tie.Pv.Lay.PlanBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay

open OnBytes OnBytes.Params

/-- from b open bytes to b' open bytes; what stood stays in front -/
def KeepsB (s : Setting) (b b' : Nat) (x : Planning Unit) : Prop :=
  ∀ p q, At s b p → x p = .ok ((), q) → At s b' q ∧ ∃ f : List PlanRound, q.rounds = p.rounds ++
      f.toArray

abbrev Keeps (s : Setting) (x : Planning Unit) : Prop := KeepsB s 0 0 x

theorem AddsW.keeps {s : Setting} {b b' : Nat} {x : Planning Unit} {L : List PlanRound} (h : AddsW
    s b b' x L) :
    KeepsB s b b' x := fun p q hp hq => ⟨(h p q hp hq).1, L, (h p q hp hq).2⟩

theorem KeepsB.bind {s : Setting} {b b' b'' : Nat} {x y : Planning Unit} (hx : KeepsB s b b' x)
    (hy : KeepsB s b' b'' y) :
    KeepsB s b b'' (x >>= fun _ => y) := fun p q hp h => by
  obtain ⟨_, r, h1, h2⟩ := bind_ok h
  obtain ⟨a1, f1, e1⟩ := hx p r hp h1
  obtain ⟨a2, f2, e2⟩ := hy r q a1 h2
  exact ⟨a2, f1 ++ f2, by rw [e2, e1]; simp⟩

theorem keeps_pure (s : Setting) (b : Nat) : KeepsB s b b (pure ()) := (AddsW.pure s b).keeps

theorem KeepsB.ite {s : Setting} {b b' : Nat} {c : Prop} [Decidable c] {x y : Planning Unit}
    (hx : KeepsB s b b' x) (hy : KeepsB s b b' y) : KeepsB s b b' (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem keeps_needs (s : Setting) (b : Nat) (c : Bool) : KeepsB s b b (needs c) := by
  unfold needs
  split
  · exact keeps_pure s b
  · intro p q _ h
    cases h

/-- a routine that closes a round of the field's kind, whatever its bound and draws -/
theorem keeps_close (s : Setting) (b : Nat) (name : String) (e : Bound) (d : Draws) :
    KeepsB s b 0 (close name .field e d) :=
  fun p q hp h => ⟨(closeW_at hp name e d h).1, [roundOf s name b e d], by
    rw [(closeW_at hp name e d h).2]
    simp⟩

theorem keeps_closeS (s : Setting) (b : Nat) (name : String) (e : Setting → Bound) (d : Draws) :
    KeepsB s b 0 (theSetting >>= fun s' => close name .field (e s') d) :=
  (addsW_close s b name e d).keeps

theorem keeps_none (s : Setting) (b : Nat) (name : String) : KeepsB s b 0 (closeNone name) :=
  fun p q hp h => ⟨(noneW_at hp name h).1, [quietOf name b], by rw [(noneW_at hp name h).2]; simp⟩

theorem keeps_scalars (s : Setting) (b n : Nat) : KeepsB s b (b + 24 * n) (planScalars n) :=
    (addsW_scalars s b n).keeps

/-- the rounds of the variables, of any degrees -/
theorem keeps_vars (s s' : Setting) : ∀ g : List Nat, Keeps s (planPscRounds s' g)
  | [] => keeps_pure s 0
  | d :: g => KeepsB.bind (keeps_scalars s 0 (d - 1)) (KeepsB.bind (keeps_close s _ _ _ _)
      (keeps_vars s s' g))

/-- a masked sumcheck of any size, with or without Y, from b open bytes -/
theorem keeps_psc (s : Setting) (b : Nat) (z : PscSize) : KeepsB s b 0 (planPsc z) := fun p q hp h
    => by
  have h' : (theSetting >>= fun s' =>
      planScalars 1 >>= fun _ =>
      close "PSC epsilon" .field (fieldError s' 1) { drawE := 1, priced := .settingAlone } >>= fun
          _ =>
      planPscRounds s' z.degree >>= fun _ =>
      (if z.withY then
        (planScalars z.degreeY >>= fun _ =>
        close "PSC Y" .field (fieldErrorNonzero s' z.degreeY) { drawE := 1, drawNZ := 1, priced :=
            .roundItself } >>= fun _ =>
        planScalars z.values >>= fun _ =>
        closeNone "PSC values") else pure ())) p = .ok ((), q) := h
  obtain ⟨s4, m4, g4, k4⟩ := bind_ok h'
  obtain ⟨rfl, rfl⟩ : p.set = s4 ∧ p = m4 := Prod.mk.inj (Except.ok.inj g4)
  exact (KeepsB.bind (keeps_scalars s b 1) (KeepsB.bind (keeps_close s _ _ _ _) (KeepsB.bind
      (keeps_vars s p.set z.degree)
    (KeepsB.ite (KeepsB.bind (keeps_scalars s 0 z.degreeY) (KeepsB.bind (keeps_close s _ _ _ _)
      (KeepsB.bind (keeps_scalars s 0 z.values) (keeps_none s _ _)))) (keeps_pure s 0))))) p q hp k4

theorem keeps_times (s : Setting) {x : Planning Unit} (hx : Keeps s x) : ∀ n, Keeps s (times n x)
  | 0 => keeps_pure s 0
  | n + 1 => KeepsB.bind hx (keeps_times s hx n)

theorem keeps_forEach (s : Setting) {α : Type} {f : α → Planning Unit} (hf : ∀ a, Keeps s (f a)) :
    ∀ l : List α, Keeps s (forEach l f)
  | [] => keeps_pure s 0
  | a :: l => KeepsB.bind (hf a) (keeps_forEach s hf l)

theorem keeps_levels (s : Setting) (more : Nat) : ∀ fuel l, Keeps s (planTreeLevels more fuel l)
  | 0, _ => keeps_pure s 0
  | fuel + 1, l => KeepsB.bind (keeps_psc s 0 _) (KeepsB.bind (addsW_line s).keeps (keeps_levels s
      more fuel (l + 1)))

theorem keeps_tree (s : Setting) (levels more : Nat) : Keeps s (planProductTree levels more) :=
    keeps_levels s more levels 0

theorem keeps_setting (s : Setting) (b b' : Nat) {f : Setting → Planning Unit} (hf : ∀ s', KeepsB
    s b b' (f s')) :
    KeepsB s b b' (theSetting >>= f) := fun p q hp h => by
  obtain ⟨s4, m4, g4, k4⟩ := bind_ok h
  obtain ⟨rfl, rfl⟩ : p.set = s4 ∧ p = m4 := Prod.mk.inj (Except.ok.inj g4)
  exact hf p.set p q hp k4

theorem keeps_lookup (s : Setting) (x : LookupSize) : Keeps s (planLookup x) := by
  unfold planLookup
  refine keeps_setting s 0 0 fun s' => ?_
  -- Lean lays "if x.shifted then planShift .." as: if .. then (planShift .., then the rest)
  -- else (nothing, then the rest)
  have rest := KeepsB.bind (keeps_close s 0 "LKP"
      (Bound.ratio (sumT ((if x.parts.isEmpty then [x.v] else x.parts).map (2 ^ ·)) - 1) s'.cardE)
          { drawE := 1, priced := .callersWord })
    (KeepsB.bind (keeps_psc s 0 { degreeY := 3, values := 3 })
    (KeepsB.bind (keeps_times s (keeps_psc s 0 { degreeY := 3, values := 2 }) ((if x.live != 0
        then x.live else 2 ^ min x.mu 6) - 2))
    (KeepsB.bind (keeps_times s (keeps_psc s 0 {}) ((if x.parts.isEmpty then [x.v] else
        x.parts).length - 1))
    (KeepsB.bind (addsW_join s x.mu).keeps
    (KeepsB.bind (keeps_forEach s (fun v => keeps_tree s v 0) (if x.parts.isEmpty then [x.v] else
        x.parts))
    (KeepsB.bind (keeps_tree s x.d x.mu)
    (KeepsB.bind (keeps_psc s 0 { degree := List.replicate x.d 3 ++ List.replicate x.mu 2, withY
        := false })
    (KeepsB.bind (addsW_zero s (x.mu + x.d)).keeps
      (keeps_psc s 0 { degree := List.replicate (x.mu + x.d) 3, degreeY := 2, values := 1 })))))))))
  exact KeepsB.bind (keeps_needs s 0 _) (KeepsB.bind (keeps_needs s 0 _)
    (KeepsB.ite (KeepsB.bind (keeps_closeS s 0 "LKP shift" (fun s'' => fieldError s'' (2 ^ x.d))
        _) rest)
      (KeepsB.bind (keeps_pure s 0) rest)))

/-- The lookup of a group of calls keeps such a state. -/
theorem keeps_forest (s : Setting) (z : ForestSize) : Keeps s (planForest z) := keeps_lookup s _

/-- The rounds of a layers' sub-proof after moment 0 end in `ownRounds s x`. -/
theorem layer0_rounds (s : Setting) (look : ForestSize) (x : LayerRounds) (small : SmallSize)
    (claims : Nat)
    (p q : PlanState) (hp : At s 0 p) (h : layerRounds look x small claims 0 p = .ok ((), q)) :
    At s 0 q ∧ ∃ f : List PlanRound, q.rounds = p.rounds ++ (f ++ ownRounds s x).toArray := by
  have h' : (planForest look >>= fun _ => planLayerOwn x) p = .ok ((), q) := h
  obtain ⟨_, r, h1, h2⟩ := bind_ok h'
  obtain ⟨a1, f, e1⟩ := keeps_forest s look p r hp h1
  obtain ⟨a2, e2⟩ := own_addsW s x r q a1 h2
  exact ⟨a2, f, by rw [e2, e1]; simp⟩

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.keeps_forest
#print axioms OnBytes.Tie.Pv.Lay.layer0_rounds
