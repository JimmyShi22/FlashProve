-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ReadsAtt.lean: K1's READS AT AN ATTENTION LINK, ON SHAPES, AT TWO PLANS THAT DIFFER ONLY IN WHAT MOVES
(Scope/Rel.lean, stripPlan): the step goes alike under strip: from two laws on the plans (hT: the one Bool on the shape does not see
what moves, and what the lookup heard only through stripH; hF: the tables' shapes are equal), which Scope/AttGeo.lean pays.

  keep_attG        the quiet step on the shape leaves the two lookups' components as they stand.
  readsAtt_bind    readsAttGS is commitGS, then the quiet step under the Bool.
  tabsGC_rel       the Bool at two states that differ in the lookups' components alone, under hT.
  reads_att_alike  the step at two shapes with one strip.

Limits. Laws on terms; nothing is evaluated; nothing says that a step returns. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.PlainCells
import Johnson.AtFull.Shape.Scope.Join
import Johnson.AtFull.Shape.Scope.AttGeo
import Johnson.AtFull.Shape.ReadsAttAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Att (attG)
open H2K5.Honest (tabsGC tabsG attFuns)

/-- The quiet step behind the reads leaves what stands in the two lookups' components. -/
theorem keep_attG (fs : Option (List FunSh)) : KeepO (attG fs) := by
  intro a l h
  unfold attG
  simp only [pC_here, pC_tl, pC_link, pC_core]
  split
  · rfl
  · split
    · simp only [Option.map_map]
      rfl
    · rfl

/-- The step at the seat: the commitment at the seat, then the Bool and the quiet step. -/
theorem readsAtt_bind (P : VerifiableInference.Desc.K1.Par) (link : Nat) (arrays : Option (List Nat))
    (A : Attention.Plan) (a : ChainSh) :
    readsAttGS P link arrays A a = (commitGS P link 1 arrays a).bind fun m =>
      if tabsGC A m then attG (some (attFuns A)) m else none := by
  unfold readsAttGS commitGS
  split <;> rfl

/-- The Bool at two states that differ in the lookups' components alone. -/
theorem tabsGC_rel {A A₀ : Attention.Plan}
    (hT : ∀ H K K' L, stripH K = stripH K' → tabsG A H K L = tabsG A₀ H K' L)
    {l l' h h' : Option HeardAll} (e : l.map stripH = l'.map stripH) (m : ChainSh) :
    tabsGC A (pC l h m) = tabsGC A₀ (pC l' h' m) := by
  cases l with
  | none =>
    cases l' with
    | none =>
      unfold tabsGC
      show (match m.att.bind (·.heard5), (none : Option HeardAll), m.led with
        | some H, some K, some L => tabsG A H K L
        | _, _, _ => false) = (match m.att.bind (·.heard5), (none : Option HeardAll), m.led with
        | some H, some K, some L => tabsG A₀ H K L
        | _, _, _ => false)
      generalize m.att.bind (·.heard5) = a1
      generalize m.led = b1
      cases a1 <;> cases b1 <;> rfl
    | some K' => cases e
  | some K =>
    cases l' with
    | none => cases e
    | some K' =>
      have eK : stripH K = stripH K' := Option.some.inj e
      clear e
      unfold tabsGC
      show (match m.att.bind (·.heard5), some K, m.led with
        | some H, some K, some L => tabsG A H K L
        | _, _, _ => false) = (match m.att.bind (·.heard5), some K', m.led with
        | some H, some K, some L => tabsG A₀ H K L
        | _, _, _ => false)
      generalize m.att.bind (·.heard5) = a1
      generalize m.led = b1
      cases a1 with
      | none => rfl
      | some H =>
        cases b1 with
        | none => rfl
        | some L => exact hT H K K' L eK

/-- The step at a shape with the lookups' components laid. -/
theorem step_pC (A : Attention.Plan) (P : VerifiableInference.Desc.K1.Par) (link : Nat)
    (arrays : Option (List Nat)) (l h : Option HeardAll) (c : ChainSh) :
    readsAttGS P link arrays A (pC l h c) = (commitGS P link 1 arrays c).bind fun m =>
      if tabsGC A (pC l h m) then (attG (some (attFuns A)) m).map (pC l h) else none := by
  rw [readsAtt_bind, keep_commit P link 1 arrays]
  cases commitGS P link 1 arrays c with
  | none => rfl
  | some m =>
    show (if tabsGC A (pC l h m) then attG (some (attFuns A)) (pC l h m) else none) = _
    rw [keep_attG]
    rfl

/-- **THE READS AT AN ATTENTION LINK GO ALIKE UNDER strip.** -/
theorem reads_att_alike {A A₀ : Attention.Plan}
    (hT : ∀ H K K' L, stripH K = stripH K' → tabsG A H K L = tabsG A₀ H K' L)
    (hF : attFuns A = attFuns A₀) (P : VerifiableInference.Desc.K1.Par) (link : Nat)
    (arrays : Option (List Nat)) {x y : ShA} (e : strip x = strip y) :
    Alike (fun b b' => strip b = strip b') (readsA (readsAttGS P link arrays A) P x)
      (readsA (readsAttGS P link arrays A₀) P y) := by
  have e1 : x.1.look.map stripH = y.1.look.map stripH := congrArg (fun z : ShA => z.1.look) e
  have e2 : x.1.lookHeard.map stripH = y.1.lookHeard.map stripH :=
    congrArg (fun z : ShA => z.1.lookHeard) e
  have ecore0 : (strip x).1.core = (strip y).1.core := congrArg (fun z : ShA => z.1.core) e
  have ecore : x.1.core = y.1.core := ecore0
  have eform0 : (strip x).2 = (strip y).2 := congrArg Prod.snd e
  have eform : x.2 = y.2 := eform0
  have ex : x.1 = pC x.1.look x.1.lookHeard (strip x).1 := rfl
  have ey : y.1 = pC y.1.look y.1.lookHeard (strip x).1 := by
    rw [e]
    rfl
  have es : ∀ b : ShA, strip (pF x.1.look x.1.lookHeard b) = strip (pF y.1.look y.1.lookHeard b) := by
    intro b
    show pF (x.1.look.map stripH) (x.1.lookHeard.map stripH) b =
      pF (y.1.look.map stripH) (y.1.lookHeard.map stripH) b
    rw [e1, e2]
  unfold readsA
  have gx : readsAttGS P link arrays A x.1 = (commitGS P link 1 arrays (strip x).1).bind fun m =>
      if tabsGC A (pC x.1.look x.1.lookHeard m) then
        (attG (some (attFuns A)) m).map (pC x.1.look x.1.lookHeard) else none :=
    step_pC A P link arrays x.1.look x.1.lookHeard (strip x).1
  have gy : readsAttGS P link arrays A₀ y.1 = (commitGS P link 1 arrays (strip x).1).bind fun m =>
      if tabsGC A₀ (pC y.1.look y.1.lookHeard m) then
        (attG (some (attFuns A₀)) m).map (pC y.1.look y.1.lookHeard) else none :=
    (congrArg (readsAttGS P link arrays A₀) ey).trans
      (step_pC A₀ P link arrays y.1.look y.1.lookHeard (strip x).1)
  rw [gx, gy]
  cases commitGS P link 1 arrays (strip x).1 with
  | none => exact Or.inr ⟨rfl, rfl⟩
  | some m =>
    simp only [Option.bind_some]
    rw [tabsGC_rel hT (h := x.1.lookHeard) (h' := y.1.lookHeard) e1 m, hF]
    cases tabsGC A₀ (pC y.1.look y.1.lookHeard m) with
    | false => exact Or.inr ⟨rfl, rfl⟩
    | true =>
      simp only [if_true]
      cases attG (some (attFuns A₀)) m with
      | none => exact Or.inr ⟨rfl, rfl⟩
      | some u =>
        refine Or.inl ⟨_, _, rfl, rfl, ?_⟩
        show strip (pC x.1.look x.1.lookHeard u, sendForms P x.1.core.st.oracles.length x.2) =
          strip (pC y.1.look y.1.lookHeard u, sendForms P y.1.core.st.oracles.length y.2)
        rw [ecore, eform]
        exact es (u, sendForms P y.1.core.st.oracles.length y.2)

variable {X X₀ : Verify.Public}

/-- Where neither record has the plan, or both have. -/
theorem reads_plans_alike (S : SameRead X X₀) (g : Nat) :
    (X.A[g]? = none ∧ X₀.A[g]? = none) ∨
      ∃ p q, X.A[g]? = some p ∧ X₀.A[g]? = some q ∧ stripPlan p = stripPlan q := by
  have e := S.atA g
  cases h1 : X.A[g]? with
  | none =>
    cases h2 : X₀.A[g]? with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some q =>
      rw [h1, h2] at e
      cases e
  | some p =>
    cases h2 : X₀.A[g]? with
    | none =>
      rw [h1, h2] at e
      cases e
    | some q =>
      rw [h1, h2] at e
      exact Or.inr ⟨p, q, rfl, rfl, Option.some.inj e⟩

theorem odd_inside {l : Nat} (hl : l < 24) (ho : l % 2 = 1) : oddAt (14 * l + 4 + 1) = true := by
  have e : (14 * l + 4 + 1 - 1) / 14 = l := by omega
  unfold oddAt
  rw [e]
  simp [ho]
  omega

/-- **The reads at an attention link.** -/
theorem reads_att_rel (S : SameRead X X₀) {l : Nat} (hl : l < 24) (ho : l % 2 = 1) :
    CellRel X X₀ (14 * l + 4 + 1) ((TabL.linkRow (LW X) l).at 4) ((TabL.linkRow (LW X₀) l).at 4) := by
  intro a a' h
  have hn := odd_inside hl ho
  have hn' : oddAt (14 * l + 4 + 1 + 1) = oddAt (14 * l + 4 + 1) := oddAt_inside hl (by omega)
  have e : strip a = strip a' := by
    unfold RelAt at h
    rw [if_pos hn] at h
    exact h
  show Alike _ ((TabL.reads (LW X) l).1 a) ((TabL.reads (LW X₀) l).1 a')
  have hb : (l % 2 == 0) = false := by simp [ho]
  unfold TabL.reads
  rw [nums_same S l]
  cases (LW X₀).nums l with
  | none => exact Or.inr ⟨rfl, rfl⟩
  | some q =>
    obtain ⟨_, _, rd, _⟩ := q
    simp only [hb, Bool.false_eq_true, if_false]
    rcases reads_plans_alike S (l / 2) with ⟨h1, h2⟩ | ⟨p, q, h1, h2, ep⟩
    · have e1 : (LW X).XG.A[l / 2]? = none := h1
      have e2 : (LW X₀).XG.A[l / 2]? = none := h2
      rw [e1, e2]
      exact Or.inr ⟨rfl, rfl⟩
    · have e1 : (LW X).XG.A[l / 2]? = some p := h1
      have e2 : (LW X₀).XG.A[l / 2]? = some q := h2
      rw [e1, e2]
      rcases reads_att_alike (fun H K K' L eK => tabsG_same ep H eK L) (attFuns_same ep)
        ((LW X).k1 l 4 1) l rd e with ⟨b, b', x, y, r⟩ | ⟨x, y⟩
      · refine Or.inl ⟨b, b', x, y, ?_⟩
        unfold RelAt
        rw [hn', if_pos hn]
        exact r
      · exact Or.inr ⟨x, y⟩

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.odd_inside
#print axioms Johnson.AtFull.Shape.Scope.reads_att_rel
#print axioms Johnson.AtFull.Shape.Scope.keep_attG
#print axioms Johnson.AtFull.Shape.Scope.readsAtt_bind
#print axioms Johnson.AtFull.Shape.Scope.tabsGC_rel
#print axioms Johnson.AtFull.Shape.Scope.reads_att_alike
