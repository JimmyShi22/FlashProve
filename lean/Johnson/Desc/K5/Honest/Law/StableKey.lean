-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/StableKey.lean: the honest prover's side of an attention segment's own
rounds: the values and the summands that are made of the lookup calls' key points alone are the same
at all challenges of the segment's own rounds. Statements with their proofs. No frame of a prover is
imported.

c, c': two lists of challenges with the same key points (hz). Nothing else is asked of them.

  planeOf_same, maxAt_same, flat_same, krAt_same, kAt_same   a value at two lists of named points
                 whose fields made of the key points alone are the same (KeySame,
                 Johnson/Desc/K5/Honest/Law/PointsIs.lean)
  stable_aloneKR   the remainder-table units' values
  stable_aloneK, stable_leadK   a softmax-table unit's planes' values and maximum; its seven
                 scalars, at one handed-in total sv
  stable_leadSE    the scalars in front of the division's sumcheck, at one handed-in total zo (that
                 the total is the same: `stable_sSE`, Law/Stable.lean, which asks more of the two
                 lists)
  stable_sK        a softmax-table unit's summand

Limits. Every statement is conditional on hz. The equations are of the program's elements, word for
word. Nothing holds a value against the verifier's claims. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PointsIs
import Johnson.Desc.K5.Honest.Products
import Johnson.Desc.K5.Honest.Alone

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc.First.Att.P (Geo Pts RemP ScoreP scoreTiles)

/-! ## 1 At two lists of named points -/

theorem planeOf_same (g : Geo) (w : K5In) {u u' : RemP} (h : remKey u = remKey u') :
    planeOf g w u = planeOf g w u' := by
  simp only [remKey, Prod.mk.injEq] at h
  obtain ⟨_, e2, e3, e4, _⟩ := h
  funext x
  unfold planeOf
  rw [e2, e3, e4]

theorem maxAt_same (g : Geo) (w : K5In) {k k' : ScoreP} (h : unitKey k = unitKey k') :
    maxAt g w k = maxAt g w k' := by
  simp only [unitKey, Prod.mk.injEq] at h
  obtain ⟨_, _, _, e4, e5, _, e7, _, e9⟩ := h
  unfold maxAt
  rw [e4, e5, e7, e9]

theorem flat_same (g : Geo) (w : K5In) : ∀ l l' : List RemP, l.map remKey = l'.map remKey →
    (l.flatMap fun u => (List.range 3).map (planeOf g w u)) =
      l'.flatMap fun u => (List.range 3).map (planeOf g w u)
  | [], [], _ => rfl
  | u :: l, u' :: l', e => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at e
    rw [List.flatMap_cons, List.flatMap_cons, planeOf_same g w e.1, flat_same g w l l' e.2]
  | [], _ :: _, e => by cases e
  | _ :: _, [], e => by cases e

theorem krAt_same (g : Geo) (w : K5In) {p p' : Pts} (K : KeySame p p') (n : Nat) :
    krAt g w p n = krAt g w p' n := by
  unfold krAt
  refine flat_same g w _ _ ?_
  rw [List.map_take, List.map_take, K.planes]

theorem kAt_same (g : Geo) (w : K5In) {p p' : Pts} (K : KeySame p p') (i : Nat) :
    kAt g w p i = kAt g w p' i := by
  unfold kAt
  simp only [Option.bind_eq_bind, Option.pure_def]
  have hk := congrArg (fun l => l[i]?) K.scores
  simp only [List.getElem?_map, Array.getElem?_toList] at hk
  cases a : p.scores[i]? with
  | none =>
    cases b : p'.scores[i]? with
    | none => rfl
    | some k' =>
      rw [a, b] at hk
      cases hk
  | some k =>
    cases b : p'.scores[i]? with
    | none =>
      rw [a, b] at hk
      cases hk
    | some k' =>
      rw [a, b] at hk
      have e : unitKey k = unitKey k' := Option.some.inj hk
      have ec : k.claim = k'.claim := by
        have e' := e
        simp only [unitKey, Prod.mk.injEq] at e'
        exact e'.2.1
      have hu := congrArg (fun l => l[k.claim]?) K.planes
      simp only [List.getElem?_map, Array.getElem?_toList] at hu
      simp only [Option.bind_some]
      rw [← ec, maxAt_same g w e]
      cases a2 : p.planes[k.claim]? with
      | none =>
        cases b2 : p'.planes[k.claim]? with
        | none => rfl
        | some u' =>
          rw [a2, b2] at hu
          cases hu
      | some u =>
        cases b2 : p'.planes[k.claim]? with
        | none =>
          rw [a2, b2] at hu
          cases hu
        | some u' =>
          rw [a2, b2] at hu
          simp only [Option.bind_some]
          rw [planeOf_same g w (Option.some.inj hu)]

/-! ## 2 At two lists of challenges -/

section
variable (P : Pub5) (w : K5In) {c c' : Chal} (hz : c.zk = c'.zk)
include hz

/-- The prover's named points at two lists of challenges. -/
theorem ptsOf_key {p : Pts} (hp : ptsOf P c = some p) :
    ∃ p', ptsOf P c' = some p' ∧ KeySame p p' := by
  obtain ⟨p', hp', K⟩ :=
    ptsOf_agree P (q := 0) hz (fun i hi => absurd hi (Nat.not_lt_zero i)) hp
  exact ⟨p', hp', K.key⟩

/-- **The remainder-table units' values.** -/
theorem stable_aloneKR : aloneKR P w c = aloneKR P w c' := by
  unfold aloneKR
  cases hp : ptsOf P c with
  | none => rw [ptsOf_none P hz hp]
  | some p =>
    obtain ⟨p', hp', K⟩ := ptsOf_key P hz hp
    rw [hp']
    simp only [Option.map_some, Option.getD_some]
    exact krAt_same P.g w K _

/-- **A softmax-table unit's planes' values and maximum.** -/
theorem stable_aloneK (i : Nat) : aloneK P w c i = aloneK P w c' i := by
  unfold aloneK
  cases hp : ptsOf P c with
  | none => rw [ptsOf_none P hz hp]
  | some p =>
    obtain ⟨p', hp', K⟩ := ptsOf_key P hz hp
    rw [hp']
    simp only [Option.bind_some]
    rw [kAt_same P.g w K i]

/-- **The seven scalars in front of a softmax-table unit's sumcheck**, at one handed-in total sv. -/
theorem stable_leadK (i : Nat) (sv : E) : leadK P w c i sv = leadK P w c' i sv := by
  unfold leadK
  rw [stable_aloneK P w hz i]

/-- **The scalars in front of the division's sumcheck**, at one handed-in total zo. -/
theorem stable_leadSE (zo : E) : leadSE P w c zo = leadSE P w c' zo := by
  unfold leadSE
  cases hp : ptsOf P c with
  | none => rw [ptsOf_none P hz hp]
  | some p =>
    obtain ⟨p', hp', K⟩ := ptsOf_key P hz hp
    have hk := K.d
    simp only [divKey, Prod.mk.injEq] at hk
    obtain ⟨e1, e2, e3, _, _, e6, e7, e8, e9, e10, e11, e12, e13⟩ := hk
    rw [hp']
    simp only [Option.map_some, Option.getD_some, accAt, zcAt, rhAt, rhpAt, ibAt, rh2At, rhp2At,
      atChan, atRow]
    rw [e1, e2, e3, e6, e7, e8, e9, e10, e11, e12, e13]

/-- **A softmax-table unit's summand.** -/
theorem stable_sK (i : Nat) : sK P w c i = sK P w c' i := by
  have hk : ((ptsOf P c).bind (·.scores[i]?)).map unitKey =
      ((ptsOf P c').bind (·.scores[i]?)).map unitKey := by
    cases hp : ptsOf P c with
    | none => rw [ptsOf_none P hz hp]
    | some p =>
      obtain ⟨p', hp', K⟩ := ptsOf_key P hz hp
      rw [hp']
      have h1 := congrArg (fun l => l[i]?) K.scores
      simp only [List.getElem?_map, Array.getElem?_toList] at h1
      exact h1
  unfold sK
  dsimp only
  cases hu : P.g.scores[i]? with
  | none => rfl
  | some u =>
    cases a : (ptsOf P c).bind (·.scores[i]?) with
    | none =>
      cases b : (ptsOf P c').bind (·.scores[i]?) with
      | none => rfl
      | some k' =>
        rw [a, b] at hk
        cases hk
    | some k =>
      cases b : (ptsOf P c').bind (·.scores[i]?) with
      | none =>
        rw [a, b] at hk
        cases hk
      | some k' =>
        rw [a, b] at hk
        have e : unitKey k = unitKey k' := Option.some.inj hk
        simp only [unitKey, Prod.mk.injEq] at e
        obtain ⟨_, _, e3, e4, _, _, e7, e8, _⟩ := e
        simp only [scoreTiles]
        rw [e3, e4, e7, e8, hz]

end

end H2K5.Honest

#print axioms H2K5.Honest.planeOf_same
#print axioms H2K5.Honest.maxAt_same
#print axioms H2K5.Honest.flat_same
#print axioms H2K5.Honest.krAt_same
#print axioms H2K5.Honest.kAt_same
#print axioms H2K5.Honest.ptsOf_key
#print axioms H2K5.Honest.stable_aloneKR
#print axioms H2K5.Honest.stable_aloneK
#print axioms H2K5.Honest.stable_leadK
#print axioms H2K5.Honest.stable_leadSE
#print axioms H2K5.Honest.stable_sK
