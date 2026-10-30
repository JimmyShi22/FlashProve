-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/PansB.lean: CONDITIONAL, on a test: a test with code on public
data for the panels' public readings of the sub-protocol K4's batched sumcheck (hearStack,
OnBytes/Model/Layer.lean): callsTS; panelsT over panelsA; the number of places against the plan's
rounds; the next weight claim's number; stackEnd. The end of pans_of_B is the text of the field pans
of StackPub (Johnson/Desc/First/K4/Returns/Stack.lean); the tie to that structure stands in
JoinPans.lean.

Limits. NO FILE OF THIS FOLDER PROVES THE TEST TRUE AT ANY PLAN. #guard is Lean's evaluator and
gives no proof. PansBTest.lean [not in this library; so here read: not tested in this library]
evaluates it at the small synthetic plan; no file of this folder
evaluates it at a model's plan. It builds the two forms of the end, with one step for each row and
column of each panel, and sorts the panels. The field join of StackPub is not treated.
No property is claimed.

  blankEnv     the environment of the forms by the plan, with no point of the lookup.
  pansB        THE TEST: the five readings at an environment v₀, with empty arrays for what the
               lookup and the second token sumcheck leave, lamS zeros for the challenges, empty
               arrays for the shown values.
  pans_of_B    where the test is true at v₀, the readings return at every environment of v₀'s
               layout, tables and number of columns, at every heard state, and at all values.
  pansB_of_one the converse from single returns: one list of panels, the two comparisons, and one
               return of stackEnd at lamS challenges give the test.
  B_of_pans    the converse: the test asks no more than the readings at one heard state.
-/
import Johnson.Desc.First.K4.Returns.Pub.End
import Johnson.Desc.First.K4.Returns.Pub.Panels

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel)
open OnBytes.Desc.First.K4.Total (EnvSkel)

/-- The environment of the forms by the plan, with no point of the lookup. iU3: the number of the
array of the reads. tab: the list of tables. -/
def blankEnv (P : Pub) (hp : HPlan2) (g iU3 : Nat) (tab : List TableAt) : Env :=
  { y := P.y, sc := P.sc, g := g, iU3 := iU3, K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0,
    tab := tab, zk := #[] }

/-- **THE TEST.** v₀: meant for an environment made of public data, of P's layout; the type asks
neither. lamS: the number of rounds by the plan.
NCLp: the number of the panels' weight claims by the plan. -/
def pansB (P : Pub) (v₀ : Env) (lamS NCLp : Nat) : Bool :=
  match callsTS P with
  | none => false
  | some TS =>
    match panelsT ⟨v₀, #[], #[], #[], stubO P.y⟩ TS (panelsA ⟨v₀, #[], #[], #[], stubO P.y⟩ {}) with
    | none => false
    | some pans =>
      ceilLog2 (placePanels pans.bl).2 == lamS && pans.nextV == NCLp &&
        (stackEnd P.y (placePanels pans.bl).1 (Array.replicate lamS zeroE) lamS #[] #[] #[] zeroE
          zeroE).isSome

/-- **Where the test is true, the panels' public readings return**, at all values. -/
theorem pans_of_B {P : Pub} {v v₀ : Env} (S : EnvSkel v v₀) {lamS NCLp : Nat}
    (h : pansB P v₀ lamS NCLp = true) (H : Heard) :
    ∃ TS, callsTS P = some TS ∧ ∀ shownT : Array E, shownT.size = nEndT P.y →
      ∃ pans, panelsT ⟨v, H.fo.e, shownT, H.ztF, stubO P.y⟩ TS
          (panelsA ⟨v, H.fo.e, shownT, H.ztF, stubO P.y⟩ {}) = some pans ∧
        (ceilLog2 (placePanels pans.bl).2 == lamS) = true ∧ (pans.nextV == NCLp) = true ∧
        ∀ (rs om H1 V : Array E) (a b : E), rs.size = lamS → om.size = 2 →
          H1.size = 1 + P.y.LamM → V.size = NCLp →
          ∃ fin, stackEnd P.y (placePanels pans.bl).1 rs lamS om H1 V a b = some fin := by
  unfold pansB at h
  split at h
  · cases h
  · rename_i TS hTS
    split at h
    · cases h
    · rename_i pans₀ hp
      rw [Bool.and_eq_true, Bool.and_eq_true] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨TS, hTS, fun shownT _ => ?_⟩
      obtain ⟨pans, e, e1, e2, e3⟩ := panels_at (p := ⟨v, H.fo.e, shownT, H.ztF, stubO P.y⟩)
        (p₀ := ⟨v₀, #[], #[], #[], stubO P.y⟩) S TS hp
      refine ⟨pans, e, by rw [e2]; exact h1, by rw [e1]; exact h2,
        fun rs om H1 V a b hr _ _ _ => ?_⟩
      have hk := stackEnd_rel P.y (rs := rs) (rs₀ := Array.replicate lamS zeroE) lamS om H1 V #[]
        #[] #[] a b zeroE zeroE e3 (by rw [hr, Array.size_replicate])
      rw [h3] at hk
      exact Option.isSome_iff_exists.mp hk

/-- **The converse from single returns**, at whatever arrays and elements. -/
theorem pansB_of_one {P : Pub} {v v₀ : Env} (S : EnvSkel v v₀) {lamS NCLp : Nat}
    {e shownT zt : Array E} {TS : List Nat} {pans : Panels} (hT : callsTS P = some TS)
    (hp : panelsT ⟨v, e, shownT, zt, stubO P.y⟩ TS (panelsA ⟨v, e, shownT, zt, stubO P.y⟩ {}) =
      some pans)
    (hl : (ceilLog2 (placePanels pans.bl).2 == lamS) = true) (hn : (pans.nextV == NCLp) = true)
    {rs om H1 V : Array E} {a b : E} (hr : rs.size = lamS)
    (hs : (stackEnd P.y (placePanels pans.bl).1 rs lamS om H1 V a b).isSome = true) :
    pansB P v₀ lamS NCLp = true := by
  obtain ⟨pans₀, e0, e1, e2, e3⟩ := panels_at (p := ⟨v₀, #[], #[], #[], stubO P.y⟩)
    (p₀ := ⟨v, e, shownT, zt, stubO P.y⟩) ⟨S.y.symm, S.tab.symm, S.K3.symm⟩ TS hp
  have hk := stackEnd_rel P.y (rs := Array.replicate lamS zeroE) (rs₀ := rs) lamS #[] #[] #[] om H1
    V zeroE zeroE a b e3 (by rw [hr, Array.size_replicate])
  rw [hs] at hk
  unfold pansB
  simp only [hT, e0]
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨by rw [e2]; exact hl, by rw [e1]; exact hn⟩, hk⟩

/-- **The converse**: the readings at one environment and one heard state give the test. -/
theorem B_of_pans {P : Pub} {v v₀ : Env} (S : EnvSkel v v₀) {lamS NCLp : Nat} (H : Heard)
    (h : ∃ TS, callsTS P = some TS ∧ ∀ shownT : Array E, shownT.size = nEndT P.y →
      ∃ pans, panelsT ⟨v, H.fo.e, shownT, H.ztF, stubO P.y⟩ TS
          (panelsA ⟨v, H.fo.e, shownT, H.ztF, stubO P.y⟩ {}) = some pans ∧
        (ceilLog2 (placePanels pans.bl).2 == lamS) = true ∧ (pans.nextV == NCLp) = true ∧
        ∀ (rs om H1 V : Array E) (a b : E), rs.size = lamS → om.size = 2 →
          H1.size = 1 + P.y.LamM → V.size = NCLp →
          ∃ fin, stackEnd P.y (placePanels pans.bl).1 rs lamS om H1 V a b = some fin) :
    pansB P v₀ lamS NCLp = true := by
  obtain ⟨TS, hTS, hall⟩ := h
  obtain ⟨pans, e, h1, h2, h3⟩ := hall (Array.replicate (nEndT P.y) zeroE) Array.size_replicate
  obtain ⟨fin, hf⟩ := h3 (Array.replicate lamS zeroE) (Array.replicate 2 zeroE)
    (Array.replicate (1 + P.y.LamM) zeroE) (Array.replicate NCLp zeroE) zeroE zeroE
    Array.size_replicate Array.size_replicate Array.size_replicate Array.size_replicate
  exact pansB_of_one S hTS e h1 h2 Array.size_replicate (by rw [hf]; rfl)

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.pans_of_B
#print axioms OnBytes.Desc.First.K4.RtPub.pansB_of_one
#print axioms OnBytes.Desc.First.K4.RtPub.B_of_pans
