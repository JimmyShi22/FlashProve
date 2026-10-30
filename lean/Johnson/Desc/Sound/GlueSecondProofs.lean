-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Proofs of statements of Johnson/Desc/Sound/GlueSecond.lean.
import Johnson.Desc.Sound.GlueSecond
import Johnson.Desc.Sound.BordersSharedQProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared

/-- The table's shared rows, as lists. -/
def insLSh (split : Bool) (k : ℕ) : List ItemS :=
  ((rowAtS split k).ins ++ (rowAtS split k).ctx).filter fun i => !i.own
@[inherit_doc insLSh]
def outsLSh (split : Bool) (k : ℕ) : List ItemS :=
  ((rowAtS split k).outs ++ (rowAtS split k).ctx).filter fun i => !i.own
@[inherit_doc insLSh]
def startLSh : List ItemS := startS.filter fun i => !i.own

theorem own_false_iff (i : ItemS) : i.own = false ↔ (!i.own) = true := by
  cases i.own <;> simp

theorem insSh_eq (split : Bool) : insSh split = fun k i => i ∈ insLSh split k := by
  funext k i
  refine propext ?_
  show (i.own = false ∧ _) ↔ _
  rw [insLSh, List.mem_filter, own_false_iff]
  exact And.comm

theorem outsSh_eq (split : Bool) : outsSh split = fun k i => i ∈ outsLSh split k := by
  funext k i
  refine propext ?_
  show (i.own = false ∧ _) ↔ _
  rw [outsLSh, List.mem_filter, own_false_iff]
  exact And.comm

theorem startSh_eq : startSh = (· ∈ startLSh) := by
  funext i
  refine propext ?_
  show (i.own = false ∧ _) ↔ _
  rw [startLSh, List.mem_filter, own_false_iff]
  exact And.comm

theorem endL (split : Bool) (i : ItemS) :
    i ∈ openL (insLSh split) (outsLSh split) startLSh (sharedPlaces split).length ↔ i = .pin .oOmega := by
  cases split
  · have h : (openL (insLSh false) (outsLSh false) startLSh (sharedPlaces false).length).dedup =
        [.pin .oOmega] := by decide
    rw [← List.mem_dedup, h, List.mem_singleton]
  · have h : (openL (insLSh true) (outsLSh true) startLSh (sharedPlaces true).length).dedup =
        [.pin .oOmega] := by decide
    rw [← List.mem_dedup, h, List.mem_singleton]

theorem endShared : EndShared := by
  intro split i
  rw [insSh_eq, outsSh_eq, startSh_eq, openIsList ItemS (insLSh split) (outsLSh split) startLSh]
  exact endL split i

theorem glueSecond : GlueSecond := by
  intro C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt pub start₁ start₂ start₃ T Q N Mg Pm Oc split hlen hA hB
    x b w h
  by_cases hon : onQ₂ N Pm Oc split T.p₂ T.l₂ (1 + T.l₂.length) b
  · refine Or.inl ?_
    obtain ⟨t, ht, hw⟩ : ∃ t, (start₃ b.1.1.1 b.1.1.2 b.1.2).map
        (fun s => ((b.1.1.1, b.1.1.2, b.1.2), s)) = some t ∧
        (Q.R₃ 0 (t, b.2) w ∨ ¬ Q.on₃ 0 (t, b.2)) := h
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 ht
    have hr := hw.elim id fun n => absurd (hA b s hon hs) n
    obtain ⟨h1, h2⟩ := hB b s w hon hs hr
    refine ⟨fun i hi => ?_, fun i hi => h2 i ?_⟩
    · have hi' : openAfter (insSh split) (outsSh split) startSh (1 + T.l₂.length) i := hi
      rw [hlen] at hi'
      obtain rfl := (endShared split i).1 hi'
      exact h1
    · have hk : ownAt (1 + T.l₂.length) = endS.filter (·.own) := by
        have h2le : ¬ 1 + T.l₂.length ≤ pointAt := by
          rw [hlen]
          cases split <;> decide
        unfold ownAt
        rw [if_neg h2le]
      have hi' : i ∈ ownAt (1 + T.l₂.length) := hi
      rw [hk] at hi'
      exact hi'
  · exact Or.inr hon

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.endShared
#print axioms VerifiableInference.Desc.Sound.glueSecond
