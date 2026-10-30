-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormLeft.lean: behind a fold, the switch into the fold's new group and the
batching behind it, nothing is left untested again (`ChainEnd.NothingLeft`,
Johnson/Desc/ChainEndLaw.lean): a proximity test has begun on every group, and every sampled oracle
message is in such a group.

Main names (namespace `Johnson.Prover.Link`).
  `left_step`   nothing left in front of the fold · the soundness side's record `Did` of the switch,
      at the statement behind the fold, into the fold's new group, with one message riding: then
      nothing is left behind the batching

By: `did_groups`, `did_new`, `did_oracles` (Johnson/Desc/K12/Law/OutK2.lean), `new_behind`,
`rider_behind` (Johnson/Prover/Link/BaseBehindSwitch.lean).

Limits. Between the fold and the batching the new group is not marked: the clause holds in front of
a fold and behind a batching alone. Nothing on whether a test was carried through. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BaseBehindSwitch
import Johnson.Desc.K12.Law.OutK2
import Johnson.Desc.ChainEndLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

/-- An entry that a look-up finds. -/
theorem get_of_some {α : Type} {A : Array α} {i : ℕ} (hi : i < A.size) {x : α}
    (h : A[i]? = some x) : A[i] = x := by
  rw [Array.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

/-- **Nothing is left untested behind a stage.** -/
theorem left_step {ft : ℕ} {cols : List Tw.L9.Col} {old : SingleRows} {T : SwitchTarget}
    {N : OracleNotice} {S₀ S' : Statement} {Bk Bk' : TreeBook} {roots : ℕ} {out : Switched}
    {row : GroupRow} {lay : GroupLayout} {theta : E} {D : Taken} (id a b : ℕ)
    (h0 : ChainEnd.NothingLeft S₀)
    (h : Did ft cols old T S₀.groups.size #[N] (Ground.withGroup (spent S₀ id) a b) Bk roots S' Bk'
      out row lay theta D) (hm : D.G.members = #[]) : ChainEnd.NothingLeft S' := by
  obtain ⟨hsz, hoth⟩ := H2K.Out.did_groups h
  obtain ⟨G', hG', hrun', -⟩ := H2K.Out.did_new h
  obtain ⟨hosz, hold⟩ := H2K.Out.did_oracles h hm
  have hgs : (Ground.withGroup (spent S₀ id) a b).groups.size = S₀.groups.size + 1 := by
    simp [Ground.withGroup, spent]
  have hos : (Ground.withGroup (spent S₀ id) a b).oracles.size = S₀.oracles.size := by
    simp [Ground.withGroup, spent]
  have hgold : ∀ q, q < S₀.groups.size → S'.groups[q]? = S₀.groups[q]? := by
    intro q hq
    rw [hoth q (by omega)]
    show (S₀.groups.push _)[q]? = _
    rw [Array.getElem?_push_lt hq, Array.getElem?_eq_getElem hq]
  refine ⟨fun i hi => ?_, fun i hi hs => ?_⟩
  · by_cases c : i = S₀.groups.size
    · subst c
      rw [get_of_some hi hG']
      exact hrun'
    · have hlt : i < S₀.groups.size := by omega
      have e := hgold i hlt
      rw [Array.getElem?_eq_getElem hlt] at e
      rw [get_of_some hi e]
      exact h0.1 i hlt
  · rcases Nat.lt_trichotomy i S₀.oracles.size with c | c | c
    · -- an older message
      have e : S'.oracles[i]? =
          (S₀.oracles.modify id fun x => { x with spentAsMask := true })[i]? :=
        hold i (by rw [hos]; exact c)
      rw [Array.getElem?_modify, Array.getElem?_eq_getElem c] at e
      have hsg : (S'.oracles[i]).sampled = (S₀.oracles[i]).sampled ∧
          (S'.oracles[i]).groups = (S₀.oracles[i]).groups := by
        by_cases k : id = i
        · rw [if_pos k] at e
          rw [get_of_some hi e]
          exact ⟨rfl, rfl⟩
        · rw [if_neg k] at e
          rw [get_of_some hi e]
          exact ⟨rfl, rfl⟩
      obtain ⟨g', hg', G, hG, hrun⟩ := h0.2 i c (hsg.1 ▸ hs)
      have hlt : g' < S₀.groups.size := by
        rcases Nat.lt_or_ge g' S₀.groups.size with k | k
        · exact k
        · rw [Array.getElem?_eq_none k] at hG
          cases hG
      exact ⟨g', hsg.2 ▸ hg', G, (hgold g' hlt).trans hG, hrun⟩
    · -- the new message
      obtain ⟨x, hx, -, hxg⟩ := new_behind D T S₀.groups.size #[N]
        (Ground.withGroup (spent S₀ id) a b)
      rw [← h.st, hos, ← c] at hx
      rw [get_of_some hi hx, hxg]
      exact ⟨S₀.groups.size, List.mem_singleton.2 rfl, G', hG', hrun'⟩
    · -- the message that rode with it
      have hr := rider_behind D T S₀.groups.size N (Ground.withGroup (spent S₀ id) a b) hm
      rw [← h.st, hos] at hr
      have hi2 : i = S₀.oracles.size + 1 := by
        have : (OnBytes.Slice.sentOf T #[N]).size = 2 := by simp [OnBytes.Slice.sentOf]
        rw [hosz, hos, this] at hi
        omega
      subst hi2
      rw [get_of_some hi hr] at hs
      cases hs

end Johnson.Prover.Link
