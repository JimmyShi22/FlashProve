--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesLocAt.lean: the function of the place "LOC" of the linear claim's shared
rounds returns a state, which is written out.

The place lays one constraint for each location sampled, off the committed table's column there. A
location is taken modulo the code's length.

The function is the own text of the IOP as written in Lean (Johnson/Desc/K14/Text.lean). The
sub-protocol's decide function is that function under the names of its tests. A decision is the
format's step (Johnson/Desc/Block.lean: Block.step), which tests the rounds' form and the columns in
front of the decide function. That the eight decide functions return .ok: Returned.decides
(Johnson/Desc/K14/Honest/YesChain.lean). That the eight steps do: eight_steps_hold
(Johnson/Desc/K14/Honest/ChainSteps.lean).

Main name: loc_returns.

What is not claimed. That a decision accepts. That the facts in front hold at any state, or that the
columns are there. Nothing on what the constraints mean, on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesFacts
import Johnson.Desc.Key.Laid.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (withRows)
open OnBytes.Means (addRowsP_of_fits)
open VerifiableInference.Desc.Key (mapM_some)

/-- **The function of "LOC" returns**: the constraints, one for each location sampled, stand behind
the rows of o_u's group. hcols: each location sampled has its column, of as many words as the
table has rows. -/
theorem loc_returns (p : Par) (d : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (h : FrontU p d [d.loc.oU.oracle])
    (hcols : ∀ x ∈ r.drawn.poss, ∃ col,
      cols.lookup (x % 2 ^ p.S.fold.index.code.logN) = some col ∧
        col.length = p.S.fold.index.rows) :
    ∃ rows, Law.locRows p d.loc r cols = some rows ∧
      loc p d [r] [cols] = some { d with st := (withRows d.st d.loc.gU rows) } := by
  obtain ⟨G, hG, _, _, hrun, hmem⟩ := h.gU
  have R := shapeSizes_of d.st.codes p.S h.lin
  have hw := weights_size p d h.psi
  have hS0 := sits_u h.lin h.u G (contains_of hmem _ (by simp))
  rw [← h.lay] at hS0
  obtain ⟨rows, hm⟩ := mapM_makes (fun x : Nat => do
      locX p.S.fold x (weights p.S d.loc) ((← cols.lookup x).toArray) d.loc.oU)
    (r.drawn.poss.map (· % 2 ^ p.S.fold.index.code.logN)) (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      obtain ⟨col, hc1, hc2⟩ := hcols x hx
      obtain ⟨row, hrow⟩ := locX_makes p.S.fold (x % 2 ^ p.S.fold.index.code.logN)
        (weights p.S d.loc) col.toArray d.loc.oU (by rw [hw, List.size_toArray, hc2])
      refine ⟨row, ?_⟩
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
      exact ⟨col, hc1, hrow⟩)
  have ha := addRowsP_of_fits d d.loc.gU G rows hG hrun (by
    intro row hrow
    obtain ⟨a, _, e⟩ := (mapM_some _ _ _ hm).2 row hrow
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e
    obtain ⟨col, _, e⟩ := e
    exact locX_fits _ _ _ _ _ _ _ row e hS0 (by rw [h.lay]; exact R.cube)
      (by rw [h.lay]; exact R.tail) R.aligned)
  refine ⟨rows, hm, ?_⟩
  unfold loc
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  exact ⟨rows, hm, ha⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.loc_returns
