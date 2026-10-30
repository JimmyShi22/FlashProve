-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/EvalAlone.lean: kind K13 (the members' batching), the block behind W's
commitment (`rowsB`): behind its yes the request's own group holds just one open row, the row
(Eval). Two definitions; statements with their proofs.

What it is for. The library's `EvalLaid` (Johnson/Desc/K13/Law/Laid.lean) says that (Eval) is AMONG
the own group's open rows. The first member of the last chain reads EVERY open row of that group
(`RowsHold`, Johnson/Desc/Third/Law/Row0.lean). An honest prover's side knows of (Eval) that it says
its claim (`WRow`, Johnson/Desc/K13/Law/Letters.lean); to go from that one row to all open rows one
needs that there is no other.

Main names.
  `NoRow S g`: the group number g of the statement S is there and has no open row.
  `rows_alone`: wherever the text behind W's commitment (`rows`) returns, the own group's open rows
    are just the row (Eval) that the text makes.
  `EvalAlone P s`: **the sentence on a state of the first chain**: what goes on to the last chain is
    laid in it (`linAt`); (Eval) is made of that; the own group is there and its open rows are
    (Eval) alone.
  `K13RowsKeeps.alone`: **behind every yes of the block `EvalAlone` holds** (from `K13RowsKeeps`,
    RowsKeeps.lean of this folder, which every yes gives).
  `allSay_of_wRow`: under `EvalAlone`, if (Eval) says its claim of some words, every open row of the
    own group does.

How. The text makes a new group, which has no row; the joinings change its members alone; then one
row is added.

Limits. Statements on the verifier's public state and text alone: no prover, coin or witness is
named. `EvalAlone` is shown behind the block's yes, at that state. That a later member of the chain
leaves it is not shown here.

What is not claimed. None of these is one of the library's goals. Nothing on soundness, completeness
or hiding.
-/
import Johnson.Desc.K13.Honest.RowsKeeps
import Johnson.Desc.K13.Law.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open OnBytes.Means (Words AllSay)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law

/-- The group number g is there and has no open row. -/
def NoRow (T : Statement) (g : ℕ) : Prop := ∃ G : Group, T.groups[g]? = some G ∧ G.rows = #[]

/-- A group that has just been made has no open row. -/
theorem NoRow.start (T : Statement) (c z : ℕ) : NoRow (Ground.withGroup T c z) T.groups.size :=
  ⟨{ code := c, maskCode := z }, by simp [Ground.withGroup], rfl⟩

/-- A joining changes the group's members alone. -/
theorem NoRow.step {T : Statement} {g : ℕ} (h : NoRow T g) (o : ℕ) (k : Bool) (G₀ : Group) :
    NoRow (withMessageInGroup T g o k G₀) g := by
  obtain ⟨G, hG, hr⟩ := h
  have e : (withMessageInGroup T g o k G₀).groups[g]? = some { G with
                  members := G.members.insertIdxIfInBounds (G₀.members.filter (· < o)).size o
                  kept := G.kept.insertIdxIfInBounds (G₀.members.filter (· < o)).size k } := by
    simp [withMessageInGroup, Array.getElem?_modify, hG]
  exact ⟨_, e, hr⟩

/-- One joining that returns. -/
theorem join_noRow {g o : ℕ} {k : Bool} {d d' : St} (h : NoRow d.st g)
    (hj : Ground.joinP d g o k = some d') : NoRow d'.st g := by
  obtain ⟨G, _, _, e⟩ := joinP_inv hj
  rw [e]
  exact h.step o k G

/-- Joinings in a row that return. -/
theorem joinAll_noRow {g : ℕ} : ∀ (l : List ℕ) (d d' : St), NoRow d.st g →
    K13.joinAll g l d = .ok d' → NoRow d'.st g
  | [], d, d', h, hj => by
    obtain rfl : d = d' := Except.ok.inj hj
    exact h
  | o :: l, d, d', h, hj => by
    simp only [K13.joinAll, Law.bind_ok, Law.there_ok] at hj
    obtain ⟨d₁, h1, h2⟩ := hj
    exact joinAll_noRow l d₁ d' (join_noRow h h1) h2

/-- **Wherever the text behind W's commitment returns, the own group's open rows are just the row
(Eval) that the text makes.** -/
theorem rows_alone {Sh : LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St}
    {o : LinFirst × St} (h : rows Sh claim ids d = .ok o) :
    ∃ (r : OnBytes.Row) (G : Group),
      linEvalRow Sh claim o.1.w (linLayW d.st.codes Sh) = some r ∧
      o.2.st.groups[o.1.own]? = some G ∧ G.rows.toList = [r] := by
  simp only [rows_is, Law.bind_ok, Law.there_ok, Law.pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, hr, d₄, h4, rfl⟩ := h
  obtain ⟨e1, e2⟩ := newGroupP_inv hb
  have B0 : NoRow b.2.st b.1 := by
    rw [e1, e2]
    exact NoRow.start d.st _ _
  have B2 := join_noRow (joinAll_noRow _ _ _ B0 h1) h2
  have B3 : NoRow d₃.st b.1 := by
    split at h3
    · exact join_noRow B2 h3
    · rw [← Option.some.inj h3]
      exact B2
  obtain ⟨G, hG, hG0⟩ := B3
  obtain ⟨_, _, _, e4⟩ := addRows_one h4
  have hc : d₃.st.codes = d.st.codes := by
    have c2 : d₂.st.codes = d.st.codes := by
      rw [join_codes h2, joinAll_codes _ _ _ _ h1, newGroup_codes hb]
    split at h3
    · rw [join_codes h3, c2]
    · rw [← Option.some.inj h3, c2]
  rw [hc] at hr
  refine ⟨row, { G with rows := G.rows.push row }, hr, ?_, by rw [hG0]; rfl⟩
  show d₄.st.groups[b.1]? = _
  rw [e4]
  exact withRow_group _ _ _ _ hG

/-- **THE SENTENCE.** What goes on to the last chain is laid in the state (l); (Eval) is made of l's
claim at W's layout (r); the own group is there, and its open rows are r alone. -/
def EvalAlone (P : Where) (s : S) : Prop :=
  ∃ (l : LinFirst) (r : OnBytes.Row) (G : Group), linAt s = some l ∧
    linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin) = some r ∧
    s.st.groups[l.own]? = some G ∧ G.rows.toList = [r]

/-- **Behind every yes of the block behind W's commitment.** -/
theorem K13RowsKeeps.alone {P : Where} {t s' : S} (h : K13RowsKeeps P t s') : EvalAlone P s' := by
  obtain ⟨m₀, l, o, _, _, hr, rfl⟩ := h
  obtain ⟨r, G, h1, h2, h3⟩ := rows_alone hr
  obtain ⟨_, _, _, hc, _, _, _, _, _, hcodes⟩ := rows_ok hr
  refine ⟨o.1, r, G, rfl, ?_, h2, h3⟩
  show linEvalRow P.lin o.1.claim o.1.w (linLayW o.2.st.codes P.lin) = some r
  rw [hc, hcodes]
  exact h1

/-- **Under the sentence: if (Eval) says its claim of the words, every open row of the own group
does.** -/
theorem allSay_of_wRow {P : Where} {s : S} (hA : EvalAlone P s) (m : Words GE) (hR : WRow P s m) :
    ∀ l G, linAt s = some l → s.st.groups[l.own]? = some G → AllSay ρg s.st G.rows.toList m := by
  obtain ⟨l, r, G, hl, hr, hG, hrows⟩ := hA
  intro l' G' hl' hG' r' hr'
  obtain rfl : l = l' := Option.some.inj (hl.symm.trans hl')
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  rw [hrows] at hr'
  obtain rfl := List.mem_singleton.1 hr'
  exact hR l r' hl hr

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.NoRow.start
#print axioms VerifiableInference.Desc.K13.Honest.NoRow.step
#print axioms VerifiableInference.Desc.K13.Honest.join_noRow
#print axioms VerifiableInference.Desc.K13.Honest.joinAll_noRow
#print axioms VerifiableInference.Desc.K13.Honest.rows_alone
#print axioms VerifiableInference.Desc.K13.Honest.K13RowsKeeps.alone
#print axioms VerifiableInference.Desc.K13.Honest.allSay_of_wRow
