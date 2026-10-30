-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Honest/RidesQuiet.lean: the linear claim's shared rounds: claims on words GO
FORWARDS over a step that leaves what the kind notes, the messages and the book (QuietStep:
Johnson/Desc/K14/Law/LedgerOne.lean), and over a sending. At every family of words.

The library carries these claims backwards over such steps. Its lemmas are equalities on what a
claim reads of the state, so they serve forwards too.

Main names:
  says_quiet          a constraint says behind a QuietStep what it said in front
  rowsU_quiet         a stretch of the constraints on o_u's group, if it lies within the list in
                      front
  seated_quiet, omU_quiet, nearAt_quiet   where o_u stands in front: it stands behind; the library's
                      OmU and NearAt
  SendStep, SendStep.extends   what a sending leaves of the statement: the codes, the groups, the
                      messages that were there; so the statement behind is a later one in the
                      library's sense (Johnson/Desc/Means/Keeps.lean: Extends)
  smpOwn_send, rowsU_send   **over a sending**, where the statement in front is in order: by the
                      library's says_extends

What is not claimed. That a sending is a SendStep: not shown here. Nothing on soundness, on
completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.ItemsOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words InOrder)
open OnBytes.Slice (rdE)
open Desc.K14.Law (rowsOn RowsU OmU NearAt QuietStep uRK uRK_seated seatedUB seatedUB_grows
  omU_of_same)

/-- Over a step that leaves the messages a constraint says what it said. -/
theorem says_quiet {a b : St} (q : QuietStep a b) (r : Row) (m : Words Cb.Gl.E) :
    Means.Says rdE b.st r m ↔ Means.Says rdE a.st r m := by
  refine Means.says_of_shapes rdE q.msgs.1 (fun j => ?_) r m
  have ej := congrArg (Option.map Prod.fst) (q.msgs.2 j)
  simpa [Option.map_map, Function.comp_def] using ej

/-- **A stretch of the constraints on o_u's group goes forwards over such a step**, if it lies
within the list in front. -/
theorem rowsU_quiet {a b : St} (q : QuietStep a b) {i n : Nat} {m : Words Cb.Gl.E}
    (hlen : i + n ≤ (rowsOn a a.loc.gU).length) (h : RowsU rdE i n a m) : RowsU rdE i n b m := by
  obtain ⟨x, hx⟩ := q.on.later a.loc.gU
  intro r hr
  rw [q.loc, hx, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)] at hr
  exact (says_quiet q r m).2 (h r hr)

/-- o_u stands behind such a step, if it stands in front. -/
theorem seated_quiet (p : Par) {a b : St} (q : QuietStep a b) (hs : seatedUB p a = true) :
    seatedUB p b = true :=
  seatedUB_grows p a b q.on.grows (by rw [q.loc]) hs

/-- **The library's OmU goes forwards over such a step**, where o_u stands in front. -/
theorem omU_quiet (p : Par) (omW : Words Cb.Gl.E → Nat → Cb.Gl.E) {a b : St} (q : QuietStep a b)
    (hs : seatedUB p a = true) {w : Words Cb.Gl.E}
    (h : OmU p (uRK p) (fun w : Words Cb.Gl.E => w) omW a w) :
    OmU p (uRK p) (fun w : Words Cb.Gl.E => w) omW b w :=
  omU_of_same p (uRK p) _ omW b a w (by rw [q.loc])
    (by rw [uRK_seated p a hs, uRK_seated p b (seated_quiet p q hs), q.loc]) h

/-- **The library's NearAt goes forwards over such a step**, where o_u stands in front. -/
theorem nearAt_quiet (p : Par) {a b : St} (q : QuietStep a b) (hs : seatedUB p a = true)
    {w : Words Cb.Gl.E} {tab : Nat → List UInt64} {e' : Nat}
    (h : NearAt rdE p (uRK p a) w tab e') : NearAt rdE p (uRK p b) w tab e' := by
  rw [uRK_seated p a hs] at h
  rw [uRK_seated p b (seated_quiet p q hs)]
  exact NearAt.of_same rdE (by rw [q.loc]) (by rw [q.loc]) h

/-! ## Over a sending -/

/-- What a sending leaves of the statement: the codes, the groups, and every message that was
there. -/
structure SendStep (S S' : Statement) : Prop where
  codes : S'.codes = S.codes
  groups : S'.groups = S.groups
  old : ∀ o, o < S.oracles.size → S'.oracles[o]? = S.oracles[o]?

/-- The statement behind is a later statement, in the library's sense. -/
theorem SendStep.extends {S S' : Statement} (q : SendStep S S') : Means.Extends S S' :=
  ⟨q.codes, fun o x hx =>
    ⟨x, by rw [q.old o (Array.getElem?_eq_some_iff.1 hx).1]; exact hx, rfl⟩⟩

/-- **A message's sample constraints go forwards over a sending**, where the statement in front is
in order. -/
theorem smpOwn_send {o : Nat} {a b : St} {m : Words Cb.Gl.E} (hI : InOrder a.st)
    (q : SendStep a.st b.st) (h : SmpOwn o a m) : SmpOwn o b m := by
  obtain ⟨x, hx, hs⟩ := h
  exact ⟨x, by rw [q.old o (Array.getElem?_eq_some_iff.1 hx).1]; exact hx, fun r hr =>
    (Means.says_extends rdE q.extends (hI.samples o x hx r hr) m).2 (hs r hr)⟩

/-- **A stretch of the constraints on o_u's group goes forwards over a sending**, where the
statement in front is in order. -/
theorem rowsU_send {i n : Nat} {a b : St} {m : Words Cb.Gl.E} (hI : InOrder a.st)
    (q : SendStep a.st b.st) (g : b.loc.gU = a.loc.gU) (h : RowsU rdE i n a m) :
    RowsU rdE i n b m := by
  have e : rowsOn b b.loc.gU = rowsOn a a.loc.gU := by
    unfold rowsOn
    rw [g, q.groups]
  intro r hr
  rw [e] at hr
  have hm : r ∈ rowsOn a a.loc.gU := List.mem_of_mem_drop (List.mem_of_mem_take hr)
  unfold rowsOn at hm
  cases hG : a.st.groups[a.loc.gU]? with
  | none =>
    rw [hG] at hm
    cases hm
  | some G =>
    rw [hG] at hm
    exact (Means.says_extends rdE q.extends (hI.rows _ G hG r hm) m).2 (h r hr)

end Desc.K14.Honest

#print axioms Desc.K14.Honest.says_quiet
#print axioms Desc.K14.Honest.rowsU_quiet
#print axioms Desc.K14.Honest.seated_quiet
#print axioms Desc.K14.Honest.omU_quiet
#print axioms Desc.K14.Honest.nearAt_quiet
#print axioms Desc.K14.Honest.SendStep.extends
#print axioms Desc.K14.Honest.smpOwn_send
#print axioms Desc.K14.Honest.rowsU_send
