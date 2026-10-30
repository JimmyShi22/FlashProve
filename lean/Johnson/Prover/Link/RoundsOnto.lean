-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/RoundsOnto.lean: A ROUND AS A VIEW SHOWS IT IS THE LIBRARY's rvW d m c
(OnBytes/Slice/BlkHead.lean), at which the laws on the link's front are typed. Two forms: from items
as shown and any verifier message; from a message of the protocol that the description runs, whose
rounds' data are PQ.ofLib of the library's (OnBytes/TypedOracleCompiler/Run/PlanQJoin.lean).

Main names (namespace Johnson.Prover.Link).
  rvW_onto   items whose kinds are the round's, any c, any oracle part o: some m with that oracle
    part shows these items, and rvW d m c is (the items, what c draws).
  rvW_of_two   at (m, c) of the round at PQ.ofLib d: rvW d (o, m.2) c is what that protocol's view
    shows: by unfolding: the two rounds have one type of plain parts and one of verifier messages.

By: plain_onto, gplain_old (Johnson/Desc/K12/Law/TrOnto.lean).

Limits. The oracle part is free: what a view reads of a tree is tied nowhere here. The verifier
message is HANDED, not made: no premise on what is drawn (DrawnIs) is needed.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Law.TrOnto
import OnBytes.Slice.BlkHead
import OnBytes.TypedOracleCompiler.Run.PlanQJoin

set_option autoImplicit false

namespace Johnson.Prover.Link
open OnBytes.Slice _root_.Run Iop
open VerifiableInference.Desc (itemOf)

/-- **From items.** Items as shown whose kinds are the round's, and ANY verifier message c of the
library's round: some prover message m has rvW d m c = ⟨the items, what c draws⟩; its oracle part is
free. -/
theorem rvW_onto (d : PQ.RD) (vals : List Fmt.ItemValue)
    (hk : vals.map itemOf = d.items.filter (· != .root)) (o : (wRound d).Orc)
    (c : (wRound d).Chal) :
    ∃ m : (wRound d).Msg, m.1 = o ∧
      PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2) = vals ∧
      rvW d m c = ⟨vals, (ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ := by
  obtain ⟨x, hx⟩ := H2K.Onto.plain_onto d.items vals hk
  refine ⟨(o, GPlain.mk d.entry.work x (default : ℕ)), rfl, ?_, ?_⟩
  · rw [H2K.Onto.gplain_old]
    exact hx
  · unfold rvW
    rw [H2K.Onto.gplain_old, hx]

/-- **From a message of the protocol that the description runs.** The round that its view shows of
(m, c) at PQ.ofLib d is rvW d (o, m.2) c, at any oracle part o: by unfolding. -/
theorem rvW_of_two (d : PQ.RD)
    (m : (TypedOracleCompiler.Run.PQ.roundS (ckP .two) (TypedOracleCompiler.Run.PQ.ofLib d)).up.Msg)
    (c : (TypedOracleCompiler.Run.PQ.roundS (ckP .two) (TypedOracleCompiler.Run.PQ.ofLib d)).up.Chal)
    (o : (wRound d).Orc) :
    rvW d (o, m.2) c =
      ⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
        (ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩ := rfl

end Johnson.Prover.Link
