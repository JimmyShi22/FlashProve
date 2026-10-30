-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FenceSendGround.lean: THE FENCE AT A SENDING (Johnson/Desc/Sound/FenceSend.lean): ITS FIVE CLAUSES ON WHAT A RECEIVING
WRITES (`Received`), PROVED OF THE DESCRIPTION's OWN RECEIVING: the plain ground's `recvP`
(Johnson/Desc/First/Base/Ground.lean). One theorem.

  `recvP_received`: where recvP ft d sent returns (ids, d₁): there is the planner's layout lay with
    Received ft sent lay d.st d.book d.roots d₁.st d₁.book d₁.roots. By `recvP_iff`, `recvD`
    (Johnson/Desc/K1/Law/Writes3.lean); the number of messages by the text of `stSent`; the book is `recvBook` by rfl; "statement and book are in
    step" is the last clause of the receiving's own test (`recvL`).
LEFT AT A REAL SENDING (K14's "send o_u", "send o_omega"): that the block's decision is recvP at the record in front and
then steps that leave the number of messages, the book and the roots · lay.shapes.size = the number of trees
that the piece's stretch lists · rec.

Every "there is", walked: lay: what the planner returned.
Limits. One routine of the ground. It closes no row. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FenceSend
import Johnson.Desc.K1.Law.Writes3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.Sound (Received recvBook)

variable {L : Type}

/-- **The ground's receiving writes what the fence's rule asks.** -/
theorem recvP_received (ft : Nat) (d d₁ : DState L) (sent : Array OracleNotice) (ids : Array Nat)
    (h : Ground.recvP ft d sent = some (ids, d₁)) :
    ∃ lay, Received ft sent lay d.st d.book d.roots d₁.st d₁.book d₁.roots := by
  obtain ⟨hok, lay, hlay, _, rfl⟩ := (recvP_iff ft d d₁ sent ids).1 h
  refine ⟨lay, hlay, ?_, ?_, rfl, rfl⟩
  swap
  · show (d.st.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle)).size = _
    rw [Array.size_append, Array.size_map]
  have h2 : (Ground.recvL d.st d.book sent).all (·.2) = true := hok
  unfold Ground.recvL at h2
  rw [List.all_append, Bool.and_eq_true] at h2
  have h3 := h2.2
  simp only [List.all_cons, List.all_nil, Bool.and_true, beq_iff_eq] at h3
  exact h3

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.recvP_received
