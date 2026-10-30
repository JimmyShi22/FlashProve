-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/TiesAtSeat.lean: THE TIES OF THE LINK's LAW AT THE SEAT, FOR EVERY KIND
AT ONCE, DOWN TO THE LOT's OWN BLOCK: at a link of the description's first chain, whatever run
stands at an entry (i, name) of an order stands under the run that a lot's own block, at the place
⟨1, l, i + 1, ‹the kind›⟩, states under that name (`Under`, Johnson/Desc/First/Link/Law/Under.lean).
Theorems, over the seat's own law on its hearing blocks (Johnson/IMR/LaidFirst.lean:
`chain_hear_alone`; Johnson/IMR/SeatForm.lean: `claim_yes`, `after_yes`).

Why. The assembly of the kinds' laws (PayLayers.lean, PayAttention.lean, PayHead.lean) takes, an
entry at a time, a tie: the run that stands there stands under the kind's own run. At the seat a
hearing block is a lot's block behind the seat's wrappers and the driver's guard. All of these only
add refusals. So each tie comes down to one fact a kind: which block its lot lays at the place, and
what that block states.

What is said. `under_alone`, `underAfter_alone`: a run that is looked up in a seated block stands
under the run of that name in the lot's block. `ties_at_seat`: **at the hearing block number i (1 ≤
i ≤ 8) of the link number l: there is a lot of the seat's list and a block b' of it at that place,
such that every run at an entry (i, name), in front of the batching or behind it, stands under b' 's
run of that name.**

Limits. WHICH block b' is (that it is the kind's own block, at which parameters), and that its run
is the run of the kind's law, stays each kind's to show. Nothing on soundness.

-/
import Johnson.IMR.LaidFirst
import Johnson.Desc.First.Link.Law.Under
import Johnson.Desc.First.Link.Law.LinkJoinPay

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (At AtAfter Under UnderAfter)
open ProofFile (Cl)
open IM (LaidAlone)

/-- A run of claims that is looked up in a seated block stands under the lot's block's. -/
theorem under_alone {same : S → S → Bool} {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidAlone same b b' name a) {n : String} {r : ℕ → S → Except String (List Cl × S)}
    (hr : b.claims.lookup n = some r) : ∃ r', b'.claims.lookup n = some r' ∧ Under r r' := by
  obtain ⟨r', h1, _, h3⟩ := IM.claim_yes h hr
  exact ⟨r', h1, fun k t c t₁ hy => ((h3 k t (c, t₁)).1 hy).1⟩

/-- The like behind the batching. -/
theorem underAfter_alone {same : S → S → Bool} {b b' : Block S Cl} {name : String} {a : Place}
    (h : LaidAlone same b b' name a) {n : String} {r : S → Except String S}
    (hr : b.after.lookup n = some r) : ∃ r', b'.after.lookup n = some r' ∧ UnderAfter r r' := by
  obtain ⟨r', h1, _, h3⟩ := IM.after_yes h hr
  exact ⟨r', h1, fun t u hy => ((h3 t u).1 hy).1⟩

variable {o : ProofFile.SecondHashFunctionArgument}

/-- **THE TIES AT THE SEAT, DOWN TO THE LOT's OWN BLOCK.** -/
theorem ties_at_seat {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub) (i : ℕ) (k : KindName)
    (hk : (kindsBeforeBatching sub (l == 0))[i]? = some k) (hk9 : k ≠ KindName.K9) (hk10 : k ≠ KindName.K10)
    (hi : 2 ≤ i + 1 ∧ i + 1 ≤ 9) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, ∃ b' ∈ L.blocks B.G₀,
      b'.place = { chain := 1, link := some l, piece := i + 1, kind := k } ∧
      (∀ name run, At Lk (i, name) run → ∃ r', b'.claims.lookup name = some r' ∧ Under run r') ∧
      ∀ name run, AtAfter Lk (i, name) run →
        ∃ r', b'.after.lookup name = some r' ∧ UnderAfter run r' := by
  obtain ⟨Lk, b, e1, e2, sp, _, L, hL, b', hb', _, ep, ha⟩ :=
    IM.chain_hear_alone hB hb hc l sub hl i k hk hk9 hk10 hi
  refine ⟨Lk, e1, L, hL, b', hb', ep, fun name run h => ?_, fun name run h => ?_⟩
  · have h' : ((Lk.hear[i]?).bind fun x => x.claims.lookup name) = some run := h
    rw [e2] at h'
    exact under_alone ha h'
  · have h' : ((Lk.hear[i]?).bind fun x => x.after.lookup name) = some run := h
    rw [e2] at h'
    exact underAfter_alone ha h'

end LPFK9

#print axioms LPFK9.under_alone
#print axioms LPFK9.underAfter_alone
#print axioms LPFK9.ties_at_seat
