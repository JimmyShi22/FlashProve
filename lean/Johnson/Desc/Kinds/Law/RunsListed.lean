-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RunsListed.lean: the lists of claims that the blocks of the output head's own
rounds (K6) and of the next token (K7) state are just those that the driver's order names at their
numbers in the head's segment, each once, in the order's own order.

What the file holds.
  k6_number, k7_number      in the head's segment K6's block has the number 3 and K7's the number 0,
                            whether or not the segment is the chain's first.
  listed3, listedAfter3, listed0, listedAfter0   what the two orders name at these numbers, written
                            out: at 3: norm, join, policy, logits, and none after the batching; at
                            0: none.
  once3                     each of the four stands in the order just once.
  k6_states_listed          **blockClaims W l = some b: the names of b's lists, under the number 3,
                            are the order's entries at 3, in order; after the batching b has none,
                            and the order names none at 3.**
  seated_states_listed      **the same of seatedClaims W l before = some b**, for every list before:
                            the term that the description seats.
  k7_states_none            Reply.blockOf W l states no list, and the orders name none at 0.
  kind_lacks_join           a control: the kind without the join (Johnson/Desc/Kinds/HeadKind.lean:
                            kind) states three lists: not the order's four.
Why. The test on a segment's order (Johnson/Desc/Block.lean: orderOk, orderAfterOk) asks that every
named list of every block stands in the order just once, and that the order names no other. The
driver lays the orders uncut (Johnson/Desc/First/Driver/Chain.lean: orderOf, orderAfterOf). This
file pays that test's share of two blocks.

What it does not give. Nothing on soundness. Nothing on what the lists hold. Not orderOk of a whole
segment: that asks the like of the other blocks of the head's segment. That the two blocks are
seated at these two numbers is not shown here.

-/
import Johnson.Desc.First.Driver.Chain
import Johnson.Desc.Kinds.Law.BlockClaimsIs
import Johnson.Stored.ReplySeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Listed

open OnBytes.Model.Verify (Public)
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.First (S ModelPart orderOf orderAfterOf kindsBeforeBatching)

theorem k6_number (first : Bool) : (kindsBeforeBatching .head first)[3]? = some KindName.K6 := by
  cases first <;> rfl

theorem k7_number (first : Bool) : (kindsBeforeBatching .head first)[0]? = some KindName.K7 := by
  cases first <;> rfl

/-- What the order names at number 3 of the head's segment. -/
theorem listed3 : (orderOf .head).filter (fun o => o.1 == 3) =
    [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")] := by
  decide
theorem listedAfter3 : (orderAfterOf .head).filter (fun o => o.1 == 3) = [] := by decide
theorem listed0 : (orderOf .head).filter (fun o => o.1 == 0) = [] := by decide
theorem listedAfter0 : (orderAfterOf .head).filter (fun o => o.1 == 0) = [] := by decide

/-- Each of the four stands in the order just once. -/
theorem once3 : ∀ o ∈ [((3 : Nat), "norm"), (3, "join"), (3, "policy"), (3, "logits")],
    (orderOf .head).count o = 1 := by
  decide

/-- **K6's block states just the runs that the order lists at its number.** -/
theorem k6_states_listed (W : Public) (l : Nat) (b : Block S Claim) (h : blockClaims W l = some b) :
    b.claims.map (fun c => ((3 : Nat), c.1)) = (orderOf .head).filter (fun o => o.1 == 3) ∧
      b.after.map (fun c => ((3 : Nat), c.1)) =
        (orderAfterOf .head).filter (fun o => o.1 == 3) := by
  have h1 := AtClaim.runs_are W l
  rw [h] at h1
  have h2 : b.claims.map (·.1) = ["norm", "join", "policy", "logits"] := Option.some.inj h1
  have h3 : b.after = [] := by
    unfold blockClaims at h
    obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  refine ⟨?_, by rw [h3, listedAfter3]; rfl⟩
  rw [listed3]
  have e : b.claims.map (fun c => ((3 : Nat), c.1)) =
      (b.claims.map (·.1)).map fun n => ((3 : Nat), n) := by
    rw [List.map_map]
    rfl
  rw [e, h2]
  rfl

/-- **The same at the term that the lot seats.** -/
theorem seated_states_listed (W : Public) (l : Nat) (before : List (Nat × Nat)) (b : Block S Claim)
    (h : seatedClaims W l before = some b) :
    b.claims.map (fun c => ((3 : Nat), c.1)) = (orderOf .head).filter (fun o => o.1 == 3) ∧
      b.after.map (fun c => ((3 : Nat), c.1)) =
        (orderAfterOf .head).filter (fun o => o.1 == 3) := by
  unfold seatedClaims at h
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  exact k6_states_listed W l b0 h0

/-- **K7's block states no run**, and the orders name none at its number. -/
theorem k7_states_none (W : Public) (l : Nat) :
    (Reply.blockOf W l).claims.map (fun c => ((0 : Nat), c.1)) =
        (orderOf .head).filter (fun o => o.1 == 0) ∧
      (Reply.blockOf W l).after.map (fun c => ((0 : Nat), c.1)) =
        (orderAfterOf .head).filter (fun o => o.1 == 0) := by
  rw [listed0, listedAfter0]
  exact ⟨rfl, rfl⟩

/-- **A control**: the kind without the join states three runs: not the order's four. -/
theorem kind_lacks_join {σ Cl : Type} (cl : Form → Cl) (L : Seat σ) (link piece : Nat) (p : Par) :
    (kind cl L link piece p).claims.map (fun c => ((3 : Nat), c.1)) ≠
      (orderOf .head).filter (fun o => o.1 == 3) := by
  rw [listed3]
  intro h
  have := congrArg List.length h
  simp [kind, runsBy] at this

end VerifiableInference.Desc.Kinds.Head.Law.Listed

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Listed.k6_states_listed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Listed.seated_states_listed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Listed.k7_states_none
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Listed.kind_lacks_join
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Listed.once3
