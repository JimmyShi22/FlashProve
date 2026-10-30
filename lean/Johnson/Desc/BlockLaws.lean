-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/BlockLaws.lean: small facts about the general functions of Johnson/Desc/Block.lean,
which hold of every description. Two so far. The tests behind the runs of claims can only refuse
(`claimsIn_of_claimsInBy`, with its two steps): so a law on a yes of `claimsIn` reaches the function
that `Link.blocksInOrder` hands the batching, `claimsInBy L.each L.hear L.order`. THE FUNCTION, NOT THE
BLOCK: `L.batch` is a letter here: what follows for the batching's block is for the files that
define it, in which it is seen how the block uses the function. And the chain's flat list with
its blocks outside the links under a name (`Chain.flat_eq`, `Block.asBare`), by unfolding.

Limits: tools: they hold of every list of blocks, so they say nothing of the protocol.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- The test behind a run can only refuse: a yes of a step with it is the same yes without it. -/
theorem claimsInStep_ok (each : Nat × String → List Cl → S → Except String Unit)
    (bs : List (Block S Cl)) (x z : List Cl × S) (o : Nat × String)
    (h : claimsInStep each bs x o = .ok z) : claimsInStep (fun _ _ _ => .ok ()) bs x o = .ok z := by
  unfold claimsInStep at h ⊢
  cases hn : named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.claims.lookup o.2) with
  | error e => simp [hn, Except.bind] at h
  | ok run =>
    simp only [hn, Except.bind] at h ⊢
    cases hr : run x.1.length x.2 with
    | error e => simp [hr] at h
    | ok y =>
      simp only [hr] at h ⊢
      cases he : each o y.1 y.2 with
      | error e => simp [he] at h
      | ok u => simpa [he] using h

/-- A fold of such steps that stands at a refusal stays there. -/
theorem claimsInFold_error (each : Nat × String → List Cl → S → Except String Unit)
    (bs : List (Block S Cl)) (order : List (Nat × String)) (e : String) :
    order.foldl
        (fun (acc : Except String (List Cl × S)) o => acc.bind fun x => claimsInStep each bs x o)
        (Except.error e) = Except.error e := by
  induction order with
  | nil => rfl
  | cons o l ih => exact ih

/-- **The tests behind the runs can only refuse**: a yes of the gatherer with them is the same yes,
with the same claims and the same record, of the gatherer without. So every law on a yes of
`claimsIn` reaches the function that `Link.blocksInOrder` hands the batching. -/
theorem claimsIn_of_claimsInBy (each : Nat × String → List Cl → S → Except String Unit)
    (bs : List (Block S Cl)) (order : List (Nat × String)) (s : S) (z : List Cl × S)
    (h : claimsInBy each bs order s = .ok z) : claimsIn bs order s = .ok z := by
  unfold claimsIn
  unfold claimsInBy at h ⊢
  generalize (Except.ok ([], s) : Except String (List Cl × S)) = acc at h ⊢
  induction order generalizing acc with
  | nil => exact h
  | cons o l ih =>
    cases acc with
    | error e =>
      rw [List.foldl_cons] at h
      rw [show (Except.error e : Except String (List Cl × S)).bind
        (fun x => claimsInStep each bs x o) = .error e from rfl, claimsInFold_error] at h
      cases h
    | ok x =>
      rw [List.foldl_cons] at h ⊢
      cases hs : claimsInStep each bs x o with
      | error e =>
        rw [show (Except.ok x : Except String (List Cl × S)).bind
          (fun x => claimsInStep each bs x o) = .error e from hs, claimsInFold_error] at h
        cases h
      | ok y =>
        rw [show (Except.ok x : Except String (List Cl × S)).bind
          (fun x => claimsInStep each bs x o) = .ok y from hs] at h
        rw [show (Except.ok x : Except String (List Cl × S)).bind
          (fun x => claimsInStep (fun _ _ _ => .ok ()) bs x o) = .ok y from
            claimsInStep_ok each bs x y o hs]
        exact ih _ h

/-! ## The chain's flat list, by name -/

/-- A block outside the links as `Chain.blocksInOrder` lays it: the same block, whose test on the plan also
asks that it has neither claims nor runs behind a batching. -/
def Block.asBare (b : Block S Cl) : Block S Cl := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

/-- **The chain's flat list**, with that block under a name: so that a law can lean on this equation
and not on `Chain.blocksInOrder`'s body. -/
theorem Chain.flat_eq (c : Chain S Cl) :
    c.blocksInOrder = c.first.asBare :: c.front.map Block.asBare ++ c.links.flatMap Link.blocksInOrder ++
      c.back.map Block.asBare ++ [c.last.asBare] := rfl

/-- Its test on the plan. -/
theorem Block.asBare_planOk (b : Block S Cl) : b.asBare.planOk = (b.planOk && b.hasNoClaimsAndNothingAfter) := rfl

/-- All else of the block stays. -/
theorem Block.asBare_decide (b : Block S Cl) : b.asBare.decide = b.decide := rfl
theorem Block.asBare_rounds (b : Block S Cl) : b.asBare.rounds = b.rounds := rfl
theorem Block.asBare_oracles (b : Block S Cl) : b.asBare.oracles = b.oracles := rfl
theorem Block.asBare_before (b : Block S Cl) : b.asBare.before = b.before := rfl
theorem Block.asBare_place (b : Block S Cl) : b.asBare.place = b.place := rfl
theorem Block.asBare_name (b : Block S Cl) : b.asBare.name = b.name := rfl
theorem Block.asBare_claims (b : Block S Cl) : b.asBare.claims = b.claims := rfl
theorem Block.asBare_after (b : Block S Cl) : b.asBare.after = b.after := rfl

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.claimsInStep_ok
#print axioms VerifiableInference.Desc.claimsInFold_error
#print axioms VerifiableInference.Desc.claimsIn_of_claimsInBy
#print axioms VerifiableInference.Desc.Chain.flat_eq
