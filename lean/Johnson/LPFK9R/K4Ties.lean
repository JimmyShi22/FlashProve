-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/K4Ties.lean: THREE TIES OF THE LINK's LAW, WHOLE, AT THE SEAT: at a link
of the description's first chain whose hearing block number 2 is of the kind K4: the runs at the
entries (2, «front»), (2, «back») and, behind the batching, (2, «free-slot») stand under the runs of
the layers' own kind's block `blockAtC p`: the fields tFront, tBack, tFree of `LayersTies`
(Johnson/Desc/First/Link/Law/PayLayers.lean) to the letter, WITH p NAMED: `k4ParAt Z G₀ l = some p`:
a function of the public part, the letters at which the lots' tables are made, and l. Theorems,
after the pattern of Johnson/LPFK9R/MergeTie.lean.

What is said. `parOfMember`: the parameters at which the lot lays a member of its list. `k4_lists`:
every block of K4's lot is made of a member of that list, and has the place and the two lists of
`blockAtC` at its parameters. `k4ParAt`: the parameters at the segment number l. `k4ParAt_of_mem`: a
member that bears the number l is the one that it names, since one member at most bears a number
(Johnson/Desc/ProofFile/Lot/K4One.lean: `k4From_link_inj`). `k4_ties`: **the three ties.**

Limits. Three of 21 ties. What p's numbers are, field by field, is the kind's own files' to say.
Under the seat's three yeses. Nothing on soundness.

-/
import Johnson.LPFK9R.TiesAtSeat
import Johnson.Desc.ProofFile.Lot.K4One

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (At AtAfter Under UnderAfter)
open OnBytes.Desc.First.K4 (Par blockAtC)
open ProofFile (Cl)

/-- The parameters at which K4's lot lays a member of its list. -/
def parOfMember (x : Bool × Par) : Par := { x.2 with k3Runs := true }

/-- Every block of K4's lot is made of a member x of the lot's own list, and has the place and the
two lists of the layers' own kind's block at that member's parameters. -/
theorem k4_lists {Z : ProofFile.Pub} {G : ProofFile.Ground} {b : Block S Cl}
    (hb : b ∈ (ProofFile.k4Lot Z).blocks G) :
    ∃ x ∈ ProofFile.k4From Z G G.built.toList 0 none, b.place = (blockAtC (parOfMember x)).place ∧
      b.claims = (blockAtC (parOfMember x)).claims ∧
      b.after = (blockAtC (parOfMember x)).after := by
  rcases IM.blocks_mem hb with ⟨x, hx, _⟩ | h
  · exact absurd hx (List.not_mem_nil)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    exact ⟨x, hx, rfl, rfl, rfl⟩

/-- **The layers' own kind's parameters at the segment number l**: of the first member of the lot's
own list that bears that number. A function of the public part, the letters and l. -/
def k4ParAt (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) : Option Par :=
  ((ProofFile.k4From Z G G.built.toList 0 none).find? fun x => x.2.link == l).map parOfMember

/-- A member of the lot's list that bears the number l is the one that k4ParAt names: one member at
most bears a number. -/
theorem k4ParAt_of_mem {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : ℕ} {x : Bool × Par}
    (hx : x ∈ ProofFile.k4From Z G G.built.toList 0 none) (hl : x.2.link = l) :
    k4ParAt Z G l = some (parOfMember x) := by
  unfold k4ParAt
  cases hf : (ProofFile.k4From Z G G.built.toList 0 none).find? fun y => y.2.link == l with
  | none =>
    have := List.find?_eq_none.1 hf x hx
    simp [hl] at this
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    have e : y.2.link = x.2.link := by
      rw [hl]
      simpa using hp
    rw [ProofFile.k4From_link_inj Z G _ _ _ y x hy hx e]
    rfl

variable {o : ProofFile.SecondHashFunctionArgument}

/-- **K4's THREE TIES, WHOLE, AT THE SEAT, AT THE PARAMETERS THAT k4ParAt NAMES.** -/
theorem k4_ties {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub)
    (hk : (kindsBeforeBatching sub (l == 0))[2]? = some KindName.K4) :
    ∃ Lk, c.links[l]? = some Lk ∧ ∃ p : Par, k4ParAt Z B.G₀ l = some p ∧
      (∀ run, At Lk (2, "front") run →
        ∃ r, (blockAtC p).claims.lookup "front" = some r ∧ Under run r) ∧
      (∀ run, At Lk (2, "back") run →
        ∃ r, (blockAtC p).claims.lookup "back" = some r ∧ Under run r) ∧
      ∀ run, AtAfter Lk (2, "free-slot") run →
        ∃ r, (blockAtC p).after.lookup "free-slot" = some r ∧ UnderAfter run r := by
  obtain ⟨Lk, e1, L, hL, b', hb', ep, t1, t2⟩ :=
    ties_at_seat hB hb hc l sub hl 2 .K4 hk (by decide) (by decide) (by decide)
  obtain rfl : L = ProofFile.k4Lot Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  obtain ⟨x, hx, c0, c1, c2⟩ := k4_lists hb'
  rw [c1] at t1
  rw [c2] at t2
  have e : (some x.2.link : Option ℕ) = some l := congrArg Place.link (c0.symm.trans ep)
  exact ⟨Lk, e1, _, k4ParAt_of_mem hx (Option.some.inj e), t1 "front", t1 "back", t2 "free-slot"⟩

end LPFK9

#print axioms LPFK9.k4_lists
#print axioms LPFK9.k4ParAt_of_mem
#print axioms LPFK9.k4_ties
