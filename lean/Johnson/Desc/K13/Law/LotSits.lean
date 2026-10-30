-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/LotSits.lean: kind K13's three lots of the proof file's description, under the
seat's wrappers, say yes only where the blocks of which the kind's laws speak say the same yes, at
the plan's numbers. Statements with their proofs.

The maker of the proof file's description (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean, partsAt) lays at a
place a member x of a lot's blocks as "{ guardMark x with name := the place's name }": x with
another name and with a refusal at a marked record behind its decision. A lot's blocks are its own
blocks at the description's type of claims (Block.retype; Johnson/Desc/ProofFile/LotCore.lean,
Lot.blocks). Here the wrapper is a letter c with Guards c x (Johnson/Desc/First/K8/LawSeated.lean):
"c has x's rounds, and c's decision is x's with that refusal behind it". The maker's own term has
it by unfolding; that is not typed here, so that this file stands on the lots alone.

Main theorems, for every public part Z, all segments' records G, every member x of the lot's blocks
and every c with Guards c x:
  lot_one, lot_sits        the lot of the members' batching has one block; it stands at atM3's
                           place; c.UnderR (atM3 (whereOf Z)).
  lot4_sits                the lot of W's commitment: there is the message msg that the shape gives,
                           and c.UnderR (atM4 (whereOf Z) (K1.sendAtS (K1.parW … 4 msg))).
  lotEnd_one, lotEnd_sits  the lot of the first chain's end has one block;
                           c.UnderR (ChainEnd.chainEnd 1 5 true (inFrontOf Z) endAsks).
  lot_under, lot4_under, lotEnd_under   the same of the member x itself, without a wrapper: for a
                           seat's statement that ends in "b.UnderR x" in a form of its own.
  guards_written           the maker's wrapper, written out, has Guards: at every block and name.
  lot_is, lotEnd_is        each of these two lots' one block IS the law's block at the description's
                           type of claims, field for field, but for its test on the plan.
  lot4_is                  the lot of W's commitment holds atM4 over K1's sending, by Block.retype.
The laws that pass along UnderR are called at such a c in Johnson/Desc/K13/Law/LotSitsCalls.lean
[not in this library].
Block.UnderR (Johnson/Desc/Sound/SeatGuardChain.lean): the same rounds, and a yes of the first is
the same yes of the second. It reads neither the name nor the test on the plan: so the conjunct that
the first lot adds to its block's test on the plan does not enter.

What is not claimed. THAT THE DESCRIPTION's LIST OF BLOCKS HOLDS SUCH A c AT THE KIND's PLACES: that
is a statement on the maker, general in the lot, and is typed elsewhere. That whereOf Z has given
values. The other premises of the laws that are called stay premises. Nothing on the key file's
description, which seats the kind too. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Lot.K13At4
import Johnson.Desc.ProofFile.Lot.K13End
import Johnson.Desc.Sound.SeatedGuards
import Johnson.Desc.K13.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (S endAsks)
open VerifiableInference.Desc.First.K8 (Guards)
open ProofFile (Pub Lot Ground Cl)

/-! ## 0 The wrapper -/

/-- The maker's wrapper, written out: another name, and a refusal at a marked record behind the
decision. ("{ guardMark b with name := n }", Johnson/Desc/ProofFile/Frames1.lean, unfolds to it.) -/
theorem guards_written (b : Block S Cl) (n : String) :
    Guards { b with
      name := n
      decide := fun s rs gs => (b.decide s rs gs).bind fun t =>
        match t.failed with
        | none => .ok t
        | some m => .error ("marked: " ++ m) } b :=
  ⟨rfl, fun _ _ _ => rfl⟩

/-! ## 1 The members' batching -/

/-- **The lot's one block is atM3 at the plan's numbers**, at the description's type of claims, but
for its test on the plan, which asks two things more: that the table of stretches has the step, and
that the block states no run of claims. -/
theorem lot_is (Z : Pub) (G : Ground) : (lot Z).blocks G =
    [{ (atM3 (whereOf Z) : Block S Cl) with
        planOk := ((atM3 (Cl := Unit) (whereOf Z)).planOk && (fromOf? Z).isSome) &&
          (atM3 (Cl := Unit) (whereOf Z)).claims.isEmpty }] := rfl

/-- The lot has one block: atM3 at the plan's numbers, with one conjunct more in its test on the
plan, at the description's type of claims. -/
theorem lot_one (Z : Pub) (G : Ground) : ∃ x, (lot Z).blocks G = [x] ∧
    x.place = (atM3 (Cl := Cl) (whereOf Z)).place ∧
    x.rounds = (atM3 (Cl := Cl) (whereOf Z)).rounds ∧
    x.decide = (atM3 (Cl := Cl) (whereOf Z)).decide :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- The lot's member itself, without a wrapper. -/
theorem lot_under (Z : Pub) (G : Ground) (x : Block S Cl) (hx : x ∈ (lot Z).blocks G) :
    x.UnderR (atM3 (whereOf Z)) := by
  obtain ⟨y, e, _, hr, hd⟩ := lot_one Z G
  rw [e] at hx
  obtain rfl := List.mem_singleton.1 hx
  exact ⟨hr, fun s rs gs s' h => by rw [← hd]; exact h⟩

/-- **The tie at the members' batching.** -/
theorem lot_sits (Z : Pub) (G : Ground) (x : Block S Cl) (hx : x ∈ (lot Z).blocks G)
    (c : Block S Cl) (hc : Guards c x) : c.UnderR (atM3 (whereOf Z)) :=
  hc.underR.trans (lot_under Z G x hx)

/-! ## 2 W's commitment, the own group and (Eval) -/

/-- **The lot's blocks are atM4 at the plan's numbers over kind K1's sending of W**, at the
description's type of claims by Block.retype: one block where the shape gives the message, none
where it gives none. -/
theorem lot4_is (Z : Pub) (G : Ground) : (lot4 Z).blocks G =
    ((linMessageW Z.first.lin).toList.map fun msg =>
      ((atM4 (whereOf Z) (K1.sendAtS (K1.parW Z.first
        { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg)) : Block S Unit).retype :
          Block S Cl)) := by
  show ((wBlock Z).toList.map (atM4 (whereOf Z))).map
      (fun b : Block S Unit => (b.retype : Block S Cl)) ++ [] = _
  unfold wBlock K1.wAt
  cases linMessageW Z.first.lin <;> rfl

/-- The lot's member itself, without a wrapper. -/
theorem lot4_under (Z : Pub) (G : Ground) (x : Block S Cl) (hx : x ∈ (lot4 Z).blocks G) :
    ∃ msg, linMessageW Z.first.lin = some msg ∧
    x.UnderR (atM4 (whereOf Z) (K1.sendAtS
      (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg))) := by
  have hx' : x ∈ ((wBlock Z).toList.map (atM4 (whereOf Z))).map
      (fun b : Block S Unit => (b.retype : Block S Cl)) ++ [] := hx
  rw [List.append_nil, List.map_map] at hx'
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx'
  have hw' : wBlock Z = some w := by simpa using hw
  unfold wBlock K1.wAt at hw'
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hw'
  exact ⟨msg, hm, atM4_retype _ _⟩

/-- **The tie at W's commitment.** -/
theorem lot4_sits (Z : Pub) (G : Ground) (x : Block S Cl) (hx : x ∈ (lot4 Z).blocks G)
    (c : Block S Cl) (hc : Guards c x) : ∃ msg, linMessageW Z.first.lin = some msg ∧
    c.UnderR (atM4 (whereOf Z) (K1.sendAtS
      (K1.parW Z.first { samples := Z.P.samples, firstTree := Z.P.firstTree } 4 msg))) := by
  obtain ⟨msg, hm, hu⟩ := lot4_under Z G x hx
  exact ⟨msg, hm, hc.underR.trans hu⟩

/-! ## 3 The first chain's end -/

/-- **The lot's one block is the chain's end at the plan's rounds**, at the description's type of
claims, but for its test on the plan, which asks one thing more: that it states no run of claims. -/
theorem lotEnd_is (Z : Pub) (G : Ground) : (lotEnd Z).blocks G =
    [{ (ChainEnd.chainEnd 1 5 true (inFrontOf Z) endAsks : Block S Cl) with
        planOk := (ChainEnd.chainEnd (Cl := Unit) 1 5 true (inFrontOf Z) endAsks).planOk &&
          (ChainEnd.chainEnd (S := S) (Cl := Unit) 1 5 true (inFrontOf Z)
            endAsks).claims.isEmpty }] :=
  rfl

/-- The lot has one block: the chain's end, at the description's type of claims. -/
theorem lotEnd_one (Z : Pub) (G : Ground) : ∃ x, (lotEnd Z).blocks G = [x] ∧
    x.place = ⟨1, none, 5, .frame⟩ ∧
    x.rounds = (ChainEnd.chainEnd (Cl := Cl) 1 5 true (inFrontOf Z) endAsks).rounds ∧
    x.decide = (ChainEnd.chainEnd (Cl := Cl) 1 5 true (inFrontOf Z) endAsks).decide :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-- The lot's member itself, without a wrapper. -/
theorem lotEnd_under (Z : Pub) (G : Ground) (x : Block S Cl) (hx : x ∈ (lotEnd Z).blocks G) :
    x.UnderR (ChainEnd.chainEnd 1 5 true (inFrontOf Z) endAsks) := by
  obtain ⟨y, e, _, hr, hd⟩ := lotEnd_one Z G
  rw [e] at hx
  obtain rfl := List.mem_singleton.1 hx
  exact ⟨hr, fun s rs gs s' h => by rw [← hd]; exact h⟩

/-- **The tie at the first chain's end.** -/
theorem lotEnd_sits (Z : Pub) (G : Ground) (x : Block S Cl) (hx : x ∈ (lotEnd Z).blocks G)
    (c : Block S Cl) (hc : Guards c x) :
    c.UnderR (ChainEnd.chainEnd 1 5 true (inFrontOf Z) endAsks) :=
  hc.underR.trans (lotEnd_under Z G x hx)

end VerifiableInference.Desc.K13.Law
