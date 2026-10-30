-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BackPlace.lean. chain_back IS ALONE OUTRIGHT (chainBy joins a frame's block only behind a block that stands in the role's link: behind the links there is none).
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND THE DRIVER, NO PART OF THEM: BY INDEX: the block number j BEHIND THE
LINKS of onlineDescription's first chain (c.back[j]) is a lot's block at the blank letters, in the form of
Johnson/IMR/SeatForm.lean.
OBJECT. ProofFile.chainBy · chainC · fill and the driver's firstChain · firstChainWithoutReplyGuard (its field back := (addresses none (backKinds several)).mapM blockAt). USER. `K2Seat` («F:1»); K12's, K13's and K1's places behind the links, when somebody wants them.
LETTERS. As in Johnson/IMR/PureChain.lean; j k: the index and the kind, with (backKinds several)[j]?
= some k AT BOTH VALUES OF several (so j = 0: K2 · j = 1: K12).


THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut).

  firstChain_back   where the driver's firstChain returns a chain: its block number j behind the links is what the socket gives at the address (1, none, j + 1, k), with that address written into it, behind the driver's guard.
  chain_back        (general in the seat, under MakersK9) block number j behind the links is a lot's
    block at the blank letters: ALONE (LaidAlone): no second arm.

What is not claimed. Which lot. In Chain.blocksInOrder a block behind the links stands as { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }. No soundness.
-/
import Johnson.IMR.FirstPlace
import Johnson.IMR.SeatOpen

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain firstChainWithoutReplyGuard blockAt backKinds addresses hearsReply)
open ProofFile (Cl)

/-- **A block behind the links is the socket's at the driver's address, behind the driver's guard.** -/
theorem firstChain_back {σ C : Type} {H : Blocks σ C} {links : List ModelPart} {several : Bool}
    {c : Chain σ C} (h : firstChain H links several = some c) (j : ℕ) (k : KindName)
    (hk : (backKinds several)[j]? = some k) :
    ∃ b, H.block { chain := 1, link := none, piece := j + 1, kind := k } = some b ∧
      c.back[j]? = some (Block.guarded H.same hearsReply
        { b with place := { chain := 1, link := none, piece := j + 1, kind := k } }) := by
  obtain ⟨-, c0, ⟨-, -, -, hbk, -⟩, rfl⟩ := VerifiableInference.Desc.Shape.firstChain_shape h
  have h1 := congrArg (·[j]?) hbk
  simp only [List.getElem?_map, addresses_at none _ j k hk, Option.map_some] at h1
  obtain ⟨x, e, hx⟩ := Option.map_eq_some_iff.1 h1
  unfold blockAt at hx
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hx.symm
  refine ⟨b, hb, ?_⟩
  show (c0.back.map _)[j]? = _
  rw [List.getElem?_map, e]
  rfl

/-- **THE JOIN BEHIND THE LINKS, BY INDEX**: block number j behind the links is a lot's block at the blank letters: ALONE: chainBy joins a frame's block behind a block that stands IN THE ROLE's LINK alone. -/
theorem chain_back {Z : ProofFile.Pub} {T : ProofFile.PureSeat} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hM : MakersK9 T B.G₀) (hb : (ProofFile.partsAt T B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c) (j : ℕ)
    (k : KindName) (hk : ∀ several, (backKinds several)[j]? = some k) (hk9 : k ≠ KindName.K9) :
    ∃ b, c.back[j]? = some b ∧
      ∃ sp ∈ B.spots, ∃ L ∈ T.lots, ∃ b' ∈ L.blocks B.G₀,
        sp.place = { chain := 1, link := none, piece := j + 1, kind := k } ∧
        b'.place = { chain := 1, link := none, piece := j + 1, kind := k } ∧
        LaidAlone T.same b b' sp.name { chain := 1, link := none, piece := j + 1, kind := k } := by
  unfold ProofFile.chainBy at hc
  dsimp only at hc
  unfold ProofFile.chainC at hc
  split at hc
  · cases hc
  · rename_i z hz
    dsimp only at hc
    split at hc
    · cases hc
    · rename_i c1 h1
      split at hc
      · cases hc
      · obtain rfl := Except.ok.inj hc
        obtain ⟨b, hbk, eb⟩ := firstChain_back h1 j k (hk _)
        refine ⟨_, eb, ?_⟩
        have hm := List.mem_of_find?_eq_some hbk
        have hpl : b.place = { chain := 1, link := none, piece := j + 1, kind := k } := by
          simpa using List.find?_some hbk
        obtain ⟨b0, hb0, ej⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hm)
        obtain ⟨x, hx, ex⟩ := OnBytes.Road.L5.mapM_mem _ _ _ hb b0 hb0
        obtain ⟨sp, y⟩ := x
        obtain rfl : y = .ok b0 := ex
        obtain ⟨hsp, harm⟩ := places_from_lots hall sp b0 hx
        have eplace : b0.place = { chain := 1, link := none, piece := j + 1, kind := k } := by
          split at ej <;> subst ej <;> exact hpl
        rcases harm with ⟨mk, hmk, rfl⟩ | ⟨-, L, hL, b', hb', ep, rfl⟩
        · exfalso
          have hk' := face_kind hM hmk (fun s => .ok ([], s))
          rw [eplace] at hk'
          exact hk9 hk'
        · refine ⟨sp, hsp, L, hL, b', hb', ep.symm.trans eplace, eplace, ?_⟩
          split at ej
          · rename_i w hw
            exfalso
            have hpred := List.find?_some hw
            obtain ⟨r, q⟩ := w
            cases r with
            | behind l' m =>
              have em : sp.name = m ∧ b'.place.link = some l' := by simpa using hpred
              have eplace' : b'.place = { chain := 1, link := none, piece := j + 1, kind := k } := eplace
              rw [eplace'] at em
              exact nomatch em.2
            | front => cases hpred
            | lay _ => cases hpred
            | clear _ => cases hpred
            | common => cases hpred
            | stray => cases hpred
          · subst ej
            rfl

end IM

#print axioms IM.firstChain_back
#print axioms IM.chain_back
