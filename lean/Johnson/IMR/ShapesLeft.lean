-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ShapesLeft.lean: FoldFacts' FIELD "K12.msgShapes": WHAT IS LEFT FOR THE SHAPES, in
the goals' scope, at the second hash function, at the named table snAt Z Bs.G₀ placesW: FOUR DEBTS,
AT 26 NUMBERS. One theorem, proved.

Compiled with the whole library.

  shapeDebts_left   ShapesOn, each asked at the states that the fold from s₀ reaches in front of it
    alone, at:
      k2link    (23) K2's code switch at a link's first place, l = 1 … 23;
      k2head    (1)  K2 at the head's link's second place (number 339);
      k2finish  (1)  K2's finish (353);
      k12       (1)  the proximity test (354):
    these four give ShapeDebts ft (snAt Z Bs.G₀ placesW) Z Bs.G₀ c s₀ (Johnson/IMR/ShapesJoin.lean).
      K1's 52
    places: by Johnson/IMR/ShapesK1.lean. The field "grows": by Johnson/IMR/GrowsFlat.lean.

With shapes_start (Johnson/IMR/ShapesJoin.lean): the field's own sentence from these four, the debts
on the
book (SendDebts) and the test sendsAreB.

OBJECT: ShapeDebts. USER: IMR/ShapesK2.lean. LETTERS: ft, s₀: free.

What is not claimed. The four debts. NO MEMBER. No soundness.
-/
import Johnson.IMR.SendsLeft
import Johnson.IMR.ShapesK1
import Johnson.IMR.GrowsFlat

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S kindsBeforeBatching backKinds)
open VerifiableInference.Desc.K12.Door (snAt sendsAreB msgsOfChain atFirstShapes)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **WHAT IS LEFT FOR THE SHAPES: FOUR DEBTS, AT 26 NUMBERS.** -/
theorem shapeDebts_left (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : ℕ} {s₀ : S}
    (k2link : ∀ l, 1 ≤ l → l < 24 → ∀ b' : Block S Cl,
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 } →
      ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ (14 * l + 2)) (snAt Z Bs.G₀ placesW (14 * l + 2)) b')
    (k2head : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := some 24, piece := 2, kind := .K2 } →
      ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ 339) (snAt Z Bs.G₀ placesW 339) b')
    (k2finish : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 1, kind := .K2 } →
      ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ 353) (snAt Z Bs.G₀ placesW 353) b')
    (k12 : ∀ b' : Block S Cl, (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) →
      b'.place = { chain := 1, link := none, piece := 2, kind := .K12 } →
      ShapesOn ft (ReachedAt ft c.blocksInOrder s₀ 354) (snAt Z Bs.G₀ placesW 354) b') :
    ShapeDebts ft (snAt Z Bs.G₀ placesW) Z Bs.G₀ c s₀ := by
  refine ⟨?_, ?_, ?_, grows_calm hS hR O⟩
  · intro l hl k b' hk hs lot hp
    by_cases h24 : l < 24
    · have e := (first_kind l h24).symm.trans hk
      by_cases h0 : l = 0
      · subst h0
        obtain rfl : KindName.K1 = k := Option.some.inj e
        exact shapes_K1_link (l := 0) (i := 0) (by omega) hk lot hp
      · rw [if_neg h0] at e
        obtain rfl : KindName.K2 = k := Option.some.inj e
        exact k2link l (by omega) h24 b' lot hp
    · obtain rfl : l = 24 := by omega
      obtain rfl : KindName.K7 = k := Option.some.inj hk
      exact nomatch hs
  · intro l hl i k b' hi hk hs lot hp
    have hi9 : i < 9 := Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.1 hk).1 (hear_lt9 l hl)
    have hk3 : k = .K1 ∨ k = .K2 ∨ k = .K12 := by
      revert hs
      cases k <;> simp [senderKind]
    rcases hk3 with rfl | rfl | rfl
    · exact shapes_K1_link hl hk lot hp
    · obtain ⟨rfl, rfl⟩ := hear_k2 l hl i hi9 hi hk
      exact k2head b' lot hp
    · exact absurd hk (hear_no_k12 l hl i hi9)
  · intro j k b' hk hs lot hp
    rcases j with _ | _ | _ | _ | j
    · obtain rfl : KindName.K2 = k := Option.some.inj hk
      exact k2finish b' lot hp
    · obtain rfl : KindName.K12 = k := Option.some.inj hk
      exact k12 b' lot hp
    · obtain rfl : KindName.K13 = k := Option.some.inj hk
      exact nomatch hs
    · obtain rfl : KindName.K1 = k := Option.some.inj hk
      exact shapes_K1_back O lot hp
    · exact nomatch hk

end IM

#print axioms IM.shapeDebts_left
