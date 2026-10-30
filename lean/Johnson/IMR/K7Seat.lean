-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K7Seat.lean: the place's first half (K2.headFrontQ's quiet block) is guarded (sameReply,
at every place) before the join. k7_of's LaidFramed IS OVERTAKEN by Johnson/IMR/FirstSeats.lean's
k7_sits.
Where the rest of this head and the Lean text differ, the Lean text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K7's place (the reply) in onlineDescription's
first chain.
OBJECT. THE SEATED CONSTANT: IM.k7Block X 24 := front.andThen "H:1" own, carried over by Block.retype, where own := Kinds.Reply.blockOf X 24 (Johnson/Stored/ReplySeatAt.lean; Johnson/Desc/ProofFile/Lot/K6K7.lean: k7Core) and front is a block without a
round that does K2.headFrontQ X.H.tl at own's place (Johnson/Desc/ProofFile/Lots/H1.lean: h1Own's text, to the letter), as it stands at F.first.links[24].hear[0].
USER. K7's laws. LETTERS. As in Johnson/IMR/K6Seat.lean.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean · Ladder/Bits.lean) hand every o: for these the in-scope halves are owed, at PublicCut (Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean)).

  lot_K7            a block of kind K7 of a lot of the seat is one of ProofFile.h1Own's, carried over.
  k7_of             at an opening's letters, in scope: link 24's first block in front of the
                    batching is LaidFramed (Johnson/IMR/FirstPlace.lean) of (k7Block X 24).retype at
                    ⟨1, some 24, 1, K7⟩.
  k7_alone_z        the same in one piece, from onlineDescription's value: LaidFramed, NOT «alone».
  k7_yes            a yes of that block gives: (k7Block X 24).decide says yes, with no mark behind it: at all the rounds and groups (alone), or at the front of them (a block joined) (yes_laid). AT K7's ADDRESS THE DRIVER's GUARD LEAVES THE DECISION FREE: nothing on the reply.

WHO PAYS THE PREMISES: as in Johnson/IMR/K6Seat.lean: that onlineDescription returns in scope is a premise.
What is not claimed. WHICH ARM, AND WHICH BLOCK OF THE FRAMES' LOT IS JOINED: FirstPlace.lean's head says why. What headFrontQ does. No soundness.
-/
import Johnson.IMR.FirstPlace
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

/-- **A block of kind K7 is one of ProofFile.h1Own's, carried over.** -/
theorem lot_K7 {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b : Block S Cl} (hb : b ∈ L.blocks G) (hk : b.place.kind = KindName.K7) :
    ∃ x ∈ ProofFile.h1Own G, b = x.retype := by
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  · rw [kind_frames Z G b hb] at hk; cases hk
  · rw [kind_K1 Z G b hb] at hk; cases hk
  · rw [kind_K2 Z G b hb] at hk; cases hk
  · rw [kind_K3 Z G b hb] at hk; cases hk
  · rw [kind_K4 Z G b hb] at hk; cases hk
  · rw [kind_K5 Z G b hb] at hk; cases hk
  · rw [kind_K8 Z G b hb] at hk; cases hk
  · rcases kind_K9 Z G b hb with e | e <;> rw [e] at hk <;> cases hk
  · rw [kind_K11 Z G b hb] at hk; cases hk
  · rw [kind_K12 Z G b hb] at hk; cases hk
  · rw [kind_K13 Z G b hb] at hk; cases hk
  · rw [kind_K13_4 Z G b hb] at hk; cases hk
  · rw [kind_K13_end Z G b hb] at hk; cases hk
  · rw [kind_K6 Z G b hb] at hk; cases hk
  · rcases blocks_mem hb with ⟨x, hx, rfl⟩ | hb
    · exact ⟨x, hx, rfl⟩
    · exact nomatch hb

/-- K7's place's block, as the seat's lot lays it (Johnson/Desc/ProofFile/Lots/H1.lean: h1Own). -/
def k7Block (X : Verify.Public) (l : ℕ) : Block S Unit :=
  let own : Block S Unit := VerifiableInference.Desc.Kinds.Reply.blockOf X l
  Block.andThen "H:1"
    (Block.guarded ProofFile.sameReply (fun _ => false)
      ({ (roundlessBlock "H:1" 1 (some l) 1 (VerifiableInference.Desc.First.K2.headFrontQ X.H.tl) :
        Block S Unit) with place := own.place })) own

/-- K7's address. -/
abbrev k7Place : Place := { chain := 1, link := some 24, piece := 1, kind := .K7 }

/-- **K7's PLACE, AT AN OPENING's OWN LETTERS.** -/
theorem k7_of {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b : Block S Cl),
      c.links[24]? = some Lk ∧ Lk.hear[0]? = some b ∧
      LaidFramed Z b (k7Block Bs.G₀.W 24).retype b.name k7Place := by
  have hZ := O.pub
  have hG := O.blank
  obtain ⟨sz, -⟩ := ground_gets hS hR hZ hG
  have hk : (kindsBeforeBatching .head (24 == 0))[0]? = some KindName.K7 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, L, hL, b', hb', ep, hla⟩ :=
    chain_hear_first O.made O.places O.chain 24 .head (subs_head hS hR hZ hG) 0 .K7 hk (by decide)
  obtain ⟨x, hm, rfl⟩ := lot_K7 hL hb' (by rw [ep])
  unfold ProofFile.h1Own at hm
  rw [sz] at hm
  obtain rfl := List.mem_singleton.1 hm
  exact ⟨Lk, b, e1, e2, hla⟩

/-- **The same in one piece, from onlineDescription's value.** -/
theorem k7_alone_z {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ (X : Verify.Public) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (c : Chain S Cl) (A : ProofFile.SharedSeat)
        (B : ProofFile.SecondSeat),
      ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z ∧ publicOf P.pol P.KL (some lay) = .ok X ∧
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀ ∧ G₀.W = X ∧
      ProofFile.onlineSharedChain Z = some A ∧ ProofFile.onlineLastChain Z = some B ∧
      F = ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∃ (Lk : Link S Cl) (b : Block S Cl),
        c.links[24]? = some Lk ∧ Lk.hear[0]? = some b ∧
        LaidFramed Z b (k7Block X 24).retype b.name k7Place := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := seat_open hF
  exact ⟨Bs.G₀.W, Z, Bs.G₀, c, A, B, O.pub, O.public, O.blank, rfl, O.shared, O.second, O.desc,
    k7_of hS hR O⟩

/-- **A yes at K7's place holds the lot's block's yes**, with no mark behind it: at all the rounds and groups where the block stands alone; at the front of them where a block is joined. -/
theorem k7_yes {Z : ProofFile.Pub} {X : Verify.Public} {b : Block S Cl} {name : String}
    (h : LaidFramed Z b (k7Block X 24).retype name k7Place) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} (hy : b.decide s rs gs = .ok t) :
    ((k7Block X 24).decide s rs gs = .ok t ∧ t.failed = none) ∨
      ∃ t', (k7Block X 24).decide s (rs.take (k7Block X 24).rounds.length)
        (gs.take (k7Block X 24).openings) = .ok t' ∧ t'.failed = none := by
  rcases yes_laid h.laid hy with ⟨-, h1, h2⟩ | ⟨q, t', -, h1, h2, -⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨t', h1, h2⟩

end IM

#print axioms IM.lot_K7
#print axioms IM.k7_of
#print axioms IM.k7_alone_z
#print axioms IM.k7_yes
