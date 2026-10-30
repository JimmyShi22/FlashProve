-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K11Seat.lean. The seated block of k11_of is the lot's (Lot/K11.lean): K11.blkAt Z "H.8.call" G₀ (= K11.blk (K11.parOf Z G₀) with «and the step is found» laid to its test on the plan).
The rest of this head may differ from this file's text; where it does, the text holds.
A LAW ABOUT ProofFile.chainBy AND ProofFile.pureSeat, NO PART OF THEM: K11's block (the merge of the claims on
the weights) at its place in onlineDescription's first chain.
OBJECT. THE SEATED CONSTANT: K11.blk (K11.parOf Z G₀) := Johnson.Desc.First.ForkMerge.headClaimMergeKind (K11.parOf Z G₀) (Johnson/Desc/First/Fork/MergeKind.lean · Johnson/Desc/ProofFile/Lot/K11.lean), as it stands at F.first.links[24].hear[8].
USER. K11's laws; the head's order's last run «the merge» is stated by this block. LETTERS. As in K6Seat.lean.


THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut).

  k11_of            at an opening's letters, in scope: link 24's ninth block in front of the batching IS seatedAs sameReply (K11.blk (K11.parOf Z G₀)) b.name ⟨1, some 24, 9, K11⟩: ALONE; (K11.parOf Z G₀).link = 24.
  k11_yes           yes_alone at K11's address.

WHO PAYS THE PREMISES: as in K6Seat.lean. What is not claimed. Nothing on what the block decides or states. No soundness.
-/
import Johnson.IMR.LaidFirst
import Johnson.IMR.SeatOpen
import Johnson.IMR.Subs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open ProofFile (Cl)

/-- K11's address. -/
abbrev k11Place : Place := { chain := 1, link := some 24, piece := 9, kind := .K11 }

/-- **K11 AT THE HEAD's LINK: THE LOT's BLOCK, ALONE.** -/
theorem k11_of {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (b : Block S Cl), c.links[24]? = some Lk ∧ Lk.hear[8]? = some b ∧
      LaidAlone ProofFile.sameReply b (K11.blkAt Z "H.8.call" Bs.G₀) b.name k11Place ∧
      (K11.parOf Z Bs.G₀).link = 24 := by
  obtain ⟨sz, -⟩ := ground_gets hS hR O.pub O.blank
  have hk : (kindsBeforeBatching .head (24 == 0))[8]? = some KindName.K11 := by
    unfold kindsBeforeBatching
    rfl
  obtain ⟨Lk, b, e1, e2, sp, -, L, hL, b', hb', -, ep, hla⟩ :=
    chain_hear_alone O.made O.places O.chain 24 .head (subs_head hS hR O.pub O.blank) 8 .K11 hk
      (by decide) (by decide) (by decide)
  obtain rfl : L = K11.lot Z := lot_of_kind hL hb' (by rw [ep]; rfl)
  have hb'' : b' ∈ [K11.blkAt Z "H.8.call" Bs.G₀] := by
    rcases blocks_mem hb' with ⟨y, hy, -⟩ | h
    · exact nomatch hy
    · exact h
  obtain rfl := List.mem_singleton.1 hb''
  refine ⟨Lk, b, e1, e2, ?_, ?_⟩
  · rw [alone_name hla]
    exact hla
  · show Bs.G₀.built.size - 1 = 24
    rw [sz]

/-- **The seated block's yes is the lot's block's yes**, with no mark behind it and the reply as it was. -/
theorem k11_yes {b b' : Block S Cl} {name : String} (h : LaidAlone ProofFile.sameReply b b' name k11Place)
    (s t : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) :
    b.decide s rs gs = .ok t ↔
      b'.decide s rs gs = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true :=
  yes_alone h (by decide) s t rs gs

end IM

#print axioms IM.k11_of
#print axioms IM.k11_yes
