-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/SecondFrontAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN
BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING FIVE OF THE ELEVEN FIELDS OF `SecondFront`
(Johnson/Desc/K8/Honest/SecondOpen.lean) HOLD; SIX STAY PREMISES. UNDER THE SCOPE, THE FILES READ
AND IM.Open. A structure and lemmas; none of the library's goals. No prover stands in them; nothing
on completeness, soundness or hiding. A joining.

  `SecondLeft tl F`   the six fields that stay: front (`TieFront`,
      Johnson/Desc/K8/Honest/TieWords.lean), row, blocks, cEnd, leaves, want (`PieceFront`,
      PieceWhole.lean, at every expected piece)
  **`five_at_batch`**   the five that hold: laid, sym, apart, pieces, zero
  **`secondFront_at_batch`**   so `SecondFront` there, from `SecondLeft`
By: `tiesLaid_at_batch` (Johnson/P1K8R/TiesAtBatch.lean) · `symbolsLaid_at_batch`
(SymbolsAtBatch.lean) · `apart_at_batch` (ApartAtBatch.lean) · `public_at_batch`
(PublicAtBatch.lean) · LinkJoin.zero_at_reach (ZeroSeat.lean). Three facts that these hand besides
are not carried into the end: `piecesFit`, `keyFitB` (public_at_batch), DgP.colsTest
(apart_at_batch): whoever wants them calls the sources.
Limits. THE SIX THAT STAY ARE THE HEAVY ONES, AND ARE SHOWN OF NO STATE HERE. Nothing on whether any
state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.SecondOpen
import Johnson.P1K8R.TiesAtBatch
import Johnson.P1K8R.SymbolsAtBatch
import Johnson.P1K8R.ApartAtBatch
import Johnson.P1K8R.PublicAtBatch
import Johnson.P1K8R.ZeroSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **What of `SecondFront` (Johnson/Desc/K8/Honest/SecondOpen.lean) stays a premise at a state
reached in front of a segment's batching**: six of its eleven fields. -/
structure SecondLeft (tl : HTailF2) (F : Fork) : Prop where
  front : TieFront tl
  row : ∀ mu, mu < tl.NM → Fo.HasRow F (tl.gtTree.getD mu 0) 0
  blocks : ∀ nbW W, tl.wants = some (nbW, W) → nbW = tl.zzBlocks
  cEnd : ∀ g, tl.heard = some g → g.cEnd.ents.isEmpty = true
  leaves : ∀ g, tl.heard = some g → g.leaves.start.ents.isEmpty = true
  want : ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) → ∀ w ∈ W, PieceFront tl g w

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT A STATE REACHED IN FRONT OF A SEGMENT's BATCHING FIVE FIELDS OF `SecondFront` HOLD**: the
ties', the symbols' and the pieces' tests on public numbers; the arrays' numbers are apart; every
virtual row of every array begins at column 0. -/
theorem five_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ tiesLaid tl = true ∧ symbolsLaid tl = true ∧ apartB tl = true ∧
      piecesLaid tl = true ∧
      ∀ G, s.fork? = some G → ∀ t r, ((G.trees.getD t {}).rows.getD r {}).L0 = 0 := by
  obtain ⟨tl, ht, h1⟩ := tiesLaid_at_batch hS hR O hl h
  obtain ⟨tl2, ht2, h2⟩ := symbolsLaid_at_batch hS hR O hl h
  obtain ⟨tl3, ht3, h3, -⟩ := apart_at_batch hS hR O hl h
  obtain ⟨tl4, ht4, h4, -, -⟩ := public_at_batch hS hR O hl h
  obtain rfl : tl = tl2 := Option.some.inj (ht.symm.trans ht2)
  obtain rfl : tl = tl3 := Option.some.inj (ht.symm.trans ht3)
  obtain rfl : tl = tl4 := Option.some.inj (ht.symm.trans ht4)
  exact ⟨tl, ht, h1, h2, h3, h4, fun G hG t r =>
    LinkJoin.zero_at_reach hS hR O (by split_ifs <;> omega) h G hG t r⟩

/-- **So `SecondFront` there, from the six that stay.** -/
theorem secondFront_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} {G : Fork} (ht : s.tl? = some tl) (hG : s.fork? = some G)
    (hL : SecondLeft tl G) : SecondFront tl G := by
  obtain ⟨tl', ht', h1, h2, h3, h4, h5⟩ := five_at_batch hS hR O hl h
  obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
  exact ⟨h1, h2, hL.front, h3, h4, h5 G hG, hL.row, hL.blocks, hL.cEnd, hL.leaves, hL.want⟩

end

end P1K8

#print axioms P1K8.five_at_batch
#print axioms P1K8.secondFront_at_batch
