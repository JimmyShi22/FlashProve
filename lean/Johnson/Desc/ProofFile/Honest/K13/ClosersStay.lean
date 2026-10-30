-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ClosersStay.lean: THE PREMISE `stays` OF `PileWalk`
(Johnson/Desc/K13/Honest/PileInduction.lean) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN
IN LEAN: SHOWN AT THE CLOSING's THREE SUB-PROTOCOLS, AT EVERY SITE, THE HEAD's TOO; SO THE PREMISE
IS NARROWED FROM FIVE NUMBERS A SITE TO TWO. Statements with their proofs.

THE LIBRARY HAS THE LAW OUTRIGHT. Johnson/Desc/First/Batch/Law/Keeps.lean: `K9.Beside f`: the reader
f of the state does not see what K9 and the closing write (the segment's book-keeping; its ledger;
the statement and the rows owed; the walk's own field); `K9.closeOf_keeps`: every decision of the
closing's three leaves such an f: at whatever rounds, with no other premise. The places by number:
`IM.close_of` (Johnson/IMR/CloseSeat.lean), `IM.close_numbers` (IMR/FirstSeats.lean), `IM.frame_of`
(for the number of hearing sub-protocols), `IM.yes_alone` (IMR/SeatForm.lean). All called. That the
decision of a sub-protocol carried over to the chain's type of claims (`Block.retype`) is its own:
by unfolding. Kin: the library shows `K9.Beside` of other readers (`beside_out`, `beside_tl`,
`beside_funs`, `beside_tlFuns`, and of every function of such a one: `Beside.map`: Keeps.lean;
`beside_read`: Johnson/Desc/First/Link/Law/BatchLeaves.lean; `beside_k8Field`:
Johnson/Desc/First/TailClaims/K8SitsBetween.lean); a search found none of these two.
Main names. In the goals' scope (`VerifierAndGoals.InScope`, `VerifierAndGoals.readFiles`), under the opening of the
proof file's IOP (`IM.Open`: its letters Z, Bs, c are what is public, the blank ground's holder, the
first chain):
  `beside_leftLay`, `beside_leftHead`: **`K9.Beside` of the two readers of what a merge left.**
  `closers_keep`: **for every l < 25 and j < 3: every decision of number 14 l + `IM.nAt` l + 4 + j
    leaves every f with `K9.Beside f`.**
  `stays_closers`: **so at every site of `sitesAt c Z` (SitesAtFlat.lean of this folder) every
    decision of a number c − 3, c − 2, c − 1 leaves what the site's reader reads.** At every state.
  `hfive_of_two`: **the premise hfive of `pileWalk_at_desc_five` (StaysAtFlat.lean),
    `pileWalk_at_chain` (SitesClaims.lean) and what calls them, from its share at two numbers a
    site**: the batching (c − 5) and the sub-protocol behind it (c − 4).

What is not claimed. `stays` at these two numbers. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.K13.SitesClaims
import Johnson.Desc.First.Batch.Law.Keeps
import Johnson.IMR.CloseSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S closeKinds)
open VerifiableInference.Desc.First.Close (leftHead)
open VerifiableInference.Desc.K9 (Beside closeOf_keeps)
open VerifiableInference.Desc.K13.Honest (PileSite PileWalk PileIs ClaimsIs SiteClaims FoldReaches
  pileBySites pileIs_of_claimsIs LayersFront ClaimsFromHearing HeadClaimIs roundsAhead)
open Johnson.Desc.First.Walk (leftLay)
open ProofFile (Cl)

/-- **What a layers' segment's merge left is read beside what K9 and the closing write.** -/
theorem beside_leftLay : Beside leftLay where
  link := fun s L => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here <;> first
      | rfl
      | (rename_i a; by_cases h : a.opened = true <;> simp [S.putLink, leftLay, h])
  fork := fun s F => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here <;> first
      | rfl
      | (rename_i a; by_cases h : a.opened = true <;> simp [S.putFork, leftLay, h])
  rows := fun _ _ _ => rfl
  walk := fun _ _ => rfl

/-- **So is what the head's merge left.** -/
theorem beside_leftHead : Beside leftHead where
  link := fun s L => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here <;> first
      | rfl
      | (rename_i a; by_cases h : a.opened = true <;> simp [S.putLink, leftHead, h])
  fork := fun s F => by
    obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
    cases here <;> first
      | rfl
      | (rename_i a; by_cases h : a.opened = true <;> simp [S.putFork, leftHead, h])
  rows := fun _ _ _ => rfl
  walk := fun _ _ => rfl

variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE CLOSING's THREE SUB-PROTOCOLS OF EVERY SEGMENT, BY NUMBER, KEEP EVERY SUCH READER.** -/
theorem closers_keep {α : Type} {f : S → α} (hf : Beside f) (hS : VerifierAndGoals.InScope Pp = true)
    (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (j : ℕ)
    (hj : j < 3) (blk : Block S Cl) (hb : c.blocksInOrder[14 * l + IM.nAt l + 4 + j]? = some blk) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hd : blk.decide s rs gs = .ok t) :
    f t = f s := by
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, _, _, _, _, e1, hn, _⟩ := hall l hl
  have hn' : Lk.hear.length = IM.nAt l := hn
  obtain ⟨LkC, p, Q, eC, -, -, hcl⟩ := IM.close_of hS hR O l hl
  obtain rfl : Lk = LkC := Option.some.inj (e1.symm.trans eC)
  obtain ⟨kq, hkq⟩ : ∃ kq, closeKinds[j]? = some kq :=
    ⟨_, List.getElem?_eq_getElem (by show j < 3; exact hj)⟩
  obtain ⟨b0, x, e2, ex, hla⟩ := hcl j kq hkq
  have hix := IM.close_numbers hS hR O hl e1 e2
  rw [hn'] at hix
  obtain rfl : b0 = blk := Option.some.inj (hix.symm.trans hb)
  have h7 : (IM.cAt l (IM.subAt l) j kq).kind ≠ KindName.K7 := by
    have hm := List.mem_of_getElem? hkq
    intro q
    have q' : kq = KindName.K7 := q
    subst q'
    revert hm
    decide
  exact closeOf_keeps hf p Q (List.mem_of_getElem? ex) ((IM.yes_alone hla h7 s t rs gs).1 hd).1

/-- **`stays` AT THE THREE NUMBERS IN FRONT OF A SITE's LAYING**: c − 3, c − 2, c − 1. -/
theorem stays_closers (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (σ : PileSite)
    (hσ : σ ∈ sitesAt c Z) (k : ℕ) (h1 : σ.c ≤ k + 3) (h2 : k < σ.c) (blk : Block S Cl)
    (hb : c.blocksInOrder[k]? = some blk) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s rs gs = .ok t) :
    σ.left t = σ.left s := by
  rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
  · have a1 : 28 * g + 14 ≤ k + 3 := h1
    have a2 : k < 28 * g + 14 := h2
    have hn : IM.nAt (2 * g) = 7 := by
      unfold IM.nAt
      rw [if_neg (by omega)]
    have e : k = 14 * (2 * g) + IM.nAt (2 * g) + 4 + (k - (28 * g + 11)) := by omega
    rw [e] at hb
    exact closers_keep beside_leftLay hS hR O (2 * g) (by omega) _ (by omega) blk hb s t rs gs hd
  · have a1 : 352 ≤ k + 3 := h1
    have a2 : k < 352 := h2
    have hn : IM.nAt 24 = 9 := rfl
    have e : k = 14 * 24 + IM.nAt 24 + 4 + (k - 349) := by omega
    rw [e] at hb
    exact closers_keep beside_leftHead hS hR O 24 (by omega) _ (by omega) blk hb s t rs gs hd

/-- **SO THE PREMISE hfive (`stays` at the five numbers in front of a site's laying) FOLLOWS FROM
ITS SHARE AT TWO**: the batching (c − 5) and the sub-protocol behind it (c − 4). At any start. -/
theorem hfive_of_two (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) {Xi : Type} (start : Xi → S)
    (htwo : ∀ σ ∈ sitesAt c Z, ∀ k blk, k + 5 = σ.c ∨ k + 4 = σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder start k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    ∀ σ ∈ sitesAt c Z, ∀ k blk, σ.c ≤ k + 5 → k < σ.c → c.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches c.blocksInOrder start k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s := by
  intro σ hσ k blk h5 hc hb x rs cols s cl hF R gs t hd
  by_cases h3 : σ.c ≤ k + 3
  · exact stays_closers hS hR O σ hσ k h3 hc blk hb s t R gs hd
  · exact htwo σ hσ k blk (by omega) hb x rs cols s cl hF R gs t hd

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.beside_leftLay
#print axioms ProofFile.Honest.K13.beside_leftHead
#print axioms ProofFile.Honest.K13.closers_keep
#print axioms ProofFile.Honest.K13.stays_closers
#print axioms ProofFile.Honest.K13.hfive_of_two
