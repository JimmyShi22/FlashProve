-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/BehindStays.lean: THE PREMISE `stays` OF `PileWalk`
(Johnson/Desc/K13/Honest/PileInduction.lean) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN
IN LEAN: SHOWN AT THE SUB-PROTOCOL BEHIND THE BATCHING, AT EVERY SITE, UNDER THE LIBRARY's ONE
HYPOTHESIS AT THE FULL SIZE; SO THE PREMISE IS NARROWED FROM TWO NUMBERS A SITE TO ONE. Statements
with their proofs: calls.

WHOSE THE LAW IS. Honest/Law/NoHouse/BehindShare.lean: `after_share_head`: under h, at every
segment, every run behind the batching stands in whatever the nine known runs keep; `after_state`:
so an accepting `Link.runBehind` leaves the state but for what the library's `rest9` blanks
(Johnson/Desc/First/Link/Law/Rest9.lean: the segment's book-keeping, its ledger, the smallness
test's state, the rows owed). Both are called. Here the two readers are taken whole, by the
library's `ReadsRest9.alike`.
The ties to the chain's own numbers are the library's: `IM.frame_of` (Johnson/IMR/FrameSeat.lean:
number 14 m + `IM.nAt` m + 3 decides as its segment's `runBehind`), `IM.k9_of` (IMR/LinkSeat.lean:
the segment's two orders and its number of hearing sub-protocols: `SegAt`), `K1.hlk_atAll`
(Johnson/Desc/K1/Law/LinksQuietAtAll.lean: the segment that h's data name at m is the chain's m-th).
All called.
Main names. Under h : `P5J.AtMgA`:
  `readsRest9_leftLay`, `readsRest9_leftHead`: the two readers of what a merge left have the
    library's `ReadsRest9`: they read the same of a state and of its `rest9`. No premise.
  `behind_keeps_head`: **for every m < 25: every decision of number 14 m + `IM.nAt` m + 3 leaves
    every reader with `ReadsRest9`.**
  `stays_behind_head`: **so at every site of `sitesAt cF Zp` every decision of number c − 4 leaves
    what the site's reader reads.** At every state.
  `hfive_of_one_head`: **the premise hfive (ClosersStay.lean of this folder: `hfive_of_two`) from
    its share at the batching (c − 5) alone.**

What is not claimed. `stays` at the batching. That h holds at any public files. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.ClosersStay
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindShare
import Johnson.Desc.K1.Law.LinksQuietAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (leftHead)
open VerifiableInference.Desc.LinkJoin (ReadsRest9 SegAt)
open VerifiableInference.Desc.K13.Honest (PileSite FoldReaches)
open Johnson.Desc.First.Walk (leftLay)
open ProofFile.Honest.FirstThread (after_state after_share_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- What a layers' segment's merge left is the same when the segment's book-keeping, its ledger
and the smallness test's state are blanked. -/
theorem readsRest9_leftLay (L₀ : LinkCtx) (F₀ : Fork) (t₀ : HTailF2) :
    ReadsRest9 L₀ F₀ t₀ leftLay := fun s => by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> rfl

/-- So is what the head's merge left. -/
theorem readsRest9_leftHead (L₀ : LinkCtx) (F₀ : Fork) (t₀ : HTailF2) :
    ReadsRest9 L₀ F₀ t₀ leftHead := fun s => by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE SUB-PROTOCOL BEHIND THE BATCHING, OF EVERY SEGMENT, BY NUMBER, KEEPS EVERY SUCH
READER.** -/
theorem behind_keeps_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {β : Type} {f : S → β}
    (hf : ∀ L₀ F₀ t₀, ReadsRest9 L₀ F₀ t₀ f) (m : ℕ) (hm : m < 25) (blk : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[14 * m + IM.nAt m + 3]? = some blk) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s rs gs = .ok t) : f t = f s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, _, _, bB, _, e1, hn, _, _, _, _, _, _, _, _, iB, _, dB, _⟩ := hall m hm
  have hn' : Lk.hear.length = IM.nAt m := hn
  rw [hn'] at iB
  obtain rfl : bB = blk := Option.some.inj (iB.symm.trans hb)
  rw [dB] at hd
  obtain ⟨Lk9, _, _, _, e9, _, _, _, _, _, _, _, _, _, _, ho, hoa, hlen, _⟩ :=
    (IM.k9_of h.scope h.reads O).2 m hm
  obtain rfl : Lk = Lk9 := Option.some.inj (e1.symm.trans e9)
  have hlk : h.𝔇.lk m = some Lk := (VerifiableInference.Desc.K1.hlk_atAll h m hm).trans e1
  have hseg : SegAt m (IM.subAt m) Lk := ⟨ho, hoa, hlen⟩
  have q := (after_state Lk (after_share_head h hm hlk hseg) s t hd).2.1
  exact ReadsRest9.alike { check := s.check } {} {} (hf _ _ _) (q _ _ _)

/-- **`stays` AT THE NUMBER c − 4 OF EVERY SITE.** -/
theorem stays_behind_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (σ : PileSite)
    (hσ : σ ∈ sitesAt cF Zp) (k : ℕ) (hk : k + 4 = σ.c) (blk : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[k]? = some blk) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s rs gs = .ok t) :
    σ.left t = σ.left s := by
  rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
  · have a1 : k + 4 = 28 * g + 14 := hk
    have hn : IM.nAt (2 * g) = 7 := by
      unfold IM.nAt
      rw [if_neg (by omega)]
    have e : k = 14 * (2 * g) + IM.nAt (2 * g) + 3 := by omega
    rw [e] at hb
    exact behind_keeps_head h readsRest9_leftLay (2 * g) (by omega) blk hb s t rs gs hd
  · have a1 : k + 4 = 352 := hk
    have hn : IM.nAt 24 = 9 := rfl
    have e : k = 14 * 24 + IM.nAt 24 + 3 := by omega
    rw [e] at hb
    exact behind_keeps_head h readsRest9_leftHead 24 (by omega) blk hb s t rs gs hd

/-- **SO, UNDER h, THE PREMISE hfive FOLLOWS FROM ITS SHARE AT ONE NUMBER A SITE**: the batching
(c − 5). At any start. -/
theorem hfive_of_one_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Xi : Type} (start : Xi → S)
    (hone : ∀ σ ∈ sitesAt cF Zp, ∀ k blk, k + 5 = σ.c → cF.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches cF.blocksInOrder start k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s) :
    ∀ σ ∈ sitesAt cF Zp, ∀ k blk, σ.c ≤ k + 5 → k < σ.c → cF.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches cF.blocksInOrder start k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine hfive_of_two h.scope h.reads O start ?_
  intro σ hσ k blk hk hb x rs cols s cl hF R gs t hd
  rcases hk with h5 | h4
  · exact hone σ hσ k blk h5 hb x rs cols s cl hF R gs t hd
  · exact stays_behind_head h σ hσ k h4 blk hb s t R gs hd

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.readsRest9_leftLay
#print axioms ProofFile.Honest.K13.readsRest9_leftHead
#print axioms ProofFile.Honest.K13.behind_keeps_head
#print axioms ProofFile.Honest.K13.stays_behind_head
#print axioms ProofFile.Honest.K13.hfive_of_one_head
