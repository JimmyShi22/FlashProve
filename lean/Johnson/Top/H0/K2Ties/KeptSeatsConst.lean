-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/KeptSeatsConst.lean: code switching: THE NAMED TEST keptSeatsB
(Johnson/Top/H0/K2Caller/KeptSeatsB.lean) ACCEPTS AT THE CONSTANT's OWN LETTERS, AT EACH OF THE 25
WRITTEN TYPED ROWS: where the constant's parameters are the written values and the description's
first chain tells what the written cut tells. NO SUB-PROTOCOL IMPORTS THIS FILE.
  laidFull · laidFull_is   ONE-LINE NAMES for the closed term LFull
               (Johnson/HB/LLHARD/LaidWritten.lean) and for laid_here (K2Caller/PlacesWritten.lean):
               kept for a caller (Johnson/P1K2R/ListsAtConst.lean)
  orcFull             the oracle message at tree j, by the written cut
  keptSeats25B        the test's text with a letter for the description's reading (keptSeatsOrc,
                      K2Caller/KeptSeatsOrc.lean) at every row of a list: row number m at the kept
                      members' tenants seatOld N m r and olds := K2.oldsAt (m + 1). A HELPER
  keptSeats25_full    THE CLOSED FACT: it accepts at the written values, at all 25: by the kernel.
                      The 25th row (m = 24) keeps no member: there the test accepts idly
  kept_members        how many kept members the 25 rows have: so that the fact is not idle
  keptSeats25_moved   a negative test: the first 24 rows, each of which keeps a member, moved by one
                      place: it rejects
  toldFull_length · orc_at   the written cut tells 83 trees; below 83 a description whose first
                      chain tells the written list reads orcFull
  keptSeats_const     THE STATEMENT, at the constant's letters
CALLED BESIDE: AtWritten (K2Ties/WrittenAt.lean) · toldFull (K2Ties/ToldAt.lean) · tenantsFull ·
laid_here (K2Caller/PlacesWritten.lean) · codes_of_sends (K2Ties/IndexPlace.lean).
LIMITS. The full size alone. AtWritten stands under the first pinned test's accept; «the first chain
tells the written list» under the cut's; «the sendings are the written ones» is a premise. THAT olds
ARE THE KEPT MEMBERS' NUMBERS IN THE VERIFIER's STATE IS NOT SAID HERE (the test's own Limits). No
soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.KeptSeatsOrc
import Johnson.Top.H0.K2Caller.SeatsOfN
import Johnson.Top.H0.K2Hears.PlaceNums
import Johnson.Top.H0.K2Ties.IndexPlace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open Johnson.G (proofSends0)
open VerifiableInference.Desc (Chain FileDescription Oracle oraclesOf)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.K2 (oldsAt)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit seatOld keptSeatsB keptSeatsOrc
  keptSeatsB_of)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)
open VerifiableInference.Desc.K13.Law (LFull)
open P1Named (tenantsFull laid_here)
open P5J (TS)

/-- The written sendings' laid list: a name for the closed term LFull (LaidWritten.lean). -/
abbrev laidFull : Laid := LFull

theorem laidFull_is : laidAtCodes proofSends0.codes proofSends0 = some laidFull := laid_here

/-- The oracle message at tree j, by the written cut. -/
def orcFull (j : ℕ) : Option Oracle := toldFull.flatten[j]?

/-- The test at every row of a list. -/
def keptSeats25B (L : Laid) (seats : List (ℕ × ℕ)) (N : Numbers) (rows : List SwRow) : Bool :=
  rows.zipIdx.all fun x =>
    keptSeatsOrc x.1.cs L seats 83 x.1.lo (seatOld N x.2 x.1) orcFull x.1.kept (oldsAt (x.2 + 1))

set_option maxRecDepth 1000000 in
/-- **The closed fact.** -/
theorem keptSeats25_full : keptSeats25B laidFull tenantsFull P5T.N0Full tableFullLit = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem kept_members : (tableFullLit.map (·.kept.length)).sum = 36 ∧
    ((tableFullLit.take 24).all fun r => !r.kept.isEmpty) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem keptSeats25_moved :
    keptSeats25B laidFull tenantsFull P5T.N0Full ((tableFullLit.take 24).drop 1) = false := by
  decide +kernel

theorem toldFull_length : toldFull.flatten.length = 83 := by decide +kernel

theorem orc_at {Xi : Type} {G : FileDescription Xi} (hO : oraclesOf G.first.blocksInOrder = toldFull.flatten) :
    ∀ j, j < 83 → G.oracleAt j = orcFull j := by
  intro j hj
  unfold FileDescription.oracleAt orcFull
  rw [hO, List.append_assoc, List.getElem?_append_left (by rw [toldFull_length]; exact hj)]

theorem seatOld_congr {N N' : Numbers} (hk : N.keptOf = N'.keptOf) (m : ℕ) (r : SwRow) :
    seatOld N m r = seatOld N' m r := by
  funext i
  unfold seatOld
  rw [hk]

/-- **The test accepts at the constant's own letters**, at each written typed row. -/
theorem keptSeats_const {Xi : Type} {G : FileDescription Xi} {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl}
    (A : AtWritten Zp cF) (hO : oraclesOf G.first.blocksInOrder = toldFull.flatten)
    (hs : Zp.made.proof.1 = proofSends0) {L : Laid} (hl : P5J.At.laid? Zp = some L) {m : ℕ}
    {r : SwRow} (hr : tableFullLit[m]? = some r) :
    keptSeatsB G r.cs L (P5J.At.seats Zp) 83 r.lo (seatOld (P5J.At.N Zp cF) m r) r.kept
      (oldsAt (m + 1)) = true := by
  have hl' : laidAtCodes (P5J.At.cs Zp) Zp.made.proof.1 = some L := hl
  rw [A.cs, codes_of_sends, hs, laidFull_is] at hl'
  obtain rfl : laidFull = L := Option.some.inj hl'
  rw [A.seats, seatOld_congr A.keptOf]
  exact keptSeatsB_of _ _ _ _ _ _ (orc_at hO)
    (List.all_eq_true.1 keptSeats25_full (r, m) (List.mem_zipIdx_iff_getElem?.2 hr))

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.laidFull_is
#print axioms VerifiableInference.Desc.First.K2Ties.keptSeats25_full
#print axioms VerifiableInference.Desc.First.K2Ties.kept_members
#print axioms VerifiableInference.Desc.First.K2Ties.keptSeats25_moved
#print axioms VerifiableInference.Desc.First.K2Ties.toldFull_length
#print axioms VerifiableInference.Desc.First.K2Ties.orc_at
#print axioms VerifiableInference.Desc.First.K2Ties.seatOld_congr
#print axioms VerifiableInference.Desc.First.K2Ties.keptSeats_const
