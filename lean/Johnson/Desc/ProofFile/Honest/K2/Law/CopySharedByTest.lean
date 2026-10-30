-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopySharedByTest.lean: the kind "the code switch" (K2): THE
THREE LAWS OF CopySharedAtHead.lean WITH THE BOOK's ENTRY ASKED BY ONE PUBLIC TEST: where these have
an entry e, its number, and four premises on it, their sisters here have one: `entryRunIs`
(Honest/Small/EntryRunIs.lean) at the book's carrying entries for the switch. Statements with their
proofs: one call each; no definition.

  `copyShared_first_by_test`, `copyShared_mask_by_test`, `copyShared_later_by_test`

ht: among the entries that the book carries to the switch's part, the one with the message's number
names the sender's address o, the start of the message's coins among the sender's, and their count.
It is a test with code, on the book and on public numbers. Two tests of
Honest/K2/Law/CarriedAsks.lean (not imported) are made of it. `carriedEntryFits` always holds an
entry's name, owner and count against a member of the place's front; it puts the entry to this test,
with the start and the count of the owner's own sending, only if the owner's address belongs to a
place of its list of switches: at every other owner no start is compared. `carriedSame` goes through
what one switch carries, number by number, and puts the other switch's entry of that number to this
test with the first one's owner, start and count, whoever the owner is.

HOW THEY ARE MADE: by program, off the elders' texts: the binders e, i, hi, he, t1, t2, t3 become
ht, with hi's, t2's and t3's right sides laid in. In the statements' code nothing else turns but the


By: `entryRunIs_gives`, `carryE_is` (EntryRunIs.lean), of another author · the three elders.

Limits. THE TEST IS A PREMISE: IT IS SHOWN AT NO BOOK: which entries the maker of the book lays for
a switch's part is not said here. The elders' other premises stay: hc, ho, hdat, hR; hS, hn, hy. o,
the sender's address, is a letter, bound by ho and by the test. As the elders': the rows, not the
texts, nor the tables; no lot is laid. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopySharedAtHead
import Johnson.Desc.ProofFile.Honest.Small.EntryRunIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left zeroG)
open VerifiableInference.Desc.K1 (firstPar gpOf parL)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Bk : ProverCoinCounts}
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **A MESSAGE OF THE FIRST SEGMENT, IN FRONT OF THE FOLD's MASK.** n: its number there, and in the
opening's sending. The sister of `copyShared_first_at_head`: the book's entry is asked by one public
test. -/
theorem copyShared_first_by_test (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {withFresh : Bool} {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      withFresh = .ok R) {n : Nat} (hn : n < (Sg.sent.headD #[]).size - 1)
    {P : VerifiableInference.Desc.K1.Par} (hP : firstPar Bs.G₀.first (gpOf Zp) = P)
    {ρ : Nat → Option K1.Ride} (hρ : K1.rideOf (K1.firstFold Bs.G₀.first) = ρ)
    (o : Addr) {cs : Cs (K1.dueR P ρ)}
    (ho : K1.lentCut k ch o (K1.dueR P ρ) = some cs)
    (ht : entryRunIs (carryE Bk ⟨p.place, 0⟩) (b₀ + n) o
      (K1.startR P ρ n)
      (K1.dueMsg P.codes (shapeAt P n) (ρ n)) = true)
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK n = asShared (shapeAt P n) (dataAtOf Sg prev own n)) :
    R.rows[n]? = some (K1.rowsR P ρ dataK cs n) := by
  obtain ⟨e, he, t1, t2, t3⟩ := entryRunIs_gives ht
  rw [carryE_is] at he
  exact copyShared_first_at_head h O ch p k c hc hS hR hn hP hρ o ho e rfl he t1 t2 t3 dataK hdat

/-- **THE FIRST SEGMENT's FOLD's FRESH MASK.** The sister of `copyShared_mask_at_head`: the book's
entry is asked by one public test. -/
theorem copyShared_mask_by_test (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      true = .ok R)
    {P : VerifiableInference.Desc.K1.Par} (hP : firstPar Bs.G₀.first (gpOf Zp) = P)
    {ρ : Nat → Option K1.Ride} (hρ : K1.rideOf (K1.firstFold Bs.G₀.first) = ρ)
    (o : Addr) {cs : Cs (K1.dueR P ρ)}
    (ho : K1.lentCut k ch o (K1.dueR P ρ) = some cs)
    (ht : entryRunIs (carryE Bk ⟨p.place, 0⟩) (b₀ + ((Sg.sent.headD #[]).size - 1)) o
      (K1.startR P ρ ((Sg.sent.headD #[]).size - 1))
      (K1.dueMsg P.codes (shapeAt P ((Sg.sent.headD #[]).size - 1)) (ρ ((Sg.sent.headD #[]).size -
        1))) = true)
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK ((Sg.sent.headD #[]).size - 1) =
      asShared (shapeAt P ((Sg.sent.headD #[]).size - 1)) fun _ _ => zeroG) :
    R.fresh = some (K1.rowsR P ρ dataK cs ((Sg.sent.headD #[]).size - 1)) := by
  obtain ⟨e, he, t1, t2, t3⟩ := entryRunIs_gives ht
  rw [carryE_is] at he
  exact copyShared_mask_at_head h O ch p k c hc hS hR hP hρ o ho e rfl he t1 t2 t3 dataK hdat

/-- **A MESSAGE BEHIND A SEGMENT's FIRST SENDING.** m: the segment. q: its number among these: 0:
the "reads"; 1: the "digits". The sister of `copyShared_later_at_head`: the book's entry is asked by
one public test. -/
theorem copyShared_later_by_test (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {m : Nat} {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {withFresh : Bool} {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      withFresh = .ok R) {q : Nat} {y : OnBytes.OracleNotice}
    (hy : ((Sg.sent.drop 1).flatMap (·.toList))[q]? = some y)
    {P : VerifiableInference.Desc.K1.Par} (hP : parL Zp Bs.G₀ m (q == 1) = P)
    {ρ : Nat → Option K1.Ride} (hρ : K1.rideOf none = ρ)
    (o : Addr) {cs : Cs (K1.dueR P ρ)}
    (ho : K1.lentCut k ch o (K1.dueR P ρ) = some cs)
    (ht : entryRunIs (carryE Bk ⟨p.place, 0⟩) (b₀ + ((Sg.sent.headD #[]).size - 1) + (if withFresh
      then 1 else 0) + q) o
      (K1.startR P ρ 0)
      (K1.dueMsg P.codes (shapeAt P 0) (ρ 0)) = true)
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK 0 = asShared (shapeAt P 0) (own ((Sg.sent.headD #[]).size - 1 -
      (if prev.isSome then 1 + Sg.sizes.kept.length else 0) + q))) :
    R.rows[(Sg.sent.headD #[]).size - 1 + q]? = some (K1.rowsR P ρ dataK cs 0) := by
  obtain ⟨e, he, t1, t2, t3⟩ := entryRunIs_gives ht
  rw [carryE_is] at he
  exact copyShared_later_at_head h O ch p k c hc hS hR hy hP hρ o ho e rfl he t1 t2 t3 dataK hdat

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.copyShared_first_by_test
#print axioms ProofFile.Honest.K2.Law.copyShared_mask_by_test
#print axioms ProofFile.Honest.K2.Law.copyShared_later_by_test
