-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/DoorFactsAtAll.lean: THE KIND K1's FIFTY LATER SENDINGS (every
link's reads and digits): WHAT THE OPEN PUBLIC ITEMS SAY BESIDE THEIR TESTS (Meaning.pubP,
Johnson/Desc/First/Borders.lean) HOLDS BEHIND A MEMBER's ACCEPTING STEP, OF EVERY ITEM THAT IS OPEN
THERE: at a meaning whose extra public rows are the closed list moreAll
(Johnson/Desc/Sound/MoreAll.lean), whose public tests are pubAll's and whose sentences are those of
the lookups' layer over the pending claim's layer over the closed meaning mgBase
(Johnson/Desc/First/Look/K3Fill.lean, Johnson/Top/H0/Fill/FillP1.lean,
Johnson/Desc/Sound/MgBase.lean). No thread and no prover occurs, and no string is read: the type of
strings stands once, in the type of an idle letter (cr) of the pending claim's layer. No definition.
Statements and proofs.

Why it can be had whole. By the three layers' texts: at left m and leftOn m the sentence is the
lookups'; at hasRow m it is True; at every other item it is "the table gives the item no sentence"
(First.saysNone, Johnson/Desc/First/AllSaid.lean), which reads no state.

  led_all, noLeft_all, said_all: THREE CLOSED TESTS ON THE TABLE AT moreAll, at the written lists,
    at all fifty places, by evaluation in Lean's kernel: "ledger l" is open in front · no "left" is
    open in front · behind: no "left" is open, every "leftOn" that is open was open in front, and
    every other open item is hasRow's sort or has no sentence. The first two tests are the library's
    (inSetB, noLeftB, Johnson/Desc/K1/Law/DoorFactsAtPlus13.lean, which decides them at another
    closed list).
  hled_all, hnl_all: the first two in the letters of the binders hled and hnl of the library's
    aLeft_of (Johnson/Desc/K1/Law/ALeftOf.lean), at any meaning with these extra rows.
  pubP_later_all: THE SENTENCES BEHIND, ALL OF THEM: from the member's accepting step, the six tests
    in front at P1K2.EQ (Johnson/P1K2R/TieTwo.lean), and the sentence in front of each "leftOn" that
    is open there. Of no other item is a sentence asked in front.

Beside the library's aLeft_of: that law is the wider one (the meaning beneath the lookups' layer is
a free letter; it speaks of left and leftOn alone, inside the whole promise with its strings). This
one pins the meaning beneath, and closes the list of items.

Limits. The three equations on the meaning (hP, hMg, hm) are premises: shown here of no meaning.
That the member stands under the lot's sub-protocol (hu), accepts (hy), and that the tests and the
sentence hold in front (hx, hpp) are premises. The three closed tests are evaluations in Lean's
kernel (decide +kernel) over the written lists of links and places: no compiled code; a row more in
the table reopens them. said_all shows too that no item whose sentence is false outright at mgBase
(an item other than left, leftOn and hasRow at which First.saysNone answers none) is open behind a
place; whether leftOn's own sentence can be met it does not say; of the borders elsewhere it says
nothing. Nothing on the first segment's opening or on W's sending. Nothing on soundness, on
completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.FormBehind
import Johnson.Desc.K1.Law.DoorFactsAtPlus13
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.Sound.MgBase
import Johnson.Top.H0.Fill.FillP1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Strs)
open VerifiableInference.Desc.First (S Numbers Meaning flatPlacesOf pubSets saysNone PubData pubAll)
open VerifiableInference.Desc.First.FillP1 (p1Item fillP1 PileWit)
open VerifiableInference.Desc.First.Look (fillK3)
open VerifiableInference.Desc.Sound (linksFull moreAll mgBase)
open VerifiableInference.Desc.K1 (blkL noL inSetB noLeftB inSet_of noLeft_of)
open OnBytes.Model.Stages (LinkH)
open HashBuild (epub_parts)
open IM (k1Ix)

/-! ## 1 Three closed tests on the table, by evaluation in Lean's kernel -/

/-- "ledger l" is open in front of each of link l's two later places. -/
theorem led_all : ((List.range 25).all fun l => [false, true].all fun d =>
    inSetB moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)
      (.ledger l)) = true := by
  decide +kernel

/-- No "left" is open in front of any of the fifty. -/
theorem noLeft_all : ((List.range 25).all fun l => [false, true].all fun d =>
    noLeftB moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)) = true := by
  decide +kernel

/-- **Behind each of the fifty**: no "left" is open; every "leftOn" that is open was open in front;
every other open item is of hasRow's sort or one to which the table gives no sentence. -/
theorem said_all : ((List.range 25).all fun l => [false, true].all fun d =>
    ((pubSets moreAll linksFull (flatPlacesOf linksFull true))[14 * l + k1Ix l d + 2 + 1]?.getD
      []).all fun q =>
      match q with
      | .left _ => false
      | .leftOn _ =>
        ((pubSets moreAll linksFull (flatPlacesOf linksFull true))[14 * l + k1Ix l d + 2]?.getD
          []).contains q
      | _ => p1Item q || (saysNone q).isSome) = true := by
  decide +kernel

/-! ## 2 In the binders' letters -/

variable {Pp W : Type}

/-- **hled**, at the segment's own ledger. -/
theorem hled_all {Mg : Meaning Pp W} (hm : Mg.more = moreAll) : ∀ l, l < 25 → ∀ d : Bool,
    First.Pub.ledger l ∈
      (pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] := by
  intro l hl d
  rw [hm]
  exact inSet_of (List.all_eq_true.1 (List.all_eq_true.1 led_all l (List.mem_range.2 hl)) d
    (by cases d <;> simp))

/-- **hnl.** -/
theorem hnl_all {Mg : Meaning Pp W} (hm : Mg.more = moreAll) : ∀ l, l < 25 → ∀ d : Bool, ∀ m,
    First.Pub.left m ∉
      (pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] := by
  intro l hl d m
  rw [hm]
  exact noLeft_of (List.all_eq_true.1 (List.all_eq_true.1 noLeft_all l (List.mem_range.2 hl)) d
    (by cases d <;> simp)) m

/-! ## 3 The sentences behind -/

/-- **WHAT EVERY PUBLIC ITEM THAT IS OPEN BEHIND THE PLACE SAYS BESIDE ITS TEST HOLDS BEHIND AN
ACCEPTING STEP.** -/
theorem pubP_later_all {nR kC : ℕ} (D : PubData) (base : First.Pub → Pp × S → Bool)
    (X3 : OnBytes.Model.Verify.Public) (D3 : First.Look.Sent) (d1 : First.FillP1.PubData)
    (rw1 : Pp × S → W → PileWit nR kC) (A : ℕ → Pp × S → W → ℕ → ℕ → ℕ → Cb.Gl.E)
    (cr : ℕ → Pp × S → Strs → W → Prop) (Mg : Meaning Pp W)
    (hP : Mg.pubP = (fillK3 X3 D3 (fillP1 d1 rw1 A cr mgBase)).pubP)
    (hMg : Mg.pub = pubAll D base) (hm : Mg.more = moreAll) (N : Numbers) (z : Pp) (ft : ℕ)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (c : Block S ProofFile.Cl)
    (hu : c.UnderR ((blkL Z G l d X arrs).retype : Block S ProofFile.Cl)) (s s' : S)
    (hy : IM.Yes ft c s s')
    (hx : IM.XK N linksFull (flatPlacesOf linksFull true)
      (P1K2.EQ Mg linksFull (flatPlacesOf linksFull true) z) (noL l d) s = true)
    (hpp : ∀ m, First.Pub.leftOn m ∈ P1K2.pubAt Mg linksFull (flatPlacesOf linksFull true)
      (noL l d) → Mg.pubP (.leftOn m) (z, s)) :
    ∀ q ∈ P1K2.pubAt Mg linksFull (flatPlacesOf linksFull true) (noL l d + 1),
      Mg.pubP q (z, s') := by
  intro q hq
  have hq' : q ∈ (pubSets moreAll linksFull (flatPlacesOf linksFull true))[14 * l + k1Ix l d + 2 +
      1]?.getD [] := by
    unfold P1K2.pubAt at hq
    rw [hm] at hq
    exact hq
  have ht := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 said_all l
    (List.mem_range.2 hl)) d (by cases d <;> simp)) q hq'
  rw [hP]
  cases q with
  | left m => exact absurd ht (by simp)
  | leftOn m =>
    have hin : First.Pub.leftOn m ∈ P1K2.pubAt Mg linksFull (flatPlacesOf linksFull true)
        (noL l d) := by
      unfold P1K2.pubAt
      rw [hm]
      exact List.contains_iff_mem.1 ht
    have h0 := hpp m hin
    rw [hP] at h0
    have he : HashBuild.EPub z Mg linksFull (flatPlacesOf linksFull true) (noL l d) s = true := by
      rw [epub_eq]
      exact (IM.xk_parts hx).2.2.2.2
    have hz := (epub_parts he).2.1 _ (hled_all hm l hl d)
    rw [hMg] at hz
    exact leftOn_later_yes X3 m ft Z G l d X arrs c hu s s' hy hz h0
  | hasRow m => exact trivial
  | _ => exact ht

end ProofFile.Honest.K1
