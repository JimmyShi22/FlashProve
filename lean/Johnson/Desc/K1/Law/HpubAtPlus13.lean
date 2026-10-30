-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HpubAtPlus13.lean: **hpub**: the
binder hpub of k01_fifty at the wider meaning
`plus13 (d13 Dm) dk (mgAll Dm Mg₀)` and N := Dm.N: the public items that COME at a later sending's
place (`tiedL`: the tied ones, and what the list of extra public tests makes
there) pass their tests behind an accepting run of the place's piece.
WHAT COMES, by evaluation in Lean's kernel at the closed list `mwMore` (read off the print of
a file not in this library first): at a link's digits nothing; at a link's reads the tied items
and ONE made name, "frame.sentIs1" of the segment.
  `made_mw`, `sentIn_mw`   [kernel] what is made at the fifty; "frame.sentIs" of the segment stands
                   in the open public set in front of its reads
  `sentIs_congr`   the test `sentIsB d m` reads `d` at m alone
  `own1B`          A TEST WITH CODE on the list of rounds: at each segment, the numbers that the
                   data give the second sending's messages (`secondNos`) are the place's own
                   (`idsOf`, at the table's count of messages in front of the reads)
  `sentIs1_made`   **the made half**: `sentIs_k1Reads_plan`, from
                   "frame.sentIs" and the clause on the book off the promise in front
  `hpub_plus13`    **the binder**; the tied half is `hpub_reads_full`
  `madeTests_fail`   [kernel] the two tests on the closed list can fail
PREMISES, BY NAME. hM. hOwn1: `own1B … = true`. And the three that `hpub_reads_full` leaves: hP
(`laterSeatsB` at the reads), hRd (`ReadersStay`), hfound (`SecondFound`).
NOT SHOWN MEETABLE: hRd and hfound are asked at EVERY pair of states with an accept between them,
not only inside the promise. `SecondFound` leans on the length of the open link's frame's list "own"
in front, of which we have found no test in the sending's decision: we see no way to pay hfound in
this form, and have no state that refutes it. UNTIL IT IS PAID OR RE-FORMED hpub_plus13 COUNTS FOR
NOTHING.
THE LETTERS. The frame F, the piece's base and its two numbers are free here: at
F := Sound.frameAt (dataOf aN R₁ R₂ R₃) all (dataOf aN R₁ R₂ R₃).key₁ T.ft₁, base := baseL …,
cc := (parL …).coordinates, e := errPort … it is the binder; the binder's two premises on d₁ are not
needed.
The recursion limit is raised in this file (maxRecDepth 1000000), as in FormsAtFifty.lean:
for the elaboration of the kernel's evaluations alone.
What is not claimed. The premises, at any list of rounds. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.DoorFactsAtPlus13
import Johnson.Desc.K1.Law.RestAtPlus13
import Johnson.Desc.K1.Law.HpubAtFull
import Johnson.Desc.K1.Law.SentIsAtReads

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData pubAll
  flatPlacesOf)
open VerifiableInference.Desc.First.FillSent (SentData sentIsB secondNos base1At)
open VerifiableInference.Desc.Sound (Frame linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

/-! ## 1 What comes at the fifty: the kernel's facts -/

theorem made_mw : ((List.range 25).all fun l =>
    madeAt mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2) == [] &&
    madeAt mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) ==
      [.more (some l) "frame.sentIs1"]) = true := by
  decide +kernel

theorem sentIn_mw : ((List.range 25).all fun l =>
    inSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)
      (.more (some l) "frame.sentIs")) = true := by
  decide +kernel

/-- **The tests can fail**: one sub-protocol in front of segment 3's reads nothing is made; and in
front of its digits "frame.sentIs" stands no more. -/
theorem madeTests_fail :
    (madeAt mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 false + 1) ==
      [.more (some 3) "frame.sentIs1"]) = false ∧
    inSetB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      (.more (some 3) "frame.sentIs") = false := by
  decide +kernel

/-! ## 2 The made half -/

/-- The test reads the data at m alone. -/
theorem sentIs_congr (d d' : SentData) (m : ℕ) (s : S) (hb : d'.born m = d.born m)
    (ho : d'.own m = d.own m) (hk : d'.kept m = d.kept m) : sentIsB d' m s = sentIsB d m s := by
  unfold sentIsB
  rw [hb, ho, hk]

/-- **A TEST on the list of rounds**: the numbers of each segment's second sending's messages. -/
def own1B (shape : Params.ReqShape) (N : Numbers) (links : List ModelPart) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) : Bool :=
  (List.range 25).all fun l =>
    secondNos shape (base1At N links (flatPlacesOf links true)) l ==
      idsOf (parL Z G l false) (N.msgsAt (flatPlacesOf linksFull true)[noL l false]?)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The made half.** -/
theorem sentIs1_made (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hOwn1 : own1B Dm.shape Dm.N Dm.links Z G = true) (l : ℕ) (hl : l < 25) (X : LinkH)
    (arrs : Option (List ℕ)) (x x' : P × S) (y : Strs) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (hd : (blkL Z G l false X arrs).decide x.2 rs gs = .ok x'.2)
    (hIn : InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
      (noL l false) x y) :
    (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub (.more (some l) "frame.sentIs1") x' = true := by
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  have hin : Pub.more (some l) "frame.sentIs" ∈
      (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
        (flatPlacesOf linksFull true))[noL l false]?.getD [] := by
    rw [plus13_more_closed Dm dk Mg₀ hM]
    exact inSet_of (List.all_eq_true.1 sentIn_mw l (List.mem_range.2 hl))
  have h0 := inAt_pub hIn _ (List.mem_append_left _ hin)
  rw [pub_plus13, First.pubAll_more_sentIs] at h0
  rw [pub_plus13, First.pubAll_more_sentIs1]
  have h1 := sentIs_k1Reads_plan Z G l X _ arrs x.2 x'.2 r₁ r₂ gs hd Dm.pubD.dS l Dm.N _
    (inAt_bookHeld hIn) h0
  have ho : Dm.pubD.dS1.own l = (ownPlus Dm.pubD.dS l (idsOf (parL Z G l false)
      (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l false]?))).own l := by
    show Dm.pubD.dS.own l ++ secondNos Dm.shape (base1At Dm.N Dm.links
      (flatPlacesOf Dm.links true)) l = (if l = l then Dm.pubD.dS.own l ++ idsOf (parL Z G l false)
        (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l false]?) else Dm.pubD.dS.own l)
    rw [if_pos rfl]
    exact congrArg _ (eq_of_beq (List.all_eq_true.1 hOwn1 l (List.mem_range.2 hl)))
  rw [sentIs_congr (ownPlus Dm.pubD.dS l (idsOf (parL Z G l false)
    (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l false]?))) Dm.pubD.dS1 l x'.2 rfl ho rfl]
  exact h1

end

/-! ## 3 The binder -/

section
variable {Xi Tok Cl : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public} {F : Frame}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE BINDER hpub OF k01_fifty, AT THE WIDER MEANING.** -/
theorem hpub_plus13 (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (hOwn1 : own1B Dm.shape Dm.N Dm.links Z Bs.G₀ = true)
    (hP : ∀ l, l < 25 → laterSeatsB Dm.N (parL Z Bs.G₀ l false) l 1
      (Dm.N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?) = true)
    (hRd : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (s s' : S) rs gs j r,
      rs.length = 2 → (blkL Z Bs.G₀ l false X arrs).decide s rs gs = .ok s' →
      Pub.formsInT l j r ∈ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true)
        (14 * l + k1Ix l false + 2)) → ReadersStay Dm.pubD l j r s s')
    (hfound : ∀ l, l < 25 → ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (s s' : S) rs gs,
      rs.length = 2 → (blkL Z Bs.G₀ l false X arrs).decide s rs gs = .ok s' →
      SecondFound (idsOf (parL Z Bs.G₀ l false) s.st.oracles.size).toList s s') :
    ∀ l, l < 25 → ∀ d : Bool, ∀ (base : ℕ) (d₁ d₂ : RDT) (cc e : ℕ),
      ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (c' : Block S Cl),
      c'.UnderR ((blkL Z Bs.G₀ l d X arrs).retype : Block S Cl) →
      ∀ (z : ProofFile.InstPub) (a : S × F.E.Str) τ x,
      Sound.onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (fun s : S => (z, s)) (noL l d) a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := F) c' base d₁ d₂ cc e).ior.red.out
        a τ = some x →
      ∀ q ∈ tiedL (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more l d,
        (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q (z, x.1) = true := by
  intro l hl d base d₁ d₂ cc e X arrs hX c' hu z a τ x ha hm hx q hq
  rw [plus13_more_closed Dm dk Mg₀ hM] at hq
  have hmade := List.all_eq_true.1 made_mw l (List.mem_range.2 hl)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hmade
  cases d with
  | true =>
    have hq' : q ∈ [] ++ madeAt mwMore linksFull (flatPlacesOf linksFull true)
        (14 * l + k1Ix l true + 2) := hq
    rw [hmade.1] at hq'
    simp at hq'
  | false =>
    have hq' : q ∈ tiedAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) ++
        madeAt mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) := hq
    rw [hmade.2] at hq'
    rcases List.mem_append.1 hq' with ht | hmk
    · exact hpub_reads_full Dm.pubD _ _ (pub_plus13 Dm dk Mg₀) l hl (parL Z Bs.G₀ l false)
        (blkL Z Bs.G₀ l false X arrs) (laterSend_k1Reads _ _ _ _ _ _)
        (rounds_blkL Z Bs.G₀ l false X arrs) c' hu base d₁ d₂ cc e z 1 (by decide) (hP l hl)
        (hRd l hl X arrs hX) (hfound l hl X arrs hX) a τ x ha hm hx q ht
    · obtain rfl := List.mem_singleton.1 hmk
      obtain ⟨rs, gs, h2, hd⟩ := yes_of_piece (W := Wit (CellsQ rows cols) Tok MsgT) (F := F)
        (blkL Z Bs.G₀ l false X arrs) (rounds_blkL Z Bs.G₀ l false X arrs) c' hu base d₁ d₂ cc e
        a τ x hx
      exact sentIs1_made Dm dk Mg₀ hM Z Bs.G₀ hOwn1 l hl X arrs (z, a.1) (z, x.1)
        (Sound.strsOf F a.2) rs gs h2 hd ⟨ha, hm⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.made_mw
#print axioms VerifiableInference.Desc.K1.sentIn_mw
#print axioms VerifiableInference.Desc.K1.madeTests_fail
#print axioms VerifiableInference.Desc.K1.sentIs1_made
#print axioms VerifiableInference.Desc.K1.hpub_plus13
