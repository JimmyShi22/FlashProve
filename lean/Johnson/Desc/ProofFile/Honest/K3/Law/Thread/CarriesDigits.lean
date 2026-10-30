-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CarriesDigits.lean: the kind "lookup" (K3): the cut of a
member's acceptance into structure and values (Honest/Thread/Shape.lean), at the member of the
description's first chain at a lookup on the digits of a layers' or an attention link: the member's
guards on the first chain's shape, written as one Boolean test and one update, both definitions with
code; and `Carries` for these guards. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the shape of a state is `chainSh`
(Johnson/Desc/First/Shape/Chain.lean), of nineteen components. The guards of a member are the field
g of `Shape` (Honest/Thread/Shape.lean) at its border: a function on shapes that returns a shape or
a rejection. A filling of the cut's letters is a value of `Shape`. `Carries` and `Returns` are
definitions of Shape.lean (there labelled (B1) and (B2)).

What is shown.
  `digitsB`, `digitsU`, `digitsG`: the test; the update, written out component by component; the
    guards, which are "if the test passes then the update, else a rejection".
  `digitsHere_here`: from `DigitsHere` (Honest/K3/Law/Thread/DigitsParts.lean): the mark, the sort
    of the link, what stands at the memory and four more readers stay.
  `carriesR_digits`: the sentence of `Carries` at the member's step (helpers: `digitsU_at`,
    `sized_of_digitsB`).
  `carries_digits`: `Carries bs ft Z b`, at every filling Z of the cut's letters whose sh is the
    first chain's shape and whose g at b is `digitsG`.
The update changes two of the nineteen components: tl (four fields: one more fold sampled; the
ledger's count in front and behind; what was heard) and led (`lookUpd` of the face,
Honest/K3/Shape/Ops.lean, with the plan's number of claims laid by `setPlan`, DigitsParts.lean). The
test asks: no mark; no row waits; a structure of the smallness test is there and nothing is heard in
it yet; a ledger is there, its count is the lookup's first slot, its three arrays have their size,
the lookup's slots are there and free, and the count behind is the plan's.
The proof of `Carries` uses one clause of the test: the arrays have their size. `Returns` is not
shown in this file.

Hypotheses that remain.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the digits.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member m is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk). In `carries_digits` the one hypothesis `hm` says the
    three of the entry of bs at b.
  `hq`: which step without a round stands behind the lookup: `quietAt` at the link's digits is
    `quietDigits used claims` (Johnson/Desc/First/Look/K3Whole.lean). It is a public fact.
  `h`, `hg`: (in `carriesR_digits`) the member's step accepts from sj to sj'; the guards return at
    the shape of sj.
  `hg`: (in `carries_digits`) g at b is `digitsG s.shape s.p.first used claims`.
  In the helpers: `hC`: `DigitsHere`; `ht`, `hl`, `hF`: the shape holds the smallness test's
    structure and a ledger's shape; a ledger is open; `hB`: `digitsB` accepts.

Follows. This file is the counterpart, at the digits, of Honest/K3/Law/Thread/CarriesCalls.lean.

Imported: Johnson/Desc/First/Shape/Chain.lean and Honest/Thread/Shape.lean.

Users. `carries_digits_link` (Honest/K3/Law/Thread/AtLink.lean) calls `carries_digits` at the first
chain's flat list and the border; `carries_digits_link24` (Honest/K3/Law/Thread/QuietAtLink.lean) is
that theorem without `hq`, at a link below 24. `returns_digits`
(Honest/K3/Law/Thread/ReturnsLook.lean) is `Returns` at the same guards.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Not at the head's link. No filling Z is constructed here: `carries_digits` is stated for an
arbitrary one. With another version of Johnson/Desc/First/Shape/Chain.lean the shape is another.
`Carries` and `Returns` have different hypotheses on the link: `carries_digits` assumes `hq`, and
`returns_digits` assumes `hc`, that the site's caller is not the head. No theorem of this file ties
the two. So, of the fifty lookups of the full size: for the 25 on the calls both properties are
stated in CarriesCalls.lean and ReturnsLook.lean; for the 24 on the digits of the links other than
the head's, `Returns` is stated under `s.caller ≠ .head`, a public fact that is assumed and is not
derived here from the library's hypothesis `P5J.AtMgA` (since: `caller_ne_head`,
Honest/K3/Law/Thread/CallerAtLink.lean, shows it under `P5J.AtMgA` at every site whose link is not
24); the lookup on the digits of the head's link is not treated in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Shape.Chain
import Johnson.Desc.ProofFile.Honest.Thread.Shape
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DigitsParts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LedNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork HTailF2)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf quietAt quietDigits)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh LedSh TailSh ledSh tailSh heardAll sizedB
  freeB hereNo endSh attOf finOf)
open ProofFile.Honest.K3.Shape (lookUpd lookHeardSh)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "FShape" => OnBytes.Model.Forest.Shape
local notation "headShOf" => VerifiableInference.Desc.First.Shape.headOf

/-- **The Boolean test.** Here h is the lookup's shape, first is its first slot, and used is the
plan's count behind. -/
def digitsB (h : FShape) (first used : Nat) (a : ChainSh) : Bool :=
  !a.marked && VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits a.rowsOwed &&
    a.tl.any (fun T => T.heard.isNone) &&
    a.led.any fun Ld =>
      Ld.next == first && sizedB Ld && freeB Ld first (OnBytes.Model.Forest.elems h) &&
        (lookUpd (faceOf h) Ld).next == used

/-- **The update**, written out component by component: seventeen components stay as they are, two
are set. Where the shape lacks the smallness test's structure or the ledger's shape nothing is
changed. -/
def digitsU (h : FShape) (claims : Nat) (a : ChainSh) : ChainSh :=
  match a.tl, a.led with
  | some T, some Ld =>
    ChainSh.mk a.marked a.here
      (some { T with
        foldDrawn := T.foldDrawn + 1, slotA := Ld.next, slotB := (lookUpd (faceOf h) Ld).next,
        heard := some (lookHeardSh h Ld.next Ld.owed.length) })
      (some (setPlan (lookUpd (faceOf h) Ld) claims)) a.tables a.rowsOwed a.core a.reply
      a.indexMasks a.pile a.atEnd a.check a.link a.look a.lookHeard a.own a.head a.att a.fin
  | _, _ => a

/-- **The guards.** -/
def digitsG (h : FShape) (first used claims : Nat) (a : ChainSh) : Except String ChainSh :=
  if digitsB h first used a then .ok (digitsU h claims a) else .error "K3: the lookup on the digits"

/-- The mark, the sort of the link, what stands at the memory and four more readers stay. -/
theorem digitsHere_here {sj sj' : FS} {tl' : HTailF2} {G' : Fork} (hC : DigitsHere sj sj' tl' G') :
    sj'.failed = sj.failed ∧ hereNo sj'.here = hereNo sj.here ∧
      endSh sj'.here = endSh sj.here ∧ sj'.own? = sj.own? ∧
      headShOf sj'.here = headShOf sj.here ∧ attOf sj'.here = attOf sj.here ∧
      finOf sj'.here = finOf sj.here := by
  rcases hC with ⟨a, hh, rfl⟩ | ⟨a, hh, rfl⟩ | ⟨a, hh, ho, rfl⟩
  · exact ⟨rfl, by simp [hereNo, hh], by simp [endSh, hh], by simp [S.own?, hh],
      by rw [hh]; rfl, by rw [hh]; rfl, by rw [hh]; rfl⟩
  · exact ⟨rfl, by simp [hereNo, hh], by simp [endSh, hh], by simp [S.own?, hh],
      by rw [hh]; rfl, by rw [hh]; rfl, by rw [hh]; rfl⟩
  · exact ⟨rfl, by simp [hereNo, hh, ho], by simp [endSh, hh], by simp [S.own?, hh],
      by rw [hh]; simp [VerifiableInference.Desc.First.Shape.headOf,
        VerifiableInference.Desc.First.Shape.headSh, ho], by rw [hh]; rfl, by rw [hh]; rfl⟩

/-- The update, where both shapes are there. -/
theorem digitsU_at {h : FShape} {claims : Nat} {a : ChainSh} {T : TailSh} {Ld : LedSh}
    (ht : a.tl = some T) (hl : a.led = some Ld) :
    digitsU h claims a = ChainSh.mk a.marked a.here
      (some { T with
        foldDrawn := T.foldDrawn + 1, slotA := Ld.next, slotB := (lookUpd (faceOf h) Ld).next,
        heard := some (lookHeardSh h Ld.next Ld.owed.length) })
      (some (setPlan (lookUpd (faceOf h) Ld) claims)) a.tables a.rowsOwed a.core a.reply
      a.indexMasks a.pile a.atEnd a.check a.link a.look a.lookHeard a.own a.head a.att a.fin := by
  unfold digitsU
  rw [ht, hl]

/-- The test includes the test on the ledger's arrays, at the ledger that the state holds. -/
theorem sized_of_digitsB {h : FShape} {first used : Nat} {sj : FS}
    (hB : digitsB h first used (chainSh sj) = true) (F : Fork) (hF : sj.fork? = some F) :
    sizedB (ledSh F) = true := by
  have hl : (chainSh sj).led = some (ledSh F) := by
    show sj.fork?.map ledSh = _
    rw [hF]
    rfl
  unfold digitsB at hB
  rw [hl] at hB
  simp only [Bool.and_eq_true, Option.any_some] at hB
  exact hB.2.1.1.2

/-- **The sentence of `Carries` at the member's step.** Conditional on what this file's head lists.
No instance of these hypotheses is exhibited in this file. -/
theorem carriesR_digits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (used claims : Nat)
    (hq : quietAt Z.p.X s.link true = some (quietDigits used claims)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (t : ChainSh)
    (h : m.step ft sj rs c = .ok (sj', n))
    (hg : digitsG s.shape s.p.first used claims (chainSh sj) = .ok t) : t = chainSh sj' := by
  unfold digitsG at hg
  cases hB : digitsB s.shape s.p.first used (chainSh sj) with
  | false =>
    rw [hB] at hg
    exact nomatch hg
  | true =>
    rw [hB] at hg
    have ht : digitsU s.shape claims (chainSh sj) = t := Except.ok.inj hg
    obtain ⟨tl, F, htl, a1, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, _, _⟩ :=
      digits_parts o pol lay KL Fd Z Bs base ch A B O s hs hd lot m hb hbs hm hmp hpk used claims
        hq ft sj sj' n rs c h (sized_of_digitsB hB)
    obtain ⟨tl₂, F₂, H, G, htl₂, a1₂, _, _, _, _, _, e, _⟩ := digits_state o pol lay KL Fd Z Bs base
      ch A B O s hs hd lot m hb hbs hm hmp hpk used claims hq ft sj sj' n rs c h
    obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := digitsHere_here (digits_here_of a1₂ e)
    have hl : (chainSh sj).led = some (ledSh F) := by
      show sj.fork?.map ledSh = _
      rw [a1]
      rfl
    have hT : (chainSh sj).tl = some (tailSh tl) := by
      show sj.tl?.map tailSh = _
      rw [htl]
      rfl
    rw [← ht, digitsU_at hT hl, ← heardSh_led]
    unfold chainSh
    rw [q1, q2, q3, q4, q5, q6, q7, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12]
    rfl

/-- **`Carries`, in the form of Honest/Thread/Shape.lean**, at every filling of the cut's letters
whose shape is the first chain's and whose guards at b are `digitsG`. It is stated for an arbitrary
filling: none is constructed here. -/
theorem carries_digits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (used claims : Nat)
    (hq : quietAt Z.p.X s.link true = some (quietDigits used claims))
    (bs : List (Block FS ProofFile.Cl)) (ft b : Nat)
    (hm : ∀ blk, bs[b]? = some blk → blk ∈ ch.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → FS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g b = digitsG s.shape s.p.first used claims) :
    Carries bs ft ⟨ChainSh, chainSh, g, vals⟩ b := by
  intro blk hblk sj rs cols sj' n t hst hgt
  obtain ⟨h1, h2, h3⟩ := hm blk hblk
  have hgt' : g b (chainSh sj) = .ok t := hgt
  rw [hg] at hgt'
  exact carriesR_digits o pol lay KL Fd Z Bs base ch A B O s hs hd lot blk hb hbs h1 h2 h3 used
    claims hq ft sj sj' n rs cols t hst hgt'

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.digitsHere_here
#print axioms ProofFile.Honest.K3.Law.AtThr.digitsU_at
#print axioms ProofFile.Honest.K3.Law.AtThr.sized_of_digitsB
#print axioms ProofFile.Honest.K3.Law.AtThr.carriesR_digits
#print axioms ProofFile.Honest.K3.Law.AtThr.carries_digits
