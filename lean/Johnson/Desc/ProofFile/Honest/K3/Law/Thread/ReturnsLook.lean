-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ReturnsLook.lean: the kind "lookup" (K3): the cut of a
member's acceptance into structure and values (Honest/Thread/Shape.lean): `Returns` at the
description's own member at a lookup: where the guards on the first chain's shape return at the
state's shape, and the rounds and columns pass the step's own two tests, the member's own decision
returns. This holds at every letter for the named tests on values: the proofs do not use that
hypothesis of `Returns`. So at the members treated here, which are not the head's own digits, that
letter may be given the value "true". Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: `Carries` and `Returns` are definitions of
Honest/Thread/Shape.lean (there labelled (B1) and (B2)). The guards of a member are the field g of
`Shape` (there) at its border; the letter for the named tests on values is its field vals. The shape
of a state is `chainSh` (Johnson/Desc/First/Shape/Chain.lean).

What is shown.
  `callsB_reads`, `digitsB_reads`: the guards' Boolean test, read back through the shape at the
    state.
  `returns_calls`: `Returns bs ft Z b` at a lookup on the calls, at g b = `callsG`
    (Honest/K3/Law/Thread/CarriesCalls.lean).
  `returns_digits`: the same at the digits of a layers' or an attention link, at g b = `digitsG`
    (Honest/K3/Law/Thread/CarriesDigits.lean).
These two files show `Carries` at the same guards.

Hypotheses that remain.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); its sort.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`: the member is in the description's first chain, at that place, and passes its test on the
    plan.
  `hok`; `hT2` at the calls; `hT3` at the digits: public tests with code.
  `hc`: at the digits: it is not the head's link.
  `hg`: g at b is the guards named above. At the digits the guards' letters used and claims are
    free: `Returns` holds at whatever they are; `Carries` ties them to the plan.
  `hB`: (in `callsB_reads`, `digitsB_reads`) the guard accepts at the state's shape.

How the proof goes. By `member_decides` (Honest/K3/Law/Thread/MemberDecides.lean).

Imported, through Honest/K3/Law/Thread/CarriesCalls.lean: Johnson/Desc/First/Shape/Chain.lean and
Honest/Thread/Shape.lean.

Users. These theorems are not for the lookups' own "it is accepted" (`Accepted`,
Honest/Thread/Pays.lean), which is shown outright in Honest/K3/Law/Thread/AtThreadSite.lean. They
are for a caller that runs the shape along the whole chain. `returns_calls_link` and
`returns_digits_link` (Honest/K3/Law/Thread/AtLink.lean) call them.

Limits. Not at the head's own digits: there `returns_headDigits`
(Honest/K3/Law/Thread/CarriesHeadDigits.lean) assumes something of the letter vals (`hv`). At the
digits the proof does not use the guards' clause on the count behind: it uses the public test `hT3`.
No instance of these hypotheses is exhibited in this file. No filling of the cut's letters is
constructed here: the theorems are stated for arbitrary g and vals. With another version of
Johnson/Desc/First/Shape/Chain.lean the shape is another.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.MemberDecides
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CarriesCalls
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CarriesDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf quietAt quietDigits)
open VerifiableInference.Desc.First.Look (sameShape)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ledSh tailSh heardAll freeB)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "FShape" => OnBytes.Model.Forest.Shape

/-- **The Boolean test at the calls, read back at the state.** -/
theorem callsB_reads {h : FShape} {first : Nat} {sj : FS}
    (hB : callsB h first (chainSh sj) = true) :
    sj.failed = none ∧ VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits sj.rowsOwed = true ∧
      sj.lookHeard?.isNone = true ∧ ∃ F, sj.fork? = some F ∧ F.next = first ∧
        freeB (ledSh F) F.next (faceOf h).slots = true := by
  unfold callsB at hB
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hB
  obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := hB
  have c1 : sj.failed.isSome = false := b1
  have c3 : (sj.lookHeard?.map heardAll).isNone = true := b3
  have c4 : (sj.fork?.map ledSh).any (fun Ld => Ld.next == first &&
      VerifiableInference.Desc.First.Shape.sizedB Ld &&
      freeB Ld first (OnBytes.Model.Forest.elems h)) = true := b4
  have d1 : sj.failed = none := by
    cases hf : sj.failed with
    | none => rfl
    | some v =>
      rw [hf] at c1
      exact nomatch c1
  have d3 : sj.lookHeard?.isNone = true := by
    cases hl : sj.lookHeard? with
    | none => rfl
    | some v =>
      rw [hl] at c3
      exact nomatch c3
  refine ⟨d1, b2, d3, ?_⟩
  cases hF : sj.fork? with
  | none =>
    rw [hF] at c4
    exact nomatch c4
  | some F =>
    rw [hF] at c4
    simp only [Option.map_some, Option.any_some, Bool.and_eq_true, beq_iff_eq] at c4
    have hn : F.next = first := c4.1.1
    refine ⟨F, rfl, hn, ?_⟩
    rw [Spec.slots_elems, hn]
    exact c4.2

/-- **The Boolean test at the digits, read back at the state.** -/
theorem digitsB_reads {h : FShape} {first used : Nat} {sj : FS}
    (hB : digitsB h first used (chainSh sj) = true) :
    sj.failed = none ∧ VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits sj.rowsOwed = true ∧
      (sj.tl?.bind (·.heard)).isNone = true ∧ ∃ F, sj.fork? = some F ∧ F.next = first ∧
        freeB (ledSh F) F.next (faceOf h).slots = true := by
  unfold digitsB at hB
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hB
  obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := hB
  have c1 : sj.failed.isSome = false := b1
  have c3 : (sj.tl?.map tailSh).any (fun T => T.heard.isNone) = true := b3
  have c4 : (sj.fork?.map ledSh).any (fun Ld => Ld.next == first &&
      VerifiableInference.Desc.First.Shape.sizedB Ld &&
      freeB Ld first (OnBytes.Model.Forest.elems h) &&
      (ProofFile.Honest.K3.Shape.lookUpd (faceOf h) Ld).next == used) = true := b4
  have d1 : sj.failed = none := by
    cases hf : sj.failed with
    | none => rfl
    | some v =>
      rw [hf] at c1
      exact nomatch c1
  have d3 : (sj.tl?.bind (·.heard)).isNone = true := by
    cases hl : sj.tl? with
    | none => rfl
    | some tl =>
      rw [hl] at c3
      have c3' : (tl.heard.map heardAll).isNone = true := c3
      show tl.heard.isNone = true
      cases hx : tl.heard with
      | none => rfl
      | some v =>
        rw [hx] at c3'
        exact nomatch c3'
  refine ⟨d1, b2, d3, ?_⟩
  cases hF : sj.fork? with
  | none =>
    rw [hF] at c4
    exact nomatch c4
  | some F =>
    rw [hF] at c4
    simp only [Option.map_some, Option.any_some, Bool.and_eq_true, beq_iff_eq] at c4
    have hn : F.next = first := c4.1.1.1
    refine ⟨F, rfl, hn, ?_⟩
    rw [Spec.slots_elems, hn]
    exact c4.1.2

/-- **`Returns` at a lookup on the calls**, in the form of Honest/Thread/Shape.lean, for arbitrary g
and vals. Conditional on what the head lists (`O`, `hs`, `hd`, `hb`, `hbs`, `hm`, `hok`, `hT2`,
`hg`). No instance of these hypotheses is exhibited in this file. -/
theorem returns_calls (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = false) (lot : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place)
    (hok : s.at_.face.ok = true)
    (hT2 : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true)
    (bs : List (Block FS ProofFile.Cl)) (ft b : Nat)
    (hm : ∀ blk, bs[b]? = some blk → blk ∈ ch.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → FS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g b = callsG s.shape s.p.first) :
    Returns bs ft ⟨ChainSh, chainSh, g, vals⟩ b := by
  intro blk hblk sj rs cols t hgt hFit _
  obtain ⟨h1, h2, h3⟩ := hm blk hblk
  have hgt' : g b (chainSh sj) = .ok t := hgt
  rw [hg] at hgt'
  have hB : callsB s.shape s.p.first (chainSh sj) = true := by
    unfold callsG at hgt'
    cases hx : callsB s.shape s.p.first (chainSh sj) with
    | true => rfl
    | false => rw [hx] at hgt'; exact nomatch hgt'
  obtain ⟨r1, r2, r3, F, r4, r5, r6⟩ := callsB_reads hB
  refine member_decides o pol lay KL Fd Z Bs base ch A B O s hs lot blk hb hbs h1 h2 h3 hok hT2
    (by rw [hd]; rfl) ft sj F r1 (by rw [hd]; exact r4) (by rw [hd]; exact r3)
    (by rw [hd]; exact r2) r5 r6 (fun hd1 => by rw [hd] at hd1; exact nomatch hd1) rs cols hFit

/-- **`Returns` at a lookup on the digits of a layers' or an attention link**, in the form of
Honest/Thread/Shape.lean, for arbitrary g and vals. Conditional on what the head lists (`O`, `hs`,
`hd`, `hc`, `hb`, `hbs`, `hm`, `hok`, `hT3`, `hg`). No instance of these hypotheses is exhibited in
this file. -/
theorem returns_digits (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (hc : s.caller ≠ .head)
    (lot : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hok : s.at_.face.ok = true)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true) (used claims : Nat)
    (bs : List (Block FS ProofFile.Cl)) (ft b : Nat)
    (hm : ∀ blk, bs[b]? = some blk → blk ∈ ch.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → FS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g b = digitsG s.shape s.p.first used claims) :
    Returns bs ft ⟨ChainSh, chainSh, g, vals⟩ b := by
  intro blk hblk sj rs cols t hgt hFit _
  obtain ⟨h1, h2, h3⟩ := hm blk hblk
  have hgt' : g b (chainSh sj) = .ok t := hgt
  rw [hg] at hgt'
  have hB : digitsB s.shape s.p.first used (chainSh sj) = true := by
    unfold digitsG at hgt'
    cases hx : digitsB s.shape s.p.first used (chainSh sj) with
    | true => rfl
    | false => rw [hx] at hgt'; exact nomatch hgt'
  obtain ⟨r1, r2, r3, F, r4, r5, r6⟩ := digitsB_reads hB
  refine member_decides o pol lay KL Fd Z Bs base ch A B O s hs lot blk hb hbs h1 h2 h3 hok
    (by rw [hd]; rfl) hT3 ft sj F r1 (by rw [hd]; exact r4) (by rw [hd]; exact r3)
    (by rw [hd]; exact r2) r5 r6 (fun _ hh => absurd hh hc) rs cols hFit

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.callsB_reads
#print axioms ProofFile.Honest.K3.Law.AtThr.digitsB_reads
#print axioms ProofFile.Honest.K3.Law.AtThr.returns_calls
#print axioms ProofFile.Honest.K3.Law.AtThr.returns_digits
