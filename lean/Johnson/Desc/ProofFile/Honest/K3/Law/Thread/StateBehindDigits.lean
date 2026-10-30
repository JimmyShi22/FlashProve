-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/StateBehindDigits.lean: the kind "lookup" (K3): the
state behind an accepting step of the description's own member at a lookup on the digits, as an
equation in the state's own setters, at a link whose step without a round behind the lookup is the
one that holds the planned slots taken (a layers' or an attention link). The counterpart of
`calls_state` (Honest/K3/Law/Thread/StateBehind.lean). No honest prover is spoken of. One theorem.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `digits_state`: the title's equation.

Hypotheses that remain.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the digits.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `hq`: which step without a round stands behind the lookup (a condition on public data).
  `h`: the member's step accepts.

Users. `digits_state` is called in Honest/K3/Law/Thread/K3Keeps.lean,
Honest/K3/Law/Thread/K3KeepsSh.lean [not in this library], Honest/K3/Law/Thread/K3KeepsOut.lean
[not in this library], Honest/K3/Law/Thread/OnOutMember.lean, Honest/K3/Law/Thread/DigitsParts.lean
and Honest/K3/Law/Thread/CarriesDigits.lean. Honest/K3/Law/Thread/StateBehindHead.lean imports this
file too.

Limits. Not at the head's link: there another step stands behind. On the verifier's side alone. Of
what the hearing returns nothing is said. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn named)
open VerifiableInference.Desc.K3 (seatDigits quietAt quietDigits)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.First.Look (slotsTaken)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **At the description's own member at a lookup on the digits: the state behind is the state in
front with four fields of the smallness test's structure set, then the ledger set, then the ledger
with the plan's number of claims; it bears no mark.** Conditional on the hypotheses that the head of
this file lists. No instance of these hypotheses is exhibited in this file. -/
theorem digits_state (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true) (used claims : Nat)
    (hq : quietAt Z.p.X s.link true = some (quietDigits used claims)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ tl F H G, sj.tl? = some tl ∧ sj.fork? = some F ∧
      (sj.tl?.bind (·.heard)).isNone = true ∧
      VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits sj.rowsOwed = true ∧
      (F.next == s.p.first) = true ∧ hearVia s.p F rs = some (H, G) ∧
      (G.next == used) = true ∧
      sj' = ((sj.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some H }).putFork G).putFork { G with planClaimsF := claims } ∧
      sj'.failed = none := by
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  obtain ⟨hl, hf, _⟩ := (hst ft sj sj' n rs c).1 h
  rw [hd] at Fm
  obtain ⟨F, H, G, a1, a2, a3, a4, a5, hQ⟩ := form_state Fm ft sj sj' n rs c hl
  have a1' : sj.fork? = some F := a1
  obtain ⟨tl, htl⟩ := tl_of_fork sj a1'
  have hput : (seatDigits K3Lot.ofForm).put sj H G = _ := digits_put K3Lot.ofForm sj htl a1' H G
  have hfk : ((seatDigits K3Lot.ofForm).put sj H G).fork? = some G :=
    (ProofFile.Honest.K3.Law.digits_put K3Lot.ofForm sj H G a1).2.1
  unfold QuietBehind at hQ
  rw [hq] at hQ
  have hQ' : quietDigits used claims ((seatDigits K3Lot.ofForm).put sj H G) = .ok sj' := hQ
  unfold quietDigits at hQ'
  rw [hfk] at hQ'
  by_cases hn : (G.next == used) = true
  · simp [named, slotsTaken, hn, bind, Except.bind, pure, Except.pure] at hQ'
    refine ⟨tl, F, H, G, htl, a1', a2, a3, a4, a5, hn, ?_, hf⟩
    rw [← hQ', hput]
  · simp [named, slotsTaken, hn, bind, Except.bind] at hQ'

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.digits_state
