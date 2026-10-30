-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/StateBehindHead.lean: the kind "lookup" (K3): the state
behind an accepting step of the description's own member at the lookup on the digits of the head's
link, as an equation in the state's own setters. The counterpart of `calls_state`
(Honest/K3/Law/Thread/StateBehind.lean) and `digits_state`
(Honest/K3/Law/Thread/StateBehindDigits.lean). No honest prover is spoken of. Theorems.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `quietHead_back`: the step without a round behind that lookup (`quietHead`,
    Johnson/Desc/First/Look/K3Whole.lean), taken apart where it returns.
  `headDigits_state`: the title's equation.

Hypotheses that remain, in `headDigits_state`.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the digits.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `hq`: the head's own step without a round stands behind the lookup (a condition on public data).
  `h`: the member's step accepts.

Users. `headDigits_state` is called in Honest/K3/Law/Thread/K3Keeps.lean,
Honest/K3/Law/Thread/K3KeepsSh.lean [not in this library], Honest/K3/Law/Thread/OnOutMember.lean and
Honest/K3/Law/Thread/HeadParts.lean. `quietHead_whole` (Honest/K3/Law/Thread/QuietHeadWhole.lean)
strengthens `quietHead_back`.

Limits. On the verifier's side alone. Of the claim that is set, and of what the hearing returns,
nothing is said. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StateBehindDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn named need)
open VerifiableInference.Desc.K3 (seatDigits quietAt quietHead)
open VerifiableInference.Desc.K3.Law (hearVia)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **The step without a round behind the lookup on the digits of the head's link, where it
returns**: the head's link is open, and the state behind is the state in front with one field of the
link's part set: the claim on the weights. -/
theorem quietHead_back (X : OnBytes.Model.Verify.Public) (u t : FS) (h : quietHead X u = .ok t) :
    ∃ a claim, u.here = .head a ∧ a.opened = true ∧
      t = { u with here := .head { a with claim := some claim } } := by
  unfold quietHead at h
  split at h
  · rename_i a hh
    by_cases ho : a.opened = true
    · simp only [need, ho, if_true, bind, Except.bind, pure, Except.pure] at h
      split at h
      · exact nomatch h
      · split at h
        · exact nomatch h
        · split at h
          · exact nomatch h
          · split at h
            · exact nomatch h
            · rename_i claim _
              split at h
              · exact nomatch h
              · refine ⟨a, claim, hh, ho, ?_⟩
                rw [← Except.ok.inj h, ho]
    · simp [need, ho, bind, Except.bind] at h
  · exact nomatch h

/-- **At the description's own member at the lookup on the digits of the head's link.** Conditional
on the hypotheses that the head of this file lists. No instance of these hypotheses is exhibited in
this file. -/
theorem headDigits_state (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ tl F H G a claim, sj.tl? = some tl ∧ sj.fork? = some F ∧
      (sj.tl?.bind (·.heard)).isNone = true ∧
      VerifiableInference.Desc.First.Tape.RowsOwed.noneWaits sj.rowsOwed = true ∧
      (F.next == s.p.first) = true ∧ hearVia s.p F rs = some (H, G) ∧
      ((sj.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some H }).putFork G).here = .head a ∧ a.opened = true ∧
      sj' = { (sj.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some H }).putFork G with here := .head { a with claim := some claim } } ∧
      sj'.failed = none := by
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  obtain ⟨hl, hf, _⟩ := (hst ft sj sj' n rs c).1 h
  rw [hd] at Fm
  obtain ⟨F, H, G, a1, a2, a3, a4, a5, hQ⟩ := form_state Fm ft sj sj' n rs c hl
  have a1' : sj.fork? = some F := a1
  obtain ⟨tl, htl⟩ := tl_of_fork sj a1'
  have hput : (seatDigits K3Lot.ofForm).put sj H G = _ := digits_put K3Lot.ofForm sj htl a1' H G
  unfold QuietBehind at hQ
  rw [hq] at hQ
  have hQ' : quietHead Z.p.X ((seatDigits K3Lot.ofForm).put sj H G) = .ok sj' := hQ
  rw [hput] at hQ'
  obtain ⟨a, claim, e1, e2, e3⟩ := quietHead_back _ _ _ hQ'
  exact ⟨tl, F, H, G, a, claim, htl, a1', a2, a3, a4, a5, e1, e2, e3, hf⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.quietHead_back
#print axioms ProofFile.Honest.K3.Law.AtThr.headDigits_state
