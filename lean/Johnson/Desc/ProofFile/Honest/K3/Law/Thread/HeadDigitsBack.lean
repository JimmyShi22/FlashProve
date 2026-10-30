-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/HeadDigitsBack.lean: the kind "lookup" (K3): behind an
accepting step of the description's own member at the lookup on the digits of the head's link: which
claim on the weights is laid. Honest/K3/Law/Thread/StateBehindHead.lean says that some claim is
laid; here `quietHead_whole` (Honest/K3/Law/Thread/QuietHeadWhole.lean), which keeps the equations
of the library's `quietHead` (Johnson/Desc/First/Look/K3Whole.lean), is called behind the member's
step. One theorem.

Terms. Honest/K3/GLOSSARY.md.

What is shown.
  `headDigits_stateW`: what the head heard and the head's tables are laid in front; the claim is
    what the library's `weightsClaim` (Johnson/Desc/First/Look/LookQuiet.lean) returns at these; the
    state behind is written out, field by field, over the own part of the head's link in front.

Hypotheses that remain. They are those of `headDigits_state` (StateBehindHead.lean).
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`, `hd`: s is a site of the public part (`lookSites Z`); it is on the digits.
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member m is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `hq`: what stands behind the lookup without a round is `quietHead`
    (Johnson/Desc/First/Look/K3Whole.lean).
  `h`: the member's step accepts from sj to sj'.

Users. Honest/K3/Law/Thread/CarriesHeadDigits.lean calls `headDigits_stateW`.

Limits. From an acceptance alone. On the verifier's side alone. No instance of these hypotheses is
exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.QuietHeadWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn named need)
open VerifiableInference.Desc.K3 (seatDigits quietAt quietHead)
open VerifiableInference.Desc.K3.Law (hearVia)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (weightsClaim)

local notation "FS" => VerifiableInference.Desc.First.S

/-- **Which claim is laid behind the member's accepting step.** Conditional on the hypotheses of
`headDigits_state`. No instance of these hypotheses is exhibited in this file. -/
theorem headDigits_stateW (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (hd : s.digits = true) (lot m : Block FS ProofFile.Cl)
    (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : lot.place = s.at_.place) (hm : m ∈ ch.blocksInOrder)
    (hmp : m.place = lot.place) (hpk : m.planOk = true)
    (hq : quietAt Z.p.X s.link true = some (quietHead Z.p.X)) (ft : Nat) (sj sj' : FS)
    (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn) (h : m.step ft sj rs c = .ok (sj', n)) :
    ∃ tl F H G a₀ cov x tt claim, sj.tl? = some tl ∧ sj.fork? = some F ∧
      hearVia s.p F rs = some (H, G) ∧ sj.here = .head a₀ ∧ a₀.opened = true ∧
      a₀.x = some x ∧ a₀.t = some tt ∧
      weightsClaim
        { h := Z.p.X.hS, L := Z.p.X.HLy, b := OnBytes.Model.Verify.borderOf Z.p.X.y,
          hp := Z.p.X.H, cov := cov, x := x, t := tt,
          iU3 := (Z.p.X.H.tl.ix.U.getD 2 none).getD 0 }
        Z.p.X.layers.wsLay = .ok claim ∧
      sj' = { sj with here := .head { a₀ with
        tl := { tl with
          foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some H },
        F := G, claim := some claim } } ∧
      sj'.failed = none := by
  obtain ⟨Fm, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot m hb hbs hm hmp hpk
  obtain ⟨_, _, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb m hm hmp
  obtain ⟨hl, hf, _⟩ := (hst ft sj sj' n rs c).1 h
  rw [hd] at Fm
  obtain ⟨F, H, G, a1, _, _, _, a5, hQ⟩ := form_state Fm ft sj sj' n rs c hl
  have a1' : sj.fork? = some F := a1
  obtain ⟨tl, htl⟩ := tl_of_fork sj a1'
  have hput : (seatDigits K3Lot.ofForm).put sj H G = _ := digits_put K3Lot.ofForm sj htl a1' H G
  unfold QuietBehind at hQ
  rw [hq] at hQ
  have hQ' : quietHead Z.p.X ((seatDigits K3Lot.ofForm).put sj H G) = .ok sj' := hQ
  rw [hput] at hQ'
  obtain ⟨a, cov, x, tt, claim, eh, _, _, ex, et, hw, _, e⟩ := quietHead_whole _ _ _ hQ'
  have key : ∃ a₀, sj.here = .head a₀ ∧ a₀.opened = true ∧ a₀.x = some x ∧ a₀.t = some tt ∧
      sj' = { sj with here := .head { a₀ with
        tl := { tl with
          foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next, heard := some H },
        F := G, claim := some claim } } := by
    cases hh : sj.here with
    | head a₀ =>
      have hF' : (if a₀.opened = true then some a₀.F else none) = some F := by
        have := a1'
        unfold S.fork? at this
        rw [hh] at this
        exact this
      cases ho₀ : a₀.opened with
      | false =>
        rw [ho₀] at hF'
        exact nomatch hF'
      | true =>
        simp only [S.putTl, S.putFork, hh, ho₀, if_true] at eh e
        obtain rfl := VerifiableInference.Desc.First.Here.head.inj eh
        refine ⟨a₀, rfl, ho₀, ex, et, ?_⟩
        rw [e, ho₀]
    | lay a₀ => simp [S.putTl, S.putFork, hh] at eh
    | att a₀ => simp [S.putTl, S.putFork, hh] at eh
    | between => simp [S.putTl, S.putFork, hh] at eh
    | fin a₀ => simp [S.putTl, S.putFork, hh] at eh
    | mem a₀ => simp [S.putTl, S.putFork, hh] at eh
  obtain ⟨a₀, k1, k2, k3, k4, k5⟩ := key
  exact ⟨tl, F, H, G, a₀, cov, x, tt, claim, htl, a1', a5, k1, k2, k3, k4, hw, k5, hf⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.headDigits_stateW
