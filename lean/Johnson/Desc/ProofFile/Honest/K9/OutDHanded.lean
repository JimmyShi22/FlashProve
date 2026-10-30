-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/OutDHanded.lean: AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD
SEGMENT's BATCHING THE MERGE's SLOT LIES BELOW THE FIRST SLOT OF THE LOOKUP ON THE DIGITS: SO THE PREMISE outD OF
`liveLayers_of_clauses` (Honest/K9/GoodLayLive.lean) IS PAID THERE. Statements and proofs; no definition; no goal is
stated.
  `next_in_front`   under the head, at each of the fifty lookups: in front of the member's own accepting step the
      ledger's next slot is the lookup's first: the lookups' `form_state` at `site_block`'s form (the lines of
      the smallness test's `clause_at_step`, which speaks of the state BEHIND the step)
  **`merge_below_digits`**   under the head and the walk's premises at A.length = 14 (2 g) + 9: mergeOf s' = some j
      gives j < pD.first. HOW: `mid_handed` at 14 (2 g) + 8: the digits' member's own step leads into s' ·
      `mergeBelow_reach` at the state in front of it · `next_in_front` · that member leaves what K4's rounds
      returned (`four_decide` at "the same own") · `mergeOf_own` · `list_at_layers`
WHAT IS NOT CLAIMED. That any walk returns. NO MEMBER: no walk, state or list of marks is shown at which the premises
hold together. outC (the like at the calls' stretch): paid in Honest/K9/BatFrontHandedK4.lean, not here. No mark is
spent but the fit's. `merge_below_digits` is called by Honest/K9/BatFrontHanded.lean alone; `next_in_front` by this file
and Honest/K9/SeamHanded.lean. At the full size and the format's second hash function alone. Nothing on any property.
GROUND: beneath this file lie 338 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.LayFrontFold
import Johnson.P1K8R.ClausesAtFrame
import Johnson.P1K8R.ListAtLayers
import Johnson.Road.K4.MergeBelowReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.K9 (mergeOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Lay Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3 (lookSites Site)
open ProofFile.Honest.K3.Law (site_block memberAtSite seatOf)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty site_hub border_digits form_state)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

/-- **In front of a lookup's own accepting step the ledger's next slot is the lookup's first.** -/
theorem next_in_front (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp)
    (hl : s.link < 25) {blk : Block S ProofFile.Cl} (hblk : cF.blocksInOrder[borderOf s.link s.digits]? = some blk)
    {ft n : ℕ} {sj sk : S} {R : List Fmt.RoundView} {c : List Desc.OpenedColumn} (g3 : blk.step ft sj R c = .ok (sk, n)) :
    ∃ G, sj.fork? = some G ∧ G.next = s.p.first := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  obtain ⟨Fm, -⟩ := site_block _ _ _ _ Fd Zp Bs base cF A B O s hs lot blk hb hbs m1 m2 m3
  obtain ⟨-, -, -, -, hst⟩ := memberAtSite _ _ _ _ Fd Zp Bs base cF A B O lot hb blk m1 m2
  obtain ⟨G, -, -, hG, -, -, hn, -⟩ := form_state Fm ft sj sk n R c ((hst ft sj sk n R c).1 g3).1
  refine ⟨G, ?_, beq_iff_eq.1 hn⟩
  unfold seatOf at hG
  split at hG <;> exact hG

/-- **AT THE STATES THAT THE FRAME's FIELD HANDS IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING THE MERGE's SLOT LIES
BELOW THE FIRST SLOT OF THE LOOKUP ON THE DIGITS.** No mark is spent but the fit's. -/
theorem merge_below_digits (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {pD : Look.P}
    (hD : Look.placeAt (P5J.At.X Zp) (2 * g) true = some pD) (ms : List Mark)
    {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 14 * (2 * g) + 9) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {w₀ z : ProofFile.Honest.ChainProgress S ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : S}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true)
    (ha : ProofFile.Honest.ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) [] = .ok w₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr w₀ = .ok z) (hv : z.ver = some s') :
    ∀ j, mergeOf s' = some j → j < pD.first := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have n24 : ¬ 2 * g = 24 := by omega
  -- the site of the lookup on the digits
  obtain ⟨sD, hsD, elD, hdD, -, -⟩ := site_at_all_fifty h (2 * g) (by omega) true
  obtain rfl : sD.p = pD := by
    have k := (P1K8.site_pars sD hsD).1
    rw [elD, hdD] at k
    exact Option.some.inj (k.symm.trans hD)
  have hbD : borderOf (2 * g) true = 14 * (2 * g) + 8 := by
    rw [border_digits, if_neg n24]
  -- its member, which leaves what K4's rounds returned
  obtain ⟨b8, f8, D8⟩ := P1K8.four_decide LinkJoin.sameOwn_stretch LinkJoin.quietLayers_sameOwn h.scope h.reads O hg 3
    (by omega)
  obtain ⟨tj, tk, Rt, dt, q₂, q₃, e₂, e₃, -, g8, -, -, hrj, hrk, hf8⟩ :=
    P1K8.mid_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 14 * (2 * g) + 8) f8 ms hall hfit (by omega) hpos L hft hm ha
      hn hq hz hv
  rw [hA] at hf8
  obtain rfl : s' = tk := P1K8.fold_window_end hf8
  have d8 := ((Sound.step_ok_iff 0 b8 tj s' Rt dt dt.length).1 g8).2.2.2
  have hown : LinkJoin.SameOwn tj s' := D8 tj _ _ s' d8
  -- in front of it: the next slot; the merge's slot lies below
  obtain ⟨G, hG, hnx⟩ := next_in_front h sD hsD (by omega) (blk := b8) (by
    rw [elD, hdD, hbD]
    exact f8) g8
  have hMB : OnBytes.Road.K4.MergeBelow tj :=
    OnBytes.Road.K4.mergeBelow_reach h.scope h.reads O h.laid.planOk hg (i := 3) (by omega) (by
      rw [show 28 * g + 5 + 3 = 14 * (2 * g) + 8 by omega]
      exact hrj)
  -- the merge's slot is read off what K4's rounds returned
  obtain ⟨-, -, o, -, -, eo, -⟩ :=
    P1K8.list_at_layers _ _ _ _ _ _ _ _ _ _ h.scope h.reads O _ (ProofFile.startS Zp) g hg zp s' (by
            rw [show 28 * g + 9 = 14 * (2 * g) + 8 + 1 by omega]
            exact hrk)
  have e1 : mergeOf s' = some o.wo.sFv := OnBytes.Road.K4.mergeOf_own eo
  have e2 : mergeOf tj = some o.wo.sFv := OnBytes.Road.K4.mergeOf_own (hown.symm.trans eo)
  intro j hj
  obtain rfl : o.wo.sFv = j := Option.some.inj (e1.symm.trans hj)
  obtain ⟨G', hG', hlt⟩ := hMB _ e2
  obtain rfl : G' = G := Option.some.inj (hG'.symm.trans hG)
  rw [← hnx]
  exact hlt

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.next_in_front
#print axioms ProofFile.Honest.K9.merge_below_digits
