-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/SeamHanded.lean: THE SEAM: AT A FEED-FORWARD SEGMENT NO SLOT LIES BETWEEN THE MERGE's
AND THE STRETCH OF THE LOOKUP ON THE DIGITS: the three members between K4's and that lookup's (14 l + 5, + 6, + 7: the
sending of the reads with the step that lays the tables; the smallness test's own sub-protocol; the sending of the
digits) leave the ledger's next slot. For the premise hseam of `batFrontLay_handed_nums`
(Honest/K9/BatFrontHandedNums.lean). IT SPENDS NO MARK: it goes over "reached". ONE DEFINITION; statements and proofs;
no goal is stated.
  `OwnNext s t`   A DEFINITION: t holds as K4's own what s holds, and the open ledger's next slot is the same (both read
      through `S.own?`, `S.fork?`; where no ledger is open at either, the second half is none = none and says nothing) ·
      `ownNext_trans`
  `k1_ownNext`, `k8_ownNext`, `quietLayers_ownNext`   the three texts' decisions keep it: the sealed
      `LinkJoin.k1Later_sameOwn`, `k8_sameOwn`, `quietLayers_sameOwn` for the first half; for the second the sealed
      `K1.commitAtS_next'` (Johnson/Desc/K1/Law/NextKept.lean), `First.K8.hear_leaves_fork`, `K1.same_layers`
  `ownNext_back`   from a state reached at 28 g + 8 back to one reached at 28 g + 5: the sealed `LinkJoin.ownLater_back`
      (Johnson/Desc/First/Link/Law/StretchParts.lean), ITS LINES TYPED ONCE MORE at this relation: `back_k1_of`,
      `back_k8_of`, `back_readsL_of` are general in the relation
  **`seam_reached`**   under the head: AT EVERY STATE s' REACHED AT 14 (2 g) + 9, from any start: whatever o it holds as
      K4's own: pD.first = o.wo.sFv + 1. HOW: the last step back (the sealed `reach_pred`) is the digits' lookup's own:
      in front of it the next slot is pD.first (`next_in_front`, Honest/K9/OutDHanded.lean) · `ownNext_back` · at the
      state reached behind K4 the sealed `mergeBelow_made` has o.wo.sFv + 1 = the next slot · K4's own ties the ends
      (SOME predecessor does no harm: it holds the same o)
  **`seam_handed`**   hseam's text at the states that the frame's field hands: `mid_handed`
      gives "reached"; then one call
WHAT IS NOT CLAIMED. That any state is reached: where none is, `seam_reached` is true for nothing; where s' holds
nothing as K4's own, too (`list_at_layers` shows that a reached one does). That any walk
returns. NO MEMBER: no reached state is shown. `seam_handed` is called by Honest/K9/BatFrontHandedFilled.lean alone. At
the full size and the format's second hash function alone. Nothing on any property.
GROUND: beneath this file lie 339 files that are no row of the sealed library's list (laws.11), this one among them:
reading copies, all but ours. (Files in our tree at a path of the sealed list are not counted, whatever their bytes: the
ride takes the seal's bytes.)
-/
import Johnson.Desc.ProofFile.Honest.K9.OutDHanded
import Johnson.Desc.K1.Law.NextKept
import Johnson.Desc.K1.Law.CarriesAtLater
import Johnson.Desc.First.Link.Law.StretchParts
import Johnson.Desc.First.Link.Law.OwnStay
import Johnson.Road.K4.MergeBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Lay Mid Step walk Mark marksQuiet drawsFit)
open ProofFile.Honest.K3.Law.AtThr (site_at_all_fifty border_digits)

/-- What K4's rounds returned stays, and the open ledger's next slot stays. -/
def OwnNext (s t : S) : Prop := t.own? = s.own? ∧ t.fork?.map (·.next) = s.fork?.map (·.next)

theorem ownNext_trans (a b c : S) (h : OwnNext a b) (k : OwnNext b c) : OwnNext a c :=
  ⟨k.1.trans h.1, k.2.trans h.2⟩

/-- The later sending keeps both. -/
theorem k1_ownNext (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Decides OwnNext (VerifiableInference.Desc.K1.laterAt (Cl := Unit) q gp link piece moment arrays) :=
  fun s rs gs t h => ⟨LinkJoin.k1Later_sameOwn q gp link piece moment arrays s rs gs t h,
    VerifiableInference.Desc.K1.commitAtS_next' h⟩

/-- The smallness test's own sub-protocol keeps both. -/
theorem k8_ownNext (p : First.K8.ParW) : Decides OwnNext (First.K8.whole p) :=
  fun s rs gs t h => ⟨LinkJoin.k8_sameOwn p s rs gs t h,
    congrArg (Option.map (·.next)) (First.K8.hear_leaves_fork (Cl := Claim) p.toPar s rs gs t h)⟩

/-- The step that lays the tables keeps both. -/
theorem quietLayers_ownNext (P : VerifiableInference.Desc.K8.ReadsQuiet.PG) :
    Decides OwnNext (VerifiableInference.Desc.K8.ReadsQuiet.layers P) :=
  fun s rs gs t h => ⟨LinkJoin.quietLayers_sameOwn P s rs gs t h,
    congrArg (Option.map (·.next)) (VerifiableInference.Desc.K1.same_layers P s t rs gs h).1⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **From the front of the lookup on the digits back to the border behind K4's member**: the three members between
keep what K4's rounds returned and the ledger's next slot. -/
theorem ownNext_back (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 8) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ OwnNext s s' := by
  have n24 : 2 * g ≠ 24 := by omega
  have i1 : IM.k1Ix (2 * g) true = 5 := by
    show (if true = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 5
    simp [n24]
  have i8 : LinkJoin.k8Ix (2 * g) = 4 := by
    show 4 + (if 2 * g = 24 then 1 else 0) = 4
    simp [n24]
  have e8 : 28 * g + 8 = 14 * (2 * g) + 5 + 2 + 1 := by omega
  rw [e8] at h
  obtain ⟨s₂, r2, q2⟩ := LinkJoin.back_k1_of k1_ownNext hS hR O (l := 2 * g) (by omega) (z := z)
    (s' := s') (by rw [i1]; exact h)
  rw [i1] at r2
  obtain ⟨s₁, r1, q1⟩ := LinkJoin.back_k8_of k8_ownNext hS hR O (l := 2 * g) (by omega) (z := z)
    (s' := s₂) (by rw [i8]; exact r2)
  rw [i8] at r1
  have e6 : 14 * (2 * g) + 4 + 2 = 28 * g + 6 := by omega
  rw [e6] at r1
  obtain ⟨s₀, r0, q0⟩ := LinkJoin.back_readsL_of ownNext_trans k1_ownNext quietLayers_ownNext hS hR O
    hg r1
  exact ⟨s₀, r0, ownNext_trans _ _ _ q0 (ownNext_trans _ _ _ q1 q2)⟩

end

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

/-- **AT EVERY STATE REACHED IN FRONT OF A FEED-FORWARD SEGMENT's BATCHING THE FIRST SLOT OF THE LOOKUP ON THE DIGITS IS
THE SLOT BEHIND THE MERGE's**, for whatever the state holds as K4's own. No mark; no walk. -/
theorem seam_reached (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {pD : Look.P}
    (hD : Look.placeAt (P5J.At.X Zp) (2 * g) true = some pD) {Q : Type} {start : Q → S} {z : Q} {s' : S}
    (hr : Reach 0 cF.blocksInOrder start (14 * (2 * g) + 9) (z, s')) :
    ∀ o, s'.own? = some o → pD.first = o.wo.sFv + 1 := by
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
  obtain ⟨b8, f8, D8⟩ := P1K8.four_decide LinkJoin.sameOwn_stretch LinkJoin.quietLayers_sameOwn h.scope h.reads O hg 3
    (by omega)
  -- the last step
  obtain ⟨z', tj, s'', b, e, hrj, hb, hy⟩ := OnBytes.Road.K4.reach_pred (k := 14 * (2 * g) + 8) hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain rfl : b8 = b := Option.some.inj (f8.symm.trans hb)
  obtain ⟨Rt, dt, -, g8⟩ := hy
  have d8 := ((Sound.step_ok_iff 0 b8 tj s' Rt dt dt.length).1 g8).2.2.2
  have hown : LinkJoin.SameOwn tj s' := D8 tj _ _ s' d8
  obtain ⟨G, hG, hnx⟩ := next_in_front h sD hsD (by omega) (blk := b8) (by
    rw [elD, hdD, hbD]
    exact f8) g8
  -- back over the three members to the border behind K4; there the sealed library has the equation
  obtain ⟨s₅, r5, q⟩ := ownNext_back h.scope h.reads O hg (z := z) (s' := tj) (by
    rw [show 28 * g + 8 = 14 * (2 * g) + 8 by omega]
    exact hrj)
  obtain ⟨o₅, G₅, ho₅, hG₅, e₅⟩ := OnBytes.Road.K4.mergeBelow_made h.scope h.reads O h.laid.planOk hg r5
  intro o ho
  have e1 : tj.own? = some o := hown.symm.trans ho
  have e2 : s₅.own? = some o := q.1.symm.trans e1
  obtain rfl : o₅ = o := Option.some.inj (ho₅.symm.trans e2)
  have k := q.2
  rw [hG, hG₅, Option.map_some, Option.map_some] at k
  rw [← hnx, Option.some.inj k]
  exact e₅.symm

/-- **The premise hseam of `batFrontLay_handed_nums`, at the states that the frame's field hands.** -/
theorem seam_handed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {pD : Look.P}
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
    ∀ (a₀ : LayOwn) (o : Layer.Own), s'.here = .lay a₀ → a₀.own = some o → pD.first ≤ o.wo.sFv + 1 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b8, f8, -⟩ := P1K8.four_decide LinkJoin.sameOwn_stretch LinkJoin.quietLayers_sameOwn h.scope h.reads O hg 3
    (by omega)
  obtain ⟨tj, tk, Rt, dt, q₂, q₃, e₂, e₃, -, -, -, -, -, hrk, hf8⟩ :=
    P1K8.mid_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 14 * (2 * g) + 8) f8 ms hall hfit (by omega) hpos L hft hm ha
      hn hq hz hv
  rw [hA] at hf8
  obtain rfl : s' = tk := P1K8.fold_window_end hf8
  intro a₀ o ha₀ hoa
  exact Nat.le_of_eq (seam_reached h hg hD hrk o (by
    unfold S.own?
    rw [ha₀]
    exact hoa))

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.OwnNext
#print axioms ProofFile.Honest.K9.ownNext_trans
#print axioms ProofFile.Honest.K9.k1_ownNext
#print axioms ProofFile.Honest.K9.k8_ownNext
#print axioms ProofFile.Honest.K9.quietLayers_ownNext
#print axioms ProofFile.Honest.K9.ownNext_back
#print axioms ProofFile.Honest.K9.seam_reached
#print axioms ProofFile.Honest.K9.seam_handed
