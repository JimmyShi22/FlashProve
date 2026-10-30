-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormHear.lean.
WHAT IT DOES NOT SHOW. That the reads are true, that the 26 forms are 0, that no bad element was
drawn: premises still. Nothing on probabilities.
WHAT IT IS. Norm.lean's WHOLE HEARING, TAKEN APART AT THE HEAD's ONE NORM. norm_parts: where
Norm.hear returns, its rounds fall into five stretches: the point pV; the nine sums and gam; the
squares' level; the seven products and om; the products' sumcheck: each heard by its own part at the
ledger in front of it, leaving no round.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormRows
import Johnson.Desc.Kinds.Law.Consumes
import Johnson.Desc.Kinds.Law.FilledG
import Johnson.Desc.Kinds.Law.KeepsHear

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Reading World Fork)
open OnBytes.PscRun (Later)
open Norm (lt ls d lPd T S2)
open Came (val sEndG sEndL round_some consumes_drawPoint consumes_sendThenBatch consumes_level
  consumes_sumcheck wl_sendThenBatch wl_level)

variable [Sizes] [Policy] [Request] [Token]

/-- **Where the norm's whole hearing returns.** -/
theorem norm_parts {F G : Fork} {rs left : List Fmt.RoundView} {H : Norm.Heard} (hW : WellLaid F)
    (h : Norm.hear F rs = some (H, G, left)) :
    ∃ (p0 p1 tS p2 tP : List Fmt.RoundView) (Fa Fb Fc : Fork),
      rs = p0 ++ (p1 ++ (tS ++ (p2 ++ (tP ++ left)))) ∧
      drawPoint lt F p0 = some (H.pV, F, []) ∧
      sendThenBatch 9 9 F p1 = some ((H.W, H.gam), Fa, []) ∧ H.rhoI = #[] ∧
      level (zS H.pV) (Norm.squaresStart H.W H.gam #[]) Fa tS = some (H.squares, Fb, []) ∧
      sendThenBatch 7 7 Fb p2 = some ((H.P, H.om), Fc, []) ∧
      sumcheck H.pV 4 Fc tP = some (H.products, G, []) ∧
      WellLaid Fa ∧ WellLaid Fb ∧ WellLaid Fc := by
  unfold Norm.hear at h
  obtain ⟨pV, F1, l1, h0, k0⟩ := bind_some h
  unfold Norm.hearRest at k0
  obtain ⟨Wg, Fa, l2, h1, k1⟩ := bind_some k0
  obtain ⟨W, gam⟩ := Wg
  dsimp only at k1
  obtain ⟨rhoI, Fa', l2', h2, k2⟩ := bind_some k1
  obtain ⟨rfl, rfl, rfl⟩ := pure_some h2
  obtain ⟨sq, Fb, l3, h3, k3⟩ := bind_some k2
  obtain ⟨Po, Fc, l4, h4, k4⟩ := bind_some k3
  obtain ⟨P, om⟩ := Po
  dsimp only at k4
  obtain ⟨pr, G', l5, h5, k5⟩ := bind_some k4
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k5
  -- the point's round lays nothing
  have hF1 : F = F1 := by
    unfold Norm.hearPoint drawPoint at h0
    obtain ⟨x, Fx, lx, a, b⟩ := bind_some h0
    obtain ⟨_, e, _⟩ := pure_some b
    rw [← e]
    exact round_some a
  subst hF1
  obtain ⟨p0, e0, c0⟩ := consumes_drawPoint _ _ _ _ _ _ h0
  obtain ⟨p1, e1, c1⟩ := consumes_sendThenBatch _ _ _ _ _ _ _ h1
  obtain ⟨tS, e3, c3⟩ := consumes_level _ _ _ _ _ _ _ h3
  obtain ⟨p2, e4, c4⟩ := consumes_sendThenBatch _ _ _ _ _ _ _ h4
  obtain ⟨tP, e5, c5⟩ := consumes_sumcheck _ _ _ _ _ _ _ h5
  have Wa : WellLaid Fa := wl_sendThenBatch _ _ _ _ _ _ _ hW h1
  have Wb : WellLaid Fb := wl_level _ _ _ _ _ _ _ Wa h3
  have Wc : WellLaid Fc := wl_sendThenBatch _ _ _ _ _ _ _ Wb h4
  refine ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, ?_, ?_, ?_, rfl, ?_, ?_, ?_, Wa, Wb, Wc⟩
  · rw [e0, e1, e3, e4, e5]
  · have := c0 []
    rwa [List.append_nil] at this
  · have := c1 []
    rwa [List.append_nil] at this
  · have := c3 []
    rwa [List.append_nil] at this
  · have := c4 []
    rwa [List.append_nil] at this
  · have := c5 []
    rwa [List.append_nil] at this

/-! ## What a batching round lays -/

open OnBytes (zeroE oneE subE)
open OnBytes.PscRun (Sized hideRun_ok)
open Part.MaskedSum (Var Sent readAll rowLaid)
open Came (vsG kG ownG allG_d heardBy_cut lead0_of_sent)

/-- A round that sends n hidden scalars and draws one element: the scalars lie under the next n
numbers, which are filled behind it; the ledger's next number has gone up by n. -/
theorem batch_spec {n rows : Nat} {F Fa : Fork} {p : List Fmt.RoundView} {A : Array Hid} {g : E}
    (hW : WellLaid F) (h : sendThenBatch n rows F p = some ((A, g), Fa, [])) :
    (∀ j, j < n → (A.getD j {}).var = Aff.slot (F.next + j)) ∧
      (∀ j, j < n → OnBytes.PscRun.Filled Fa (F.next + j)) ∧ Fa.next = F.next + n := by
  unfold sendThenBatch at h
  obtain ⟨vg, F1, l1, h1, k1⟩ := bind_some h
  obtain ⟨v, gs⟩ := vg
  dsimp only at k1
  obtain ⟨A', F2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨g', F3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, rfl⟩ := need_some h3
  obtain ⟨e, rfl, rfl⟩ := pure_some k3
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hF : F = F1 := round_some h1
  subst hF
  have hlen : v.length = n := by
    unfold Hear.round at h1
    cases p with
    | nil => cases h1
    | cons r tl =>
      dsimp only at h1
      cases hr : Part.MaskedSum.roundOf n 1 r with
      | none => rw [hr] at h1; cases h1
      | some x =>
        rw [hr] at h1
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨s, dd⟩ := x
        have hs := Part.MaskedSum.roundOf_spec hr
        have e1 : s = v := by
          have := h1.1
          simp only [Prod.mk.injEq] at this
          exact this.1
        rw [← e1]
        exact hs.2.1
  obtain ⟨_, h2'⟩ := hide_some h2
  obtain ⟨run, hA⟩ := hide_unfold h2'
  obtain ⟨_, _, f1, _⟩ := hideRun_ok { F with next := F.next + v.length } F2 _ _ _ (sized_of hW) run
  obtain ⟨_, _, nx, _, _⟩ := hideRun_frame (F := { F with next := F.next + v.length }) hW run
  refine ⟨fun j hj => ?_, fun j hj => ?_, ?_⟩
  · rw [hA]
    simp [Array.getD, hlen, hj]
  · exact (f1 j (by rw [List.size_toArray, hlen]; exact hj)).2.2.1
  · rw [nx, hlen]

/-! ## What a level lays -/

/-- A return of "level z start" is two runs of layings, and the start form has a public part at the
ledger in front. -/
theorem level_runs (z : Point) (start : Form) {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hWL : WellLaid F0) (hlev : level z start F0 t = some (S, F1, [])) :
    ∃ (beta Tt : E) (vals : Array E) (G : Fork) (n2 : Nat), vals.size = 2 ∧
      F0.publicPart start = some Tt ∧
      ({ F0 with next := n2 } : Fork).hideRun (F0.next + ownG z 2) vals beta = some G ∧
      G.hideRun F0.next (Array.replicate (ownG z 2) zeroE) (subE zeroE oneE) = some F1 := by
  unfold level at hlev
  obtain ⟨cs, G1, l1, h1, k1⟩ := bind_some hlev
  obtain ⟨c, s⟩ := cs
  dsimp only at k1
  obtain ⟨ag, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨a, g⟩ := ag
  dsimp only at k2
  obtain ⟨dn, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, rfl, rfl⟩ := need_some h3
  obtain ⟨rfl, rfl, rfl⟩ := pure_some k3
  have hG : G1 = G2 := round_some h2
  subst hG
  obtain ⟨e1, _, _⟩ := heardBy_cut h1
  obtain ⟨ld, Fa, G, hd, es, a1, a2, a3, a4, a5, a6, hs⟩ := heardBy_spec e1
  have hk : callOf 0 z 2 = ⟨0, vsG z, some ⟨2, 2⟩⟩ := rfl
  rw [hk] at a2 a4 hs
  obtain ⟨_, Tt, R, hpub, hread, hhd, hrun2⟩ := Part.MaskedSum.hear_spec a4
  obtain ⟨r0, used, rv, front, ht, hs0, hfl, hvr, hsv⟩ := Part.MaskedSum.readAll_spec hread
  have hfr : front = [] := List.length_eq_zero_iff.mp hfl
  subst hfr
  have hs0' : Sent r0 1 1 [R.mu] [R.eps] := hs0
  have hld : ld = [] := by
    rw [ht, lead0_of_sent hs0'] at a2
    exact (Option.some.inj a2).symm
  subst hld
  obtain ⟨run1, _⟩ := hide_unfold a3
  have hFa : Fa = F0 := by
    have h0 : ({ F0 with next := F0.next + ([] : List E).length } : Fork).hideRun F0.next
        ([] : List E).toArray oneE = some F0 := by
      simp [Fork.hideRun]
    rw [h0] at run1
    exact (Option.some.inj run1).symm
  subst hFa
  have hlenR : R.rounds.length = (kG z 2).all.length := hvr.length.2
  have hlen : (Part.MaskedSum.hidingAt ((kG z 2).all.zip (R.rounds.map (·.2)))).1.length
      = ownG z 2 := by
    have hz : ((kG z 2).all.zip (R.rounds.map (·.2))).map (·.1) = (kG z 2).all :=
      List.map_fst_zip (by rw [List.length_map, hlenR])
    rw [hidingAt_length _ ?_ ?_, hz]
    · rfl
    · intro e
      have := congrArg (List.map (·.1)) e
      rw [hz] at this
      exact absurd this (by show vsG z ++ [Var.point zeroE 3] ≠ []; simp)
    · intro x hx
      have : x.1 ∈ (kG z 2).all := by rw [← hz]; exact List.mem_map_of_mem hx
      rw [allG_d z 2 _ this]; omega
  have run3 : G.hideRun Fa.next (Array.replicate (ownG z 2) zeroE) (subE zeroE oneE) = some G1 := by
    have h5 := a5
    unfold rowLaid at h5
    rw [hhd] at h5
    dsimp only at h5
    have hlen' : (Part.MaskedSum.hidingAt ((⟨0, vsG z, some ⟨2, 2⟩⟩ : Part.MaskedSum.Call).all.zip
        (R.rounds.map (·.2)))).1.length = ownG z 2 := hlen
    rw [hlen'] at h5
    exact h5
  exact ⟨_, Tt, R.values.toArray, G, _, by rw [List.size_toArray]; exact hsv.2.1, hpub, hrun2,
    run3⟩

/-- **Behind a level every number that it lays is filled.** -/
theorem filled_rangeL (z : Point) (start : Form) {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hWL : WellLaid F0) (hlev : level z start F0 t = some (S, F1, [])) :
    ∀ j, F0.next ≤ j → j < sEndL z F0 + 2 → OnBytes.PscRun.Filled F1 j := by
  obtain ⟨beta, Tt, vals, G, n2, hv, _, r2, r3⟩ := level_runs z start hWL hlev
  obtain ⟨_, sG, fG1, _⟩ := hideRun_ok { F0 with next := n2 } G _ _ _ (sized_of hWL) r2
  obtain ⟨_, _, f31, o3⟩ := hideRun_ok G F1 _ _ _ sG r3
  have s3 : (Array.replicate (ownG z 2) zeroE).size = ownG z 2 := Array.size_replicate
  intro j h1 h2
  unfold sEndL at h2
  by_cases c2 : j < F0.next + ownG z 2
  · have a := (f31 (j - F0.next) (by rw [s3]; omega)).2.2.1
    have e : F0.next + (j - F0.next) = j := by omega
    rwa [e] at a
  · have a := (fG1 (j - (F0.next + ownG z 2)) (by omega)).2.2.1
    have e : F0.next + ownG z 2 + (j - (F0.next + ownG z 2)) = j := by omega
    rw [e] at a
    exact ((o3 j (Or.inr (by rw [s3]; omega))).2.2).mpr a

/-! ## The bridge's two bad events read few numbers -/

theorem badG_congr (c : NCells) (u : Nat → K) (Wt Wt' : Nat → K) (g : K)
    (h : ∀ s, s < 9 → Wt s = Wt' s) (hb : (dataOf c).BadG u Wt g) : (dataOf c).BadG u Wt' g := by
  have e : ∀ s, s < 9 → (dataOf c).dW u Wt 0 s = (dataOf c).dW u Wt' 0 s := fun s hs => by
    unfold D6.Bridge.Data.dW
    rw [Nat.mul_zero, Nat.zero_add, h s hs]
  obtain ⟨⟨i, hi, s, hs, hne⟩, hall⟩ := hb
  have hi' : i < 1 := hi
  obtain rfl : i = 0 := by omega
  refine ⟨⟨0, hi, s, hs, by rw [← e s hs]; exact hne⟩, fun i hi2 => ?_⟩
  have hi3 : i < 1 := hi2
  obtain rfl : i = 0 := by omega
  have h0 := hall 0 hi2
  unfold D6.Bridge.Data.dWg at h0 ⊢
  rw [← h0]
  exact Finset.sum_congr rfl fun s hs => by rw [e s (Finset.mem_range.mp hs)]

theorem badO_congr (c : NCells) (u : Nat → K) (Pt Pt' : Nat → K) (o : K)
    (h : ∀ n, n < 7 → Pt n = Pt' n) (hb : (dataOf c).BadO u Pt o) : (dataOf c).BadO u Pt' o := by
  have e : ∀ m, m < 7 → (dataOf c).dP u Pt m = (dataOf c).dP u Pt' m := fun m hm => by
    unfold D6.Bridge.Data.dP
    rw [h m hm]
  obtain ⟨⟨m, hm, hne⟩, hs⟩ := hb
  have hm' : m < 7 := hm
  refine ⟨⟨m, hm, by rw [← e m hm']; exact hne⟩, ?_⟩
  have h0 : (Finset.range 7).sum (fun m => o ^ m * (dataOf c).dP u Pt m) = 0 := hs
  show (Finset.range 7).sum (fun m => o ^ m * (dataOf c).dP u Pt' m) = 0
  rw [← h0]
  exact Finset.sum_congr rfl fun m hm => by rw [e m (Finset.mem_range.mp hm)]

/-! ## The whole hearing, in a world read off a later ledger -/

theorem drawPoint_size {n : Nat} {F G : Fork} {p left : List Fmt.RoundView} {z : Point}
    (h : drawPoint n F p = some (z, G, left)) : z.size = n := by
  unfold drawPoint at h
  obtain ⟨x, Fx, lx, a, b⟩ := bind_some h
  obtain ⟨e, _, _⟩ := pure_some b
  rw [← e, List.size_toArray]
  unfold Hear.round at a
  cases p with
  | nil => cases a
  | cons r tl =>
    dsimp only at a
    cases hr : Part.MaskedSum.roundOf 0 n r with
    | none => rw [hr] at a; cases a
    | some y =>
      rw [hr] at a
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at a
      obtain ⟨s, dd⟩ := y
      have hs := Part.MaskedSum.roundOf_spec hr
      rw [← a.1]
      show dd.length = n
      rw [hs.2.2.2, List.length_map]
      exact hs.2.2.1

/-- The start form's value at the hidden scalars of the ledger in front of the level. -/
noncomputable def cvAt (mask : Nat → E) (Fa : Fork) (W : Array Hid) (gam : E) : K :=
  val (worldOf Fa mask) (Norm.squaresStart W gam #[])

section Whole
variable [FinalNorm.In] [FinalNorm.Heard] [FinalNorm.Reads]

/-- **K6's JOINT AT THE NORM's WHOLE HEARING.** The cells, the masks and the ledger in front stand
first. Where Norm.hear returns, its rounds fall into the five stretches of norm_parts; in a world
whose slots hold the hidden scalars of ANY LATER LEDGER G', with the three reads true and the 26
forms 0, without a bad draw under the two sumchecks' rules at their own stretches, and with none of
the bridge's three bad events at the hidden sums and products of the ledgers behind their rounds:
the clause rows of CellRelN. -/
theorem norm_whole (c : NCells) (mask : Nat → E) (F : Fork) (hWL : WellLaid F) (hls : ls ≤ lPd)
    (hdS : S2 ∣ d) {rs left : List Fmt.RoundView} {H : Norm.Heard} {G G' : Fork} (W : World K)
    (hcan : Canonical rs) (hhear : Norm.hear F rs = some (H, G, left)) (hL : Later G G')
    (hWs : ∀ j, W.slot j = rd (hidden G' mask j)) :
    ∃ (p0 p1 tS p2 tP : List Fmt.RoundView) (Fa Fb Fc : Fork) (Tt : E),
      rs = p0 ++ (p1 ++ (tS ++ (p2 ++ (tP ++ left)))) ∧
      drawPoint lt F p0 = some (H.pV, F, []) ∧
      sendThenBatch 9 9 F p1 = some ((H.W, H.gam), Fa, []) ∧
      level (zS H.pV) (Norm.squaresStart H.W H.gam #[]) Fa tS = some (H.squares, Fb, []) ∧
      sendThenBatch 7 7 Fb p2 = some ((H.P, H.om), Fc, []) ∧
      sumcheck H.pV 4 Fc tP = some (H.products, G, []) ∧
      Fa.publicPart (Norm.squaresStart H.W H.gam #[]) = some Tt ∧
      (let _ : Norm.Heard := H
       NormReads W c → (∀ f, f ∈ Norm.forms → val W f = 0) →
       NoBad (squaresRule c mask Fa H.pV H.gam Tt (cvAt mask Fa H.W H.gam)) tS →
       NoBad (productsRule c mask Fc H.pV H.om) tP →
       ¬ (dataOf c).BadP (tupK H.pV) →
       ¬ (dataOf c).BadG (Blocks.nat (tupK H.pV)) (fun s => rd (hidden Fa mask (F.next + s)))
         (rd H.gam) →
       ¬ (dataOf c).BadO (Blocks.nat (tupK H.pV)) (fun n => rd (hidden Fc mask (Fb.next + n)))
         (rd H.om) →
       ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0) := by
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, hrs, h0, h1, _, h3, h4, h5, Wa, Wb, Wc⟩ :=
    norm_parts hWL hhear
  obtain ⟨_, Tt, _, _, _, _, hT, _, _⟩ := level_runs _ _ Wa h3
  refine ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, Tt, hrs, h0, h1, h3, h4, h5, hT, ?_⟩
  intro _ hreads hforms hbS hbP hP hG hO
  have hz : H.pV.size = lt := drawPoint_size h0
  -- later ledgers
  have Lab : Later Fa Fb := keeps_level _ _ _ _ _ _ _ h3
  have Lbc : Later Fb Fc := keeps_sendThenBatch _ _ _ _ _ _ _ h4
  have Lcg : Later Fc G := keeps_sumcheck _ _ _ _ _ _ _ h5
  have LbG : Later Fb G' := (Lbc.trans Lcg).trans hL
  obtain ⟨vW9, fW9, _⟩ := batch_spec hWL h1
  obtain ⟨vP7, fP7, _⟩ := batch_spec Wb h4
  -- the hidden sums and products in the world
  have hWt : ∀ s, s < 9 → WtOf W s = rd (hidden Fa mask (F.next + s)) := fun s hs => by
    show val W (H.W.getD s {}).var = _
    rw [vW9 s hs]
    show Aff.value Reading.gl W (Aff.slot _) = _
    rw [Aff.value_slot, hWs, hidden_later mask (Lab.trans LbG) (fW9 s hs)]
  have hPt : ∀ n, n < 7 → PtOf W n = rd (hidden Fc mask (Fb.next + n)) := fun n hn => by
    show val W (H.P.getD n {}).var = _
    rw [vP7 n hn]
    show Aff.value Reading.gl W (Aff.slot _) = _
    rw [Aff.value_slot, hWs, hidden_later mask (Lcg.trans hL) (fP7 n hn)]
  have hWt0 : ∀ s, s < 9 → WtOf (worldOf Fa mask) s = rd (hidden Fa mask (F.next + s)) :=
    fun s hs => by
      show val (worldOf Fa mask) (H.W.getD s {}).var = _
      rw [vW9 s hs]
      show Aff.value Reading.gl (worldOf Fa mask) (Aff.slot _) = _
      rw [Aff.value_slot]
      rfl
  have hC : val W (Norm.squaresStart Norm.W Norm.gam #[]) = cvAt mask Fa H.W H.gam := by
    unfold cvAt
    rw [start_value W]
    have e := start_value (worldOf Fa mask)
    refine Eq.trans ?_ e.symm
    have es : ((Finset.range 9).sum fun s => rd Norm.gam ^ s * WtOf W s) =
        (Finset.range 9).sum fun s => rd Norm.gam ^ s * WtOf (worldOf Fa mask) s :=
      Finset.sum_congr rfl fun s hs => by
        rw [hWt s (Finset.mem_range.mp hs), hWt0 s (Finset.mem_range.mp hs)]
    rw [es]
  -- the stretches are canonical
  have hcS : Canonical tS := fun r hr => hcan r (by
    rw [hrs]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hr)))
  have hcP : Canonical tP := fun r hr => hcan r (by
    rw [hrs]
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_right _ (List.mem_append_left _ hr)))))
  -- the bridge's bad events read the sums below 9 and the products below 7 alone
  have hG' : ¬ (dataOf c).BadG (Blocks.nat (tupK H.pV)) (WtOf W) (rd H.gam) := by
    intro hb
    apply hG
    exact badG_congr c _ _ _ _ hWt hb
  have hO' : ¬ (dataOf c).BadO (Blocks.nat (tupK H.pV)) (PtOf W) (rd H.om) := by
    intro hb
    apply hO
    exact badO_congr c _ _ _ _ hPt hb
  exact norm_rows c mask Fa Fc Tt _ Wa Wc hz hls hdS W
    (fun j a b => by rw [hWs, hidden_later mask LbG (filled_rangeL _ _ Wa h3 j a b)])
    (fun j a b => by rw [hWs]; exact Came.world_laterG _ _ mask Wc h5 hL j a b)
    hcS hcP h3 h5 hT hC hreads hforms hbS hbP hP hG' hO'

end Whole

end VerifiableInference.Desc.Kinds.Head.Law
