-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PlacesIn.lean: kind K5: the record PlacesIn
(Johnson/Desc/First/Att/Claims/AgreeAll.lean), paid at a record of the kind's own.

Main names:
  `lens_at`: the lengths that tablesP stores for the 21 tables are lenOf S T
    (Johnson/Desc/First/Att/Claims/PlacesNum.lean): out of tables_are
    (Johnson/Desc/First/Att/Claims/TablesSpec.lean).
  `places_in`: PlacesIn (oldOf S gL i), from shapeHid's yes, i.g = geoOf S, the return of tablesP,
    PosG and "there are just two units".
Limit: PosG is a plan fact that no test of the verifier asks
(Johnson/Desc/First/Att/Claims/PlanLaw.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PlacesNum
import Johnson.Desc.First.Att.Claims.AgreeAll
import Johnson.Desc.First.Att.Claims.SayAt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ScoreP LookIn geoOf)
open Cb.Pv.Att.End (AttTab)

variable {tl : HTailF2} {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In}

/-- **The lengths that tablesP stores for the 21 tables.** -/
theorem lens_at {nW : ℕ} {lk : LookIn} (hg : i.g = geoOf S)
    (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t) (hp : PosG i.g) {k1 k2 : ScoreP}
    (hs : i.p.scores.toList = [k1, k2]) (T : AttTab) :
    ((oldOf S gL i).t.tabLen.lookup (tabOfAtt (oldOf S gL i) T)).getD 0 = lenOf S T := by
  obtain ⟨n, R⟩ := tables_are ht hp
  rw [hg] at R
  have F := R.score
  rw [hs] at F
  obtain ⟨y0, l1, a0, F1, e0⟩ := List.forall₂_cons_left_iff.1 F
  obtain ⟨y1, l2, a1, F2, e1⟩ := List.forall₂_cons_left_iff.1 F1
  have e2 := List.forall₂_nil_left_iff.1 F2
  subst e2 e1
  have g0 : (oldOf S gL i).t.score.getD 0 default = tbBack y0 := by
    rw [Array.getD_eq_getD_getElem?, old_score, ← Array.getElem?_toList, e0]; rfl
  have g1 : (oldOf S gL i).t.score.getD 1 default = tbBack y1 := by
    rw [Array.getD_eq_getD_getElem?, old_score, ← Array.getElem?_toList, e0]; rfl
  have tab : ∀ {a mat len e : ℕ} {phi : Array E}, Tab (stOf i.t n) a mat len phi e →
      ((oldOf S gL i).t.tabLen.lookup a).getD 0 = e := by
    intro a mat len e phi Q
    show (i.t.tabLen.lookup a).getD 0 = e
    have hz : i.t.tabLen.lookup a = some e := Q.size
    rw [hz]; rfl
  have asT : ∀ {a : ℕ} {phi : Array E}, AsTabS (stOf i.t n) (geoOf S) a phi →
      ((oldOf S gL i).t.tabLen.lookup a).getD 0 = S.cf.NAs * (S.kAs / S.cf.NAs) := by
    intro a phi Q
    show (i.t.tabLen.lookup a).getD 0 = _
    have hz : i.t.tabLen.lookup a = some _ := Q.size
    rw [hz]; rfl
  have lng : ∀ {a mat e : ℕ} {zc tokv : Array E}, QLong (geoOf S) (matsOf tl.mats) mat zc tokv e a (stOf i.t n) →
      ((oldOf S gL i).t.tabLen.lookup a).getD 0 = e := by
    intro a mat e zc tokv ⟨c, _, Q, _⟩
    exact tab Q
  cases T with
  | tA => exact asT R.tA.1
  | tVM => exact asT R.tVM.1
  | tVD => exact asT R.tVD.1
  | tMm => show ((oldOf S gL i).t.tabLen.lookup ((oldOf S gL i).t.score.getD 0 default).tM).getD 0 = _
           rw [g0]; exact tab a0.1.1
  | tQm => show ((oldOf S gL i).t.tabLen.lookup ((oldOf S gL i).t.score.getD 0 default).tQ).getD 0 = _
           rw [g0]; exact lng a0.2.1
  | tKm => show ((oldOf S gL i).t.tabLen.lookup ((oldOf S gL i).t.score.getD 0 default).tK).getD 0 = _
           rw [g0]; exact lng a0.2.2
  | tMd => show ((oldOf S gL i).t.tabLen.lookup ((oldOf S gL i).t.score.getD 1 default).tM).getD 0 = _
           rw [g1]; exact tab a1.1.1
  | tQd => show ((oldOf S gL i).t.tabLen.lookup ((oldOf S gL i).t.score.getD 1 default).tQ).getD 0 = _
           rw [g1]; exact lng a1.2.1
  | tKd => show ((oldOf S gL i).t.tabLen.lookup ((oldOf S gL i).t.score.getD 1 default).tK).getD 0 = _
           rw [g1]; exact lng a1.2.2
  | hW => exact tab R.hW.1
  | hX => exact tab R.hX.1
  | hE => exact tab R.hE.1
  | hT => exact tab R.hT.1
  | hPi => exact tab R.hPi.1
  | hR2 => exact tab R.hR2.1
  | tO => exact lng R.tO
  | qO => exact lng R.qO
  | qVM => exact lng R.qVM
  | qVD => exact lng R.qVD
  | qF => exact lng R.qF
  | qKx => exact lng R.qKx

/-- **PlacesIn, paid**: every listed name's place lies in its table. -/
theorem places_in {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (hid : shapeHid lid cf = Except.ok (S, fs)) {nW : ℕ} {lk : LookIn} (hg : i.g = geoOf S)
    (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t) (hp : PosG i.g) {k1 k2 : ScoreP}
    (hs : i.p.scores.toList = [k1, k2]) : PlacesIn (oldOf S gL i) := by
  intro T r hr
  rw [lens_at (gL := gL) hg ht hp hs T]
  have hp' := hp
  rw [hg] at hp'
  have hN : 0 < S.cf.NAs := hp'.nas
  have hw : 0 < cf.wcH := by
    rcases Nat.eq_zero_or_pos cf.wcH with h0 | h0
    · have hf : 0 < S.fillH := hp'.fillH
      rw [(fills_of_hid hid).fillH, h0] at hf
      unfold roundUp at hf
      simp at hf
    · exact h0
  exact place_lt_len hid hN hw T r hr

end K5Law
