-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/EndsAll.lean: kind K5: the twins, gathered: what the claims say
(Johnson/Desc/First/Att/Claims/Say.lean, Johnson/Desc/First/Att/Claims/Say58.lean) gives, for all
pairs, layers and bits at once: the hidden values under the end values' slots are the library's maps
on the cells. It is the twin of the gatherings in Johnson/Road/Rows/AttEndsAll.lean and
AttEndsAt58.lean, whose "…Given" records hold runs of routines in a context: here Say5 … Say8 and
UnitAt stand in their place. The public records of Johnson/Road/Rows are used as they stand
(ProductPub, BelowPub, OnPub, IndexPub, BitsPub, ScorePub: lengths; points tied coordinate by
coordinate; tables in the list; "piece b is pair b"). They are premises here: that they hold of what
pointsOf and tablesP make is not shown in this file or in what it imports.

Main names:
  `InTail h`, `InUnit h k tb`: what those proofs took from the runs' return: the indices read lie in
    the tables; the heads' features are lawful. On public numbers and lengths.
    Johnson/Desc/First/Att/Claims/InRunAll.lean pays both.
  `ends8_all`, `ends11_all`, `ends12_all`: EndsAt … scE .s8, vpm .s11, vpd .s12. `index_all`: the
    row maxima's rvM6, the queries of .s16, rvKC, rvIBP, the bits' two.
  `unit_fd_all`, `unit_fm_all`: EndsAt … k.sc .s6d, .s6b.
What these reach, and what not: as the head of Johnson/Desc/First/Att/Claims/EndsQ.lean says.
Used: what the seven files of twins name, and EndsAt, PiecesAll, pair_of_piece, the six public
records.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEndsAll
import Johnson.Road.Rows.AttEndsAt58
import Johnson.Desc.First.Att.Claims.EndsH
import Johnson.Desc.First.Att.Claims.EndsVB
import Johnson.Desc.First.Att.Claims.EndsU

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Cb.Pv.Att
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Calls Pub Aext Bext rvM6 rvKC rvIBP)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf}
  {h : Attention.Heard} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls} {p : Pub Kf}

/-- What the proofs of Johnson/Road/Rows took from the runs' return, behind the units. -/
structure InTail (h : Attention.Heard) : Prop where
  hE : ∀ b < h.S.NP, ∀ w : PW, h.d.pwW[b]? = some w → ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4,
    h.S.oZr + (l * h.S.Lam + w.lam) * h.S.cf.H + (g * h.S.HA + w.a) < (h.t.tabLen.lookup h.t.hE).getD 0
  qO : ∀ b < h.S.NP, ∀ w : PW, h.d.pwW[b]? = some w → InLong h h.t.qO h.S.atO w.lam (fun g => g * h.S.HA + w.a) h.d.zcW
  tVM : ∀ b < h.S.NP, ∀ w : PW, h.d.pwW[b]? = some w → ∀ x, x = 3 ∨ x = 4 →
    ∀ hi < (eqTab (h.t.ptM.extract 0 ((if false then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
      Rows.planeFirst h.S x w.lam w.a false >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup h.t.tVM).getD 0
  qVM : ∀ b < h.S.NP, ∀ w : PW, h.d.pwW[b]? = some w → InLong h h.t.qVM h.S.atV w.lam (fun g => g) h.d.zcW
  tVD : ∀ b < h.S.NP, ∀ w : PW, h.d.pwW[b]? = some w → ∀ x, x = 3 ∨ x = 4 →
    ∀ hi < (eqTab (h.t.ptD.extract 0 ((if true then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
      Rows.planeFirst h.S x w.lam w.a true >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup h.t.tVD).getD 0
  qVD : ∀ b < h.S.NP, ∀ w : PW, h.d.pwW[b]? = some w → InLong h h.t.qVD h.S.atV w.lam (fun g => g) h.d.zcW
  hT : ∀ b < h.S.NP, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 4, h.S.oMr + (l * h.S.Lam + b / h.S.HA) * h.S.cf.H +
    (g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hT).getD 0
  qF : ∀ b < h.S.NP, InLong h h.t.qF h.S.atQ (b / h.S.HA) (fun g => g * h.S.HA + b % h.S.HA) (h.x.rc h.S)
  qKx : ∀ lam < h.S.Lam, InLong h h.t.qKx h.S.atK lam (fun g => g) (h.x.rc h.S)
  hPi : ∀ b < h.S.NP, ∀ k < h.S.cf.lt, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1,
    h.S.oIb + (l * h.S.Lam + b / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
      (k * h.S.cf.H + g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hPi).getD 0
  hR2 : ∀ b < h.S.NP, ∀ k < h.S.cf.lt, ∀ g < 2 ^ h.S.cf.lgk, ∀ l < 1,
    h.S.oIb + (l * h.S.Lam + b / h.S.HA) * (h.S.cf.lt * h.S.cf.H) +
      (k * h.S.cf.H + g * h.S.HA + b % h.S.HA) < (h.t.tabLen.lookup h.t.hR2).getD 0

/-- The same at a softmax-table unit. -/
structure InUnit (h : Attention.Heard) (k : Score) (tb : ScoreTables) : Prop where
  tQ : ∀ (b : ℕ) (w : PW), k.pw[b]? = some w →
    InLong h tb.tQ h.S.atQ w.lam (fun g => g * h.S.HA + w.a) (lastCoords k.sc.r h.S.cf.ldh)
  tK : ∀ (b : ℕ) (w : PW), k.pw[b]? = some w → InLong h tb.tK h.S.atK w.lam (fun g => g) (lastCoords k.sc.r h.S.cf.ldh)

theorem getD_of {α : Type} [Inhabited α] {v : Array α} {b : ℕ} {w : α} (hw : v[b]? = some w) :
    v.getD b default = w := by
  rw [Array.getD_eq_getD_getElem?, hw]
  rfl

/-- **The division.** -/
theorem ends8_all (A : AttAt ρ W tl K3 M h lid cf fs) (pE : ProductPub ρ tl h C p) (I : InTail h)
    (s5 : Say5 ρ W h K3) : EndsAt ρ W h M C p h.d.scE .s8 := by
  intro b hb
  obtain ⟨w, hw, ha, eb⟩ := pair_of_piece pE.pairs hb
  have hg := getD_of hw
  have a := s5.ends (2 * b) (by omega)
  have c := s5.ends (2 * b + 1) (by omega)
  unfold endsE at a c
  rw [if_pos (by omega), show 2 * b / 2 = b by omega, hg] at a
  rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hg] at c
  have x := product_ends A C p pE.r pE.zc ha pE.vn pE.hE pE.qO (I.hE b hb w hw) (I.qO b hb w hw) a c
  rw [eb] at x
  exact x

/-- **The value product below the diagonal.** -/
theorem ends11_all (A : AttAt ρ W tl K3 M h lid cf fs) (pE : ProductPub ρ tl h C p)
    (pV : BelowPub ρ tl h C p) (I : InTail h) (s6 : Say6 ρ W h K3) :
    EndsAt ρ W h M C p h.d.vpm .s11 := by
  intro b hb
  obtain ⟨w, hw, ha, eb⟩ := pair_of_piece pE.pairs hb
  have hg := getD_of hw
  have a := s6.below.ends (2 * b) (by omega)
  have c := s6.below.ends (2 * b + 1) (by omega)
  unfold endsV at a c
  rw [if_pos (by omega), show 2 * b / 2 = b by omega, hg] at a
  rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hg] at c
  have x := value_below A C p pV.r pV.zi pE.zc ha pV.ptM pV.wJv pV.vi pE.vn pV.gam pV.tVM pV.qVM
    (I.tVM b hb w hw) (I.qVM b hb w hw) a c
  rw [eb] at x
  exact x

/-- **The value product on the diagonal tiles.** -/
theorem ends12_all (A : AttAt ρ W tl K3 M h lid cf fs) (pE : ProductPub ρ tl h C p)
    (pV : BelowPub ρ tl h C p) (pO : OnPub tl h) (I : InTail h) (s6 : Say6 ρ W h K3) :
    EndsAt ρ W h M C p h.d.vpd .s12 := by
  intro b hb
  obtain ⟨w, hw, ha, eb⟩ := pair_of_piece pE.pairs hb
  have hg := getD_of hw
  have a := s6.on.ends (2 * b) (by omega)
  have c := s6.on.ends (2 * b + 1) (by omega)
  unfold endsV at a c
  rw [if_pos (by omega), show 2 * b / 2 = b by omega, hg] at a
  rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hg] at c
  have x1 := value_on_A A C p pO.r pV.zi ha pO.ptD pV.vi pO.tVD (I.tVD b hb w hw) a
  have x2 := value_on_B A C p pO.r pE.zc ha pE.vn pV.gam pO.qVD (I.qVD b hb w hw).feat (I.qVD b hb w hw).inn c
  rw [eb] at x1 x2
  exact ⟨x1, x2⟩

/-- **Claim 7's four, and claim 8's two.** -/
theorem index_all (A : AttAt ρ W tl K3 M h lid cf fs) (pI : IndexPub ρ tl h p) (pB : BitsPub tl h)
    (I : InTail h) (s7 : Say7 ρ W h K3) (s8 : Say8 ρ W h K3) :
    (∀ b < h.S.NP, W.slot (h.x.sM6 + b) = rvM6 (L5.dimOf h.S) p (cellsK h.S M) b) ∧
    (∀ b < h.S.NP, W.slot (h.x.scF.sEnd + 2 * b) =
      Aext (L5.dimOf h.S) C p (cellsK h.S M) .s16 b (pt ρ h.x.scF.r)) ∧
    (∀ lam < h.S.Lam, W.slot (h.x.sKC + lam) =
      rvKC (L5.dimOf h.S) p (cellsK h.S M) (pt ρ h.x.scd.r) lam) ∧
    (∀ b < h.S.NP, ∀ k < h.S.cf.lt, W.slot (h.x.sIb h.S b k) =
      rvIBP (L5.dimOf h.S) (cellsK h.S M) (pt ρ h.x.scd.r) b k) ∧
    (∀ b < h.S.NP, W.slot (h.x.scH.sEnd + 2 * b) =
        Blocks.ext ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4)
          (bitCube 4 (L5.dimOf h.S) (cellsK h.S M) b) (pt ρ h.x.scH.r) ∧
      W.slot (h.x.scH.sEnd + (2 * b + 1)) =
        Blocks.ext ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4)
          (bitCube 4 (L5.dimOf h.S) (cellsK h.S M) b) (pt ρ h.x.scH.r) - 1) := by
  obtain ⟨k1, k2⟩ := (forall_block h.S.Lam h.S.NP h.S.cf.lt
    (fun j => W.slot (h.x.scd.sEnd + j) = (endsK h K3 j).value ρ W)).2 s7.endsK
  refine ⟨fun b hb => ?_, fun b hb => ?_, fun lam hl => ?_, fun b hb k hk => ?_, fun b hb => ?_⟩
  · exact score_start A pI.tg pI.ti hb pI.vtg pI.vti pI.hT (I.hT b hb) (s7.maxima b hb)
  · exact score_query A C p pI.rF pI.qF (I.qF b hb).feat (I.qF b hb).inn (s7.endsF b hb)
  · have e := k1 lam hl
    rw [endsK_lam h K3 hl] at e
    exact key_keys A p pI.rF pI.rD pI.vfn pI.qKx (I.qKx lam hl).feat (I.qKx lam hl).inn e
  · have e := k2 b hb k hk
    rw [endsK_bit h K3 b hk] at e
    exact key_bits A pI.rD hb pI.hPi (I.hPi b hb k hk) e
  · exact bits_ends A pB.r hb pB.hR2 (I.hR2 b hb) s8

/-- **A softmax-table unit on the diagonal.** -/
theorem unit_fd_all (A : AttAt ρ W tl K3 M h lid cf fs) {k : Score} {tb : ScoreTables} {pc : PlaneClaim}
    (P : ScorePub ρ tl h C p .fd k tb) (I : InUnit h k tb) (U : UnitAt ρ W h K3 k tb pc) :
    EndsAt ρ W h M C p k.sc .s6d := by
  intro b hb
  obtain ⟨w, hw, ha, eb⟩ := pair_of_piece P.pairs hb
  have hg := getD_of hw
  have hs : k.pw.size = h.S.NP := P.pairs.1
  have a := U.ends (2 * b) (by omega)
  have c := U.ends (2 * b + 1) (by omega)
  unfold endsU at a c
  rw [if_pos (by omega), show 2 * b / 2 = b by omega, hg] at a
  rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hg] at c
  have x := score_fd A C p P.isSeg P.r P.zi P.zj ha P.vi P.vj P.tQ P.tK (I.tQ b w hw) (I.tK b w hw) a c
  rw [eb] at x
  exact x

/-- **A softmax-table unit below the diagonal.** -/
theorem unit_fm_all (A : AttAt ρ W tl K3 M h lid cf fs) {k : Score} {tb : ScoreTables} {pc : PlaneClaim}
    (P : ScorePub ρ tl h C p .fm k tb) (I : InUnit h k tb) (U : UnitAt ρ W h K3 k tb pc) :
    EndsAt ρ W h M C p k.sc .s6b := by
  intro b hb
  obtain ⟨w, hw, ha, eb⟩ := pair_of_piece P.pairs hb
  have hg := getD_of hw
  have hs : k.pw.size = h.S.NP := P.pairs.1
  have a := U.ends (2 * b) (by omega)
  have c := U.ends (2 * b + 1) (by omega)
  unfold endsU at a c
  rw [if_pos (by omega), show 2 * b / 2 = b by omega, hg] at a
  rw [if_neg (by omega), show (2 * b + 1) / 2 = b by omega, hg] at c
  have x := score_fm A C p P.isSeg P.r P.zi P.zj ha P.vi P.vj P.tQ P.tK (I.tQ b w hw) (I.tK b w hw) a c
  rw [eb] at x
  exact x

end K5Law
