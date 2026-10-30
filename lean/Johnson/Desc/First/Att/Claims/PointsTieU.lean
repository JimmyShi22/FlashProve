-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PointsTieU.lean: kind K5: the points of the plane claims and of the
softmax-table units that pointsOf makes ARE the library's, coordinate by coordinate; and the tile
rows' weights are the library's. It goes on from Johnson/Desc/First/Att/Claims/PointsTie.lean (the
two sides as tails of the lookup's point inside a tree) over
Johnson/Desc/First/Att/Claims/PointsCut.lean (what pointsOf lays).

Main names:
  `bitsM`, `bitsD`: the bits of the lists below, on the diagonal are the library's lM, lD.
  `pc_size`, `pc_pt`, `pc_cut`: a plane claim's point has the family's length, is the family's inner
    point, and a cut of it is a stretch of that.
  `TieM`, `tieM_of`: at a unit below the diagonal: zg, zs, zi, zj are the library's zg, zs, zi',
    zj', with their lengths; the tile rows' weights are blkRow at (zP, zs).
  `TieD`, `tieD_of`: at a unit on the diagonal: zg, zi, zj are zgD, zi', zj' (the library cuts the
    last two from the family m1: the two families' inner points are tails of one point); the tile
    rows' weights are the equality weights of zID.
Premises: CallsFit S fs; Look; the claim's call's key point ends in zx (EndsIn); the shape's numbers
are in the library's form (L5.Norm S, Sizes S: norm_of_hid and sizes_of_hid,
Johnson/Road/Rows/AttReadLong.lean, give both of what shapeHid returns).
Used: PointsTie.lean, PointsCut.lean; tiles_row, eqTab_at (Johnson/Road/Rows/AttEnds14Tiles.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttEnds14Tiles
import Johnson.Desc.First.Att.Claims.PointsTie
import Johnson.Desc.First.Att.Claims.PointsCut

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Pts ScoreP RemP UnitG geoOf)
open Inst.Model.AttSeg (Pub Fam inn sh zg zP zs zi' zj' zgD zID blkRow)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {S : Attention.Shape} {fs : Model.Forest.Shape}
  {zx : Array E} {p : Pub Kf} {zk : Array (Array E)}

theorem bitsM (N : L5.Norm S) : (geoOf S).keyBits .rm = (L5.dimOf S).lM := by
  show S.cf.lgk + 2 * S.cf.lt - 1 = S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB
  have := N.lt
  omega

theorem bitsD (N : L5.Norm S) : (geoOf S).keyBits .rd = (L5.dimOf S).lD := by
  show S.cf.lgk + S.cf.lt + S.cf.lB = S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB
  have := N.lt
  omega

/-! ## A plane claim's point -/

section Plane
variable (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) {pc : RemP}
  (H : PlaneCut (geoOf S) zk pc) (hk : EndsIn (zk.getD pc.call #[]) zx) (f : Fam)
  (hb : (geoOf S).keyBits (if pc.isD then .rd else .rm) = f.l (L5.dimOf S))
include hF L H hk hb

theorem pc_size : pc.z.size = f.l (L5.dimOf S) := by
  obtain ⟨u, hu, ez, _⟩ := H
  rw [ez, inner_size hk u (by rw [hu, hb]; exact fam_le hF L f), hu, hb]

theorem pc_pt {j : ℕ} (hj : j < f.l (L5.dimOf S)) :
    pt ρ pc.z j = inn (L5.dimOf S) (L5.callsOf fs) p.z f j := by
  obtain ⟨u, hu, ez, _⟩ := H
  rw [ez]
  exact inner_tie hF L hk u f (hu.trans hb) (by rw [hu, hb]; exact hj)

theorem pc_cut {a b j : ℕ} (hbs : b ≤ f.l (L5.dimOf S)) (hj : a + j < b) :
    pt ρ (pc.z.extract a b) j = inn (L5.dimOf S) (L5.callsOf fs) p.z f (a + j) := by
  obtain ⟨u, hu, ez, _⟩ := H
  rw [ez]
  exact cut_tie hF L hk u f (hu.trans hb) (by rw [hu, hb]; exact hbs) hj

end Plane

/-! ## A unit below the diagonal -/

/-- The points and the tile rows' weights of a unit below the diagonal are the library's. -/
structure TieM (ρ : Reading Kf) (S : Attention.Shape) (fs : Model.Forest.Shape) (k : ScoreP)
    (p : Pub Kf) : Prop where
  sg : k.zg.size = S.cf.lgk
  g : ∀ j < S.cf.lgk, pt ρ k.zg j = zg (L5.dimOf S) (L5.callsOf fs) p.z j
  ss : k.zs.size = S.lnT
  s : ∀ j < S.lnT, pt ρ k.zs j = zs (L5.dimOf S) (L5.callsOf fs) p.z j
  si : k.zi.size = S.cf.lB
  i : ∀ j < S.cf.lB, pt ρ k.zi j = zi' (L5.dimOf S) (L5.callsOf fs) p.z j
  sj : k.zj.size = S.cf.lB
  j : ∀ j < S.cf.lB, pt ρ k.zj j = zj' (L5.dimOf S) (L5.callsOf fs) p.z j
  wI : ∀ I < S.nT, ρ.val (k.wI.getD I zeroE) =
    blkRow (L5.dimOf S) (zP (L5.dimOf S) (L5.callsOf fs) p.z)
      (zs (L5.dimOf S) (L5.callsOf fs) p.z) I

theorem tieM_of (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) (N : L5.Norm S) (Z : Sizes S)
    {k : ScoreP} {pc : RemP} (H : PlaneCut (geoOf S) zk pc) (U : UnitCut (geoOf S) k pc)
    (hk : EndsIn (zk.getD pc.call #[]) zx) (hbel : k.below = true) : TieM ρ S fs k p := by
  have hD : pc.isD = false := by rw [U.isD, hbel]; rfl
  have hb : (geoOf S).keyBits (if pc.isD then .rd else .rm) = Fam.l (L5.dimOf S) .m1 := by
    rw [hD]
    exact bitsM N
  have hl : Fam.l (L5.dimOf S) .m1 =
      S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB := rfl
  have hn := Z.lnT
  have hs := pc_size hF L H hk .m1 hb
  have cB : cutB (geoOf S) k.below = S.cf.lgk + (S.lnT - 1) + S.lnT := by rw [hbel]; rfl
  have ezg : k.zg = pc.z.extract 0 S.cf.lgk := U.zg
  have ezi : k.zi = pc.z.extract (S.cf.lgk + (S.lnT - 1) + S.lnT)
      (S.cf.lgk + (S.lnT - 1) + S.lnT + S.cf.lB) := by rw [U.zi, cB]; rfl
  have ezj : k.zj = pc.z.extract (S.cf.lgk + (S.lnT - 1) + S.lnT + S.cf.lB)
      (S.cf.lgk + (S.lnT - 1) + S.lnT + 2 * S.cf.lB) := by rw [U.zj, cB]; rfl
  have ezs : k.zs = pc.z.extract (S.cf.lgk + (S.lnT - 1)) (S.cf.lgk + (S.lnT - 1) + S.lnT) := by
    rw [U.zs, hbel, if_pos rfl, ← hbel, cB]
    rfl
  have tP : ∀ j < S.lnT - 1, pt ρ (pc.z.extract S.cf.lgk (S.cf.lgk + (S.lnT - 1))) j =
      zP (L5.dimOf S) (L5.callsOf fs) p.z j := fun j hj =>
    pc_cut hF L H hk .m1 hb (by omega) (by omega)
  have tS : ∀ j < S.lnT, pt ρ (pc.z.extract (S.cf.lgk + (S.lnT - 1))
      (S.cf.lgk + (S.lnT - 1) + S.lnT)) j = zs (L5.dimOf S) (L5.callsOf fs) p.z j := fun j hj =>
    pc_cut hF L H hk .m1 hb (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ezg, sizeCut _ (by omega)]
    rfl
  · intro j hj
    rw [ezg]
    exact pc_cut hF L H hk .m1 hb (by omega) (by omega)
  · rw [ezs, sizeCut _ (by omega)]
    omega
  · intro j hj
    rw [ezs]
    exact tS j hj
  · rw [ezi, sizeCut _ (by omega)]
    omega
  · intro j hj
    rw [ezi, pc_cut hF L H hk .m1 hb (j := j) (by omega) (by omega)]
    show _ = inn _ _ _ .m1 (S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + j)
    congr 1
    omega
  · rw [ezj, sizeCut _ (by omega)]
    omega
  · intro j hj
    rw [ezj, pc_cut hF L H hk .m1 hb (j := j) (by omega) (by omega)]
    show _ = inn _ _ _ .m1 (S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + j)
    congr 1
    omega
  · intro I hI
    have ew : k.wI = (Attention.tileSums S (eqTab (pc.z.extract S.cf.lgk (S.cf.lgk + (S.lnT - 1))))
        (eqTab (pc.z.extract (S.cf.lgk + (S.lnT - 1)) (S.cf.lgk + (S.lnT - 1) + S.lnT)))).1 := by
      rw [U.wI, hbel, if_pos rfl, ← hbel, cB]
      rfl
    rw [ew]
    exact tiles_row ρ Z (sizeCut _ (by omega) |>.trans (by omega))
      (sizeCut _ (by omega) |>.trans (by omega)) tP tS hI

/-! ## A unit on the diagonal -/

/-- The points and the tile rows' weights of a unit on the diagonal are the library's. -/
structure TieD (ρ : Reading Kf) (S : Attention.Shape) (fs : Model.Forest.Shape) (k : ScoreP)
    (p : Pub Kf) : Prop where
  sg : k.zg.size = S.cf.lgk
  g : ∀ j < S.cf.lgk, pt ρ k.zg j = zgD (L5.dimOf S) (L5.callsOf fs) p.z j
  si : k.zi.size = S.cf.lB
  i : ∀ j < S.cf.lB, pt ρ k.zi j = zi' (L5.dimOf S) (L5.callsOf fs) p.z j
  sj : k.zj.size = S.cf.lB
  j : ∀ j < S.cf.lB, pt ρ k.zj j = zj' (L5.dimOf S) (L5.callsOf fs) p.z j
  wI : ∀ I < S.nT, ρ.val (k.wI.getD I zeroE) =
    Blocks.eqN ((L5.dimOf S).lP + 1) 0 (zID (L5.dimOf S) (L5.callsOf fs) p.z) I

theorem tieD_of (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) (N : L5.Norm S) (Z : Sizes S)
    {k : ScoreP} {pc : RemP} (H : PlaneCut (geoOf S) zk pc) (U : UnitCut (geoOf S) k pc)
    (hk : EndsIn (zk.getD pc.call #[]) zx) (hbel : k.below = false) : TieD ρ S fs k p := by
  have hD : pc.isD = true := by rw [U.isD, hbel]; rfl
  have hb : (geoOf S).keyBits (if pc.isD then .rd else .rm) = Fam.l (L5.dimOf S) .d1 := by
    rw [hD]
    exact bitsD N
  have hl : Fam.l (L5.dimOf S) .d1 = S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB := rfl
  have hlM : Fam.l (L5.dimOf S) .m1 =
      S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + S.cf.lB := rfl
  have hdm : Fam.l (L5.dimOf S) .d1 + (S.lnT - 1) = Fam.l (L5.dimOf S) .m1 := by
    rw [hl, hlM]
    omega
  have hn := Z.lnT
  have hs := pc_size hF L H hk .d1 hb
  have cB : cutB (geoOf S) k.below = S.cf.lgk + S.lnT := by rw [hbel]; rfl
  have ezg : k.zg = pc.z.extract 0 S.cf.lgk := U.zg
  have ezi : k.zi = pc.z.extract (S.cf.lgk + S.lnT) (S.cf.lgk + S.lnT + S.cf.lB) := by
    rw [U.zi, cB]
    rfl
  have ezj : k.zj = pc.z.extract (S.cf.lgk + S.lnT + S.cf.lB)
      (S.cf.lgk + S.lnT + 2 * S.cf.lB) := by rw [U.zj, cB]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ezg, sizeCut _ (by omega)]
    rfl
  · intro j hj
    rw [ezg]
    exact pc_cut hF L H hk .d1 hb (by omega) (by omega)
  · rw [ezi, sizeCut _ (by omega)]
    omega
  · intro j hj
    rw [ezi, pc_cut hF L H hk .d1 hb (j := j) (by omega) (by omega),
      inn_shift hF L .d1 .m1 hdm (by omega)]
    show _ = inn _ _ _ .m1 (S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + j)
    congr 1
    omega
  · rw [ezj, sizeCut _ (by omega)]
    omega
  · intro j hj
    rw [ezj, pc_cut hF L H hk .d1 hb (j := j) (by omega) (by omega),
      inn_shift hF L .d1 .m1 hdm (by omega)]
    show _ = inn _ _ _ .m1 (S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB + j)
    congr 1
    omega
  · intro I hI
    have ew : k.wI = eqTab (pc.z.extract S.cf.lgk (S.cf.lgk + S.lnT)) := by
      rw [U.wI, hbel, if_neg (by decide), ← hbel, cB]
      rfl
    rw [ew]
    have e1 : S.lnT = S.lnT - 1 + 1 := by omega
    refine eqTab_at ρ (n := (L5.dimOf S).lP + 1) (sizeCut _ (by omega) |>.trans ?_)
      (fun j hj => ?_) ?_
    · show S.cf.lgk + S.lnT - S.cf.lgk = S.lnT - 1 + 1
      omega
    · have hj' : j < S.lnT - 1 + 1 := hj
      exact pc_cut hF L H hk .d1 hb (by omega) (by omega)
    · show I < 2 ^ (S.lnT - 1 + 1)
      rw [← e1, ← Z.nT]
      exact hI

end K5Law

#print axioms K5Law.tieM_of
#print axioms K5Law.tieD_of
