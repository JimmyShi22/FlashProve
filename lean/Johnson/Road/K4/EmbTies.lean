-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/EmbTies.lean: three of the clauses of EmbDict (Johnson/Road/K4/EmbPort.lean), paid:
the weights of the blocks, from the reading of the verifier's point; the reads of the stream's limbs
at the embedding's point, from true reads; and the record itself at a public record Pub34.

Main names:
  `embW_of`: the clause wts: the verifier's table of equality weights of a point z against the
    library's weights of a point that agrees with the reading of z.
  `xbA_there`, `emb_there`: where K4's form is there, the family "xbI@Z_E" is there and U3at
    returns at every limb of every block that the form reads.
  `embI_meet`: limb l of block kh of the stream that comes in, in the table named xbI@Z_E, in the
    first group: the twin of sqI_meet (Johnson/Road/K4/ReadsMeetLong.lean).
  `embReads_of`: the clause reads, where the library-side entries are the library's readAt.
  `embDict_at`: EmbDict at a run's record whose environment is that of a record Pub34, on true
    reads.
Limits. What stays a premise of embDict_at: the hidden value under the slot; that the two points'
readings are the library's pa and pb; sizes; that the library-side entries are readAt at the cells
of the matrices Mm; that the table of scales is the record's; that the record has its second level;
that D is the record's dimension; that the group is the first; that K4's form is there. Implications
in one world: no draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.EmbPort
import Johnson.Road.K4.FrontDictAtPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Finset
open OnBytes.Model (Reading World Aff Level tenCell eqTab)
open OnBytes.Model.Layer (Env Heard Own)
open OnBytes.Road.Rows (readAtW foldForms_there)
open OnBytes.Desc.First.K4 (embeddingForm)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr zpos)
open Blocks (eqN ext)

variable {K : Type} [Field K]

/-- The clause wts. -/
theorem embW_of {ρ : Reading K} {z : Array E} {gB nb : ℕ} {pb : ℕ → K} (hz : z.size = gB)
    (hp : ∀ j, j < gB → pt ρ z j = pb j) (hn : nb ≤ 2 ^ gB) :
    ∀ kh, kh < nb → ρ.val ((eqTab z).getD kh zeroE) = eqN gB 0 pb kh := by
  intro kh hk
  rw [eqTab_value ρ z kh (by rw [hz]; exact Nat.lt_of_lt_of_le hk hn), hz]
  exact eqN_congr' gB 0 (fun j hj => by rw [Nat.zero_add]; exact hp j hj) kh

/-- Where xbA returns, each limb's read is there. -/
theorem xbA_there {v : Env} {t kh : ℕ} {a : Aff} (h : v.xbA t kh = some a) {l : ℕ}
    (hl : l < v.y.xb.nl) :
    ∃ a', v.U3at t (tenCell v.y.xb l 0 0 / v.y.S2 + kh) = some a' := by
  unfold Env.xbA Env.limbs at h
  obtain ⟨x, hx⟩ := foldForms_there _ (List.range v.y.xb.nl) _ _ h l (List.mem_range.mpr hl)
  obtain ⟨a', ha', _⟩ := map_some hx
  exact ⟨a', ha'⟩

/-- Where K4's form is there, so are the family of tables and all reads that the form names. -/
theorem emb_there {v : Env} {H : Heard} {sVE : ℕ} {a : Aff}
    (h : embeddingForm v H sVE = some a) :
    ∃ t, v.tabAt "xbI@Z_E" = some t ∧ ∀ l kh, l < v.y.xb.nl → kh < v.y.h.d / v.y.S2 →
      ∃ a', v.U3at t (tenCell v.y.xb l 0 0 / v.y.S2 + kh) = some a' := by
  unfold embeddingForm at h
  obtain ⟨t, ht, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨s, hs, -⟩ := Option.bind_eq_some_iff.mp h1
  refine ⟨t, ht, fun l kh hl hk => ?_⟩
  obtain ⟨x, hx⟩ := foldForms_there _ (List.range (v.y.h.d / v.y.S2)) _ _ hs kh
    (List.mem_range.mpr hk)
  obtain ⟨b, hb, _⟩ := map_some hx
  exact xbA_there hb hl

section Records

variable {ρ : Reading K} {W : World K} {v : Env} {c : Cells K} {t : Cell → K} [scl : Scl]
  {D : Dim} {low u lowV uV uP uR lowE uE : ℕ → K}

/-- The stream that comes in, at the embedding's point, in the first group: from Fits (the tie of
the array x0 and the whole blocks) and TrueAt3 (the table named xbI@Z_E is true at lowE, uE), where
U3at returns. -/
theorem embI_meet (F : Fits ρ W v D c t low u) (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE)
    (hg : v.g = 0) :
    ∀ tE, v.tabAt "xbI@Z_E" = some tE → ∀ l kh a,
      v.U3at tE (tenCell v.y.xb l 0 0 / v.y.S2 + kh) = some a →
      readAtW W v tE (tenCell v.y.xb l 0 0 / v.y.S2 + kh) =
        ∑ r ∈ range (2 ^ v.y.ls), eqN v.y.ls 0 lowE r *
          ext D.lT (fun p => t ⟨.x0, l, 0, kh * 2 ^ v.y.ls + r, p⟩) uE := by
  intro tE hE l kh a h
  obtain ⟨_, _, _, _, _, _, _, _, _, T0, _, _, _, _, _, halb, _⟩ := F.stream
  exact long_meet T0 (T3.xiE hg tE hE) F.S2 (halb l) h

/-- The clause reads. pa: the library's point; ls: the bits of a feature in its block. -/
theorem embReads_of {J : Type} (F : Fits ρ W v D c t low u)
    (T3 : TrueAt3 ρ W v D.lT c lowV uV uP uR lowE uE) (hg : v.g = 0) {H : Heard} {sVE : ℕ}
    {a : Aff} (h : embeddingForm v H sVE = some a) (nl5 : v.y.xb.nl = 5) {nb : ℕ}
    (hB : v.y.h.d / v.y.S2 = nb) {ls : ℕ} (hls : v.y.ls = ls) {pa : ℕ → K}
    (p1 : ∀ j, j < ls → lowE j = pa j) (p2 : ∀ j, j < D.lT → uE j = pa (ls + j))
    {y : J → K} {uX : ℕ → ℕ → J}
    (hL : ∀ l kh, l < 5 → kh < nb →
      y (uX l kh) = Cb.Pv.Lay.End.Gated.readAt D t .x0 pa 0 ls l 0 kh) :
    ∀ t', v.tabAt "xbI@Z_E" = some t' → ∀ l kh, l < 5 → kh < nb →
      readAtW W v t' (tenCell v.y.xb l 0 0 / v.y.S2 + kh) = y (uX l kh) := by
  intro t' ht' l kh hl hk
  obtain ⟨t0, ht0, hU⟩ := emb_there h
  obtain rfl : t0 = t' := Option.some.inj (ht0.symm.trans ht')
  obtain ⟨a', ha'⟩ := hU l kh (by rw [nl5]; exact hl) (by rw [hB]; exact hk)
  rw [embI_meet F T3 hg t0 ht0 l kh a' ha', hL l kh hl hk, hls]
  unfold Cb.Pv.Lay.End.Gated.readAt
  exact long_join _ p1 fun j hj => by rw [Nat.zero_add]; exact p2 j hj

end Records

/-- **EmbDict at a record Pub34, on true reads.** -/
theorem embDict_at [scl : Scl] {J : Type} [Fintype J] [DecidableEq J] (X : Rows.Pub34 K)
    (Wo : World K) (Mm : Mats K) (hRd : X.ReadsTrue Wo Mm)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) {o : Own} (hv : o.v = X.p.v)
    {o2 : Level} (h2X : X.hd2 = some o2) {D : Dim} (hD : X.D = D) {t : Cell → K}
    (ht : cellsOf D (cellsAt X.p.v.y Mm) = t) (hg : o.v.g = 0) (nl5 : o.v.y.xb.nl = 5)
    {nb gB ls : ℕ} (hB : o.v.y.h.d / o.v.y.S2 = nb) (hls : o.v.y.ls = ls) {pa pb : ℕ → K}
    (pa1 : ∀ j, j < ls → pt X.ρ X.H.ZE j = pa j)
    (pa2 : ∀ j, j < D.lT → pt X.ρ X.H.ZE (ls + j) = pa (ls + j))
    (hk : o.H.tkh.size = gB) (pbT : ∀ j, j < gB → pt X.ρ o.H.tkh j = pb j) (hn : nb ≤ 2 ^ gB)
    {sh : K} {mE : J} {uX : ℕ → ℕ → J} {y : J → K} (hslot : Wo.slot o.sVE = sh - y mE)
    (hL : ∀ l kh, l < 5 → kh < nb →
      y (uX l kh) = Cb.Pv.Lay.End.Gated.readAt D t .x0 pa 0 ls l 0 kh) {a : Aff}
    (h : embeddingForm o.v o.H o.sVE = some a) :
    EmbDict X.ρ Wo o.v o.H o.sVE sh mE uX nb gB pb y := by
  subst hD
  subst ht
  obtain ⟨ZV, ZA, ZB, -, -, -, PF, -, T3, -, -, -⟩ := truths_of_pub34 X Wo Mm hRd h2X
  rw [← hscl] at PF
  have hlsX : X.p.v.y.ls = ls := by rw [← hv]; exact hls
  rw [hlsX] at T3
  have F : Fits X.ρ Wo o.v X.D (cellsAt X.p.v.y Mm) (cellsOf X.D (cellsAt X.p.v.y Mm))
      (pt X.ρ X.Zp) (zpos X.D (zOf X.ρ X.H.fo.zx X.H.fo.zy)) := by rw [hv]; exact PF.fits
  have T3' : TrueAt3 X.ρ Wo o.v X.D.lT (cellsAt X.p.v.y Mm) (pt X.ρ ZV)
      (fun j => pt X.ρ ZV (ls + j)) (pt X.ρ X.H.PV) (pt X.ρ X.H.tV.r) (pt X.ρ X.H.ZE)
      (fun j => pt X.ρ X.H.ZE (ls + j)) := by rw [hv]; exact T3
  exact
    { num := F.num
      nl5 := nl5
      hB := hB
      slot := hslot
      wts := embW_of hk pbT hn
      reads := embReads_of F T3' hg h nl5 hB hls pa1 pa2 hL }

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.embW_of
#print axioms OnBytes.Road.K4.emb_there
#print axioms OnBytes.Road.K4.embI_meet
#print axioms OnBytes.Road.K4.embReads_of
#print axioms OnBytes.Road.K4.embDict_at
