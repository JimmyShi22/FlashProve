-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEndsAt58.lean: what the claims 6, 7 and 8 of an attention sub-proof give for
all pairs at once: the hidden values under the slots of the last four sumchecks are the library's.

Johnson/Road/Rows/AttEnds58.lean has one statement for each claim, and the files beside it prove
them. This file gathers their premises in records and draws the conclusions for all pairs, layers
and bits of a sub-proof. No draw is used: every theorem holds at every transcript.

Main definitions.
 - OnPub, IndexPub, BitsPub: the public premises, for all pairs at once.
 - OnGiven, IndexGiven, BitsGiven: the forms have been made and the claims have the value 0.
Main theorems.
 - ends12_of: both end values of every pair of the value product on the diagonal tiles are the
   library's maps of step s12.
 - m6_of: the values sent for the row maxima are the library's rvM6. qry_of: the first end values of
   the score at the index are the first maps of step s16.
 - keys_of, ibits_of: the end values of the key at the index are the library's rvKC and rvIBP.
 - bits_of: the two end values of every pair of the sumcheck for the bits are the extension of
   bitCube with 4 bits, and that minus 1.

What this file does not claim. No field of the records is shown to hold of a run. The second end
values of the score at the index are tied down by no claim, and nothing is said of them here.
Nothing is said about probabilities or about hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttBetween
import Johnson.Road.Rows.AttEnds58ProofsV
import Johnson.Road.Rows.AttEnds58ProofsP

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork HTailF2 eqTab ofNat)
open OnBytes.Attention (Heard sc3A sc3B plane readHead readGroup readIndexBit readMaximum tok
  lastCoords lastN pointD)
open Inst.Model.AttSeg (Calls Pub Step Aext Bext rvM6 rvKC rvIBP)

variable {K : Type} [Field K]

/-! ## What the run gives -/

/-- The public premises of ValueOnEndA and ValueOnEndB that ProductPub and BelowPub do not hold. -/
structure OnPub (tl : HTailF2) (h : Heard) : Prop where
  /-- the length of the sumcheck's point -/
  r : h.d.vpd.r.size = h.S.nvVD
  /-- the point at which the softmax weights are read -/
  ptD : h.t.ptD = pointD h.S h.d
  /-- the table on the softmax weights -/
  tVD : AsAt h h.t.tVD (lastN h.t.ptD h.S.cf.lmS)
  /-- the table on the values -/
  qVD : QaAt tl h h.t.qVD h.d.zcW
    (tok h.S (eqTab (h.d.vpd.r.extract h.S.cf.lgk (h.S.cf.lgk + h.S.lnT)))
      (lastCoords h.d.vpd.r h.S.cf.lB))

/-- For each piece of segment wl: the three forms of the value product on the diagonal tiles have
been made, and the two claims have the value 0. -/
def OnGiven (ρ : Reading K) (W : World K) (K3 : ℕ) (h : Heard) : Prop :=
  ∀ b w, h.d.pwW[b]? = some w →
    ∃ (p3 p4 v : Aff) (F F' G G' G'' : Fork) (c c1 c' c1' c'' c1'' : Ctx),
    Cols F h K3 ∧ Cols F' h K3 ∧
    (plane h h.t.tVD 3 w.lam w.a h.t.ptD true F).Yields c (p3, G) c1 ∧
    (plane h h.t.tVD 4 w.lam w.a h.t.ptD true F).Yields c' (p4, G') c1' ∧
    (readGroup h h.t.qVD h.S.atV h.d.vpd.r h.d.zcW w.lam F').Yields c'' (v, G'') c1'' ∧
    (sc3A h.d.vpd b - (p3 + Aff.ofConst (ofNat 128) + Aff.scale p4 (ofNat 256))).value ρ W = 0 ∧
    (sc3B h.d.vpd b - (Aff.ofConst h.d.gam + v)).value ρ W = 0

/-- The public premises of the four statements on claim 7. -/
structure IndexPub (ρ : Reading K) (tl : HTailF2) (h : Heard) (p : Pub K) : Prop where
  /-- the length of the point of the score at the index -/
  rF : h.x.scF.r.size = h.S.nvF
  /-- the length of the point of the key at the index -/
  rD : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk
  /-- the length of the drawn point on the heads -/
  tg : h.x.tg.size = h.S.cf.lgk
  /-- the length of the drawn point on the positions -/
  ti : h.x.ti.size = h.S.cf.lt
  /-- the drawn point on the heads is the library's -/
  vtg : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = p.tg j
  /-- the drawn point on the positions is the library's -/
  vti : ∀ j < h.S.cf.lt, pt ρ h.x.ti j = p.ti j
  /-- the point of the score at the index, on the positions, is the library's -/
  vfi : ∀ j < h.S.cf.lt, pt ρ h.x.scF.r j = p.fi j
  /-- the point of the score at the index, on the heads, is the library's -/
  vfg : ∀ j < h.S.cf.lgk, pt ρ h.x.scF.r (h.S.cf.lt + j) = p.fg j
  /-- the point of the score at the index, on the features, is the library's -/
  vfn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = p.fn j
  /-- the table on the row maxima -/
  hT : AhAt tl h h.t.hT (eqTab h.x.ti)
  /-- the table on the queries -/
  qF : QaAt tl h h.t.qF (h.x.rc h.S) (eqTab (h.x.ri h.S))
  /-- the table on the keys -/
  qKx : QaAt tl h h.t.qKx (h.x.rc h.S) (eqTab (h.x.pj h.S))
  /-- the table on the bits of the index -/
  hPi : AhAt tl h h.t.hPi (eqTab (h.x.pi h.S))

/-- The forms of claim 7 have been made, and its claims on single values have the value 0. -/
structure IndexGiven (ρ : Reading K) (W : World K) (K3 : ℕ) (h : Heard) : Prop where
  /-- the values sent for the row maxima -/
  m6 : ∀ b < h.S.NP, ∃ (m : Aff) (F G : Fork) (c c1 : Ctx), Cols F h K3 ∧
    (readMaximum h h.t.hT h.x.tg (b / h.S.HA) (b % h.S.HA) F).Yields c (m, G) c1 ∧
    (Aff.slot (h.x.sM6 + b) - m).value ρ W = 0
  /-- the first end values of the score at the index -/
  qry : ∀ b < h.S.NP, ∃ (q : Aff) (F G : Fork) (c c1 : Ctx), Cols F h K3 ∧
    (readHead h h.t.qF h.S.atQ (h.x.rg h.S) (h.x.rc h.S) (b / h.S.HA) (b % h.S.HA) F).Yields c
      (q, G) c1 ∧
    (sc3A h.x.scF b - q).value ρ W = 0
  /-- the end values of the key at the index: the keys -/
  key : ∀ lam < h.S.Lam, ∃ (kx : Aff) (F G : Fork) (c c1 : Ctx), Cols F h K3 ∧
    (readGroup h h.t.qKx h.S.atK (h.x.pg h.S) (h.x.rc h.S) lam F).Yields c (kx, G) c1 ∧
    (Aff.slot (h.x.sKC + lam) - kx).value ρ W = 0
  /-- the end values of the key at the index: the bits -/
  bit : ∀ b < h.S.NP, ∀ k < h.S.cf.lt, ∃ (x : Aff) (F G : Fork) (c c1 : Ctx), Cols F h K3 ∧
    (readIndexBit h h.t.hPi (h.x.pg h.S) (b / h.S.HA) (b % h.S.HA) k F).Yields c (x, G) c1 ∧
    (Aff.slot (h.x.sIb h.S b k) - x).value ρ W = 0

/-- The public premises of the statements on claim 8. -/
structure BitsPub (tl : HTailF2) (h : Heard) : Prop where
  /-- the length of the sumcheck's point -/
  r : h.x.scH.r.size = h.S.nvH
  /-- the table on the bits of the index -/
  hR2 : AhAt tl h h.t.hR2 (eqTab (h.x.ri2 h.S))

/-- For each pair: the form of claim 8 on the first end value has been made, and the two claims have
the value 0. -/
def BitsGiven (ρ : Reading K) (W : World K) (K3 : ℕ) (h : Heard) : Prop :=
  ∀ b < h.S.NP, ∃ (f : Aff) (F G : Fork) (c c1 : Ctx), Cols F h K3 ∧
    (bitsForm h b F).Yields c (f, G) c1 ∧ f.value ρ W = 0 ∧
    (sc3B h.x.scH b - sc3A h.x.scH b + Aff.ofConst oneE).value ρ W = 0

/-! ## The theorems -/

section
variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls} {p : Pub K}

/-- **The end values of the value product on the diagonal tiles.** -/
theorem ends12_of (A : AttAt ρ W tl K3 M h lid cf fs)
    (pE : ProductPub ρ tl h C p) (pV : BelowPub ρ tl h C p) (pO : OnPub tl h)
    (g : OnGiven ρ W K3 h) : EndsAt ρ W h M C p h.d.vpd .s12 := by
  intro b hb
  obtain ⟨hsz, hpw⟩ := pE.pairs
  have hb' : b < h.d.pwW.size := by rw [hsz]; exact hb
  have hw : h.d.pwW[b]? = some h.d.pwW[b] := Array.getElem?_eq_getElem hb'
  obtain ⟨e1, e2⟩ := hpw b hb _ hw
  obtain ⟨p3, p4, v, F, F', G, G', G'', c, c1, c', c1', c'', c1'', k1, k2, r1, r2, r3, v1, v2⟩ :=
    g b _ hw
  have ha : h.d.pwW[b].a < h.S.HA := by
    rw [e2]
    exact Nat.mod_lt b (heads_pos hb)
  have eb : h.d.pwW[b].lam * h.S.HA + h.d.pwW[b].a = b := by
    rw [e1, e2]
    exact Nat.div_add_mod' b h.S.HA
  have x1 := valueOnEndA K ρ W tl K3 M h F lid cf fs C p b h.d.pwW[b] p3 p4 G G' c c1 c' c1' A k1
    pO.r pV.zi ha (sizes_of_hid A.shape).lmS pO.ptD pV.vi pO.tVD r1 r2 v1
  have x2 := valueOnEndB K ρ W tl K3 M h F' lid cf fs C p b h.d.pwW[b] v G'' c'' c1'' A k2 pO.r
    pE.zc ha pE.vn pV.gam pO.qVD r3 v2
  rw [eb] at x1 x2
  exact ⟨x1, x2⟩

/-- **The values sent for the row maxima.** -/
theorem m6_of (A : AttAt ρ W tl K3 M h lid cf fs) (pI : IndexPub ρ tl h p)
    (g : IndexGiven ρ W K3 h) (b : ℕ) (hb : b < h.S.NP) :
    W.slot (h.x.sM6 + b) = rvM6 (L5.dimOf h.S) p (cellsK h.S M) b := by
  obtain ⟨m, F, G, c, c1, k1, r1, v1⟩ := g.m6 b hb
  exact scoreStartEnd K ρ W tl K3 M h F lid cf fs p b m G c c1 A k1 pI.tg pI.ti hb pI.vtg pI.vti
    pI.hT r1 v1

/-- **The first end values of the score at the index.** -/
theorem qry_of (A : AttAt ρ W tl K3 M h lid cf fs) (pI : IndexPub ρ tl h p)
    (g : IndexGiven ρ W K3 h) (b : ℕ) (hb : b < h.S.NP) :
    W.slot (h.x.scF.sEnd + 2 * b) =
      Aext (L5.dimOf h.S) C p (cellsK h.S M) .s16 b (pt ρ h.x.scF.r) := by
  obtain ⟨q, F, G, c, c1, k1, r1, v1⟩ := g.qry b hb
  exact scoreAtIndexEnd K ρ W tl K3 M h F lid cf fs C p b q G c c1 A k1 pI.rF hb pI.qF r1 v1

/-- **The end values of the key at the index: the keys.** -/
theorem keys_of (A : AttAt ρ W tl K3 M h lid cf fs) (pI : IndexPub ρ tl h p)
    (g : IndexGiven ρ W K3 h) (lam : ℕ) (hl : lam < h.S.Lam) :
    W.slot (h.x.sKC + lam) = rvKC (L5.dimOf h.S) p (cellsK h.S M) (pt ρ h.x.scd.r) lam := by
  obtain ⟨kx, F, G, c, c1, k1, r1, v1⟩ := g.key lam hl
  exact keyAtIndexEndK K ρ W tl K3 M h F lid cf fs p lam kx G c c1 A k1 pI.rF pI.rD hl pI.vfn
    pI.qKx r1 v1

/-- **The end values of the key at the index: the bits.** -/
theorem ibits_of (A : AttAt ρ W tl K3 M h lid cf fs) (pI : IndexPub ρ tl h p)
    (g : IndexGiven ρ W K3 h) (b : ℕ) (hb : b < h.S.NP) (k : ℕ) (hk : k < h.S.cf.lt) :
    W.slot (h.x.sIb h.S b k) = rvIBP (L5.dimOf h.S) (cellsK h.S M) (pt ρ h.x.scd.r) b k := by
  obtain ⟨x, F, G, c, c1, k1, r1, v1⟩ := g.bit b hb k hk
  exact keyAtIndexEndB K ρ W tl K3 M h F lid cf fs b k x G c c1 A k1 pI.rD hb hk pI.hPi r1 v1

/-- **The end values of the sumcheck for the bits.** -/
theorem bits_of (A : AttAt ρ W tl K3 M h lid cf fs) (pB : BitsPub tl h)
    (g : BitsGiven ρ W K3 h) (b : ℕ) (hb : b < h.S.NP) :
    W.slot (h.x.scH.sEnd + 2 * b) =
        Blocks.ext ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4)
          (bitCube 4 (L5.dimOf h.S) (cellsK h.S M) b) (pt ρ h.x.scH.r) ∧
      W.slot (h.x.scH.sEnd + (2 * b + 1)) =
        Blocks.ext ((L5.dimOf h.S).lT + (L5.dimOf h.S).lg + 4)
          (bitCube 4 (L5.dimOf h.S) (cellsK h.S M) b) (pt ρ h.x.scH.r) - 1 := by
  obtain ⟨f, F, G, c, c1, k1, r1, v1, v2⟩ := g b hb
  have a1 := bitsEndA K ρ W tl K3 M h F lid cf fs b f G c c1 A k1 pB.r hb pB.hR2 r1 v1
  exact ⟨a1, by rw [bitsEndB K ρ W h b v2, a1]⟩

end

end OnBytes.Road.Rows
