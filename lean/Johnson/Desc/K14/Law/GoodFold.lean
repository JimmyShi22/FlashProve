-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/GoodFold.lean: the law of (fold) in the form that the rule of composition asks
of a block at its stretch (Piece.GoodIn): for the block "SPLIT" and for the block "LIN zeta" of the
shared chain.

The borders, at the chain's own record. A witness w gives words (rw w); Pin a w says that the
statement a (the record and the oracles) pins w's words.
  Base a w        Pin, and for each of the two groups: the record reaches a state at which all
                  constraints on that group hold of w's words (HoldsAt).
  behind "SPLIT"        Base
  in front of "SPLIT"   Base, and (fold)'s equation at the point z_fd that the record notes (FoldAt)
  in front of "LIN zeta"  Base, and omega_col is col_psi_lo(u) on the rows of M (OmegaCol)
The promises (On7, On8, On9): the places in front have said yes, one behind the other.
  split_goodIn    no draw counts: by goodIn_of_sure and shared_means.
  zeta_goodIn     by the bridge goodIn_of_count and the count foldCatches: the lost points are those
                  at which (fold)'s equation holds of a pinned witness's words though omega_col is
                  not col_psi_lo(u).
  split_goodIn8   the first at the shared chain's own eighth block.

What is not claimed. PREMISES, EACH ASKED UNDER THE PROMISE IN FRONT ALONE (the history and a letter
Prm): the extractor is the identity; at a yes a witness that is pinned behind the block is pinned in
front of it; a yes leads from Prm in front to a second letter Prm' behind; two witnesses pinned by
one statement have the same words on o_omega and on o_u; the stretch's written round reads as one
typed draw of a point, the one that the block notes, at errors that fit. Pin, Prm and Prm' are
letters: a pin of nobody meets the premises, and the laws are idle at it. TWO CODES: the promises
On7, On8 and On9 hold of a statement only at a shape with two codes (On7.twoCodes, On8.twoCodes): at
a shape with one code the two laws are true and empty. A block that refuses all has GoodIn too. No
soundness of a verifier.

-/
import Johnson.Desc.K14.Law.BlocksSound
import Johnson.Desc.K14.Law.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece goodIn_of_sure)
open _root_.Run.PQ (CK)
open Iop.IOR (drawRound)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- The record reaches a state at which all constraints on the group hold of the words. -/
def HoldsAt (d : St) (g : Nat) (m : Words K) : Prop :=
  ∃ e : St, Reaches d e g ∧ Means.AllSay ρ e.st (rowsOn e g) m

/-- What holds behind a step onward holds in front of it. -/
theorem HoldsAt.back {a b : St} {g : Nat} {m : Words K} (h : Onward a b)
    (k : HoldsAt ρ b g m) : HoldsAt ρ a g m := by
  obtain ⟨e, r, s⟩ := k
  exact ⟨e, ⟨h.grows.trans r.grows, (h.later g).trans r.later⟩, s⟩

/-- (fold)'s equation at the point that the record notes. -/
def FoldAt (S : LinShape) (d : St) (m : Words K) : Prop :=
  FoldEq S ((d.loc.psiSh.take S.kLo).map ρ.val) (d.loc.zFd.map ρ.val)
    (omegaOf d.loc (linLayOmega d.st.codes S) m) (uOf d.loc m)

/-- omega_col is col_psi_lo(u) on the rows of M. -/
def OmegaCol (S : LinShape) (d : St) (m : Words K) : Prop :=
  ∀ j < S.matrixRows, omegaOf d.loc (linLayOmega d.st.codes S) m j =
    ∑ t ∈ Finset.range (2 ^ S.kLo),
      eqK ((d.loc.psiSh.take S.kLo).map ρ.val) t * uOf d.loc m (t + 2 ^ S.kLo * j)

variable {W : Type} {C : CK} {F : Frame} (rw : W → Words K) (Pin : St × F.E.Str → W → Prop)

/-- What every border of the shared rounds holds. -/
def Base (a : St × F.E.Str) (w : W) : Prop :=
  Pin a w ∧ HoldsAt ρ a.1 a.1.loc.gU (rw w) ∧ HoldsAt ρ a.1 a.1.loc.gOmega (rw w)

/-- The places up to the joinings have said yes and have led to this record. -/
def On7 (p : Par) (a : St × F.E.Str) : Prop :=
  ∃ d0 d2 d3 r4 cols, SharedFront p d0 d2 d3 a.1 r4 cols

/-- The places up to "LIN zeta" have said yes and have led to this record. -/
def On8 (p : Par) (a : St × F.E.Str) : Prop :=
  ∃ d0 d2 d3 d6 r4 cols r7, SharedFront p d0 d2 d3 d6 r4 cols ∧ linZeta d6 [r7] = some a.1

/-- The places up to "SPLIT" have said yes and have led to this record. -/
def On9 (p : Par) (a : St × F.E.Str) : Prop :=
  ∃ d0 d2 d3 d7 r4 cols, SharedRun p d0 d2 d3 d7 a.1 r4 cols

/-- The promise in front of "LIN zeta" holds only at a shape with two codes. -/
theorem On7.twoCodes {p : Par} {a : St × F.E.Str} (h : On7 p a) :
    p.S.sharedSplitNeeded = true := by
  obtain ⟨_, _, _, _, _, hF⟩ := h
  exact hF.twoCodes

/-- So does the promise in front of "SPLIT". -/
theorem On8.twoCodes {p : Par} {a : St × F.E.Str} (h : On8 p a) :
    p.S.sharedSplitNeeded = true := by
  obtain ⟨_, _, _, _, _, _, _, hF, _⟩ := h
  exact hF.twoCodes

/-- **"SPLIT" in the form of the rule of composition.** -/
theorem split_goodIn (pc : Piece C F St Unit W) (p : Par) (hb : DecidesBySplit p pc.b)
    (hext : ∀ a τ w, pc.ext a τ w = w) (Prm Prm' : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, On8 p a → Prm a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hkeep : ∀ a τ b, On8 p a → Prm a → pc.ior.red.out a τ = some b → Prm' b) :
    pc.GoodIn (fun a => On8 p a ∧ Prm a) (fun b => On9 p b ∧ Prm' b)
      (fun a w => Base ρ rw Pin a w ∧ FoldAt ρ p.S a.1 (rw w)) (Base ρ rw Pin) := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha0 hout => ?_
  obtain ⟨hy, gs, hd⟩ := piece_yes pc a τ b hout
  obtain ⟨d0, d2, d3, d6, r4, cols, r7, hF, h7⟩ := id ha0.1
  have k8 := hb _ _ _ _ hd
  obtain ⟨r8, hr⟩ := split_one _ _ _ _ hF.twoCodes k8
  rw [hr] at k8
  have hR := hF.toRun a.1 b.1 r7 r8 h7 k8
  obtain ⟨o8, l8⟩ := onward_split p a.1 b.1 r8 hF.twoCodes k8
  refine ⟨⟨⟨d0, d2, d3, a.1, r4, cols, hR⟩, hkeep a τ b ha0.1 ha0.2 hout⟩, fun w hw => ?_⟩
  obtain ⟨hpin, hU, hO⟩ := hw
  rw [hext]
  refine ⟨⟨hback a τ b w ha0.1 ha0.2 hout hpin, ?_, ?_⟩, ?_⟩
  · rw [← l8]; exact hU.back ρ o8
  · rw [← l8]; exact hO.back ρ o8
  · obtain ⟨eU, rU, sU⟩ := hU
    obtain ⟨eO, rO, sO⟩ := hO
    exact (shared_means ρ p d0 d2 d3 a.1 b.1 eU eO r4 cols hR rU rO (rw w) sU sO).2.2

open Classical in
/-- **"LIN zeta" in the form of the rule of composition.** -/
theorem zeta_goodIn [Fintype K] (pc : Piece C F St Unit W) (p : Par)
    (hz : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → linZeta d rs = some d')
    (hext : ∀ a τ w, pc.ext a τ w = w)
    (Prm Prm' : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, On7 p a → Prm a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hkeep : ∀ a τ b, On7 p a → Prm a → pc.ior.red.out a τ = some b → Prm' b)
    (hdet : ∀ (a : St × F.E.Str) w w', On7 p a → Prm a → Pin a w → Pin a w' →
      AgreeOn a.1.loc.oOmega (rw w) (rw w') ∧ AgreeOn a.1.loc.oU.oracle (rw w) (rw w'))
    (c : Nat) (hc : p.S.kRow * Fintype.card K ^ (p.S.kRow - 1) ≤ c)
    (G : St × F.E.Str → CarryS (uLT C pc.ds) [drawRound (Fin p.S.kRow → K)])
    (fits : ∀ a, (G a).Fits ((c, ()) : Nat × Unit) pc.err)
    (hread : ∀ a τ b r7, pc.ior.red.out a τ = some b →
      (rvT C pc.ds τ ++ pc.back).map noDigest = [r7] →
      ∃ z, (G a).tr τ = some (((), ()), z, ()) ∧ (drawn r7).map ρ.val = List.ofFn z) :
    pc.GoodIn (fun a => On7 p a ∧ Prm a) (fun b => On8 p b ∧ Prm' b)
      (fun a w => Base ρ rw Pin a w ∧ OmegaCol ρ p.S a.1 (rw w))
      (fun a w => Base ρ rw Pin a w ∧ FoldAt ρ p.S a.1 (rw w)) := by
  refine goodIn_of_count pc _ _ _ _ (Fin p.S.kRow → K) c G fits
    (fun a z => ∃ w, Pin a w ∧ ¬ OmegaCol ρ p.S a.1 (rw w) ∧
      FoldEq p.S ((a.1.loc.psiSh.take p.S.kLo).map ρ.val) (List.ofFn z)
        (omegaOf a.1.loc (linLayOmega a.1.st.codes p.S) (rw w)) (uOf a.1.loc (rw w))) ?_ ?_
  · intro a ha
    by_cases hw0 : ∃ w0, Pin a w0 ∧ ¬ OmegaCol ρ p.S a.1 (rw w0)
    · obtain ⟨w0, hp0, hn0⟩ := hw0
      have hgap : ∃ j < p.S.matrixRows,
          omegaOf a.1.loc (linLayOmega a.1.st.codes p.S) (rw w0) j ≠
            ∑ t ∈ Finset.range (2 ^ p.S.kLo),
              eqK ((a.1.loc.psiSh.take p.S.kLo).map ρ.val) t *
                uOf a.1.loc (rw w0) (t + 2 ^ p.S.kLo * j) := by
        unfold OmegaCol at hn0
        push Not at hn0
        exact hn0
      refine le_trans (cnt_mono fun z hzl => ?_) (le_trans (le_trans (le_of_eq (cnt_eq_card _))
        (foldCatches p.S ((a.1.loc.psiSh.take p.S.kLo).map ρ.val)
          (omegaOf a.1.loc (linLayOmega a.1.st.codes p.S) (rw w0)) (uOf a.1.loc (rw w0))
          (le_two_pow_ceilLog2 _) hgap)) hc)
      obtain ⟨w, hp, _, hf⟩ := hzl
      obtain ⟨aO, aU⟩ := hdet a w0 w ha.1 ha.2 hp0 hp
      have eO : omegaOf a.1.loc (linLayOmega a.1.st.codes p.S) (rw w) =
          omegaOf a.1.loc (linLayOmega a.1.st.codes p.S) (rw w0) := funext fun j => aO _
      have eU : uOf a.1.loc (rw w) = uOf a.1.loc (rw w0) := funext fun k => aU _
      rw [← eO, ← eU]
      exact hf
    · rw [cnt_false fun z hzl => hw0 (by obtain ⟨w, hp, hn, _⟩ := hzl; exact ⟨w, hp, hn⟩)]
      exact Nat.zero_le _
  · intro a τ b ha hout
    obtain ⟨hy, gs, hd⟩ := piece_yes pc a τ b hout
    have h7a := ha.1
    obtain ⟨⟨d0, d2, d3, r4, cols, hF⟩, hprm⟩ := ha
    have k7 := hz _ _ _ _ hd
    obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k7
    obtain ⟨z, htr, hzs⟩ := hread a τ b r7 hout hr
    rw [hr] at k7
    have e7 := linZeta_inv a.1 b.1 r7 k7
    refine ⟨_, htr, fun hnl => ⟨⟨⟨d0, d2, d3, a.1, r4, cols, r7, hF, k7⟩,
      hkeep a τ b h7a hprm hout⟩, fun w hw => ?_⟩⟩
    obtain ⟨⟨hpin, hU, hO⟩, hf⟩ := hw
    have hpa := hback a τ b w h7a hprm hout hpin
    have o7 : Onward a.1 b.1 := Onward.of_st (by rw [e7])
    rw [hext]
    refine ⟨⟨hpa, ?_, ?_⟩, ?_⟩
    · have : b.1.loc.gU = a.1.loc.gU := by rw [e7]
      rw [← this]; exact hU.back ρ o7
    · have : b.1.loc.gOmega = a.1.loc.gOmega := by rw [e7]
      rw [← this]; exact hO.back ρ o7
    · by_contra hn
      refine hnl ⟨w, hpa, hn, ?_⟩
      unfold FoldAt at hf
      rw [e7] at hf
      rw [← hzs]
      exact hf

/-- The same at the shared chain's own eighth block. -/
theorem split_goodIn8 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pc : Piece C F St Unit W)
    (hpc : pc.b = b8) (hext : ∀ a τ w, pc.ext a τ w = w) (Prm Prm' : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, On8 P.par a → Prm a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (hkeep : ∀ a τ b, On8 P.par a → Prm a → pc.ior.red.out a τ = some b → Prm' b) :
    pc.GoodIn (fun a => On8 P.par a ∧ Prm a) (fun b => On9 P.par b ∧ Prm' b)
      (fun a w => Base ρ rw Pin a w ∧ FoldAt ρ P.par.S a.1 (rw w)) (Base ρ rw Pin) :=
  split_goodIn ρ rw Pin pc P.par
    (hpc ▸ decidesBySplit_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl) hext Prm Prm' hback hkeep

end Desc.K14.Law
