-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PointKey.lean: the key's sort of lost points at "LIN point" IS THE LIBRARY's:
the letter BadKey of the law of "LIN point" (Johnson/Desc/K14/Law/PointGood.lean) is filled with the
library's bad points of the fold (Cb/Ld/LdFoldEq.lean: Bad), the letters Dec and Tab with what the
library's decoder with the record makes of the stored table (dec: that it returns a table; which),
at the typed data of the encoded index that is made of the public shape; and the premise "what not
bad gives" (hgood) is PROVED.

  tabF            the stored table's columns, read, as the library's table of words: row by row.
  recK            the key's seeds and record, read, as the library's record.
  foldCol_eq      the fold of a stored column by the program's weights is the library's fold of that
                  table at gamma.
  recRow_of_all   (rec_gamma)'s equation at every seed is the library's RecRow.
  BadX, DecX, TabX   the three letters' fillings.
  good_of_notBad  **what not bad gives**: at a gamma that is not bad, near and RecAll give that the
                  table decodes, and that the folded row's message is the fold at gamma of the rows
                  that it decodes to.
  point_goodInX   the law of "LIN point" at these fillings: of its two premises on the key's sort
                  one is left: the library's count of the bad points.
  point_goodInY   the same, with that count asked as the library has it: at every table and record
                  without a collision at the record's seed; and, beside Prm, no collision of the
                  stored table at the key's seeds.

What is not claimed. THE COUNT OF THE BAD POINTS (hkey: the library's FoldErr at this data) stays a
premise: the statement on codes'. The typed data's letters err, eM, rank stay letters. New premises,
by name: the stored table's shape meets its conditions; M's places lie in front of the pads; beside
Prm the key fits the shape. Where the table does not decode, TabX is 0: THE RELATION IN FRONT SAYS
THAT IT DECODES (DecX). The other premises of point_goodIn stay. No soundness of a verifier. THE
TYPED DATA ixOf OF THIS FILE IS NO INSTANCE OF THE THEOREM THAT IS MEANT TO PAY THAT COUNT: it asks
the places of a full message as one range, the tail first, and the library's own generator matrix:
the road to it is Johnson/Desc/K14/Law/PointKey2.lean (ixOf2), which spends this file's tabF,
foldCol_eq and recRow_of_all. No other file of this tree names point_goodInX or point_goodInY; here
point_goodInY calls point_goodInX.

-/
import Johnson.Desc.K14.Law.PointGood
import Johnson.Desc.K14.Law.TypedRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- The stored table's columns, read, as a table of words: row by row. -/
def tabF (s : IndexShape) (tab : Nat → List UInt64) :
    (Fin s.v → Bool) → Fin (2 ^ s.code.logN) → K :=
  fun r x => ρ.val (ofF ((tab x.val).toArray.getD (numOf s.v r) 0))

/-- The fold of a stored column by the program's weights is the library's fold of the table. -/
theorem foldCol_eq (p : Par) (d : St) (tab : Nat → List UInt64)
    (gam : Fin p.S.fold.index.v → K) (hg : (gamma p.S d.loc).map ρ.val = List.ofFn gam)
    (x : Fin (2 ^ p.S.fold.index.code.logN)) :
    foldCol ρ p d tab x.val = Cb.foldAll gam (tabF ρ p.S.fold.index tab) x := by
  have hl : (gamma p.S d.loc).length = p.S.fold.index.v := by
    have := congrArg List.length hg
    simpa using this
  unfold foldCol Cb.foldAll
  rw [Finset.sum_apply, sum_bits]
  have hs : (weights p.S d.loc).size = 2 ^ p.S.fold.index.v := by
    unfold weights
    rw [eqTable_size, hl]
  rw [hs]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.1 hr
  rw [weights_val ρ p.S d.loc r (by rw [hl]; exact hr'), hg, eqK_ofFn]
  show _ = Alg.eqk gam (bitsOf p.S.fold.index.v r) * tabF ρ p.S.fold.index tab
    (bitsOf p.S.fold.index.v r) x
  unfold tabF
  rw [numOf_bitsOf _ _ hr']

/-- (rec_gamma)'s equation at every seed is the library's RecRow. -/
theorem recRow_of_all [Fintype K] (p : Par) (d : St) (m : Words K) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin p.S.fold.index.code.ell ⊕ Fin p.S.fold.index.code.r → K) → Nat)
    (gam : Fin p.S.fold.index.v → K) (hg : (gamma p.S d.loc).map ρ.val = List.ofFn gam)
    (hi : p.S.fold.index.ok = true) (hfit : d.loc.key.fits p.S.fold.index = true)
    (h : RecAll ρ p d m) :
    (ixOf ρ p.S.fold err eM rank).RecRow
      (seedsFn ρ p.S.fold.index d.loc.key,
        recOf p.S.fold.index fun k => ρ.val (d.loc.key.record.getD k zeroE)) gam
      (fullOf p.S.fold (uOf d.loc m)) := by
  have hl : (gamma p.S d.loc).length = p.S.fold.index.v := by
    have := congrArg List.length hg
    simpa using this
  simp only [TableKey.fits, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hfit
  obtain ⟨⟨_, hsl⟩, hzl⟩ := hfit
  have hpads : p.S.fold.index.plain + 3 * p.S.fold.index.answers = p.S.fold.index.code.ell := by
    simp only [IndexShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hi
    have : p.S.fold.index.pads < p.S.fold.index.code.ell := by tauto
    unfold IndexShape.plain
    unfold IndexShape.pads at this ⊢
    omega
  rw [recRow_iff ρ p.S.fold err eM rank hpads]
  intro a
  have ha : a.val < d.loc.key.seeds.length := by rw [hsl]; exact a.isLt
  have hmem : (d.loc.key.seeds[a.val], a.val) ∈ d.loc.key.seeds.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [ha]
  have h0 := h _ hmem
  have hgd : d.loc.key.seeds.getD a.val default = d.loc.key.seeds[a.val] :=
    List.getD_eq_getElem _ _ ha
  unfold RecAt RecEq at h0
  unfold RecEq
  simp only [seedsFn, hgd]
  rw [ofFn_ptFn ρ _ _ (hzl _ (List.getElem_mem ha))]
  refine h0.trans (Finset.sum_congr rfl fun r hr => ?_)
  show ρ.val ((weights p.S d.loc).getD r zeroE) * _ = _
  rw [weights_val ρ p.S d.loc r (by rw [hl]; exact Finset.mem_range.1 hr), hg]

variable [Fintype K]

/-- The bad points of the fold, at the typed data made of the public shape, the stored table's
columns and the key. -/
def BadX (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin p.S.fold.index.code.ell ⊕ Fin p.S.fold.index.code.r → K) → Nat)
    (e' : Nat) (tab : Nat → List UInt64) (key : TableKey) (gam : Fin p.S.fold.index.v → K) : Prop :=
  (ixOf ρ p.S.fold err eM rank).Bad (tabF ρ p.S.fold.index tab)
    (seedsFn ρ p.S.fold.index key,
      recOf p.S.fold.index fun k => ρ.val (key.record.getD k zeroE)) e' gam

/-- What the stored table decodes to, with the record: row r, place k; 0 where it does not decode,
and beyond a row's message. -/
noncomputable def TabX (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin p.S.fold.index.code.ell ⊕ Fin p.S.fold.index.code.r → K) → Nat)
    (tab : Nat → List UInt64) (key : TableKey) (r k : Nat) : K :=
  match (ixOf ρ p.S.fold err eM rank).dec (tabF ρ p.S.fold.index tab)
      (seedsFn ρ p.S.fold.index key,
        recOf p.S.fold.index fun k => ρ.val (key.record.getD k zeroE)) with
  | some U => if h : k < p.S.fold.index.code.ell then U (bitsOf p.S.fold.index.v r, ⟨k, h⟩) else 0
  | none => 0

/-- The stored table decodes, with the record. -/
def DecX (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin p.S.fold.index.code.ell ⊕ Fin p.S.fold.index.code.r → K) → Nat)
    (tab : Nat → List UInt64) (key : TableKey) : Prop :=
  ((ixOf ρ p.S.fold err eM rank).dec (tabF ρ p.S.fold.index tab)
    (seedsFn ρ p.S.fold.index key,
      recOf p.S.fold.index fun k => ρ.val (key.record.getD k zeroE))).isSome = true

/-- **What not bad gives.** -/
theorem good_of_notBad (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin p.S.fold.index.code.ell ⊕ Fin p.S.fold.index.code.r → K) → Nat)
    (e' : Nat) (tab : Nat → List UInt64) (d : St) (m : Words K)
    (gam : Fin p.S.fold.index.v → K) (hi : p.S.fold.index.ok = true)
    (hroom : p.S.matrixRows * 2 ^ p.S.kLo ≤ p.S.fold.index.plain)
    (hfit : d.loc.key.fits p.S.fold.index = true)
    (hnb : ¬ BadX ρ p err eM rank e' tab d.loc.key gam)
    (hg : (gamma p.S d.loc).map ρ.val = List.ofFn gam) (hnear : NearAt ρ p d m tab e')
    (hrec : RecAll ρ p d m) :
    DecX ρ p err eM rank tab d.loc.key ∧
      UIsFold p.S.matrixRows p.S.kLo p.S.fold.index.v (TabX ρ p err eM rank tab d.loc.key)
        (List.ofFn gam) (uOf d.loc m) := by
  have hN := (near_iff ρ p d m tab e' err eM rank).1 hnear
  have hfc : (fun x : Fin (2 ^ p.S.fold.index.code.logN) => foldCol ρ p d tab x.val) =
      Cb.foldAll gam (tabF ρ p.S.fold.index tab) := funext fun x => foldCol_eq ρ p d tab gam hg x
  rw [hfc] at hN
  have hR := recRow_of_all ρ p d m err eM rank gam hg hi hfit hrec
  have hW : ¬ (ixOf ρ p.S.fold err eM rank).Wrong (tabF ρ p.S.fold.index tab)
      (seedsFn ρ p.S.fold.index d.loc.key,
        recOf p.S.fold.index fun k => ρ.val (d.loc.key.record.getD k zeroE)) gam
      (fullOf p.S.fold (uOf d.loc m)) := fun hw => hnb ⟨_, hN, hR, hw⟩
  unfold Cb.LdIx.Wrong at hW
  push Not at hW
  obtain ⟨U, hU, hmsg⟩ := hW
  refine ⟨by unfold DecX; rw [hU]; rfl, ?_⟩
  intro k hk
  have hkl : k < p.S.fold.index.code.ell :=
    Nat.lt_of_lt_of_le hk (Nat.le_trans hroom (Nat.sub_le _ _))
  have e := congrFun hmsg ⟨k, hkl⟩
  have eL : (ixOf ρ p.S.fold err eM rank).msg (fullOf p.S.fold (uOf d.loc m)) ⟨k, hkl⟩ =
      uOf d.loc m k := rfl
  rw [eL] at e
  rw [e]
  unfold Cb.foldV
  rw [sum_bits]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eqK_ofFn]
  unfold TabX
  rw [hU]
  show _ = _ * (if h : k < p.S.fold.index.code.ell then
    U (bitsOf p.S.fold.index.v r, ⟨k, h⟩) else 0)
  rw [dif_pos hkl]
  rfl

variable {W : Type} {F : Frame}

/-- **The law of "LIN point" with the key's sort of lost points the library's.** -/
theorem point_goodInX (rg : W → Words GE) (wv : W → Nat → GE) (Pin : St × F.E.Str → W → Prop)
    (Prm Prm' : St × F.E.Str → Prop) (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (g : Nat → GE) (e' : Nat) (base : Nat) (d : RDT)
    {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin P.par.S.fold.index.code.ell ⊕ Fin P.par.S.fold.index.code.r → GE) → Nat)
    (ef e : Nat)
    (he : ef * Fintype.card GE ^ P.par.S.kLo +
      P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1) ≤ e)
    (hkey : ∀ a : St × F.E.Str, Prm a → cnt (BadX OnBytes.Model.Reading.gl P.par err eM rank e'
      (tabOf a.2) a.1.loc.key) ≤ ef)
    (hi : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hfit : ∀ a : St × F.E.Str, Prm a → a.1.loc.key.fits P.par.S.fold.index = true)
    (c1 : Carries (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e) Pin Prm Prm')
    (hdetV : ∀ (x : St × F.E.Str) w w', Prm x → Pin x w → Pin x w' → wv w = wv w') :
    (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e).GoodIn
      (fun a => Prm a) (fun a => (∃ d0, H1 P.par d0 a.1) ∧ Prm' a)
      (fun a w => Pin a w ∧
        DecX OnBytes.Model.Reading.gl P.par err eM rank (tabOf a.2) a.1.loc.key ∧
        VIs P.par.S g
          (TabX OnBytes.Model.Reading.gl P.par err eM rank (tabOf a.2) a.1.loc.key) (wv w))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) ∧
          DotUAt P.par.S g (withNext P.par a.1).loc (rg w) (wv w))) :=
  point_goodIn rg wv Pin Prm Prm' P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS g e' base d hd
    (fun a => BadX OnBytes.Model.Reading.gl P.par err eM rank e' (tabOf a.2) a.1.loc.key)
    (fun a => TabX OnBytes.Model.Reading.gl P.par err eM rank (tabOf a.2) a.1.loc.key)
    (fun a => DecX OnBytes.Model.Reading.gl P.par err eM rank (tabOf a.2) a.1.loc.key) ef e he
    hkey
    (fun a x m gam ha hnb hg hk _ hnear hrec => by
      have h := good_of_notBad OnBytes.Model.Reading.gl P.par err eM rank e' (tabOf a.2) x m gam
        hi hroom (by rw [hk]; exact hfit a ha) (by rw [hk]; exact hnb) hg hnear hrec
      rw [hk] at h
      exact h)
    c1 hdetV

/-- **The same, with the count of the bad points asked as the library has it**: at every table and
record without a collision at the record's seed no more than ef points are bad; and beside Prm the
stored table has no collision at the key's seeds. -/
theorem point_goodInY (rg : W → Words GE) (wv : W → Nat → GE) (Pin : St × F.E.Str → W → Prop)
    (Prm Prm' : St × F.E.Str → Prop) (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) (g : Nat → GE) (e' : Nat) (base : Nat) (d : RDT)
    {ns a0 : Nat} (hd : SendsDraws (toRD d) ns P.par.S.kCol 0 a0) (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin P.par.S.fold.index.code.ell ⊕ Fin P.par.S.fold.index.code.r → GE) → Nat)
    (ef e : Nat)
    (he : ef * Fintype.card GE ^ P.par.S.kLo +
      P.par.S.kCol * Fintype.card GE ^ (P.par.S.kCol - 1) ≤ e)
    (hbad : ∀ f rec,
      ¬ (ixOf OnBytes.Model.Reading.gl P.par.S.fold err eM rank).Coll f rec.1 →
      cnt ((ixOf OnBytes.Model.Reading.gl P.par.S.fold err eM rank).Bad f rec e') ≤ ef)
    (hcoll : ∀ a : St × F.E.Str, Prm a →
      ¬ (ixOf OnBytes.Model.Reading.gl P.par.S.fold err eM rank).Coll
        (tabF OnBytes.Model.Reading.gl P.par.S.fold.index (tabOf a.2))
        (seedsFn OnBytes.Model.Reading.gl P.par.S.fold.index a.1.loc.key))
    (hi : P.par.S.fold.index.ok = true)
    (hroom : P.par.S.matrixRows * 2 ^ P.par.S.kLo ≤ P.par.S.fold.index.plain)
    (hfit : ∀ a : St × F.E.Str, Prm a → a.1.loc.key.fits P.par.S.fold.index = true)
    (c1 : Carries (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e) Pin Prm Prm')
    (hdetV : ∀ (x : St × F.E.Str) w w', Prm x → Pin x w → Pin x w' → wv w = wv w') :
    (vecPiece (W := W) (F := F) b1 base d P.par.S.kCol e).GoodIn
      (fun a => Prm a) (fun a => (∃ d0, H1 P.par d0 a.1) ∧ Prm' a)
      (fun a w => Pin a w ∧
        DecX OnBytes.Model.Reading.gl P.par err eM rank (tabOf a.2) a.1.loc.key ∧
        VIs P.par.S g
          (TabX OnBytes.Model.Reading.gl P.par err eM rank (tabOf a.2) a.1.loc.key) (wv w))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) ∧
          DotUAt P.par.S g (withNext P.par a.1).loc (rg w) (wv w))) :=
  point_goodInX rg wv Pin Prm Prm' P b1 b2 b3 b4 b5 b6 b7 b8 hbl hS g e' base d hd err eM rank ef e
    he
    (fun a ha => hbad _ _ (hcoll a ha)) hi hroom hfit c1 hdetV

end Desc.K14.Law
