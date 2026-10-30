-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/ZetaRead.lean: the written round of "LIN zeta" read as one typed draw of a
point, by the library's own maps of written rounds (OnBytes/Flat/CarrySMaps.lean, CarrySForms.lean);
and with it "LIN zeta" in the form of the rule of composition at the shared chain's own seventh
block, in the library's field, WITHOUT the three premises on the carriage.

  vecMaps d n      the written round d is read as one typed draw of n elements.
  vecMaps_ok       it is as the library asks where d draws n elements and no position.
  shownAt          what the verifier is shown of one written round.
  drawn_shown      the elements that the block reads as drawn are, read in the field, the point that
                   the map reads.
  vecPiece         the piece that holds a block at one written round d: no round laid behind, the
                   identity for its extractor, for its errors the written count that bears e.
  zeta_goodIn7     that piece, at the seventh block and at any e from kRow |K| ^ (kRow - 1) on, has
                   GoodIn between the two borders of "LIN zeta".

What is not claimed. PREMISES LEFT: the written round draws kRow elements and no position
(SendsDraws); and, EACH UNDER THE PROMISE IN FRONT ALONE (On7 and a letter Prm):
at a yes a witness that is pinned behind the block is pinned in front of it,
and a second letter Prm' holds behind; two witnesses pinned by one statement have the same words on
o_omega and on o_u. A block that refuses all has GoodIn too. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.GoodFold
import OnBytes.Flat.CarrySForms
import OnBytes.Slice.RoundsMaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open Iop.IOR (drawRound)

/-- The written round d, read as one typed draw of n elements. -/
def vecMaps (d : RDT) (n : Nat) : Maps [d] [drawRound (Fin n → GE)] :=
  .step (RMap.vec (fun _ => ((), ())) n id) .nil

/-- It is as the library asks. -/
theorem vecMaps_ok {d : RDT} {ns n a : Nat} (h : SendsDraws (toRD d) ns n 0 a) :
    (vecMaps d n).OK :=
  ⟨RMap.vec_ok _ h Function.injective_id, trivial⟩

/-- What the verifier is shown of one written round. -/
def shownAt (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) : Fmt.RoundView :=
  ⟨PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
    (ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩

/-- **The elements that the block reads as drawn are the point that the map reads.** -/
theorem drawn_shown {d : RDT} {ns n a : Nat} (h : SendsDraws (toRD d) ns n 0 a)
    (m : (wT d).Msg) (c : (wT d).Chal) :
    (drawn (noDigest (shownAt d m c))).map OnBytes.Model.Reading.gl.val =
      List.ofFn (gVec n _ (valsOf (toRD d) c)) := by
  have he : (noDigest (shownAt d m c)).drawn.elems = (rvOf (toRD d) (msgRD d m) c).els := rfl
  have hl : (rvOf (toRD d) (msgRD d m) c).els.length = n := by
    have := congrArg List.length (rvOf_els (toRD d) (msgRD d m) c)
    rw [List.length_map, elemsV_length, h.els] at this
    exact this
  have hm : (drawn (noDigest (shownAt d m c))).map OnBytes.Model.Reading.gl.val =
      (rvOf (toRD d) (msgRD d m) c).els.map toE := by
    unfold drawn
    rw [he, List.map_map]
    rfl
  rw [hm, gVec_rvOf (toRD d) (msgRD d m) c n]
  refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_ofFn, ptL]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

/-- What is shown of a stretch of one written round. -/
theorem rvT_one (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) :
    rvT (ckP .two) [d] (m, c, ()) = [shownAt d m c] := rfl

/-- The test of work that the map asks is the stretch's. -/
theorem vecMaps_pass (d : RDT) (n : Nat) (τ : Tr (uLT (ckP .two) [d])) :
    (vecMaps d n).pass τ = passT (ckP .two) [d] (rhoT (ckP .two) [d] τ) := by
  obtain ⟨m, c, τ'⟩ := τ
  rfl

variable {W : Type} {F : Frame} (rw : W → Words GE) (Pin : St × F.E.Str → W → Prop)

/-- The piece that holds a block at one written round that draws n elements: no round is laid
behind; the extractor is the identity; the errors are the written count that bears e. -/
def vecPiece (b : Block St Unit) (base : Nat) (d : RDT) (n e : Nat) :
    Piece (ckP .two) F St Unit W :=
  ⟨b, base, [d], [], fun _ _ w => w, (vecMaps d n).err ((e, ()) : Nat × Unit)⟩

/-- **"LIN zeta" in the form of the rule of composition**, at the chain's own seventh block. e: a
number that is at least kRow |K| ^ (kRow - 1). -/
theorem zeta_goodIn7 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (base : Nat) (d : RDT) {ns a : Nat}
    (hd : SendsDraws (toRD d) ns P.par.S.kRow 0 a) (e : Nat)
    (he : P.par.S.kRow * Fintype.card GE ^ (P.par.S.kRow - 1) ≤ e)
    (Prm Prm' : St × F.E.Str → Prop)
    (hback : ∀ x τ b w, On7 P.par x → Prm x →
      (vecPiece (W := W) (F := F) b7 base d P.par.S.kRow e).ior.red.out x τ = some b →
      Pin b w → Pin x w)
    (hkeep : ∀ x τ b, On7 P.par x → Prm x →
      (vecPiece (W := W) (F := F) b7 base d P.par.S.kRow e).ior.red.out x τ = some b → Prm' b)
    (hdet : ∀ (x : St × F.E.Str) w w', On7 P.par x → Prm x → Pin x w → Pin x w' →
      AgreeOn x.1.loc.oOmega (rw w) (rw w') ∧ AgreeOn x.1.loc.oU.oracle (rw w) (rw w')) :
    (vecPiece (W := W) (F := F) b7 base d P.par.S.kRow e).GoodIn
      (fun x => On7 P.par x ∧ Prm x) (fun x => On8 P.par x ∧ Prm' x)
      (fun x w => Base OnBytes.Model.Reading.gl rw Pin x w ∧
        OmegaCol OnBytes.Model.Reading.gl P.par.S x.1 (rw w))
      (fun x w => Base OnBytes.Model.Reading.gl rw Pin x w ∧
        FoldAt OnBytes.Model.Reading.gl P.par.S x.1 (rw w)) := by
  refine zeta_goodIn OnBytes.Model.Reading.gl rw Pin
    (vecPiece (W := W) (F := F) b7 base d P.par.S.kRow e) P.par
    (zeta_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl) (fun _ _ _ => rfl) Prm Prm' hback hkeep hdet e he
    (fun _ => (vecMaps d P.par.S.kRow).carry)
    (fun _ => (vecMaps d P.par.S.kRow).fits (vecMaps_ok hd) _) ?_
  intro x τ b r7 hout hr
  have ht := piece_tests _ x τ b hout
  simp only [sTests, Bool.and_eq_true] at ht
  have hp : (vecMaps d P.par.S.kRow).pass τ = true := (vecMaps_pass d _ τ).trans ht.1.1
  obtain ⟨m, c, ⟨⟩⟩ := τ
  have hr' : [noDigest (shownAt d m c)] = [r7] := hr
  obtain rfl := (List.cons.inj hr').1
  exact ⟨gVec P.par.S.kRow _ (valsOf (toRD d) c),
    (vecMaps d P.par.S.kRow).tr_of_pass (m, c, ()) hp, drawn_shown hd m c⟩

end Desc.K14.Law
