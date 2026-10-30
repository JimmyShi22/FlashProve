-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsW.lean: THE COMMITTED WEIGHTS AS THE TABLE OF JOINTS' PIN ON THE STORED TABLE,
K4's VALUE AND THE CALLER OF THE LOOKUP ON A LAYERS' LINK's CALLS READ THEM: ONE READING IN § 1 (at
Cells := oW.Msg); FROM § 2 ON, AND AT THE END THEOREM (Johnson/Road/K4/K4PinsEnd.lean), THREE, OF
WHICH decT AND enc ARE TWO FREE LETTERS TIED BY NOTHING. The table's letters Cells and decT
(`pinWOf`, `decodesOf`: Johnson/Desc/Sound/MeaningSig.lean) are filled by an oracle message oW of
the library (`Cb.OMsg`): the very letter that the lookup's caller takes as its signature's external
member (Johnson/Desc/First/Look/K3CallerLay.lean). Definitions and theorems, by unfolding. No draw,
no count.

  `decTOf oW strC smpZ`: A GUARDED DECODER: at the stored table's out-of-domain (OOD) sample (our
    files call it the record), as smpZ reads it off the verifier's state: nothing where the word has
    a collision at the sample's seed (`OMsg.Clash`), else the library's decoder with a sample
    (`OMsg.dec`); nothing where smpZ finds no OOD sample. The cells are oW's messages.
  `pinW_lay`: the table's pin on the stored table, at that decoder, gives: smpZ finds an OOD sample
    σ, and `oW.dec (strC y.cell) σ = some w.cells`.
  `decodes_lay`: the table's promise "the stored table decodes", at that decoder, gives: smpZ
    holds a sample σ, and the word has no collision at σ's seed.
  `table_decTOf`: the line table of `RecRides` (Johnson/Road/K4/K4Pins.lean) at that decoder, if
    smpZ reads the same at two states of the verifier with `Rest`.
  `PinPlan.mat_some`: where the tuple holds cells C, `PinPlan.mat` is rc of C.
  `cutW enc wOf nr nc`: the caller's reader of a weight's cell, at the image under enc of the stored
    table's cells; 0 outside nr rows and nc columns. enc : Cells → oW.Msg IS A LETTER: THE TABLE's
    TYPE OF CELLS IS FREE FROM HERE ON (the first part of the file stands at Cells := oW.Msg).
  `mat_lay`: `wOfE (msgLay x tl D rad oW wOf nr nc mm)` is `PinPlan.mat` at
    rc := `cutW enc wOf nr nc`, at a tuple t that holds cells C with `mm none = enc C`.
  `lay_part_W`: at a witness w and a tuple mm of the caller's whose external member is the image of
    w's cells under enc and whose first chain's part is w's own messages, under `SitsIn`: the
    matrices, the mask row below the place's number of slots, and the weights that the caller reads
    are those that K4's value reads off the pinned part of w.

THE TWO SENTENCES THAT `pinW_lay` AND `decodes_lay` CONCLUDE are, at smpW s := smpZ (Zt, s),
strW y := strC (strsOf Fr y).cell, msgW w := w.cells, the second half of `LayPin` and the third
clause of `LayCond` (Johnson/Desc/First/Look/K3LayGoodIn.lean): BY READING: that file is not
imported here.

NEEDS, beside this folder's files: what Johnson/Road/K4/K4PinsLay.lean needs.

OBJECT: none of its own. USER: Johnson/Road/K4/K4PinsPlanes.lean; meant: whoever ties K4's row and
the lookup's row at one meaning. LETTERS, filled by nobody: oW, strC (the stored table's cells read
as oW's word), smpZ (the stored table's OOD sample, as the key file holds it), Cells, enc, wOf, nr,
nc, and those of K4PinsLay.lean.

Limits. K04_law IS NOT PROVED BY THIS. IT IS NOT SHOWN THAT THE REAL STORED TABLE's DECODER IS AN
`OMsg`'s: the library's decoder of a stored table with an OOD sample is another notion (`DecR.dcd`,
OnBytes/Slice/DecoderRec.lean: a table of rows, each with its own answers); no term here makes the
one of the other. IT IS OWED BY WHOEVER WRITES THE STORED TABLE's DECODER AS AN `OMsg` (fills oW,
strC and smpZ). THE GUARD IS "NO COLLISION AT THE SEED"
(two members of the word's list with one answer), which is more than "no two members have the
OOD sample's answers". K4's value cuts the matrix to its own numbers of rows and columns: the two
cuts are one only where nr and nc are these numbers: not asked here.
-/
import Johnson.Road.K4.K4PinsLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open OnBytes.Desc.First.K4 (Rest)
open VerifiableInference.Desc (Wit Strs)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls finOf finOf_some laySg ownPart msgLay
  matsOfE wOfE lyW lyMask)
open VerifiableInference.Desc.Sound (Mem MsgT msgsOf pinWOf decodesOf)

/-! ## 1 The table's decoder, of an oracle message -/

section
variable {P Tok : Type} (oW : Cb.OMsg Cb.Gl.E)
  (strC : (ℕ → Option (ℕ × List UInt64)) → oW.Str) (smpZ : P × S → Option oW.Smp)

open Classical in
/-- **A guarded decoder of the stored table.** -/
def decTOf (c : ℕ → Option (ℕ × List UInt64)) (a : P × S) : Option oW.Msg :=
  (smpZ a).bind fun σ => if oW.Clash (strC c) σ.1 then none else oW.dec (strC c) σ

theorem decTOf_some {c : ℕ → Option (ℕ × List UInt64)} {a : P × S} {C : oW.Msg}
    (h : decTOf oW strC smpZ c a = some C) :
    ∃ σ, smpZ a = some σ ∧ ¬ oW.Clash (strC c) σ.1 ∧ oW.dec (strC c) σ = some C := by
  unfold decTOf at h
  obtain ⟨σ, hσ, h⟩ := Option.bind_eq_some_iff.1 h
  by_cases hc : oW.Clash (strC c) σ.1
  · rw [if_pos hc] at h
    cases h
  · rw [if_neg hc] at h
    exact ⟨σ, hσ, hc, h⟩

/-- **The pin on the stored table** gives: smpZ finds an OOD sample with which the word decodes to
the witness's cells. -/
theorem pinW_lay (a : P × S) (y : Strs) (w : Wit oW.Msg Tok MsgT)
    (h : pinWOf (decTOf oW strC smpZ) a y w) :
    ∃ σ, smpZ a = some σ ∧ oW.dec (strC y.cell) σ = some w.cells := by
  obtain ⟨σ, h1, _, h3⟩ := decTOf_some oW strC smpZ h
  exact ⟨σ, h1, h3⟩

/-- **The promise "the stored table decodes"** gives: smpZ finds an OOD sample at whose seed the
word has no collision. -/
theorem decodes_lay (a : P × S) (y : Strs) (h : decodesOf (decTOf oW strC smpZ) a y) :
    ∃ σ, smpZ a = some σ ∧ ¬ oW.Clash (strC y.cell) σ.1 := by
  obtain ⟨C, hC⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨σ, h1, h2, _⟩ := decTOf_some oW strC smpZ hC
  exact ⟨σ, h1, h2⟩

/-- The line table of `RecRides` at that decoder, if smpZ reads the same at two states of the
  verifier with
`Rest`. -/
theorem table_decTOf (Zt : P) (h : ∀ s s' : S, Rest s s' → smpZ (Zt, s') = smpZ (Zt, s))
    (s s' : S) (c : ℕ → Option (ℕ × List UInt64)) (r : Rest s s') :
    decTOf oW strC smpZ c (Zt, s') = decTOf oW strC smpZ c (Zt, s) := by
  unfold decTOf
  rw [h s s' r]

end

/-! ## 2 The weights that the caller reads are those that K4's value reads -/

/-- Where the tuple holds cells, the committed matrix is rc of them. -/
theorem PinPlan.mat_some {Cells : Type} (A : PinPlan Cells) {t : PinM Cells} {C : Cells}
    (h : t.2 = some C) (r c : ℕ) : A.mat t r c = A.rc C r c := by
  simp only [PinPlan.mat, h]

/-- The caller's reader of a weight's cell, at the image of the stored table's cells under enc; 0
outside nr rows and nc columns. -/
def cutW {oW : Cb.OMsg Cb.Gl.E} {Cells : Type} (enc : Cells → oW.Msg)
    (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (C : Cells) (a b : ℕ) : Cb.Gl.E :=
  if a < nr ∧ b < nc then wOf (enc C) a b else 0

variable (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2) (oW : Cb.OMsg Cb.Gl.E) {Cells : Type}
  (enc : Cells → oW.Msg) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)

/-- **The weights are the caller's**, at a tuple that holds cells whose image under enc is the
caller's external member. -/
theorem mat_lay (mm : (laySg x D rad oW).Msg) (t : PinM Cells) (C : Cells) (h : t.2 = some C)
    (h0 : mm none = enc C) :
    wOfE (msgLay x tl D rad oW wOf nr nc mm) =
      (planAt x D rad seatT (cutW enc wOf nr nc) posI).mat t := by
  funext a b
  rw [PinPlan.mat_some _ h]
  show msgLay x tl D rad oW wOf nr nc mm (lyW x.ns tl nr nc a b) = cutW enc wOf nr nc C a b
  unfold lyW cutW
  rw [← h0]
  by_cases ha : a < nr
  · by_cases hb : b < nc
    · rw [finOf_some ha, finOf_some hb, if_pos ⟨ha, hb⟩]
      rfl
    · have e : finOf nc b = none := dif_neg hb
      rw [finOf_some ha, e, if_neg fun k => hb k.2]
      rfl
  · have e : finOf nr a = none := dif_neg ha
    rw [e, if_neg fun k => ha k.1]
    rfl

/-- **At a witness**: under `SitsIn`, at a tuple of the caller's whose external member is the image
of the witness's cells under enc and whose first chain's part is the witness's own messages:
  matrices, mask row
(below the place's number of slots) and weights. -/
theorem lay_part_W {Tok : Type} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)
    (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m) (w : Wit Cells Tok MsgT)
    (mm : (laySg x D rad oW).Msg) (h0 : mm none = enc w.cells)
    (h : ownPart mm = msgsOf D.codes (sigListCalls D rad x.link) seatT arr w) :
    matsOfE (msgLay x tl D rad oW wOf nr nc mm) =
        (planAt x D rad seatT (cutW enc wOf nr nc) posI).raw tl (partOf D.codes arr ms N m w) ∧
      (∀ j, j < x.ns → msgLay x tl D rad oW wOf nr nc mm (lyMask x.ns tl nr nc j) =
        (planAt x D rad seatT (cutW enc wOf nr nc) posI).mask (partOf D.codes arr ms N m w) j) ∧
      wOfE (msgLay x tl D rad oW wOf nr nc mm) =
        (planAt x D rad seatT (cutW enc wOf nr nc) posI).mat (partOf D.codes arr ms N m w) := by
  obtain ⟨h1, h2⟩ := lay_part x D rad seatT (cutW enc wOf nr nc) posI tl oW wOf nr nc arr ms N m hs
    w
    mm h
  exact ⟨h1, h2, mat_lay x D rad seatT posI tl oW enc wOf nr nc mm _ w.cells rfl h0⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pinW_lay
#print axioms OnBytes.Road.K4.decodes_lay
#print axioms OnBytes.Road.K4.table_decTOf
#print axioms OnBytes.Road.K4.mat_lay
#print axioms OnBytes.Road.K4.lay_part_W
