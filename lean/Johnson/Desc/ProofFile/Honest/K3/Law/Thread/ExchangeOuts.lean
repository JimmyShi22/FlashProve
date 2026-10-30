-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeOuts.lean: the honest side of the kind "lookup"
(K3): FOR WHAT THE LOOKUP'S ROW OPENS, IN THE FIRST CHAIN'S THREAD'S OWN LETTERS: the fields give
the items of the row's list; and the premises at one witness, under a name for each sort. Structures
of propositions; two theorems with proofs. The thread's sentence itself: ExchangeAll.lean.

  `holds_calls`, `holds_digits`   the four (three) fields give the items of the row's list
  `AtDigits`, `AtAttention`, `AtLayers`   THE PREMISES AT ONE WITNESS v, under one name for each
                     sort: the table's own reading is 0 at the place "zero"; the three sentences
                     on a filling at the table's own reading and key vectors; the reading's mask
                     entries below s.p.first + s.at_.face.slots are a given mask row's; at the
                     calls: the caller's arrays are 0 on their cubes

The field masks of the three structures speaks of every j below s.p.first + s.at_.face.slots: the
slots up to the lookup's last. Of a mask entry from there on it says nothing. See `allOpenings_digitsLookup`,
`all_attention`, `all_layers` (ExchangeAll.lean).




Limits. The lookup on the head's calls is not reached HERE (Honest/K3/Law/Thread/ExchangeHead.lean,
ExchangeHeadAll.lean). The items that the row reads and leaves are not spoken of.
No instance of the three structures is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeWorth
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtBorder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E zeroE)
open OnBytes.Model (Fork HTailF2)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block OpenedColumn Strs Wit)
open VerifiableInference.Desc.First (Meaning Item Numbers)
open VerifiableInference.Desc.First.Look (Sent digAt attAt layAt pubAt planesOk enOf mkOf attLay
  layLay attRider layRider LayPub)
open VerifiableInference.Desc.K9L (dataOf maskOracle)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "pieceOf" => VerifiableInference.Desc.K3.pieceAt
local notation "stepAt" => VerifiableInference.Desc.First.Look.stepOf

/-! ## 1 The fields give the items -/

theorem holds_calls {P W : Type} (N : Numbers) (Mg : Meaning P W) (m pc : Nat) (a : P × FS)
    (y : Strs) (v : W) (h0 : Mg.formsT m pc "objects" a y v) (h1 : Mg.worth m pc "planes" a y v)
    (h2 : Mg.worth m pc "keys" a y v) (h3 : Mg.worth m pc "rider" a y v) :
    ∀ i ∈ [Item.formsT m pc "objects", .worth m pc "planes", .worth m pc "keys",
      .worth m pc "rider"], Item.holds N Mg i a y v := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem holds_digits {P W : Type} (N : Numbers) (Mg : Meaning P W) (m pc : Nat) (a : P × FS)
    (y : Strs) (v : W) (h0 : Mg.forms m pc "objects" a y v) (h1 : Mg.worth m pc "planes" a y v)
    (h2 : Mg.worth m pc "keys" a y v) :
    ∀ i ∈ [Item.forms m pc "objects", .worth m pc "planes", .worth m pc "keys"],
      Item.holds N Mg i a y v := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

/-! ## 2 The premises at one witness -/

section
variable {Cells Tok : Type} (s : Site) (D : Sent) (Lk : K3Letters Cells Tok) (x : PlaceL)
  (tl : HTailF2) (a : Ask) (theta : GE) (heard : List Fmt.Drawn) (mask : Nat → GE)
  (v : Wit Cells Tok MsgT)

/-- **The premises at one witness, at the digits.** -/
structure AtDigits : Prop where
  zero : digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr v .zero = 0
  fills : ∃ L, FillsAt s a L
    (Cb.Fo.forK Cb.Gl.E
      (OnBytes.DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
      (Cb.Fo.zext (digMu x D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr v)))
    (digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr v) theta heard
  masks : ∀ j, j < s.p.first + s.at_.face.slots →
    digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr v (.mask j) = mask j

/-- **The premises at one witness, at attention's calls.** -/
structure AtAttention (A : OnBytes.Attention.Shape) : Prop where
  zero : attNu x A tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v .zero = 0
  fills : ∃ L, FillsAt s a L
    (Cb.Fo.forK Cb.Gl.E (attLay A x.fs x.lm x.F.next x.ns tl) ()
      (Cb.Fo.zext (attMu x tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v)))
    (attNu x A tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v) theta heard
  masks : ∀ j, j < s.p.first + s.at_.face.slots →
    attNu x A tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v (.mask j) = mask j
  cubes : Cb.Rider.OnCubes (attRider x A tl D Lk.rad Iop.extNone Unit).g
    (attRider x A tl D Lk.rad Iop.extNone Unit).f ()
    (attMs x D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v)

/-- **The premises at one witness, at the layers' calls.** -/
structure AtLayers (q : LayPub) : Prop where
  zero : layNu x q tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v .zero = 0
  fills : ∃ L, FillsAt s a L
    (Cb.Fo.forK Cb.Gl.E (layLay q x.fs x.lm x.F.next x.ns tl Lk.nr Lk.nc) ()
      (Cb.Fo.zext (layMu x tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
        (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v)))
    (layNu x q tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v) theta heard
  masks : ∀ j, j < s.p.first + s.at_.face.slots → layNu x q tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v (.mask j) = mask j
  cubes : Cb.Rider.OnCubes
    (layRider x q tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc Iop.extNone Unit).g
    (layRider x q tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc Iop.extNone Unit).f ()
    (layMs x D Lk.rad Lk.oW (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v)

end

#print axioms ProofFile.Honest.K3.Law.Exchange.holds_calls
#print axioms ProofFile.Honest.K3.Law.Exchange.holds_digits
#print axioms ProofFile.Honest.K3.Law.Exchange.AtDigits
#print axioms ProofFile.Honest.K3.Law.Exchange.AtAttention
#print axioms ProofFile.Honest.K3.Law.Exchange.AtLayers

end ProofFile.Honest.K3.Law.Exchange
