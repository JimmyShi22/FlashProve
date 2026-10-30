-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadFillG.lean: the kind "lookup" (K3), the lookup on the calls at the
head's link: THE LAYER FOR THE FIELD worth THERE, UNDER A GUARD ON THE WITNESS.

Why. The keys of the head's calls read the output matrix's weights. The lookups' authors' caller
lifts them off two bytes of the stored table's message, whatever the rest of the table is; the
head's kind's authors' law takes them off the index that the witness's cells hold, and 0 where
they hold none. The two agree just where the cells hold an index. No item that is open at these
borders says so; the items of the model's relation bear it as a guard of their own. So the three
sentences on worth at the head's calls are said UNDER THE SAME GUARD, read off the witness:
gd w → the sentence of Johnson/Desc/First/Look/K3HeadFill.lean. Meant: gd w := the witness's cells
hold an index. (Read from the programs, not shown here: that the
committed table's entries are in range is what the key file's own range proof is there to show,
once for each key; the proof file's verifier assumes it.)


Main names:
  `fillK3HeadG X D L adr rq gd Mg`: the layer. `fillHeadG_rest`: it turns no other field.
  `worthHeadG_other`: elsewhere the field is left. `worth_at_headG`: at its place it is the guard
    in front of `fillK3Head`'s sentence.
  `headP_fillG`, `headK_fillG`, `headR_fillG`: `HeadAtTable`'s three fields on worth, at the term.
    (That they have these fields' types: Johnson/Desc/First/Look/K3HeadFillFits.lean.)
  `fillAll_over_headG`: the lookups' authors' whole layer over this one leaves it at its place.

Limits: definitions and unfoldings. gd is a letter. Nothing on soundness by itself; nothing on
hiding.


-/
import Johnson.Desc.First.Look.K3HeadFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider)

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy]

section
variable {P Cells Tok : Type} (X : Verify.Public) (D : Desc.First.Look.Sent)
  (L : K3Letters Cells Tok) (adr : HeadAdr) (rq : P → Desc.Kinds.Head.Request)
  (gd : Desc.Wit Cells Tok MsgT → Prop) (Mg : Meaning P (Desc.Wit Cells Tok MsgT))

/-- **The layer, under the guard.** -/
def fillK3HeadG : Meaning P (Desc.Wit Cells Tok MsgT) :=
  { Mg with
    worth := fun m pc r a y w =>
      if m = headLink X ∧ pc = 3 then gd w → (fillK3Head X D L adr rq Mg).worth m pc r a y w
      else Mg.worth m pc r a y w }

/-- It turns no other field that has code or opens an item. -/
theorem fillHeadG_rest : (fillK3HeadG X D L adr rq gd Mg).pub = Mg.pub ∧
    (fillK3HeadG X D L adr rq gd Mg).pubP = Mg.pubP ∧
    (fillK3HeadG X D L adr rq gd Mg).more = Mg.more ∧
    (fillK3HeadG X D L adr rq gd Mg).inOrder = Mg.inOrder ∧
    (fillK3HeadG X D L adr rq gd Mg).constr = Mg.constr :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- At every other segment or piece the field is left as it was. -/
theorem worthHeadG_other (m pc : ℕ) (h : ¬ (m = headLink X ∧ pc = 3)) (r : String)
    (a : P × Desc.First.S) (y : Strs) (w : Desc.Wit Cells Tok MsgT) :
    (fillK3HeadG X D L adr rq gd Mg).worth m pc r a y w = Mg.worth m pc r a y w :=
  if_neg h

/-- At its place: the guard in front of the sentence. -/
theorem worth_at_headG (r : String) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT) :
    (fillK3HeadG X D L adr rq gd Mg).worth (headLink X) 3 r a y w =
      (gd w → (fillK3Head X D L adr rq Mg).worth (headLink X) 3 r a y w) :=
  if_pos ⟨rfl, rfl⟩

/-- **worthP.** -/
theorem headP_fillG {Cl : Type} (claim : Aff → Cl) {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3HeadG X D L adr rq gd Mg).worth (headLink X) 3 "planes" (z, s) y w)
    (hg : gd w) :
    letI := rq z
    K3WorthPlanes (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm
      x.F.next
      (headNu adr x X.H.tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
        L.msgW) s w :=
  headP_fill X D L adr rq Mg claim hx z s y w
    ((worth_at_headG X D L adr rq gd Mg "planes" (z, s) y w).mp h hg)

/-- **worthK.** -/
theorem headK_fillG {Cl : Type} (claim : Aff → Cl) {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3HeadG X D L adr rq gd Mg).worth (headLink X) 3 "keys" (z, s) y w)
    (hg : gd w) :
    letI := rq z
    ∀ g F', (Desc.K3.seatCalls claim).fork s = some F' →
      (Desc.K3.seatCalls claim).heard s = some g →
      K3OutKeys x.fs x.lm x.F.next
        (headNu adr x X.H.tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
          L.msgW w)
        (forK Cb.Gl.E (headLay adr x.fs x.lm x.F.next x.ns X.H.tl L.nr L.nc) (s.replyTok?.getD 0)
          (zext (layMu x X.H.tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1)
            L.arr L.msgW w))) Reading.gl g F' :=
  headK_fill X D L adr rq Mg claim hx z s y w
    ((worth_at_headG X D L adr rq gd Mg "keys" (z, s) y w).mp h hg)

/-- **worthR.** -/
theorem headR_fillG {Cl : Type} (claim : Aff → Cl) {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3HeadG X D L adr rq gd Mg).worth (headLink X) 3 "rider" (z, s) y w)
    (hg : gd w) :
    letI := rq z
    ∀ g F', (Desc.K3.seatCalls claim).fork s = some F' →
      (Desc.K3.seatCalls claim).heard s = some g →
      K3OutRider (headRider adr x X.H.tl D L.rad L.oW L.wOf L.nr L.nc extNone Unit) x.lm x.F.next
        (s.replyTok?.getD 0)
        (layMs x D L.rad L.oW (fun j => L.seat x.link false j.1) L.arr L.msgW w) g F' :=
  headR_fill X D L adr rq Mg claim hx z s y w
    ((worth_at_headG X D L adr rq gd Mg "rider" (z, s) y w).mp h hg)


/-- The two layers together, at the head's calls. -/
theorem fillAll_over_headG (r : String) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT) :
    (fillK3All X D L (fillK3HeadG X D L adr rq gd Mg)).worth (headLink X) 3 r a y w =
      (fillK3HeadG X D L adr rq gd Mg).worth (headLink X) 3 r a y w :=
  worthK3_head X D L _ r a y w

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.worth_at_headG
#print axioms VerifiableInference.OnPublicFiles.headP_fillG
#print axioms VerifiableInference.OnPublicFiles.headK_fillG
#print axioms VerifiableInference.OnPublicFiles.headR_fillG
#print axioms VerifiableInference.OnPublicFiles.fillAll_over_headG
