-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadFill.lean: the kind "lookup" (K3), the lookup on the calls AT THE
HEAD's LINK: its layer of the filling of the table of joints' meaning: the field `worth` at the
head's segment, piece 3. After the pattern of Johnson/Desc/First/Look/K3FillWorth.lean (the lookups'
authors'), which fills the field at the kind's other 49 places and hands the head's calls on.

Main names:
  `worthHead`: what the items worth m 3 "planes", "keys", "rider" say at a place x of the head's
    link: the sentences of `HeadAtTable`'s fields worthP, worthK, worthR
    (Johnson/Desc/First/Look/K3HeadAtTable.lean): the keys and the rider AT THE REPLY THAT THE
    RECORD HAS HEARD.
  `worthK3Head X D L adr rq f`: that, at segment `headLink X`, piece 3, at `headAt X`'s place and
    the public record's own tail; everywhere else: f. rq: the kind's letter "the request", of the
    public part.
  `fillK3Head`: the layer. `fillHead_rest`: it turns no other field.
  `headP_fill`, `headK_fill`, `headR_fill`: the three fields of `HeadAtTable` at that term, for
    every Mg (that they have the fields' types: Johnson/Desc/First/Look/K3HeadFillFits.lean).
    `worthHead_other`: at every other segment or piece the field is left as it was.
  `worthK3_head`, `fillAll_over_head`: the lookups' own field hands the head's calls on: so this
    layer stands beneath theirs.

Limits: Props on a witness: nothing to run. Where the record holds no ledger, or nothing is heard,
each item is true of every witness (Johnson/Top/H/K3Worth.lean's own limit). L, adr and rq are
letters. It fills three of `HeadAtTable`'s 26 fields. THE THREE SENTENCES READ THE STORED TABLE's
MESSAGE (L.msgW w): the table's list of what an item reads must book the cells at these items.
Nothing on soundness; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3KeepsFree
import Johnson.Desc.First.Look.K3FillWorth

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
  (L : K3Letters Cells Tok) (adr : HeadAdr)

/-- The head's arm. -/
def worthHead [Desc.Kinds.Head.Request] (x : Desc.First.Look.Place) (tl : HTailF2) (r : String)
    (s : Desc.First.S) (w : Desc.Wit Cells Tok MsgT) (els : Prop) : Prop :=
  if r = "planes" then
    K3WorthPlanes forkR heardC x.fs x.lm x.F.next
      (headNu adr x tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
        L.msgW) s w
  else if r = "keys" then
    ∀ g F', forkR s = some F' → heardC s = some g →
      K3OutKeys x.fs x.lm x.F.next
        (headNu adr x tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
          L.msgW w)
        (forK Cb.Gl.E (headLay adr x.fs x.lm x.F.next x.ns tl L.nr L.nc) (s.replyTok?.getD 0)
          (zext (layMu x tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
            L.msgW w))) Reading.gl g F'
  else if r = "rider" then
    ∀ g F', forkR s = some F' → heardC s = some g →
      K3OutRider (headRider adr x tl D L.rad L.oW L.wOf L.nr L.nc extNone Unit) x.lm x.F.next
        (s.replyTok?.getD 0)
        (layMs x D L.rad L.oW (fun j => L.seat x.link false j.1) L.arr L.msgW w) g F'
  else els

variable (rq : P → Desc.Kinds.Head.Request)

/-- **THE FIELD worth AT THE HEAD's CALLS**, over whatever says it elsewhere. -/
def worthK3Head
    (f : ℕ → ℕ → String → P × Desc.First.S → Strs → Desc.Wit Cells Tok MsgT → Prop) :
    ℕ → ℕ → String → P × Desc.First.S → Strs → Desc.Wit Cells Tok MsgT → Prop :=
  fun m pc r a y w =>
    if m = headLink X ∧ pc = 3 then
      match Desc.Kinds.Head.Law.headAt X with
      | some x => letI := rq a.1
        worthHead D L adr x X.H.tl r a.2 w (f m pc r a y w)
      | none => f m pc r a y w
    else f m pc r a y w

variable (Mg : Meaning P (Desc.Wit Cells Tok MsgT))

/-- **The layer.** -/
def fillK3Head : Meaning P (Desc.Wit Cells Tok MsgT) :=
  { Mg with worth := worthK3Head X D L adr rq Mg.worth }

theorem fillHead_worth : (fillK3Head X D L adr rq Mg).worth = worthK3Head X D L adr rq Mg.worth :=
  rfl

/-- It turns no other field that has code or opens an item. -/
theorem fillHead_rest : (fillK3Head X D L adr rq Mg).pub = Mg.pub ∧
    (fillK3Head X D L adr rq Mg).pubP = Mg.pubP ∧ (fillK3Head X D L adr rq Mg).more = Mg.more ∧
    (fillK3Head X D L adr rq Mg).inOrder = Mg.inOrder ∧
    (fillK3Head X D L adr rq Mg).constr = Mg.constr :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- At every other segment or piece the field is left as it was. -/
theorem worthHead_other (m pc : ℕ) (h : ¬ (m = headLink X ∧ pc = 3)) (r : String)
    (a : P × Desc.First.S) (y : Strs) (w : Desc.Wit Cells Tok MsgT) :
    (fillK3Head X D L adr rq Mg).worth m pc r a y w = Mg.worth m pc r a y w := by
  show worthK3Head X D L adr rq Mg.worth m pc r a y w = _
  unfold worthK3Head
  rw [if_neg h]

/-- The arm at its place. -/
theorem worth_at_head {x : Desc.First.Look.Place} (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (r : String) (a : P × Desc.First.S) (y : Strs) (w : Desc.Wit Cells Tok MsgT) :
    (fillK3Head X D L adr rq Mg).worth (headLink X) 3 r a y w =
      (letI := rq a.1
       worthHead D L adr x X.H.tl r a.2 w (Mg.worth (headLink X) 3 r a y w)) := by
  show worthK3Head X D L adr rq Mg.worth (headLink X) 3 r a y w = _
  unfold worthK3Head
  rw [if_pos ⟨rfl, rfl⟩, hx]

/-! ## `HeadAtTable`'s three fields on worth, at the term -/

/-- **worthP.** -/
theorem headP_fill {Cl : Type} (claim : Aff → Cl) {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3Head X D L adr rq Mg).worth (headLink X) 3 "planes" (z, s) y w) :
    letI := rq z
    K3WorthPlanes (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard x.fs x.lm
      x.F.next
      (headNu adr x X.H.tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
        L.msgW) s w := by
  rw [worth_at_head X D L adr rq Mg hx] at h
  unfold worthHead at h
  rw [if_pos rfl] at h
  exact h

/-- **worthK.** -/
theorem headK_fill {Cl : Type} (claim : Aff → Cl) {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3Head X D L adr rq Mg).worth (headLink X) 3 "keys" (z, s) y w) :
    letI := rq z
    ∀ g F', (Desc.K3.seatCalls claim).fork s = some F' →
      (Desc.K3.seatCalls claim).heard s = some g →
      K3OutKeys x.fs x.lm x.F.next
        (headNu adr x X.H.tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1) L.arr
          L.msgW w)
        (forK Cb.Gl.E (headLay adr x.fs x.lm x.F.next x.ns X.H.tl L.nr L.nc) (s.replyTok?.getD 0)
          (zext (layMu x X.H.tl D L.rad L.oW L.wOf L.nr L.nc (fun j => L.seat x.link false j.1)
            L.arr L.msgW w))) Reading.gl g F' := by
  rw [worth_at_head X D L adr rq Mg hx] at h
  unfold worthHead at h
  rw [if_neg (by decide), if_pos rfl] at h
  exact h

/-- **worthR.** -/
theorem headR_fill {Cl : Type} (claim : Aff → Cl) {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) (z : P) (s : Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT)
    (h : (fillK3Head X D L adr rq Mg).worth (headLink X) 3 "rider" (z, s) y w) :
    letI := rq z
    ∀ g F', (Desc.K3.seatCalls claim).fork s = some F' →
      (Desc.K3.seatCalls claim).heard s = some g →
      K3OutRider (headRider adr x X.H.tl D L.rad L.oW L.wOf L.nr L.nc extNone Unit) x.lm x.F.next
        (s.replyTok?.getD 0)
        (layMs x D L.rad L.oW (fun j => L.seat x.link false j.1) L.arr L.msgW w) g F' := by
  rw [worth_at_head X D L adr rq Mg hx] at h
  unfold worthHead at h
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl] at h
  exact h

/-! ## How the layer stands with the lookups' own -/

/-- At the head's segment piece 3 is the lookup on the calls. -/
theorem sort_head : k3SortAt X (headLink X) 3 = some false := by
  unfold k3SortAt Desc.K3.pieceAt Desc.K3.isHead headLink
  simp

/-- The layers' reader of places gives nothing at the head's segment. -/
theorem layAt_head : layAt X (headLink X) = none := by
  unfold layAt headLink Desc.First.Look.stepOf
  simp

/-- Attention's reader of places gives nothing there either: the head's number is even where
attention has links of its own. -/
theorem attAt_head : attAt X (headLink X) = none := by
  unfold attAt
  refine if_neg fun h => ?_
  have h2 := h.2
  unfold headLink at h2
  rw [if_pos h.1] at h2
  omega

/-- **THE LOOKUPS' OWN FIELD HANDS THE HEAD's CALLS ON**: so this layer stands BENEATH theirs. -/
theorem worthK3_head
    (f : ℕ → ℕ → String → P × Desc.First.S → Strs → Desc.Wit Cells Tok MsgT → Prop) (r : String)
    (a : P × Desc.First.S) (y : Strs) (w : Desc.Wit Cells Tok MsgT) :
    worthK3 X D L f (headLink X) 3 r a y w = f (headLink X) 3 r a y w := by
  unfold worthK3
  rw [sort_head, attAt_head, layAt_head]

/-- The two layers together, at the head's calls. -/
theorem fillAll_over_head (r : String) (a : P × Desc.First.S) (y : Strs)
    (w : Desc.Wit Cells Tok MsgT) :
    (fillK3All X D L (fillK3Head X D L adr rq Mg)).worth (headLink X) 3 r a y w =
      (fillK3Head X D L adr rq Mg).worth (headLink X) 3 r a y w :=
  worthK3_head X D L _ r a y w

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.attAt_head
#print axioms VerifiableInference.OnPublicFiles.worthK3_head
#print axioms VerifiableInference.OnPublicFiles.fillAll_over_head
#print axioms VerifiableInference.OnPublicFiles.fillHead_rest
#print axioms VerifiableInference.OnPublicFiles.worthHead_other
#print axioms VerifiableInference.OnPublicFiles.worth_at_head
#print axioms VerifiableInference.OnPublicFiles.headP_fill
#print axioms VerifiableInference.OnPublicFiles.headK_fill
#print axioms VerifiableInference.OnPublicFiles.headR_fill
