-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/KeysLettersHead.lean: CONDITIONAL.

What is here. THE KEY VECTORS OF THE LOOKUP's CALLER, AT A STATE BEHIND THE STEP of the member of
the feed-forward layers' own rounds (sub-protocol K4), IN THE LETTERS OF WHAT THE HEARING RETURNED.
The thread's item on the lookup's keys speaks of the caller's key vectors at the public data pubAt
X (m / stepOf X) and at the entries that the caller reads off the script's witness (layMu).
Law/W/FootB1.lean's field b1 speaks of the library's keyVec at the returned environment's layout,
scales and group, at matrices Mm and at the small input's weights. keyVec_stand says that the two
are one vector at each of the eight calls: one call of forK_lay_at
(Johnson/Road/K4/C/KeysLetters.lean), with its ties on the shape, the scales, the layout, the group
and the number of a group's layers paid at the state, and the tie on the weights by layers_of_tie
(Law/W/LayersTie.lean).

  `group_head`     the group of segment m, under h.
  `keyVec_stand`   the title's sentence.

Not shown here. THE TIE ON THE WEIGHTS (tieW: K4LayersTieAt) AND THE TIE ON THE MATRICES (hM) ARE
HYPOTHESES: no example of tieW is known. That a state behind the step exists: at a thread none of
whose steps accepts there is none. What the item says, or that it holds. h: the library's own
hypothesis on the public files; THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE. By a walk of
the import lines that stops unopened at Johnson/Goal/ the closure meets modules of that folder,
through Johnson/Road/K4/RefInScope.lean and what Law/W/FullHead.lean imports: no definition of what
the honest side sends, keeps or draws may name anything here.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LayersTie
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FullHead
import Johnson.Desc.ProofFile.Honest.K4.Law.W.FieldsAtStand
import Johnson.Road.K4.C.KeysLetters
import Johnson.Road.K4.RefInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road (Mats sclOf cellsOf cellsAt admitted_of_layout)
open OnBytes.Road.K4 (refPub_in_scope)
open OnBytes.Road.K4.C (forK_lay_at)
open OnBytes.Maker (WholeD)
open Inst.Model (tbRef)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (keyVec layerR)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.First.Look (pubAt stepOf layLay matsOfE)
open VerifiableInference.Desc.Sound (MsgT MsgQ)
open VerifiableInference.OnPublicFiles (layMu)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **The group of segment m.** CONDITIONAL: on h and Lh. -/
theorem group_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    m / stepOf (P5J.At.X Zp) = g := by
  obtain ⟨_, HL, -⟩ := (refPub_in_scope h.scope h.reads h.pubOne Lh.lt).lines x.2.hp Lh.hp
  have L := HL (P5J.At.X Zp).layers.tokv
  have es : (P5J.At.X Zp).y.h = Verify.layerShape (P5J.At.X Zp).P :=
    (admitted_of_layout L.hy L.S.p3).shape
  have e4 : (P5J.At.X Zp).p4 = true := by
    show (P5J.At.X Zp).y.h.p4 = true
    rw [es]
    exact L.h4
  have hs : (if (P5J.At.X Zp).p4 = true then 2 else 1) = 2 := by
    rw [e4]
    rfl
  show m / (if (P5J.At.X Zp).p4 = true then 2 else 1) = g
  rw [hs, Lh.seg]
  omega

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **THE CALLER's KEY VECTORS AT A STATE BEHIND THE MEMBER's STEP, IN THE RETURNED LETTERS.** xl:
the lookup's place at the segment. d: a continuation of the challenges heard. CONDITIONAL: on h, Lh,
hQ, Zs, tieW and hM. -/
theorem keyVec_stand {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {p : Par} {blk : Block TS ProofFile.Cl} {own : List (ℕ × ℕ)}
    {rdOf : WtF → ℕ × ℕ → MsgQ} {c : Coins Bk} {s s' : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X'}
    {cols : List VerifiableInference.Desc.OpenedColumn} {A' : VerifiableInference.Desc.K9.Part} {o : Own}
    (Zs : K4Stand (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k cells
      weights tokens look Qp p blk own rdOf c s mm E ds y cols s' A' o)
    {xl : VerifiableInference.Desc.First.Look.Place}
    (tieW : K4LayersTieAt Q weights xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf
      h.𝔇.l3.nr h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW g c mm)
    (d : List Fmt.Drawn) {Mm : Mats Cb.Gl.E}
    (hM : matsOfE (layMu xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
      h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
      (Q.wit c mm.st.input (mm.st.heard ++ d))) = Mm) (cc : Fin 8) :
    Cb.Fo.forK Cb.Gl.E
        (layLay (pubAt (P5J.At.X Zp) (m / stepOf (P5J.At.X Zp))) xl.fs xl.lm xl.F.next xl.ns
          x.2.hp.tl h.𝔇.l3.nr h.𝔇.l3.nc) ()
        (Cb.Fo.zext (layMu xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr
          h.𝔇.l3.nc (fun j => h.𝔇.l3.seat xl.link false j.1) h.𝔇.l3.arr h.𝔇.l3.msgW
          (Q.wit c mm.st.input (mm.st.heard ++ d)))) cc.val =
      keyVec (scl := sclOf (Verify.layerShape (P5J.At.X Zp).P) o.v.sc o.v.g o.v.y.Lam) DF
        (cellsOf DF (cellsAt o.v.y Mm)) tbRef (o.v.g * o.v.y.Lam)
        (fun l => layerR DF.P kRef
          (wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w)
          (o.v.g * o.v.y.Lam + l)) cc := by
  obtain ⟨eY, eS, eG⟩ := pub_is Lh hQ
  have Fu := fullAt_stand Zs eY eS (lam_head h)
  have eg : o.v.g = g := Fu.grp.trans eG
  exact forK_lay_at xl.fs xl.lm xl.F.next xl.ns x.2.hp.tl h.𝔇.l3.nr h.𝔇.l3.nc _ rfl Fu.sc.symm
    Fu.lay.symm ((group_head h Lh).trans eg.symm) Fu.lam hM
    (fun l => by
      rw [eg]
      exact layers_of_tie tieW Qp cells tokens (look Qp) d l) cc

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.group_head
#print axioms ProofFile.Honest.K4.W.keyVec_stand
