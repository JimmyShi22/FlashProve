-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10LinkFacts.lean: AT THE CLOSED CONSTANT, AT A LINK l BELOW 25: SIX SMALL FACTS IN THE
FORMS IN WHICH K10's FIRST TIE SPENDS THEM (K10TieLink.lean, beside this file). Statements and
proofs: calls of several theorems.

Why they stand apart. Under the first tie's own goal the tactic `obtain` runs Lean out of its stack,
whatever it opens (found by bisection with probes; `have`, projections, `clear` and `skip` pass
there; why, is not known; rewriting a hypothesis was not tried there). So what must be opened is
opened here, where the goals are small, and the first tie's proof is calls alone.
  `k10_link_is`: K10's place at `ixK10 l` has the link l. `gsAt_ok`: the written row's group in
    front is a written group in front, and its k is the formula's at the list and the flags.
    `k10_corners_l`: so the corners fit at that k.
  `k10_hX_l`: the row asks at link l (`AtMgA.hX_paid`, with l for the place's link).
    `k10_sits_l` (1 ≤ l): `SitsIn` at the link's list and seats (`sitsIn_at`,
    likewise). `k10_five_l`: the five numbers at a statement with `XK h l`
    (`five_of_facts`, by the steps of `AtMgA.hX_at`'s proof).
Limits. Under the head; `k10_sits_l` under `rowsRead Z`; `k10_hX_l` and `k10_five_l` under the
plan's list with `FoldFacts`. Nothing on soundness.

-/
import Johnson.P5J.K10HeavyLink
import Johnson.Desc.First.Link.Law.FiveOfFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo K10TwoAsks K10Heavy groupLayK
  SlotNames SbV slV ZV pullOf placeFull closeFrame entries rdK wrK k10_smpNamed)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)
open VerifiableInference.Desc.First.Close (namesOf noK10 seatK10 linksFull_corners_all link_of_stand
  RowAsks Corners kLay layAt sizesM sizesZ planOf)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt gsAt_front sitsIn_at five_of_facts SitsIn)
open IM (subAt)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option quotPrecheck false in
/-- The first chain's pieces' type. -/
local notation "PC" => Piece (ckP .two) FR (ProofFile.InstPub × TS) ProofFile.Cl
  (Wit (CellsM numsFull) At.Tok MsgT)

set_option quotPrecheck false in
/-- Its statements' type. -/
local notation "ST" => (ProofFile.InstPub × TS) × (Frame.E FR).Str

theorem k10_link_is (l : ℕ) (hl : l < 25) (p : VerifiableInference.Desc.Place)
    (hp : At.ps[ixK10 l]? = some p) : p.link.getD 0 = l := by
  rw [(k10_place l hl p hp).1]
  rfl

theorem gsAt_ok (l : ℕ) (hl : l < 25) :
    gsAt l ∈ Johnson.G.frontFull ∧ (gsAt l).k = kLay (loAt l) (kbW l) := by
  have g := List.all_eq_true.1 gsAt_front l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at g
  exact g

theorem k10_corners_l (l : ℕ) (hl : l < 25) :
    Corners (loAt l) (gsAt l).k (fun i => layAt (sizesM (loAt l) (kbW l)) i.val)
      (fun i => layAt (sizesZ (loAt l)) i.val) (kbW l) := by
  rw [(gsAt_ok l hl).2]
  exact linksFull_corners_all _ (loAt_mem l hl) _

/-- The row asks, with l for the place's link. -/
theorem k10_hX_l (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Ld : Laid)
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (l : ℕ) (hl : l < 25) (p : VerifiableInference.Desc.Place) (hp : At.ps[ixK10 l]? = some p)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) →
      RowAsks (At.cs Zp) (loAt l) (seatK10 (loAt l) (At.pseats Zp) l) (kbW l)
        (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)
        (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ
          (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l))
        (At.N Zp cF) l (oAt (ixK10 l)) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l) a.1 := by
  have t := h.hX_paid Ld hLd Fo l hl p hp hM hZ
  rw [k10_link_is l hl p hp] at t
  exact t

/-- The list's messages sit in the constant's members, and their seats' pins are open. -/
theorem k10_sits_l (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (hrr : rowsRead Z) (l : ℕ)
    (h1 : 1 ≤ l) (hl : l < 25) (p : VerifiableInference.Desc.Place)
    (hp : At.ps[ixK10 l]? = some p) (hK : p.kind = KindName.K10) :
    SitsIn h.𝔇 (At.N Zp cF) (oAt (ixK10 l)) (loAt l) (seatK10 (loAt l) (At.pseats Zp) l) := by
  have e := k10_link_is l hl p hp
  have t := sitsIn_at h hrr hp hK (by rw [e]; exact h1) (by rw [e]; exact hl)
  rw [e] at t
  exact t

/-- The five numbers at a statement with the promise, "reached" and "no mark". -/
theorem k10_five_l (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Ld : Laid)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (l : ℕ) (hl : l < 25) (p : VerifiableInference.Desc.Place) (hp : At.ps[ixK10 l]? = some p)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z)
    (Q : Par) (z : ProofFile.InstPub) (a : TS × (Frame.E FR).Str) (hx : XK h l ((z, a.1), a.2)) :
    (planOf (entries Q) (rdK a.1)).k = (stageOf (gsAt l) 219).h + (stageOf (gsAt l) 219).g ∧
      (planOf (entries Q) (rdK a.1)).h = (stageOf (gsAt l) 219).h ∧
      (∀ G lay, (rdK a.1).2.2.groups[(rdK a.1).2.1.group]? = some G →
        (begun (rdK a.1).2.2 (rdK a.1).2.1.group G).layout (rdK a.1).2.1.group = some lay →
        2 ^ lay.logEll = (stageOf (gsAt l) 219).C.l ∧
          2 ^ lay.logEllZk = (stageOf (gsAt l) 219).Z.l) ∧
      ((rdK a.1).2.2.codes.mask.getD (planOf (entries Q) (rdK a.1)).maskCode default).ell =
        (stageOf (gsAt l) 219).Z.l := by
  obtain ⟨hon, hr, hu'⟩ := hx
  have hu : a.1.failed = none := not_not.1 hu'
  obtain ⟨e1, e2, e3⟩ := k10_place l hl p hp
  have H := h.toAtMg.hinge_all Fo rfl hl ((z, a.1), a.2) hr hu
  have hsh := VerifiableInference.Desc.First.K8.shapeAt_of_onQ (At.N Zp cF) (mgAtAll h) fullLinks
    At.ps (fun a => a) (ixK10 l) ((z, a.1), a.2) hon hu
  rw [hp] at hsh
  unfold VerifiableInference.Desc.First.shapeAt at hsh
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨Lk, hLk⟩ := link_of_stand a.1 (subAt l) (hsh.1.1.trans e2)
  exact five_of_facts Fo ((z, a.1), a.2) hr hu hl p hp e1 e3 Lk hLk h.toAtMg.codes_full rfl
    h.toAtMg.shapeAt_full hM hZ (entries Q) H

end P5J

#print axioms P5J.k10_link_is
#print axioms P5J.gsAt_ok
#print axioms P5J.k10_corners_l
#print axioms P5J.k10_hX_l
#print axioms P5J.k10_sits_l
#print axioms P5J.k10_five_l
