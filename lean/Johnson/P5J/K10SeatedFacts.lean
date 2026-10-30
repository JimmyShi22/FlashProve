-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10SeatedFacts.lean: AT THE CLOSED CONSTANT, AT A LINK l BELOW 25: THE SMALL JOINS
BETWEEN THE HYPOTHESES OF K10's DEBT AT A LINK (`AtMgA.K10Seated`, K10LawSeated.lean, beside this
file) AND WHAT `k10_exists_link` (K10ExistsLink.lean) TAKES. Statements and proofs: calls.

  `k10_hM_l`, `k10_hZ_l`: the two sentences on the codes that stand in the typed group's type, at
    `At.cs Zp`: by `hMSub`, `hZSub` (GroupSub.lean) and `AtMg.codes_full`.
  `k10_hQ_l`: Q.k = (gsAt l).k: from the debt's two hypotheses on the group in front g0 and
    `gsAt_ok`.
  `k10_rounds_l`: the sub-protocol b at `ixK10 l` declares the rounds of the kind at THE PLAN's Q:
    `k10_rounds_sit` names some link, place and Q for b; they are these (the place's
    link is the link: `k10_place`; `k9At` and `k10Par` are functions).
  `k10_rows_l`: SO Q.rows = nPK + the members' samples' number + nGK (`k10_rows_due`
    with `esOf_length`): `k10_exists_link`'s e at n := Q.rows. `k10_57_l`: Q.rows ≤ 2 ^ 57
    (`hn57_at`).
Limits. Under the head. Nothing on soundness.

-/
import Johnson.P5J.K10ExistsLink
import Johnson.P5J.K10SeatedOfHeavy

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
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts rowSegs)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo K10TwoAsks K10Heavy groupLayK
  SlotNames SbV slV ZV pullOf placeFull closeFrame entries rdK wrK k10_smpNamed)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)
open VerifiableInference.Desc.First.Close (K10FirstTie K10Car K10Last k10_last_of_two namesOf noK10
seatK10 written_of_mem
  linksFull_layout onS_of_rowAsks fa_front_same good_cs
  plan_of_shapes stPub layPub begun_at shapesAre_begun)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt tie_at_laid smpDrawn covered_laid hm_at
  plainDue gensDue numBy esOf esOf_nodup esOf_all pSseed esOf_length k10_rows_due hn57_at)
open VerifiableInference.Desc.First.Close (hMSub hZSub kind kLay kbAt)
open VerifiableInference.Desc.ReqLit (shapeFull)
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

theorem k10_hM_l (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) :
    ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).C := by
  rw [h.toAtMg.codes_full]
  exact hMSub (loAt l) (written_of_mem (loAt_mem l hl)) (gsAt l) (gsAt_ok l hl).1

theorem k10_hZ_l (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25) :
    ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z := by
  rw [h.toAtMg.codes_full]
  exact hZSub (loAt l) (written_of_mem (loAt_mem l hl)) (gsAt l) (gsAt_ok l hl).1

theorem k10_hQ_l (l : ℕ) (hl : l < 25) (Q : Par) (g0 : OnBytes.Params.GroupSize)
    (e1 : Q.k = g0.k)
    (e2 : g0.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l []))) :
    Q.k = (gsAt l).k :=
  e1.trans (e2.trans (gsAt_ok l hl).2.symm)

/-- The sub-protocol at K10's number of link l declares the rounds of the kind at the plan's Q. -/
theorem k10_rounds_l (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par)
    (h9 : IM.k9At Zp l = some pw) (hQp : ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q)
    (hfl : cF.blocksInOrder[ixK10 l]? = some b) (hBK : b.place.kind = KindName.K10) :
    b.rounds = (kind (Cl := Unit) Q).rounds := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨l', hl', p', Q', h1, h2, h3, h4, -⟩ :=
    LPFK10.k10_rounds_sit h.scope h.reads O b (List.mem_of_getElem? hfl) hBK
  have a1 := (k10_place l hl b.place (k10_place_at h _ b hfl)).1
  have a2 := (k10_place l' hl' b.place (k10_place_at h _ b h3)).1
  obtain rfl : l' = l := Option.some.inj (a2.symm.trans a1)
  obtain rfl : p' = pw := Option.some.inj (h1.symm.trans h9)
  obtain rfl : Q' = Q := Option.some.inj (h2.symm.trans hQp)
  exact h4

/-- **The maker's number of rows is the sum of the three counts.** -/
theorem k10_rows_l (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par)
    (h9 : IM.k9At Zp l = some pw) (hQp : ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q)
    (hfl : cF.blocksInOrder[ixK10 l]? = some b) (hBK : b.place.kind = KindName.K10)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 →
      cMain (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 →
      cMask (At.cs Zp) ((loAt l).get i).1 = (stageOf (gsAt l) 219).Z) :
    Q.rows = nPK Zp cF l +
      (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).length +
      nGK Zp cF l := by
  rw [esOf_length]
  exact k10_rows_due h.scope h.laid hl hfl (k10_rounds_l h l hl pw b Q h9 hQp hfl hBK)

theorem k10_57_l (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 25)
    (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par)
    (h9 : IM.k9At Zp l = some pw) (hQp : ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q)
    (hfl : cF.blocksInOrder[ixK10 l]? = some b) (hBK : b.place.kind = KindName.K10) : Q.rows ≤ 2 ^ 57 :=
  hn57_at h.scope h.laid hl hfl (k10_rounds_l h l hl pw b Q h9 hQp hfl hBK)

end P5J

#print axioms P5J.k10_hM_l
#print axioms P5J.k10_hZ_l
#print axioms P5J.k10_hQ_l
#print axioms P5J.k10_rounds_l
#print axioms P5J.k10_rows_l
#print axioms P5J.k10_57_l
