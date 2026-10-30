-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BordersU.lean: the border in front of "send o_u", and the seven blocks from
"send o_u" to "SPLIT" as one row of the rule of composition.

In front of the sending of o_u the record does not yet note o_u's number and layout. The three
claims that read o_u (near, RecAll, DotU) are said there OF THE MESSAGE TO COME: the next number of
the statement, with the layout of the public shape at the statement's codes (withNext).
  withNext        the record with o_u noted as the message to come.
  NearAt.of_same, RecAll.of_same, DotUAt.of_same   what the three claims read of the small record.
  H1              "LIN point" has said yes and has led to this record; two codes.
  sendU_goodIn    **"send o_u"** in the form of the rule of composition, by the sending kind's
                  general law: in front: H1 and Prm; Base and the three claims of the message to
                  come. Behind: border 0 of the table (Johnson/Desc/K14/Law/Borders.lean).
  eachGoodIn_shift   a row from border i on is a row from border i + 1 on of the tables moved by 1.
  histC, claimsC  the table with the new border in front.
  row2to8         **the seven blocks are one row**, given the row of the six.

What is not claimed. "LIN point" stands in front of this row and has no law here. The premises of
the sending kind's general law at "send o_u" stay; so do, EACH UNDER THE PROMISE IN FRONT ALONE (H1
and Prm): at its yes the pin goes back; with the new sampled messages sealed the next border's
letter holds behind. The promise has a letter of its own at each border. Pin, Prm, g, wv are
letters. No member is shown. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.K1 (IsSend sendPiece send_goodIn Sealed sampledAt shapeAt shapesOf
  condPort errPort)
open VerifiableInference.Desc.Sound (Frame Piece EachGoodIn)
open _root_.Run.PQ (CK)

/-- The record with o_u noted as the message to come. -/
def withNext (p : Par) (d : St) : St :=
  { d with loc := { d.loc with
      oU := ⟨d.st.oracles.size, vectorLay d.st.codes p.S.fold.u p.S.fold.rowsHigh⟩ } }

/-- What "near" reads of the small record. -/
theorem NearAt.of_same {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) {p : Par} {d d' : St}
    {m : Words K} {tab : Nat → List UInt64} {e' : Nat} (hp : d'.loc.psiSh = d.loc.psiSh)
    (hu : d'.loc.oU = d.loc.oU) (h : NearAt ρ p d' m tab e') : NearAt ρ p d m tab e' := by
  unfold NearAt LocAt weights gamma at h ⊢
  rw [hp, hu] at h
  exact h

/-- What RecAll reads. -/
theorem RecAll.of_same {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) {p : Par} {d d' : St}
    {m : Words K} (hp : d'.loc.psiSh = d.loc.psiSh) (hu : d'.loc.oU = d.loc.oU)
    (hk : d'.loc.key = d.loc.key) (h : RecAll ρ p d' m) : RecAll ρ p d m := by
  unfold RecAll RecAt weights gamma at h ⊢
  rw [hp, hu, hk] at h
  exact h

/-- What DotU reads. -/
theorem DotUAt.of_same {S : LinShape} {g : Nat → GE} {l l' : Lin} {m : Words GE} {V : Nat → GE}
    (hp : l'.psiSh = l.psiSh) (hu : l'.oU = l.oU) (h : DotUAt S g l' m V) : DotUAt S g l m V := by
  unfold DotUAt uOf at h ⊢
  rw [hp, hu] at h
  exact h

/-- "LIN point" has said yes and has led to this record; two codes. -/
def H1 (p : Par) (d0 d1 : St) : Prop :=
  p.S.sharedSplitNeeded = true ∧ ∃ rs1, linPoint p d0 rs1 = some d1

variable {W : Type} {F : Frame}

/-- A row from border i on is a row from border i + 1 on of the tables moved by 1. -/
theorem eachGoodIn_shift {S Cl : Type} {C : CK} (on : Nat → S × F.E.Str → Prop)
    (R : Nat → S × F.E.Str → W → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (i : Nat), EachGoodIn on R i l →
      EachGoodIn (fun j => on (j - 1)) (fun j => R (j - 1)) (i + 1) l
  | [], _, _ => trivial
  | _ :: l, i, h => ⟨h.1, eachGoodIn_shift on R l (i + 1) h.2⟩

/-- The history at border i of the longer table. -/
def histC (p : Par) : Nat → St × F.E.Str → Prop
  | 0 => fun a => ∃ d0, H1 p d0 a.1
  | i + 1 => histB p i

/-- The claims at border i of the longer table. -/
def claimsC (p : Par) (e' : Nat) (g : Nat → GE) : Nat → St × F.E.Str → Words GE → (Nat → GE) → Prop
  | 0 => fun a m V => NearAt OnBytes.Model.Reading.gl p (withNext p a.1) m (tabOf a.2) e' ∧
      RecAll OnBytes.Model.Reading.gl p (withNext p a.1) m ∧
      DotUAt p.S g (withNext p a.1).loc m V
  | i + 1 => claimsB p e' g i

variable (rg : W → Words GE) (wv : W → Nat → GE) (Pin : St × F.E.Str → W → Prop)

/-- **"send o_u" in the form of the rule of composition.** Prm, Prm': the letters of the promise in
front of the block and behind it. -/
theorem sendU_goodIn (Prm Prm' : St × F.E.Str → Prop) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (g : Nat → GE) (e' : Nat)
    (sentU : Array OracleNotice) (hU : withU P.S = some sentU) (rad : Nat → Nat)
    (hC : condPort (parK1 P 2 "o_u and the first mask" sentU) rad = true)
    (h1 : (parK1 P 2 "o_u and the first mask" sentU).seeds = 1)
    (base : Nat) (d₁ d₂ : RDT) (hp : PlainDraws (Fmt.dsOf d₁.entry d₁.kind))
    (hE : nE (Fmt.dsOf d₁.entry d₁.kind) =
      (parK1 P 2 "o_u and the first mask" sentU).coordinates + 1)
    (hP : nP (Fmt.dsOf d₁.entry d₁.kind) = 0)
    (hz : IsNZ (Fmt.dsOf d₁.entry d₁.kind)
      (parK1 P 2 "o_u and the first mask" sentU).coordinates)
    (hl : d₁.entry.logN ≤ 64) (e : Nat)
    (he : errPort (parK1 P 2 "o_u and the first mask" sentU) rad ≤ e)
    (fOf : F.E.Str → ∀ k, (Johnson.Pack.portOmZ
      (parK1 P 2 "o_u and the first mask" sentU).codes
      (shapeAt (parK1 P 2 "o_u and the first mask" sentU) k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (Johnson.Pack.portOmZ
      (parK1 P 2 "o_u and the first mask" sentU).codes
      (shapeAt (parK1 P 2 "o_u and the first mask" sentU) k) (rad k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b2 base d₁ d₂
      (parK1 P 2 "o_u and the first mask" sentU).coordinates e).ior.imp y τ) = fIn y τ.1)
    (back2 : ∀ a τ b w, (∃ d0, H1 P.par d0 a.1) → Prm a →
      (sendPiece (W := W) (F := F) b2 base d₁ d₂
        (parK1 P 2 "o_u and the first mask" sentU).coordinates e).ior.red.out a τ = some b →
      Pin b w → Pin a w)
    (prm2 : ∀ a τ b, (∃ d0, H1 P.par d0 a.1) → Prm a →
      (sendPiece (W := W) (F := F) b2 base d₁ d₂
        (parK1 P 2 "o_u and the first mask" sentU).coordinates e).ior.red.out a τ = some b →
      (∀ k, sampledAt (parK1 P 2 "o_u and the first mask" sentU) k →
        Sealed (parK1 P 2 "o_u and the first mask" sentU).codes
          (shapeAt (parK1 P 2 "o_u and the first mask" sentU) k) (rad k.val) (fOf b.2 k) b.1.st
          (b.1.st.oracles.size -
            (shapesOf (parK1 P 2 "o_u and the first mask" sentU)).length + k.val)) → Prm' b) :
    (sendPiece (W := W) (F := F) b2 base d₁ d₂
      (parK1 P 2 "o_u and the first mask" sentU).coordinates e).GoodIn
      (fun a => (∃ d0, H1 P.par d0 a.1) ∧ Prm a) (fun a => (∃ d0, H2 P.par d0 a.1) ∧ Prm' a)
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) ∧
          DotUAt P.par.S g (withNext P.par a.1).loc (rg w) (wv w)))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par a.1 (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl P.par a.1 (rg w) ∧
          DotUAt P.par.S g a.1.loc (rg w) (wv w))) := by
  obtain ⟨⟨sentU', hU', hs2⟩, _⟩ := send_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl : sentU' = sentU := Option.some.inj (hU'.symm.trans hU)
  obtain ⟨sentU'', hU'', is2, _⟩ := isSend_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl : sentU'' = sentU' := Option.some.inj (hU''.symm.trans hU)
  have yes2 : ∀ a τ b, (sendPiece (W := W) (F := F) b2 base d₁ d₂
      (parK1 P 2 "o_u and the first mask" sentU'').coordinates e).ior.red.out a τ = some b →
      b.2 = (sendPiece (W := W) (F := F) b2 base d₁ d₂
        (parK1 P 2 "o_u and the first mask" sentU'').coordinates e).ior.imp a.2 τ ∧
      ∃ ft ids c1 c2, recvP ft a.1 sentU'' = some (ids, c1) ∧ Onward c1 c2 ∧
        c2.loc = c1.loc ∧ behindU P.par c2 ids = some b.1 := by
    intro a τ b hout
    obtain ⟨hy, gs, hd⟩ := piece_yes _ a τ b hout
    exact ⟨hy, hs2 _ _ gs _ hd⟩
  refine goodIn_weave _ _ _ _ _ _ _ _ _
    (send_goodIn (parK1 P 2 "o_u and the first mask" sentU'') rad hC h1 b2
      (fun s : St => s.st) is2 base d₁ d₂ hp hE hP hz hl e he fOf fIn hf
      (fun a => (∃ d0, H1 P.par d0 a.1) ∧ Prm a) (fun b => ∃ d0, H2 P.par d0 b.1)
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl P.par (withNext P.par a.1) (rg w) ∧
          DotUAt P.par.S g (withNext P.par a.1).loc (rg w) (wv w)))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl P.par a.1 (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl P.par a.1 (rg w) ∧
          DotUAt P.par.S g a.1.loc (rg w) (wv w)))
      (fun a τ x ha hout => ?_) (fun a τ x w ha hout hw => ?_))
    (fun a ha => ha) (fun a τ b ha hout hb => ⟨hb.1, prm2 a τ b ha.1 ha.2 hout hb.2⟩)
    (fun a τ b w _ _ _ hw => hw) (fun a τ b w _ _ _ _ hR => hR)
  · obtain ⟨⟨d0, hS, rs1, k1⟩, _⟩ := ha
    obtain ⟨_, ft, ids, c1, c2, rU, cU, cUl, k2⟩ := yes2 a τ x hout
    exact ⟨d0, hS, a.1, c1, c2, rs1, ft, sentU'', ids, k1, hU, rU, cU, cUl, k2⟩
  · obtain ⟨hy, ft, ids, c1, c2, rU, cU, cUl, k2⟩ := yes2 a τ x hout
    obtain ⟨o1, l1⟩ := onward_recvP ft a.1 c1 _ ids rU
    obtain ⟨s2, o, mask, ho, l2⟩ := behindU_inv P.par c2 x.1 ids k2
    obtain ⟨nU, sU0, _⟩ := withU_first P.S sentU'' hU
    obtain ⟨eo, _⟩ := recvP_first ft a.1 c1 sentU'' ids rU nU sU0 o ho
    have on : Onward a.1 x.1 := (o1.trans cU).trans (Onward.of_st s2)
    have hc : c2.st.codes = a.1.st.codes := (o1.trans cU).grows.1
    have l : x.1.loc = { a.1.loc with
        oU := ⟨a.1.st.oracles.size, vectorLay a.1.st.codes P.par.S.fold.u P.par.S.fold.rowsHigh⟩,
        firstMask := mask } := by rw [l2, cUl, l1, eo, hc]
    obtain ⟨⟨hpin, hUh, hOh⟩, hnear, hrec, hdot⟩ := hw
    have hgU : x.1.loc.gU = a.1.loc.gU := by rw [l]
    have hgO : x.1.loc.gOmega = a.1.loc.gOmega := by rw [l]
    have ep : x.1.loc.psiSh = (withNext P.par a.1).loc.psiSh := by rw [l]; rfl
    have eu : x.1.loc.oU = (withNext P.par a.1).loc.oU := by rw [l]; rfl
    have ek : x.1.loc.key = (withNext P.par a.1).loc.key := by rw [l]; rfl
    rw [hy, tabOf_imp] at hnear
    refine ⟨⟨back2 a τ x w ha.1 ha.2 hout hpin, ?_, ?_⟩, NearAt.of_same _ ep eu hnear,
      RecAll.of_same _ ep eu ek hrec, DotUAt.of_same ep eu hdot⟩
    · rw [← hgU]; exact hUh.back _ on
    · rw [← hgO]; exact hOh.back _ on

/-- **The seven blocks from "send o_u" to "SPLIT" are one row**, given the row of the six. -/
theorem row2to8 (Prm : Nat → St × F.E.Str → Prop) (p : Par) (e' : Nat) (g : Nat → GE)
    (p2 : Piece (ckP .two) F St Unit W) (l : List (Piece (ckP .two) F St Unit W))
    (h2 : p2.GoodIn (fun a => (∃ d0, H1 p d0 a.1) ∧ Prm 0 a)
      (fun a => (∃ d0, H2 p d0 a.1) ∧ Prm 1 a)
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl p (withNext p a.1) (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl p (withNext p a.1) (rg w) ∧
          DotUAt p.S g (withNext p a.1).loc (rg w) (wv w)))
      (fun a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        (NearAt OnBytes.Model.Reading.gl p a.1 (rg w) (tabOf a.2) e' ∧
          RecAll OnBytes.Model.Reading.gl p a.1 (rg w) ∧ DotUAt p.S g a.1.loc (rg w) (wv w))))
    (h : EachGoodIn (fun i a => histB p i a ∧ Prm (i + 1) a)
      (fun i a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        claimsB p e' g i a (rg w) (wv w)) 0 l) :
    EachGoodIn (fun i a => histC p i a ∧ Prm i a)
      (fun i a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
        claimsC p e' g i a (rg w) (wv w)) 0 (p2 :: l) := by
  refine ⟨h2, ?_⟩
  have hs := eachGoodIn_shift _ _ l 0 h
  have key : ∀ (l : List (Piece (ckP .two) F St Unit W)) (i : Nat),
      EachGoodIn (fun j a => histB p (j - 1) a ∧ Prm (j - 1 + 1) a)
        (fun j a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
          claimsB p e' g (j - 1) a (rg w) (wv w)) (i + 1) l →
      EachGoodIn (fun i a => histC p i a ∧ Prm i a)
        (fun i a w => Base OnBytes.Model.Reading.gl rg Pin a w ∧
          claimsC p e' g i a (rg w) (wv w)) (i + 1) l := by
    intro l
    induction l with
    | nil => exact fun _ _ => trivial
    | cons q l ih => exact fun i hq => ⟨hq.1, ih (i + 1) hq.2⟩
  exact key l 0 hs

end Desc.K14.Law
