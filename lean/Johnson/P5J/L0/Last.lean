-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/Last.lean: EIGHT OF THE TOWER's 21 FREE LETTERS (`P5J.Free`, Johnson/P5J/TowerFree.lean)
AS CLOSED TERMS: the last table's two (ML, PLm), the three families of extractors (e₁ e₂ e₃), the two
default witnesses (dW wEnd) and the frame's sample of the key file (rP). The other thirteen and the
one value are Johnson/P5J/L0/Const.lean's [not in this library].

WHICH OF THE EIGHT SAY SOMETHING, AND WHICH ARE IDLE:
  `mlAt`, `plmAt`, `e3At`: THE LAST TABLE's FILES' OWN TERMS, as their law `LLT25.own3_at_top`
    (Johnson/LLT25R/LastTop.lean) concludes, at the letters of the first table's constant. FOUR
    LETTERS OF THE SHARED TABLE's CONSTANT STAY ARGUMENTS HERE (X · oNo · ms₂ · Ns; meant:
    `Sh.X A 12` · `Sh.oNo A` · `Sh.ms A` ·
    `numbersSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) (0, 0) (0, 0)` at A := `Sh.planAt Zp Np F₀`):
    the file that lays the one value fills them. WHY: that constant's cone and the tower's import
    twins of one name (Johnson.Desc.K13.Law.HeldTab | Johnson.HB.LLK13L.HeldTab): this file stands in
    the tower's and the last table's world alone.
    They are read: ML in the last chain's one item of its own, PLm in its promise, e₃ in `EachOwn`.
  `rPAt` (in a file of its own, Johnson/P5J/L0/LastRP.lean [not in this library]: it wants the
    top's files): PINNED BY THE TOP: `VerifierAndGoals.AtTheName.recZ Z`: `proofFileAt_of_rows` hands its two
    letters at that value, and the tower's end reads `front₀ 𝔏.rP`, `join₀ 𝔏.rP`.
  `e1At`, `e2At`: IDLE, the identity. The first chain's pieces stand in the tower's fields with the
    table's one extractor laid over their own (`Piece.withMap`); the shared chain's field
    (`EachLawsBN`) reads a piece's reduction and errors alone; the plain form of the top reads no
    extractor. Johnson/Desc/Sound/ReExtIdle.lean [not in this library] shows the first of these
    three sentences.
  `dWAt` (= wEnd): IDLE, the witness of zeros. No field of the tower asks anything of them.
  Inside e₃ two letters of `extsLast` are idle by its text: `e3At_any`. THE LAST CHAIN's EXTRACTOR LAYS
    NO CELLS: at the piece number 2 it lays the messages and pads of the members `mine3At`; at every
    other piece it hands the witness on as it is.

THE CODES. The first table's constant reads its samples at `At.cs Zp`
(Zp.made.p.chains.proof.first.codes), the two later tables at `(p14At Zp).codes`
(Zp.p.chains.made.sized.proof.codes). The two are NOT one term by unfolding (tried). So the first
table's reader of samples is laid here as `smpNamed` AT THE LATER TABLES' CODES (`smp1At`): no cast.
Whoever calls the last table's law at the tower's meaning owes the equation of the two codes.

Limits. Definitions, and one lemma on two idle letters. No law is paid. Nothing on soundness, nothing
on hiding.
-/
import Johnson.P5J.FourAtMg
import Johnson.LLT25R.LastRowsOpen
import Johnson.LLT25R.LastLayerS
import Johnson.LLT25R.LastSeat
import Johnson.LLT25R.LastRowZero
import Johnson.LLT25R.LastTreeO
import Johnson.LLT25R.LastMine
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.Sound.SmpShared

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J.L0

open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc (Block FileDescription Chain Wit)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Third (firstOfS)
open _root_.Run _root_.Run.PQ
open _root_.Desc.K14 (St)
open ToldDesc (p14At)

variable (o : ProofFile.SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : Chain TS ProofFile.Cl)

/- THE SHARED TABLE's FOUR, AS LETTERS OF THIS FILE: its tests at its last border; who of its members
has which number; its sampled members; its numbers before they are tied to the first table's. -/
variable (X : St → Bool) (oNo : Mem → ℕ) (ms₂ : List Mem) (Ns : NumbersS)

/-- The witnesses of the tower. -/
abbrev W : Type := Wit (CellsM numsFull) At.Tok MsgT

/-- How the tables read the first chain's statement: as it is. -/
abbrev getL (a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) : ProofFile.InstPub × TS := (a.1, a.2)

/-- The first table's reader of samples, at the later tables' codes. -/
def smp1At (a : ProofFile.InstPub × TS) (s : Sending) (i : Fin s.l.length) :
    Option ((Johnson.Pack.sigOf (p14At Zp).codes s.l).om i).Smp :=
  smpNamed (p14At Zp).codes (At.seats Zp) a s i

/-- **ML: the last chain's one item of its own.** -/
def mlAt : MeaningL (F0T o Zp Np cF).S₃ W :=
  ⟨LLT25.rowsOpen (p14At Zp).codes (At.arr Zp) (D.at frS.P.T.a).t₁ (D.at frS.P.T.a).t₂⟩

/-- **PLm: the last table's book-keeping**, with the test on the last chain's own state beside it. The
shared chain has ended where X says yes (meant: the shared table's own tests at its last border). -/
def plmAt : PromMeaningL (F0T o Zp Np cF).S₂ (F0T o Zp Np cF).S₃
    ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) :=
  LLT25.besideS
    (fillAt (p14At Zp) (LLT25.c2 Np).rounds (fun q => firstOfS (getL o Zp Np cF q).2)
      (LLT25.endedX X))
    (LLT25.yTree (p14At Zp).codes (p14At Zp).S)

/-- The last chain's reader of samples: Omega's off the shared chain's state, the others off the
first chain's. -/
def smp3At := LLT25.smpLast (P := (F0T o Zp Np cF).XiPub) (S₁ := (F0T o Zp Np cF).S₁)
  (S₃ := (F0T o Zp Np cF).S₃) (p14At Zp).codes (smp1At Zp)
  (smpSt (p14At Zp).codes oNo stSh) (getL o Zp Np cF) Ns

/-- The members whose pins the last chain's proximity test closes. -/
def mine3At : List Mem :=
  LLT25.mineOf (At.ms Zp Z.lay) ms₂ (At.N Zp cF) Ns

/-- **e₃: the last chain's extractors.** -/
def e3At : (i : ℕ) → (ds : List RDT) →
    (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) × (F0T o Zp Np cF).S₃) ×
      (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₃
        (F0T o Zp Np cF).lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → W → W :=
  extsLast (Tok := At.Tok) (F0T o Zp Np cF) (D.at frS.P.T.a) (p14At Zp).codes (F0T o Zp Np cF)
    (At.arr Zp) (smp3At o Zp Np cF oNo Ns) (fun _ _ => none) At.c₀ (mine3At Z Zp cF ms₂ Ns)

/-- **The two letters of `extsLast` that are laid at "nothing" and at the table of zeros are read by
nobody**: at any other two it is the same family. -/
theorem e3At_any
    (decT : (ℕ → Option (ℕ × List UInt64)) →
      (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × (F0T o Zp Np cF).S₂) × (F0T o Zp Np cF).S₃) →
      Option (CellsM numsFull)) (c₀' : CellsM numsFull) :
    extsLast (Tok := At.Tok) (F0T o Zp Np cF) (D.at frS.P.T.a) (p14At Zp).codes (F0T o Zp Np cF)
      (At.arr Zp) (smp3At o Zp Np cF oNo Ns) decT c₀' (mine3At Z Zp cF ms₂ Ns) = e3At o Z D Zp Np cF oNo ms₂ Ns := rfl

/-- **e₁: idle.** -/
def e1At : (i : ℕ) → (ds : List RDT) → ((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) ×
    (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str →
    _root_.Iop.Tr (uLT (ckP .two) ds) → W → W := fun _ _ _ _ w => w

/-- **e₂: idle.** -/
def e2At : (i : ℕ) → (ds : List RDT) →
    (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) ×
    (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₂ 0).E.Str →
    _root_.Iop.Tr (uLT (ckP .two) ds) → W → W := fun _ _ _ _ w => w

/-- **dW and wEnd: idle: the witness of zeros.** -/
def dWAt : W := ⟨At.c₀, 0, fun _ _ _ _ => 0, fun _ _ _ _ _ => 0⟩

end P5J.L0

#print axioms P5J.L0.e3At_any
