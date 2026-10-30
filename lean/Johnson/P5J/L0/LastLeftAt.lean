-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/L0/LastLeftAt.lean: `AtMgA.LastLeft` (Johnson/P5J/L0/LastFreeT.lean) WITH ITS FOUR LETTERS LAID AS
TERMS OF THE HEAD (dB :: dt and r as the last table's files name them; Ld by this file's own term):
  dB :: dt := `l3At`: the third piece's stretch of the last chain's written rounds (the left side of
    `PlanOk₃`'s own field stretch, at the join's letters). NO DEFAULT: where that list is empty
    `LastLeftAt` is False.
  r := `H2K.Member.rWFull` · Ld := `ldAt`: `laidOfChain` at the made proof chain's sendings.
    `ldAt` IS THIS FILE's OWN TERM FOR laidOfChain Z.made.proof.1's value in scope.
    THAT IT IS THE Ld
    AT WHICH hRc AND hP ARE PAID IS SHOWN BY NOBODY. (Where this and
    lean/THEOREM.md differ, the page holds.) WHERE `laidOfChain` GIVES NOTHING `ldAt`
    IS THE EMPTY LAYING, IN SILENCE: hRc and hP then speak of that empty laying.
  `AtMgA.LastLeftAt`, `AtMgA.leads3_of_leftAt`: what is left of the last chain's field at the value, with no
    letter; the field from it.
Limits. THE FULL SIZE ALONE. A call: none of the five fields is paid; NO MEMBER is known. Nothing on
soundness, nothing on hiding.
-/
import Johnson.P5J.L0.LastFreeT

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Road OnBytes.RunA
open Iop Prob _root_.Run _root_.Run.PQ
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (ModelPart Item Numbers)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The third piece's stretch of the last chain's written rounds.** -/
def L0.l3At (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) : List RDT :=
  ds₂ (D.at frS.P.T.a).ds₃
    (held (P := (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × St) (c0 Zp))
    (held (P := (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × St) (c1 Np))
    (held (P := (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ × St) (c2 Np))

/-- **The proof chain's sendings, laid.** The empty laying where `laidOfChain` gives nothing. -/
def L0.ldAt (Zp : ProofFile.Pub) : VerifiableInference.Desc.K12.Door.Laid :=
  (VerifiableInference.Desc.K12.Door.laidOfChain Zp.made.proof.1).getD {}

/-- **WHAT IS LEFT OF THE LAST CHAIN's FIELD AT THE VALUE: NO LETTER.** -/
def AtMgA.LastLeftAt (h : AtMgA o Z D r' Zp Np cF x) : Prop :=
  match L0.l3At o D Zp Np cF with
  | [] => False
  | dB :: dt => h.LastLeft dB dt H2K.Member.rWFull (L0.ldAt Zp)

/-- **THE LAST CHAIN's FIELD AT THE VALUE, FROM IT.** -/
theorem AtMgA.leads3_of_leftAt (h : AtMgA o Z D r' Zp Np cF x) (L : h.LastLeftAt) :
    L0.Leads3 o D Zp Np cF (h.toAtMg.mq h.𝔇) h.toAtMg.rc h.free := by
  unfold AtMgA.LastLeftAt at L
  cases e : L0.l3At o D Zp Np cF with
  | nil => rw [e] at L; exact L.elim
  | cons dB dt => rw [e] at L; exact h.leads3_of_left L

end P5J

#print axioms P5J.AtMgA.leads3_of_leftAt
