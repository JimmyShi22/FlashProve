-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/FourFactsOfWorthAtStand.lean: THE SMALLNESS TEST, THE HONEST
PROVER's SIDE, AT THE STANDS OF THE HONEST THREAD: AT A STAND, AT ALL 25 SEGMENTS: THE LIBRARY's TWO
SENTENCES "worth" ON THE DIGITS' LOOKUP (`WorthTwo`, Johnson/Desc/First/Link/Law/WorthAtFront.lean)
AND FIVE NAMED PREMISES GIVE THE BUNDLE `FourFacts` (Johnson/Desc/K8/Honest/FourFacts.lean) AT WHAT
IS FIXED BEFORE THE DRAW AND AT THE DATA dataQ own a (rdW v): AT A GENERAL THREAD FROM
`ChainThread`; AND AT THE FRAME's OWN THREAD, THAT OF THE FIRST CHAIN's LETTERS AT THE LIBRARY's
HEAD, AT THE HEAD's DATA's OWN LIST OF WHAT IS SENT AND RADII. Two implications; none of the
library's goals.

`fourFacts_of_worth_of_chain` the scope · the files read · an opening of the description · its test
on its plan · l < 25 · the built segment Xl · ChainThread T b c Z l · Look.digAt Z.p.X l = some (xx,
tlD) · DigOK set xx tlD D rad pp · seatT, arr, own, rdW · ONE OF THE FIVE IN FRONT OF THE STAND:
maskB … = true ⊢ ∀ stand, ∀ a v, K9.atS.get? s = some a → WorthTwo S.fork? heardDig xx tlD D rad
seatT arr s v → the two `OneReader` at rdW v → CellOkR … a → MaskOkR … a → FourFacts tlD pi8 (fixed9
(phiAll tlD ψ) s) (dataQ own a (rdW v)), at every ψ, Lk and p
**`fourFacts_of_worth`** the library's head h · the thread's letters, all free · an opening of the
description at cF · its test on its plan · l < 25 · Xl · Look.digAt (P5J.At.X Zp) l = some (xx, tlD)
· maskB in front, at D := h.𝔇.sent and rad := h.𝔇.l3.rad ⊢ the same end at (lettersHead …).thread
and batchAt P5J.At.links P5J.At.ps l
By: `fourFactsAt_of_worth` (Johnson/Desc/K8/Honest/FourFactsOfWorth.lean) at the reach that a stand
gives: `wrapEnd_at_stand` (ValuesOfChain.lean) · `fourFacts_of_at` (FourFactsAt.lean) · the
opening's own field W (Bs.G₀.W = Z.p.X) · `chainThread_at_head` (ChainThreadAtHead.lean) · DigOK at
the head's data: Q38.digOK_at_head (Johnson/HB/LLHARD/Q38E/TiesAtHead.lean).
THE FIVE NAMED PREMISES ARE MOVED, NOT PAID: two `OneReader`: the witness's messages are what rdW v
reads (at no term for rdW: at any with these two; the library's own instances are the readers
seatTab and rdC) · maskB (on public data) · `CellOkR` and `MaskOkR` at the state's part a. NONE IS
SHOWN HERE OF ANY STATE OR WITNESS. THE TWO `OneReader` ARE ASKED AT THE ONE WITNESS v IN HAND,
BEHIND THE STAND. seatT and arr are free letters: that they be the data's own is for whoever calls
it.
THE PROMISE Ok OF A SORT OF SEGMENT IS NOT AMONG THE PREMISES. THE WITNESS v IS TIED TO THE STAND BY
NOTHING BUT `WorthTwo` AND THE `OneReader`. v IS OF THE GENERAL TYPE Wit Cells Tok MsgT: that the
frame's thread's own type of witnesses unfolds to an instance of it is not set before Lean here.
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
one line. The sign 𝔇 is the name of a field of the library's
head, as the library's own files write it.
Limits. NO MEMBER: THAT THE THREAD HOLDS AT ANY RUN, THAT A STAND EXISTS, OR THAT THE FIVE AND
`WorthTwo` CAN HOLD TOGETHER AT ONE, IS NOT SHOWN: where they cannot, all is idle. THE LIBRARY's
HEAD IS A PREMISE OF THE SECOND. THE FULL SIZE ALONE, and the format's second hash function alone. It stands
over reading copies of the frame's, the batching's and other kinds' files, which are not handed in
with it, and over files that are no part of the library. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ValuesOfChain
import Johnson.Desc.ProofFile.Honest.K8.ChainThreadAtHead
import Johnson.Desc.K8.Honest.FourFactsOfWorth
import Johnson.HB.LLHARD.Q38E.TiesAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.OnPublicFiles (CellOkR MaskOkR cellAddr maskAddr)
open VerifiableInference.Desc.First.Att.P (OneReader ReadMsgOf)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ msgsOf)
open VerifiableInference.Desc.K9L (fixed9)
open VerifiableInference.Desc.PhiAll (phiAll)
open VerifiableInference.Desc.LinkJoin (batchAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)
open ProofFile.Honest.K9 (BatStand)

section
variable {V W X Pb : Type} {Bk : ProverCoinCounts} {Lk : Link S Claim} {p : Desc.K9.Where}
  {T : Thread Bk S Claim V W X Pb} {b : ℕ}
  {P : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At a stand of a thread under the one named premise, at all 25 segments: the two sentences
"worth" and five named premises give the bundle.** -/
theorem fourFacts_of_worth_of_chain {Cells Tok β : Type} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (Ch : ChainThread T b c Z l)
    {xx : First.Look.Place} {tlD : HTailF2} (hd : Look.digAt Z.p.X l = some (xx, tlD))
    {set : Params.Setting} {pp : ℕ} {D : Sent} {rad : OracleShape → ℕ}
    (HD : DigOK set xx tlD D rad pp) (seatT : Fin (digList xx D rad).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (own : List (ℕ × ℕ)) (rdW : Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (hB : maskB D (digList xx D rad) xx.link xx.arrays.ns = true)
    (ψ : S → β) :
    ∀ κ s m En ds y cols s' x z G₁, BatStand Lk p T b κ s m En ds y cols s' x z G₁ →
      ∀ a v, Desc.K9.atS.get? s = some a →
        LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD D rad seatT arr s v →
        OneReader (ReadMsgOf (cellAddr tlD) (seatOf D xx.link)) D.codes (digList xx D rad)
          seatT (msgsOf D.codes (digList xx D rad) seatT arr v) (rdW v) →
        OneReader (ReadMsgOf (maskAddr xx.arrays.ns) (seatOf D xx.link)) D.codes
          (digList xx D rad) seatT (msgsOf D.codes (digList xx D rad) seatT arr v) (rdW v) →
        CellOkR xx tlD D rad seatT own a → MaskOkR xx D rad seatT own a →
        FourFacts tlD LinkJoin.pi8 (fixed9 (phiAll tlD ψ) s) (dataQ own a (rdW v)) := by
  intro κ s m En ds y cols s' x z G₁ hSt a v ha hW hc hm C M
  obtain ⟨q, r⟩ := wrapEnd_at_stand Ch hSt
  have hd' : Look.digAt Bs.G₀.W l = some (xx, tlD) := by
    rw [O.W]
    exact hd
  exact fourFacts_of_at tlD LinkJoin.pi8 _ _
    (fourFactsAt_of_worth hS hR O hOk hl e3 r hd' HD seatT arr own (rdW v) v hc hm hB ha C M hW ψ)

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Desc.Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Lk : Link S Claim} {p : Desc.K9.Where}

/-- **AT THE FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD, AT ALL 25 SEGMENTS, AT THE DATA's OWN LIST
OF WHAT IS SENT AND RADII.** -/
theorem fourFacts_of_worth {Cells Tok β : Type}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    {xx : First.Look.Place} {tlD : HTailF2}
    (hd : Look.digAt (P5J.At.X Zp) l = some (xx, tlD))
    (seatT : Fin (digList xx h.𝔇.sent h.𝔇.l3.rad).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (own : List (ℕ × ℕ)) (rdW : Wit Cells Tok MsgT → ℕ × ℕ → MsgQ)
    (hB : maskB h.𝔇.sent (digList xx h.𝔇.sent h.𝔇.l3.rad) xx.link xx.arrays.ns = true)
    (ψ : S → β) :
    ∀ κ s m En ds y cols s' x' z G₁,
      BatStand Lk p (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps l) κ s m En ds y cols s' x' z G₁ →
      ∀ a v, Desc.K9.atS.get? s = some a →
        LinkJoin.WorthTwo S.fork? LinkJoin.heardDig xx tlD h.𝔇.sent h.𝔇.l3.rad seatT arr s v →
        OneReader (ReadMsgOf (cellAddr tlD) (seatOf h.𝔇.sent xx.link)) h.𝔇.sent.codes
          (digList xx h.𝔇.sent h.𝔇.l3.rad) seatT
          (msgsOf h.𝔇.sent.codes (digList xx h.𝔇.sent h.𝔇.l3.rad) seatT arr v) (rdW v) →
        OneReader (ReadMsgOf (maskAddr xx.arrays.ns) (seatOf h.𝔇.sent xx.link))
          h.𝔇.sent.codes (digList xx h.𝔇.sent h.𝔇.l3.rad) seatT
          (msgsOf h.𝔇.sent.codes (digList xx h.𝔇.sent h.𝔇.l3.rad) seatT arr v) (rdW v) →
        CellOkR xx tlD h.𝔇.sent h.𝔇.l3.rad seatT own a →
        MaskOkR xx h.𝔇.sent h.𝔇.l3.rad seatT own a →
        FourFacts tlD LinkJoin.pi8 (fixed9 (phiAll tlD ψ) s) (dataQ own a (rdW v)) :=
  fourFacts_of_worth_of_chain h.scope h.reads O hOk hl e3
    (chainThread_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hl) hd
    (Q38.digOK_at_head h (by omega) hd) seatT arr own rdW hB ψ

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.fourFacts_of_worth_of_chain
#print axioms ProofFile.Honest.K8.fourFacts_of_worth
