-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/TokPublic.lean: CONDITIONAL.

What is here. The hypothesis hTok of `emb_head` (Law/W/EmbHead.lean), brought down to A SENTENCE ON
THE PUBLIC INSTANCE ALONE. hTok compares the tokens that the honest side's reader `tokens` reads
with the prompt of the request as the library makes it of the public instance, the state and the
witness. That request's prompt hangs on the instance's request bytes alone: the library's reader of
the request (`P5J.At.H`, Johnson/P5J/LettersAt.lean) reads neither the state nor the witness, and
putting the witness's token in leaves the prompt (the library's `tokX_putReq`). So hTok follows, at
every state, witness and continuation, from `TokensArePrompt tokens xi`: at every position the
reader's token is the token of the prompt that the library decodes from the instance's request
bytes. Each proof is a call.

  `req_public`   the prompt's tokens of the request as the library makes it are those of the request
      that is decoded from the instance's bytes.
  `TokensArePrompt`   THE PUBLIC SENTENCE. A definition.
  `tok_head`   **hTok, in its own text.**

Not shown here. h: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a proposition on
the public files Z, the public part Zp and the first chain cF. THAT `TokensArePrompt` HOLDS OF ANY
READER AND INSTANCE: it is a hypothesis on the parameter `tokens`, which whoever fills the honest
side's parameters lays; Law/W/TokOfBytes.lean has it at the lot's own reader where the instance's
request bytes decode. WHERE THE INSTANCE's REQUEST BYTES ARE NO WELL-FORMED REQUEST's THE LIBRARY's
READER ANSWERS A DEFAULT, THE FIRST REQUEST (`OnBytes.Flat.firstReq`), WITHOUT A WORD:
`TokensArePrompt` then ties the reader to that default's prompt. Nothing is said of the state's own
tokens (`K4TokensTieAt`, Law/ScriptAt.lean: another hypothesis). The side library AtFullSide proves,
with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Of h together with hP
no example is known to us. THE FULL SIZE ALONE, and the format's second hash function alone
(`OnBytes.secondHashFunction`). Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. BOTH
STATEMENTS CALL A STATEMENT OF A FILE UNDER Johnson/Goal/ (`Meaning.tokX_putReq`,
Johnson/Goal/Meaning/RowLocal.lean, which the library's Johnson/P5J/ConstrNoToken.lean imports). A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.EmbHead
import Johnson.P5J.ConstrNoToken

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h. **The prompt's tokens hang on the instance's request bytes alone.** pub: a
public instance. s: any state. t: any token. -/
theorem req_public (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (pub : ProofFile.InstPub) (s : TS)
    (t : Fin ppref.V) :
    Cm.Seg.tokX (h.𝔇.put (h.𝔇.H.req (pub, s)) t).val =
      Cm.Seg.tokX ((Meaning.backReq pub.request).getD OnBytes.Flat.firstReq).val :=
  Meaning.tokX_putReq ((Meaning.backReq pub.request).getD OnBytes.Flat.firstReq) t

/-- **THE PUBLIC SENTENCE**: at every position the reader's token is the token of the prompt that
the library decodes from the instance's request bytes. This defines a hypothesis; the definition
claims nothing. -/
def TokensArePrompt (tokens : ProofFile.Inst → Array Nat) (xi : ProofFile.Inst) : Prop :=
  ∀ q, q < 2 ^ DF.lT → (tokens xi).getD q 0 =
    Cm.Seg.tokX ((Meaning.backReq xi.pub.request).getD OnBytes.Flat.firstReq).val q

/-- CONDITIONAL: on h and hP. **hTok, IN ITS OWN TEXT**, at every state s, run's coins c and
continuation d. -/
theorem tok_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Tr X' : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub} (c : Coins Bk) (s : TS)
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} (hP : TokensArePrompt tokens mm.st.input.x) :
    ∀ d q, q < 2 ^ DF.lT →
      (k4Wit Qp cells weights tokens (look Qp) mm.st.input).tokv.getD q 0 =
        Cm.Seg.tokX
          (h.𝔇.put (h.𝔇.H.req (mm.st.input.x.pub, s))
            (h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).tok).val q := by
  intro d q hq
  rw [req_public h]
  exact hP q hq

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.req_public
#print axioms ProofFile.Honest.K4.W.tok_head
