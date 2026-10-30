-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/BackAtPure.lean: THE FIELD `back` OF TieOwes
(Johnson/Goal/Meaning/SpentAtPlain.lean) PAID AT THE PROOF FILE's OWN DESCRIPTION: at
`ProofFile.fileDescBy` at the carried record, which is what `ProofFile.onlineDescription` makes wherever it makes a
description (`descPure_is`), pulled back to the verifier's instances along
`LPFD.Full.instanceAsPlainRecord`: the very description whose run `LPFD.Full.proofDecisionOfDescription` lays as
the proof file's decision.
  `FP o mk Z A B c`: that description, over pairs (request, record).
  `tokPure t₀`: the token that is read off what the first chain hands on: the first word of what the
    carried record has heard (`S.heard`), as a token; t₀ where nothing was heard or that word is no
    token.
  `asked_instOf`: the asked reply at `instanceAsPlainRecord (x, rec)` is `askedReplyOf (replyBytesOf x.val)`: by
    rfl: THE ONE LINE THAT Johnson/Flat/FinIsCanonical.lean's LIMITS NAME.
  `back_pure`: **where FP's last test says yes at (x, rec) and s₁: that token, put into x without
    its reply, gives x.** By the last test's first conjunct, `fin_is_canonical`,
    `tokOfE_replyOf` and `putReq_glue`.
  `tieOwes_pure`: **TieOwes at FP, at the dictionary's reading `hidBy` with that token, FROM ITS
    FIELD `on` ALONE**: so Lean holds that `back_pure` is the field, to the letter.
  `pubEarly_pure`: one of the rule's other premises there: the public part does not read the reply:
    by rfl.
  `vocab_fits`: the vocabulary has at most 2 ^ 32 tokens: by evaluation.
It reads of the description its last test alone: no block, no chain, no border.
Limits. The field `on` and JoinOwes are not here. Whether a description is made at any files is not
said. Nothing on soundness.
-/
import Johnson.LLT25R.PureIs
import Johnson.Desc.Laid.ProofFull
import Johnson.Goal.Meaning.SpentHears

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Maker OnBytes
open VerifiableInference.Desc (FileDescription Chain)
open VerifiableInference.Desc.First (S)
open LPFD.Full (XF instanceAsPlainRecord)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat SecondSeat Cl fileDescBy startS InstPub)

/-- The proof file's description, over the verifier's instances. -/
def FP (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (B : SecondSeat)
    (c : Chain S Cl) : FileDescription (XF × RecFull) :=
  (fileDescBy o mk Z A B (fun s => s) (startS Z) c).pull instanceAsPlainRecord

/-- The vocabulary has at most 2 ^ 32 tokens. -/
theorem vocab_fits : Inst.Model.ppref.V ≤ 2 ^ 32 := by decide

/-- The asked reply at the verifier's instance. -/
theorem asked_instOf (z : XF × RecFull) :
    (instanceAsPlainRecord z).asked = askedReplyOf (replyBytesOf z.1.val) := rfl

/-- The token that is read off the carried record. -/
def tokOfS (t₀ : Fin Inst.Model.ppref.V) (s : S) : Fin Inst.Model.ppref.V :=
  ((s.heard).map (tokOfE t₀)).getD t₀

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (B : SecondSeat)
  (c : Chain S Cl) (t₀ : Fin Inst.Model.ppref.V)

/-- **The field `back`, at the proof file's own description.** -/
theorem back_pure (x : XF) (rec : RecFull) (s₁ : (FP o mk Z A B c).S₁) (s₂ : (FP o mk Z A B c).S₂)
    (s₃ : (FP o mk Z A B c).S₃) (hf : (FP o mk Z A B c).fin (x, rec) s₁ s₂ s₃ = true) :
    putReq (reqWithoutReply x) (tokOfS t₀ s₁) = x := by
  have h0 : ((s₁ : S).finAsked (instanceAsPlainRecord (x, rec)).asked &&
      (s₁ : S).req == OnBytes.Model.Verify.words32 (instanceAsPlainRecord (x, rec)).pub.request &&
      (A.ended s₂).isSome && B.done s₃) = true := hf
  simp only [Bool.and_eq_true] at h0
  have h1 : (s₁ : S).finAsked (askedReplyOf (replyBytesOf x.val)) = true := h0.1.1.1
  have h2 := fin_is_canonical x.val vocab_fits s₁ h1
  unfold tokOfS
  rw [h2]
  show putReq (reqWithoutReply x) (tokOfE t₀ (replyOf x.val)) = x
  rw [tokOfE_replyOf vocab_fits]
  exact putReq_glue x

/-- **One of the rule's other premises, at the same description**: the public part does not read the
reply. -/
theorem pubEarly_pure (x : XF) (rec : RecFull) :
    (FP o mk Z A B c).pub (reqWithoutReply x, rec) = (FP o mk Z A B c).pub (x, rec) := rfl

section
open OnBytes.Slice _root_.Run _root_.Run.PQ
open _root_.Iop (oneExternalString)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Meaning (Msgs)

variable (N₀ : MatrixNums) (pp : Inst.Model.ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N₀ pp)) (DP : WholeD) (all : List LeftT)
  {X₁ X₂ W : Type} (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all (FP o mk Z A B c) X₁ X₂ W)
  (g : (FP o mk Z A B c).XiPub → (FP o mk Z A B c).S₁ → (FP o mk Z A B c).S₂ →
    (FP o mk Z A B c).S₃ → Bool)
  (Pl : PPlaces (DP.at frS.P.T.a) all ((FP o mk Z A B c).XiPub × (FP o mk Z A B c).S₁)
    (((FP o mk Z A B c).XiPub × (FP o mk Z A B c).S₁) × (FP o mk Z A B c).S₂)
    (((FP o mk Z A B c).XiPub × (FP o mk Z A B c).S₁ × (FP o mk Z A B c).S₂) ×
      (FP o mk Z A B c).S₃))
  (X : OnBytes.Model.Verify.Public) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
  (msgOf : ((FP o mk Z A B c).XiPub × (FP o mk Z A B c).S₁) × (EAll (DP.at frS.P.T.a) all).Str →
    ℕ → Msgs)

/-- **TieOwes AT THE PROOF FILE's OWN DESCRIPTION, FROM ITS FIELD `on` ALONE**: so `back_pure` IS
the field `back`, to the letter, at the dictionary's reading with the token off the carried record.
-/
theorem tieOwes_pure
    (on : ∀ (x : Flat.Req) rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) M,
      (FP o mk Z A B c).okStart (x, rec) = true → (kcReq N₀ pp E).conf.D y rec = some M →
        Pl.on₁ 0 ((atDescFin (FP o mk Z A B c) g T).in₁ (reqWithoutReply x, rec),
          (y, fun _ => []))) :
    TieOwes N₀ pp E DP (FP o mk Z A B c) all T g Pl
      (hidBy N₀ pp E DP (FP o mk Z A B c) all X s seat (fun b => tokOfS t₀ b.1.2) msgOf) :=
  ⟨on, fun x rec s₁ s₂ s₃ _ _ hf => back_pure o mk Z A B c t₀ x rec s₁ s₂ s₃ hf⟩

end

end LLT25

#print axioms LLT25.pubEarly_pure
#print axioms LLT25.tieOwes_pure
#print axioms LLT25.vocab_fits
#print axioms LLT25.asked_instOf
#print axioms LLT25.back_pure
