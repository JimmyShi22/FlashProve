-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ConstrLettersAtAll.lean: THE THREE LETTERS THROUGH WHICH
THE CONSTRAINTS' SENTENCE OF THE COMPOSED FILLING READS THE VERIFIER's STATE (beside the decoder):
`H.req`, `digitsPart`, `headPart`: AT THE FIRST TABLE's CLOSED CONSTANT (`P5J.AtMgA.𝔇`,
Johnson/P5J/MgAtAll.lean). Three statements with their proofs: by
the make of its closed terms; no step and no promise stands in them. `req_atAll`: `H.req`
  answers alike at two statements with one public part (it is "the request's words read back, else
  a default", off the public part). `dig_atAll`: `digitsPart` names neither the statement nor the
  strings: it goes from any (x', y') to any (x, y). `head_atAll`: `headPart` names no strings, and
  reads the statement through `H.req` and, at one part, through the token of the reply that the
  state has heard: so it goes from x' to x WHERE the public part is one and the heard reply
  (`out.reply`) is one.
WHO CALLS: the premises hreq, hdig, hhead of the tie at the first segment's opening
(`first_tiedR_atBase`, TieGAtBase.lean) and of kind K1's fifty later sendings. What is
not claimed. That the constant's head can be met. Nothing on soundness.
-/
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S)
open P5J (AtMgA)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain S ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **`H.req` reads the public part alone.** -/
theorem req_atAll (h : AtMgA o Z D r Zp Np cF x₀) (x x' : ProofFile.InstPub × S) (h1 : x'.1 = x.1) :
    h.𝔇.H.req x' = h.𝔇.H.req x := by
  show (_root_.Meaning.backReq (P5J.At.reqB x'.1)).getD P5J.At.d₀ =
    (_root_.Meaning.backReq (P5J.At.reqB x.1)).getD P5J.At.d₀
  rw [h1]

/-- **`digitsPart` names neither the statement nor the strings.** -/
theorem dig_atAll (h : AtMgA o Z D r Zp Np cF x₀) (m : ℕ) (x x' : ProofFile.InstPub × S) (y y' : Strs) w
    (h0 : h.𝔇.digitsPart m x' y' w) : h.𝔇.digitsPart m x y w := h0

/-- The heard token hangs on the heard reply alone. -/
theorem tokH_same {P : Type} (x x' : P × S) (hr : x'.2.out.reply = x.2.out.reply) :
    P5J.tokHOf x' = P5J.tokHOf x := by
  unfold P5J.tokHOf P5J.tokOfHeard
  rw [← P5J.replyTok_is_heardTok, ← P5J.replyTok_is_heardTok]
  unfold VerifiableInference.Desc.First.S.replyTok?
  rw [hr]

/-- **`headPart` goes back where the public part and the heard reply are one**: by
`headPartK6_blind` (Johnson/Desc/Kinds/Law/HeadCutsK6.lean). -/
theorem head_atAll (h : AtMgA o Z D r Zp Np cF x₀) (p : P5J.TPart) i (x x' : ProofFile.InstPub × S)
    (y y' : Strs) w (h1 : x'.1 = x.1) (hr : x'.2.out.reply = x.2.out.reply)
    (h0 : h.𝔇.headPart p i x' y' w) : h.𝔇.headPart p i x y w := by
  have e : h.𝔇.headPart p i x' y' w = h.𝔇.headPart p i x y w :=
    VerifiableInference.Desc.Kinds.Head.Law.Came.headPartK6_blind _ _ _ _ _ _ _ _ _ _ _ _ p i x x' y
      y' w (req_atAll h x x' h1) fun _ => tokH_same x x' hr
  rw [← e]
  exact h0

end HashBuild
