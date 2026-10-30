-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/CoveredBehind.lean: BEHIND AN ACCEPT OF THE SUB-PROTOCOL AT THE OUTPUT HEAD
THE COVERED POSITIONS ARE THERE (Johnson/Desc/First/State.lean: S.covered answers): the premise hcov
of Law/SilentAnswers.lean's four_answer and of Law/PlanesFormsInT.lean. Statements and proofs.

How. S.covered reads the request's words and the heard reply. Law/SilentAnswers.lean's
covered_answers has it from the state's test on the request's words (S.reqOk) and a heard reply
that is an entry of the vocabulary. Where the state's words are the words of a request of the
goals' type (a window of T entries of the vocabulary, r < e ≤ T), that test accepts: so it is a fact
on the public part, not on a reached state.

  toNat_ofNat32    a number below 2^32 comes back from a machine word.
  reqOk_of_words   the test accepts at the words of a well-formed request.
  covered_behind   MAIN.

WHAT IT IS NOT. Implications. Nothing on soundness. PREMISES of covered_behind: the state's words in
front are a request's (hw) · a reply is heard in front, as a token's number (hy), below the
vocabulary's size (hyV) · the plan's T and V are the model's (hT, hV).
LETTERS. Under "there is" in the conclusion: cov: pinned by its equation.

-/
import Johnson.Desc.Kinds.Law.SilentAnswers
import Johnson.Desc.Kinds.Law.K6LedgerAt
import Johnson.Flat.InstanceLaws
import Johnson.Flat.CoveredAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Flat (requestWordsOf)
open VerifiableInference.Desc.First (S)

/-- A number below 2^32 comes back from a machine word. -/
theorem toNat_ofNat32 (n : Nat) (h : n < 2 ^ 32) : (UInt32.ofNat n).toNat = n := by
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- **The state's test on the request's words accepts at the words of a well-formed request.** -/
theorem reqOk_of_words {P : Inst.Model.Params} (x : Inst.Model.Instance P) (s : S)
    (h : s.req = requestWordsOf x) (hT : P.T < 2 ^ 32) (hV : P.V ≤ 2 ^ 32) (hre : x.r < x.e) :
    s.reqOk P.T P.V = true := by
  have hsz : s.req.size = P.T + 2 := by
    rw [h]
    exact OnBytes.Flat.size_requestWordsOf x
  have hrT : s.reqT = P.T := by
    unfold S.reqT
    omega
  have hr : s.rowR = x.r := by
    unfold S.rowR
    rw [hrT, h, OnBytes.Flat.requestWordsOf_r]
    exact toNat_ofNat32 _ (by have := x.rF.isLt; unfold Inst.Model.Instance.r; omega)
  have he : s.rowE = x.e := by
    unfold S.rowE
    rw [hrT, h, OnBytes.Flat.requestWordsOf_e]
    exact toNat_ofNat32 _ (by have := x.e_le; omega)
  have htk : (s.tokv.all fun v => Decidable.decide (v < P.V)) = true := by
    unfold S.tokv
    rw [hrT, h, OnBytes.Flat.tokens_wordsOf, Array.all_eq_true']
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Array.mem_map.1 hv
    obtain ⟨t, rfl⟩ := Array.mem_ofFn.1 hw
    have hlt := (x.prompt t).isLt
    rw [toNat_ofNat32 _ (by omega)]
    exact decide_eq_true hlt
  have hle := x.e_le
  unfold S.reqOk
  rw [hsz, htk, hr, he]
  simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  omega

namespace AtTable

open OnBytes OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.Sound (Piece Frame MsgT)

variable {P Cells Tok : Type} {Wp : OnBytes.Model.Verify.Public} {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)} {l : ℕ}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **BEHIND AN ACCEPT THE COVERED POSITIONS ARE THERE.** a: the state in front; b: behind. -/
theorem covered_behind (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (hb : q.ior.red.out a τ = some b)
    (x : Inst.Model.Instance Inst.Model.ppref) (hre : x.r < x.e)
    (hw : a.1.2.req = requestWordsOf x) (y : ℕ) (hy : a.1.2.replyTok? = some y)
    (hyV : y < Wp.hS.V) (hT : Wp.hS.T = Inst.Model.ppref.T) (hV : Wp.hS.V = Inst.Model.ppref.V) :
    ∃ cov, b.1.2.covered Wp.hS.T Wp.hS.V = .ok cov := by
  obtain ⟨o, F1, X, Q, _, _, _, e⟩ := k6_behind H a b τ hb
  have e1 : b.1.2.req = a.1.2.req := by rw [e]
  have e2 : b.1.2.replyTok? = a.1.2.replyTok? := by rw [e]; rfl
  refine covered_answers Wp.hS.T Wp.hS.V b.1.2 y (e2.trans hy) hyV ?_
  rw [hT, hV]
  exact reqOk_of_words x b.1.2 (e1.trans hw) (by decide) (by decide) hre

end AtTable

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.reqOk_of_words
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.covered_behind
