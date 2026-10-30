-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadReply.lean: the last tie of the request, on the side of the output head: the token
that the prover names as the reply.

The equations of the output head's sub-proof never read the caller's reply. At the last position
they check the token that the prover names: one plain scalar of the head's link. The library's
relation speaks of an instance with one reply y. This file shows what the head's routine does with
that scalar, and what follows if it is the caller's reply.

 1. hear (OnBytes/Model/HeadHeard.lean) takes the token from word c0 of the first plain scalar that
    it is handed, and writes it at the last position of the checked tokens (hear_win). In every run.
 2. If the scalar is ofNat so.y, the caller's reply as an element of the field, the prover's token
    is so.y (ofNat_c0, token_of_reply).
 3. Then the instance made of the request's words and the caller's reply has all that the theorems
    on the head ask of a request: its form, the record ReqFits at both terms at which the library
    reads an instance, and the number of counted positions (request_of_reply).

The one hypothesis. That the plain scalar which hear was handed is the caller's reply. It is a test
of the verifier's, and of one place alone: the block of a proof's first chain compares the reply
received with the caller's (firstBlock in OnBytes/Proof/File.lean). How that test reaches the head's
routine is followed in no file of this library.

Main theorems: replyToken_value, hear_win; ofNat_c0, token_of_reply; coveredOf_y; request_of_reply.

What is not claimed. Nothing on what a proof shows. That a routine succeeds is a hypothesis
throughout. The program does not import this file.
-/
import Johnson.Road.HeadView
import Johnson.Road.HeadSumL
import Johnson.Road.HeadPub

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Reading Fork SubM)

/-! ## The head's routine -/

/-- The token that replyToken returns is word c0 of the first plain scalar: in every run. -/
theorem replyToken_value {plain : Array E} {V y : ℕ} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.Head.replyToken plain V) F C y G D) : y = (plain.getD 0 zeroE).c0.toNat := by
  unfold Model.Head.replyToken at h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨_, _, _, -, h⟩ := bind_ok h
  exact (pure_ok h).1

/-- **The checked tokens that hear returns hold word c0 of the first plain scalar at the last
position**, if that is covered: in every run. -/
theorem hear_win {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    x.win = Model.Head.winOf cov h.T (plain.getD 0 zeroE).c0.toNat := by
  obtain ⟨yTok, F1, C1, F2, C2, g1, F3, C3, Zl, F4, C4, PV, F5, C5, sW, gp, wpl, F6, C6, sPv, omV,
    tV, F7, C7, qN, qH, tN, F8, C8, tH, rs, F9, C9, k1, -, -, -, -, -, -, -, -, -, -, -,
    rfl⟩ := hear_steps hx
  rw [← replyToken_value k1]

/-! ## Words and numbers -/

/-- A number below the prime, made an element of the field, has itself as word c0. -/
theorem ofNat_c0 {y : ℕ} (hy : y < 18446744069414584321) : (Model.ofNat y).c0.toNat = y := by
  show ((y % 18446744069414584321).toUInt64).toNat = y
  rw [Nat.mod_eq_of_lt hy]
  have h64 : y < 2 ^ 64 := by omega
  exact UInt64.toNat_ofNat_of_lt' h64

/-- If the first plain scalar is the number y as an element of the field, the prover's token is
y. -/
theorem token_of_reply {plain : Array E} {y : ℕ} (hy : y < 18446744069414584321)
    (h : plain[0]? = some (Model.ofNat y)) : (plain.getD 0 zeroE).c0.toNat = y := by
  have e : plain.getD 0 zeroE = Model.ofNat y := by
    simp [Array.getD_eq_getD_getElem?, h]
  rw [e]
  exact ofNat_c0 hy

/-! ## The request, whole -/

/-- The first test of coveredOf: the caller's reply is an entry of the vocabulary. -/
theorem coveredOf_y {so : Model.Head.StOwn} {T V : ℕ} {cov : Model.Head.Covered}
    (h : Model.Head.coveredOf so T V = .ok cov) : so.y < V := by
  unfold Model.Head.coveredOf at h
  obtain ⟨e, -⟩ := ok_of_needed h
  exact of_decide_eq_true e

/-- **The instance made of the request's words and the caller's reply has all that the theorems on
the head ask of a request**: if the plain scalar that hear was handed is the caller's reply as an
element of the field. P, Q: the words of the request file and of the reply file. -/
theorem request_of_reply {P Q : Array UInt32} {so : Model.Head.StOwn} {cov : Model.Head.Covered}
    (hs : Model.Head.stFromCall P Q 1024 = .ok so)
    (hc : Model.Head.coveredOf so 1024 202048 = .ok cov) {R : Model.Head.Run} (e1 : R.cov = cov)
    (hlt : R.h.lt = 10) {hp : Model.Head.HPlanH2} {plain : Array E} {F G : Fork} {C D : Ctx}
    (hx : Ok (Model.Head.hear R.h R.L hp R.cov plain) F C R.x G D)
    (hrep : plain[0]? = some (Model.ofNat so.y)) :
    ∃ x : Inst.Model.Instance Inst.Model.ppref, x.r = so.r ∧ x.e = so.e ∧
      (∀ t (ht : t < Inst.Model.ppref.T), (x.prompt ⟨t, ht⟩).val = (P.getD t 0).toNat) ∧
      x.y.val = so.y ∧ Inst.Model.Head3 x ∧ ReqFits R HeadSizes.ref (Cm.reqOf x) ∧
      ∀ pol, ReqFits R HeadSizes.ref (Inst.Model.Head.Req.of pol x) ∧
        (Inst.Model.Head.Req.of pol x).NB = R.cov.hRC := by
  have hy := coveredOf_y hc
  obtain ⟨x, hr, he, hp', hxy⟩ := instance_of_covered hs hc hy
  obtain ⟨q1, q2, q3, -⟩ := stFromCall_ok hs
  have hT : R.h.T = 1024 := by
    show 2 ^ R.h.lt = 1024
    rw [hlt]
  have hw : R.x.win = Model.Head.winOf cov 1024 so.y := by
    rw [hear_win hx, token_of_reply (by omega) hrep, hT, e1]
  obtain ⟨f1, f2⟩ := reqFits_of_instance hs hc e1 hw x hr he hp' hxy
  have k1 : x.r = (so.req.getD 1024 0).toNat := by rw [hr, q2, q1]
  have k2 : x.e = (so.req.getD (1024 + 1) 0).toNat := by rw [he, q3, q1]
  exact ⟨x, hr, he, hp', hxy, head3_of_call hs x hr he hxy, f1,
    fun pol => ⟨f2 pol, nb_of_covered hc e1 k1 k2⟩⟩

#print axioms hear_win
#print axioms request_of_reply

end OnBytes.Road.Hd
