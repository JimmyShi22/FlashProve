-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReplyEnds.lean: UNDER THE HEAD P5J.AtMgA: THE REPLY's SEAT ALONG THE PROOF
FILE's OWN FIRST CHAIN, BY NUMBER: member 338 alone stands at a place of the kind K7; behind its yes
a token lies in the seat; every other member leaves the seat. So the covered positions (S.covered)
can be made behind member 338's yes, where the state's own test on the request holds in front, and
they stay what they are at every later member. A joining of laws; one closed fact on the written
list of places, and a control beside it, are evaluated by the kernel.

  1 `place_at`: the member at number n stands at the n-th place of the written list (the library's
    LPFK9.blockPlaces_full, Johnson/LPFK9R/SubsFull.lean). `k7_just_338`: that list has 358 places,
    and number 338 alone is of the kind K7: by the kernel. `k7_control`: the same test at 337 says
    no. **`not_k7_at`**: so a member at a number other than 338 is not of that kind.
    **`reply_kept_but`**, **`covered_kept_but`**: ReplyKept.lean's two laws, by number.
  2 `ofNat_of_token`: a token of a vocabulary that is no larger than the field's prime is the
    natural number that ofNat lays. **`covered_of_parts`**: GENERAL: S.reqOk T V holds, a token of V
    lies in the reply's seat, V is at most the prime: then S.covered T V returns.
  3 **`reply_laid_at`**: behind every yes of the step of member 338 a token of the head's
    vocabulary lies in the reply's seat (IM.k7_sits, Johnson/IMR/FirstSeats.lean; joined_iff_K7,
    k7Block_iff, ReplyAtHead.lean; reply_iff, Johnson/Desc/First/Shape/HeadFront.lean).
    **`covered_behind_338`**: so, where S.reqOk T V held in front, at V the head's vocabulary's
    size, at most the prime: S.covered T V returns behind.

Limits. THAT MEMBER 338 SAYS YES AT ANY STATE IS NOT SHOWN: that is where the prover's reply is
tested. "V is at most the prime" is a premise on a public number. That the numbers at which each
later member asks S.covered are this T and V is not shown here. One member at a time. That the head
has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`,
Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of public files, in
a side library. At the format's second hash function. Nothing on soundness, completeness or hiding.

-/
import Johnson.AtFull.Shape.ReplyKept
import Johnson.AtFull.Shape.ReplyAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain KindName step_iff)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.Sound (linksFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 Which member hears the reply -/

/-- The member at number n stands at the n-th place of the written list. -/
theorem place_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {n : Nat} {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[n]? = some blk) : (flatPlacesOf linksFull true)[n]? = some blk.place := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : cF.blocksInOrder.map (·.place) = flatPlacesOf linksFull true :=
    LPFK9.blockPlaces_full h.scope h.reads O
  rw [← e, List.getElem?_map, hb]
  rfl

/-- The test: in a list of places number n alone is of the kind K7. -/
def k7JustB (ps : List VerifiableInference.Desc.Place) (n : Nat) : Bool :=
  ps.zipIdx.all fun p => (p.1.kind == KindName.K7) == (p.2 == n)

/-- The written list has 358 places, and number 338 alone is of the kind K7. -/
theorem k7_just_338 : ((flatPlacesOf linksFull true).length == 358 &&
    k7JustB (flatPlacesOf linksFull true) 338) = true := by decide +kernel

/-- A control: the same test at 337 says no. -/
theorem k7_control : k7JustB (flatPlacesOf linksFull true) 337 = false := by decide +kernel

/-- **A member at a number other than 338 does not stand at a place of the kind K7.** -/
theorem not_k7_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {n : Nat} {blk : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[n]? = some blk) (hn : n ≠ 338) : blk.place.kind ≠ KindName.K7 := by
  have hp := place_at h hb
  have hm : (blk.place, n) ∈ (flatPlacesOf linksFull true).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact hp
  have q := List.all_eq_true.1 (Bool.and_eq_true _ _ ▸ k7_just_338).2 _ hm
  intro hk
  have q' : ((blk.place.kind == KindName.K7) == (n == 338)) = true := q
  rw [hk] at q'
  simp [hn] at q'

/-- **Every member but number 338 leaves the reply's seat.** -/
theorem reply_kept_but (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n : Nat) (hn : n ≠ 338) :
    ∀ blk, cF.blocksInOrder[n]? = some blk → ∀ ft s rs cols s' k, blk.step ft s rs cols = .ok (s', k) →
      s'.out.reply = s.out.reply :=
  fun blk hb => reply_kept_at h n blk hb (not_k7_at h hb hn)

/-- **At every member but number 338 the covered positions are behind a yes what they were in
front.** -/
theorem covered_kept_but (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (n T V : Nat)
    (hn : n ≠ 338) :
    ∀ blk, cF.blocksInOrder[n]? = some blk → ∀ ft s rs cols s' k, blk.step ft s rs cols = .ok (s', k) →
      s'.covered T V = s.covered T V :=
  fun blk hb => covered_kept_at h n T V blk hb (not_k7_at h hb hn)

/-! ## 2 General: from the request's test and a token to the covered positions -/

/-- A token of a vocabulary no larger than the prime is the natural number that ofNat lays. -/
theorem ofNat_of_token {V : Nat} {g : E} (ht : OnBytes.Desc.Reply.isToken V g = true)
    (hV : V ≤ pW.toNat) : ofNat g.c0.toNat = g ∧ g.c0.toNat < V := by
  obtain ⟨c0, c1, c2⟩ := g
  unfold OnBytes.Desc.Reply.isToken at ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ht
  obtain ⟨⟨rfl, rfl⟩, h0⟩ := ht
  refine ⟨?_, h0⟩
  have hm : c0.toNat % pW.toNat = c0.toNat := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h0 hV)
  show E.mk3 ((c0.toNat % pW.toNat).toUInt64) 0 0 = _
  rw [hm]
  show (⟨c0.toNat.toUInt64, 0, 0⟩ : E) = ⟨c0, 0, 0⟩
  have e : c0.toNat.toUInt64 = c0 := by simp
  rw [e]

/-- **The request's test and a token give the covered positions.** -/
theorem covered_of_parts {T V : Nat} {s : S} {g : E} (hq : s.reqOk T V = true)
    (hr : s.out.reply = some g) (ht : OnBytes.Desc.Reply.isToken V g = true)
    (hV : V ≤ pW.toNat) : ∃ cov, s.covered T V = .ok cov := by
  obtain ⟨e, h0⟩ := ofNat_of_token ht hV
  have ey : s.replyTok? = some g.c0.toNat := by
    unfold S.replyTok?
    rw [hr]
    show (if ofNat g.c0.toNat == g then some g.c0.toNat else none) = _
    rw [e, if_pos (beq_self_eq_true g)]
  unfold S.reqOk at hq
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨⟨q1, q2⟩, q3⟩ := hq
  have eT : s.reqT = T := by
    unfold S.reqT
    omega
  unfold S.tokv at q2
  unfold S.rowR S.rowE at q3
  rw [eT] at q2 q3
  unfold S.covered
  rw [ey]
  show ∃ cov, s.coveredAt T V g.c0.toNat = .ok cov
  unfold S.coveredAt
  dsimp only
  rw [if_neg (by simp [h0]), if_neg (by simp [q1]), if_neg (by rw [q2]; simp),
    if_neg (by
      intro hc
      rw [hc] at q3
      cases q3)]
  exact ⟨_, rfl⟩

/-! ## 3 Member 338 -/

/-- **Behind every yes of member 338 a token of the head's vocabulary lies in the reply's seat.** -/
theorem reply_laid_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Bs : ProofFile.PureBase, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      ∀ blk, cF.blocksInOrder[338]? = some blk → ∀ ft s rs cols s' k,
        blk.step ft s rs cols = .ok (s', k) →
        ∃ g, s'.out.reply = some g ∧ OnBytes.Desc.Reply.isToken Bs.G₀.W.hS.V g = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, eL, eb, ⟨fs, f, hfs, hf, e⟩, hid⟩ := IM.k7_sits h.scope h.reads O
  have hy := joined_iff_K7 e rfl (hid fs f hfs hf)
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 24 ≤ 24) 0] at q
  refine ⟨Bs, O.made, fun blk hb ft s rs cols s' k hs => ?_⟩
  obtain rfl : b = blk := Option.some.inj (q.symm.trans hb)
  obtain ⟨_, hd, _⟩ := (step_iff ft b s s' rs cols k).1 hs
  obtain ⟨m, -, h2⟩ := (k7Block_iff Bs.G₀.W 24 s s' _ _).1 ((hy s s' _ _).1 hd).1
  obtain ⟨_, _, g, -, -, -, -, -, ht, rfl⟩ := (reply_iff 24 _ m s' _ _).1 h2
  exact ⟨g, rfl, ht⟩

/-- **Behind every yes of member 338 the covered positions can be made**, where the state's own test
on the request held in front. -/
theorem covered_behind_338 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ Bs : ProofFile.PureBase, ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      (Bs.G₀.W.hS.V ≤ pW.toNat → ∀ T blk, cF.blocksInOrder[338]? = some blk → ∀ ft s rs cols s' k,
        blk.step ft s rs cols = .ok (s', k) → s.reqOk T Bs.G₀.W.hS.V = true →
        ∃ cov, s'.covered T Bs.G₀.W.hS.V = .ok cov) := by
  obtain ⟨Bs, hB, hl⟩ := reply_laid_at h
  refine ⟨Bs, hB, fun hV T blk hb ft s rs cols s' k hs hq => ?_⟩
  obtain ⟨g, hg, ht⟩ := hl blk hb ft s rs cols s' k hs
  have hq' : s'.reqOk T Bs.G₀.W.hS.V = true := by
    rw [reqOk_kept_at h 338 T _ blk hb ft s rs cols s' k hs]
    exact hq
  exact covered_of_parts hq' hg ht hV

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.place_at
#print axioms Johnson.AtFull.Shape.k7_just_338
#print axioms Johnson.AtFull.Shape.k7_control
#print axioms Johnson.AtFull.Shape.not_k7_at
#print axioms Johnson.AtFull.Shape.reply_kept_but
#print axioms Johnson.AtFull.Shape.covered_kept_but
#print axioms Johnson.AtFull.Shape.ofNat_of_token
#print axioms Johnson.AtFull.Shape.covered_of_parts
#print axioms Johnson.AtFull.Shape.reply_laid_at
#print axioms Johnson.AtFull.Shape.covered_behind_338
