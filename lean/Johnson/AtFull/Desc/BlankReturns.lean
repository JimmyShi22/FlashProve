-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Desc/BlankReturns.lean: THE PREMISE q₃ OF baseOf_of_parts
(Johnson/AtFull/Desc/Ledger.lean): «blankBy pureRoad.links Z = some G»: THE SEGMENTS' STRUCTURES
WITHOUT A REQUEST ARE THERE: a general theorem: no evaluation. Definitions, and statements with
their proofs.

What blankBy (Johnson/Desc/ProofFile/Pub.lean) does: it lays the blank request's words (T zeros,
then 0 and 1) into the public part's first state; as no reply is heard there, it takes the covered
positions at the token 0 (S.coveredAt); it makes the links by linksPlain
(Johnson/Desc/ProofFile/PlanPlain.lean), which is listLinksH at structures that copy the plans'
fields; it returns the plan's built links, each with the one field run taken from the made ones,
beside the public parameters.
  blankReq · blankReq_size · blankReq_front · blankReq_r · blankReq_e   the blank request's words.
  covered_blank       S.coveredAt returns there, where 0 < V and 1 ≤ T.
  blank_returns       **q₃**, from two sizes, 0 < V, 1 ≤ T, and «the first state holds no reply».
  s0_reply            that last, behind the public part's return (pubBy_start and start?_is).
  blank_returns_pub   q₃ where the public part returns: «the first state holds no reply» is paid by
                      s0_reply; THE OTHER FOUR PREMISES STAY: the two sizes, 0 < V, 1 ≤ T.

What it reads of X := Z.p.X: NGr · p4 · G.size · A.size (listLinksH's one need:
listLinksH_returns, OnBytes/Flat/CoveredJoin.lean) · P.h.V · T. NONE OF THESE IS PAID HERE.
q₃ stands here at pureRoad.links. pureSeat lays «links := pureRoad.links»
(Johnson/Desc/ProofFile/OnlineDescription.lean), so q₃ at (pureSeat o Z).links is this statement, by
unfolding.
Limits. G stands under «there is»: what it holds, other files say (ProofFile.Law.blankBy_W and the like).
No soundness is claimed. No example of the head is shown in this file; two, at storedPublicFiles and at zGap
alone, are AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are
worth.

-/
import Johnson.Desc.ProofFile.OnlineDescriptionPublicPart
import Johnson.Desc.ProofFile.Law.StartAt
import OnBytes.Flat.CoveredJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc
open OnBytes OnBytes.Model OnBytes.Model.Stages
open VerifiableInference.Desc.First (S)

/-- The blank request's words: T zeros, then the covered range [0, 1). -/
def blankReq (T : Nat) : Array UInt32 := Array.replicate T 0 ++ #[0, 1]

theorem blankReq_size (T : Nat) : (blankReq T).size = T + 2 := by
  simp [blankReq]

theorem blankReq_front (T : Nat) : (blankReq T).extract 0 T = Array.replicate T 0 := by
  simp [blankReq]

theorem blankReq_r (T : Nat) : (blankReq T).getD T 0 = 0 := by
  simp [blankReq, Array.getD_eq_getD_getElem?]

theorem blankReq_e (T : Nat) : (blankReq T).getD (T + 1) 0 = 1 := by
  simp [blankReq, Array.getD_eq_getD_getElem?]

/-- The covered positions of the blank request are there. -/
theorem covered_blank (s : S) (T V : Nat) (hV : 0 < V) (hT : 1 ≤ T) :
    ∃ cov, (s.withReq (blankReq T)).coveredAt T V 0 = .ok cov := by
  unfold S.coveredAt
  have e0 : (s.withReq (blankReq T)).req = blankReq T := rfl
  simp only [e0, blankReq_size, blankReq_front, blankReq_r, blankReq_e]
  have c1 : (!decide (0 < V)) = false := by simp [hV]
  have c3' : (((Array.replicate T (0 : UInt32)).map (·.toNat)).all fun v => decide (v < V)) =
      true := by
    apply Array.all_eq_true_iff_forall_mem.2
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Array.mem_map.1 hx
    have hy0 : y = 0 := (Array.mem_replicate.1 hy).2
    subst hy0
    simpa using hV
  have c3 : (!((Array.replicate T (0 : UInt32)).map (·.toNat)).all fun v => decide (v < V)) =
      false := by
    rw [c3']
    rfl
  have c4 : (decide ((0 : UInt32).toNat ≥ (1 : UInt32).toNat) ||
      decide ((1 : UInt32).toNat > T)) = false := by
    have : ¬ (1 > T) := by omega
    simp [this]
  simp only [c1, c3, c4, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false]
  exact ⟨_, rfl⟩

/-- **q₃: the segments' structures without a request are there**, UNDER FIVE PREMISES: there are as
many layers' plans as groups (hG) and, at profile 4, as many attention plans (hA); 0 < V (hV);
1 ≤ T (hT); the first state holds no reply (h0). -/
theorem blank_returns (Z : ProofFile.Pub) (hG : Z.p.X.G.size = Z.p.X.NGr)
    (hA : Z.p.X.p4 = true → Z.p.X.A.size = Z.p.X.NGr) (hV : 0 < Z.p.X.P.h.V) (hT : 1 ≤ Z.p.X.T)
    (h0 : Z.s₀.out.reply = none) :
    ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Z = some G := by
  obtain ⟨cov, hc⟩ := covered_blank Z.s₀ Z.p.X.T Z.p.X.P.h.V hV hT
  obtain ⟨links, hl⟩ : ∃ ls, ProofFile.Plain.linksPlain Z.p.X = .ok ls := by
    unfold ProofFile.Plain.linksPlain
    exact OnBytes.Flat.listLinksH_returns _ (by rw [Array.size_map]; exact hG)
      (fun h => by rw [Array.size_map]; exact hA h)
  refine ⟨⟨Z.p.built.links.zipWith (fun b l => { b with run := l.run }) links, Z.first, Z.p.X,
    cov⟩, ?_⟩
  unfold ProofFile.blankBy ProofFile.lettersBy
  have e1 : (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])).out.reply = none := h0
  have hc' : (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])).coveredAt Z.p.X.T Z.p.X.P.h.V 0 =
      .ok cov := hc
  have hl' : ProofFile.pureRoad.links Z.p.X cov = .ok links := hl
  simp only [e1, Option.isNone_none, if_true, hc', hl', bind, Except.bind, pure, Except.pure]
  rfl

/-- The public part's first state holds no reply. -/
theorem s0_reply {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) : Z.s₀.out.reply = none := by
  obtain ⟨c, e⟩ := VerifiableInference.Desc.First.start?_is (ProofFile.Law.pubBy_start
    (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from h))
  rw [e]
  rfl
/-- **q₃ where the public part returns**, UNDER FOUR PREMISES THAT STAY: hG · hA · hV · hT, as in
blank_returns. This file derives only the fifth premise (h0) from the return, by s0_reply. Whether
the other four also follow from it is not examined here. -/
theorem blank_returns_pub {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (hG : Z.p.X.G.size = Z.p.X.NGr)
    (hA : Z.p.X.p4 = true → Z.p.X.A.size = Z.p.X.NGr) (hV : 0 < Z.p.X.P.h.V) (hT : 1 ≤ Z.p.X.T) :
    ∃ G, ProofFile.blankBy ProofFile.pureRoad.links Z = some G :=
  blank_returns Z hG hA hV hT (s0_reply h)

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.blankReq_size
#print axioms Johnson.AtFull.Desc.blankReq_front
#print axioms Johnson.AtFull.Desc.blankReq_r
#print axioms Johnson.AtFull.Desc.blankReq_e
#print axioms Johnson.AtFull.Desc.covered_blank
#print axioms Johnson.AtFull.Desc.blank_returns
#print axioms Johnson.AtFull.Desc.s0_reply
#print axioms Johnson.AtFull.Desc.blank_returns_pub
