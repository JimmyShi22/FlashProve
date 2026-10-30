-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/K9RestLight.lean: THREE LIGHT FIELDS OF WHAT IS LEFT OF K9's CONDITION
(LinkRest | ShutRest, Johnson/P5J/K09Rest.lean), AT THE CLOSED CONSTANT's OWN
LETTERS: Ahds · Ahbk (the batching's piece has K9's one round and puts nothing back) AND mh
(MeantHead h.𝔇). Statements and proofs: calls of theorems in other files.

  ds_of_rounds9    a piece's data that are, round by round, those of the one declared round k9Decl p
                   are [k9Round p] (by k9_of_is, Link/Law/PieceAtDescK9.lean)
  ahds_ahbk_at     at the row's piece qb at the batching's number of link m < 25, where the blocks
                   sit (SitsAt): (atRec qb b₀).ds = [k9Round p] ∧ (atRec qb b₀).back = []: by
                   atRow_more (Kinds/Law/RowAtConst.lean) and SitsAt.rounds
  tokHOf_of_reply  the meant reader of the heard token reads the reply alone
  meantEx_at | headIs_at MeantHead's two fields' texts at 𝔇 := h.𝔇 (cut by program out of
                   Link/Law/ShutList.lean: that
                   file is not imported, and MeantHead h.𝔇 is ⟨meantEx_at h, headIs_at h⟩ where it
                   lies): meant: meant_whole (P1L20R/FrameAtAll.lean) · headIs: the
                   constant's head part is headPartK6 at its own letters: by definition; its
                   request's reader reads the public part alone: by definition

Limits. Under q₁, q₂, q₃ (the three lists of the letter 𝔏 are the description's own), as
atRow_more. SitsAt is a premise here: LPFK9.sits_at_constant has it at every m < 25. No law of any
sub-protocol. No soundness statement.



-/
import Johnson.Desc.Kinds.Law.RowAtConst
import Johnson.Desc.First.Link.Law.PieceAtDescK9
import Johnson.LPFK9R.SitsAtConstant
import Johnson.P1L20R.FrameAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Maker
open VerifiableInference.Desc.K9L (k9Round k9Decl)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)

/-- Data that are, round by round, those of K9's one declared round. -/
theorem ds_of_rounds9 (num : Fmt.TreeSource → ℕ) (p : K9.Where) (ds : List RDT)
    (h : List.Forall₂ (fun d r => RoundIs num r d) ds [k9Decl p]) : ds = [k9Round p] := by
  cases h with
  | cons h1 h2 =>
    cases h2
    rw [k9_of_is num p _ h1]

/-- The meant reader of the heard token reads the reply alone. -/
theorem tokHOf_of_reply {P : Type} {a b : P × S} (h : b.2.out.reply = a.2.out.reply) :
    P5J.tokHOf a = P5J.tokHOf b := by
  unfold P5J.tokHOf P5J.tokOfHeard First.S.heardTok? First.S.heard
  rw [h]

end VerifiableInference.Desc.LinkJoin

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Block Chain Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9L (k9Round)
open VerifiableInference.Desc.LinkJoin (batchAt atRec ds_of_rounds9 tokHOf_of_reply)
open Johnson.Desc.First.Walk.Tied (MeantAt)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Kinds.Head.Law (atRow_more)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **LinkRest's FIELDS Ahds AND Ahbk, AT THE CONSTANT's LETTERS.** -/
theorem ahds_ahbk_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) (m : ℕ) (hm : m < 25)
    {L : Link TS ProofFile.Cl} {p : VerifiableInference.Desc.K9.Where}
    {Q : VerifiableInference.Desc.First.Close.Par} (hs : LPFK9.SitsAt cF m L p Q) (qb)
    (hq : (h.toAtMg.row 𝔏)[batchAt fullLinks At.ps m]? = some qb) (b₀ : Block TS ProofFile.Cl) :
    (atRec qb b₀).ds = [k9Round p] ∧ (atRec qb b₀).back = [] := by
  have hk : batchAt fullLinks At.ps m = 14 * m + L.hear.length + 2 := by
    rw [LPFK9.batchAt_full m hm, hs.hear]
  have hlt : batchAt fullLinks At.ps m + 1 < cF.blocksInOrder.length := by
    rw [hk]
    exact (List.getElem?_eq_some_iff.1 hs.flat₂).1
  obtain ⟨M, -⟩ := atRow_more h.toAtMg 𝔏 q₁ q₂ q₃ _ qb hq hlt
  have hb : qb.b = held L.batchB := by
    have e := M.block
    rw [List.getElem?_map, hk, hs.flat] at e
    exact (Option.some.inj e).symm
  have hr := M.rounds
  rw [hb] at hr
  have hr' : List.Forall₂ (fun d r => RoundIs _ r d) qb.ds L.batchB.rounds := hr
  rw [hs.rounds] at hr'
  exact ⟨ds_of_rounds9 _ p _ hr', M.back⟩

/-- **MeantHead's FIELD meant, AT THE CONSTANT**: its text, 𝔇 := h.𝔇 [cut by program out of
Link/Law/ShutList.lean]. -/
theorem meantEx_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ seats r, MeantAt h.𝔇 seats r :=
  ⟨_, _, P1L20.meant_whole h⟩

/-- **MeantHead's FIELD headIs, AT THE CONSTANT**: its text, 𝔇 := h.𝔇 and the structure's letters
X := At.X Zp; P · rows · cols · Tok left to Lean ("_": they are h.𝔇's own) [cut by program out of
the same file]. -/
theorem headIs_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (msR : List Mem) (Nh : Numbers)
    (sz : ℕ → Cb.Pv.Tail.Size) (seat : ∀ k, Fin (sz k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (plh : ℕ → ℕ × Bool × ℕ × ℕ) (tab : ℕ → ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq)
    (H : P5J.HidAt (At.X Zp) _ (Wit (CellsQ _ _) _ MsgT) _ _)
    (tokH : _ × S → Fin Inst.Model.ppref.V),
    h.𝔇.headPart = headPartK6 cs arr msR Nh sz seat (At.X Zp) plh tab put H tokH ∧
      (∀ p s t, H.req (p, s) = H.req (p, t)) ∧
      ∀ p s t, t.out.reply = s.out.reply → tokH (p, s) = tokH (p, t) :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, fun _ _ _ => rfl, fun _ _ _ ht => tokHOf_of_reply ht⟩

end P5J

#print axioms VerifiableInference.Desc.LinkJoin.ds_of_rounds9
#print axioms VerifiableInference.Desc.LinkJoin.tokHOf_of_reply
#print axioms P5J.ahds_ahbk_at
#print axioms P5J.meantEx_at
#print axioms P5J.headIs_at
