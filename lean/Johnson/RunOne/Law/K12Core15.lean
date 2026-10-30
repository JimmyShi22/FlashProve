-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Core15.lean: ROW 1.15 OF THE KEY FILE's TABLES: WHAT THE PROXIMITY TEST's LAW CONCLUDES (QN, AS THE FIELD «gives» OF Left15JG HOLDS IT) GIVES ONE TUPLE OF CANDIDATES OF WHOSE WORDS ALL ROWS THAT THE TEST TAKES IN HOLD. One statement; its proof is ONE CALL of core_at (Johnson/Desc/Sound/SeamFacts.lean), which is general in the place, the seat and the frame. IT MOVES THE WEIGHT INTO CoreFacts; IT PAYS NONE.
OBJECT. The premise QN of «gives» (K12Left15JG.lean), at its own spelling: the frame frameAt D (allOf D) D.key₁ 0 · the place rangesParams N · the numbering nuOf (rangesParams N) nl t.
USER. Whoever pays «back»'s law at row 1.15 (the items grows and pin 1 at the laid witness).
LETTERS. X N P DK: The35.lean's. cs · smp · mem · sits · rdT: SeamFacts.lean's (the plan's codes · a typed reading of the record's samples · which member of the list sits at a message's number · at which members the tuple is to be a candidate · the reader of a typed message's tables). nl rad rd: «gives»' own.
  core_15: CoreFacts · InOrder t.st · QN ⟹ the group under test is there, and ∃ m, AllSay … (wordsT cs mem rdT m) ∧ CandAt at whoever sits.
NOT AMONG THE PREMISES: that t is the record behind the seat's door in: core_at does not spend it.
Limits. CoreFacts is a premise: no member of it is shown at the key file. Nothing on soundness, nothing on hiding.

-/
import Johnson.Desc.Sound.SeamFacts
import Johnson.Desc.K12.Coin.GameLabels
import Johnson.RunOne.Law.K12Left15JG

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Core15
open H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi FirstState)
open OnBytes.Maker
open _root_.Run
open H2K.Pub (sgOf)
open Johnson.RunOne.KeyRows23 (Fk)
open _root_.Desc.K14.Law.Fence (CoreFacts core_at)
open LPFD

/-- **The law's conclusion at row 1.15 gives one tuple of candidates.** -/
theorem core_15 (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) (cs : Codes)
    (smp : Xi × FirstState → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (mem : ℕ → Option Mem) (sits : Mem → Prop)
    (rdT : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
    (hrd : ∀ x m part i, rdT x m part i = tabP cs (x.1.l.get x.2).1 m part i)
    (nl : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (a : (Xi × FirstState) × (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0).E.Str) (t : T12)
    (facts : CoreFacts cs (Fk X N P) (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad smp mem sits t a.2 a.1
      (strsOf (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) a.2))
    (hI : InOrder t.st)
    (hq : QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2)) :
    ∃ G0, t.st.groups[t.g]? = some G0 ∧
      ∃ m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        AllSay OnBytes.Model.Reading.gl (begun t.st t.g G0) (runRows t.st G0).toList (_root_.Desc.K14.Law.wordsT cs mem rdT m) ∧
        ∀ x, sits x → CandAt cs (Fk X N P) smp x a.1 (strsOf (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) a.2) (m x) := by
  obtain ⟨_, _, G0, _, _, hf, _⟩ := id hq
  exact ⟨G0, hf.2.1, core_at cs (Fk X N P) _ (rangesParams N) _ rad rd smp mem sits rdT hrd t a.2 a.1 _ facts hI hq G0 hf.2.1⟩

end Johnson.RunOne.Law.K12Core15

#print axioms Johnson.RunOne.Law.K12Core15.core_15
