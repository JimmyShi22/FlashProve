-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PubBehindScope.lean: FOUR ITEMS OF THE FIELD pubBehind
(Law/K6TiedAtObject.lean: K6DueAt) AT PUBLIC FILES IN THE GOALS' SCOPE: Law/K6PubBehindFour.lean's
pubBehind_four, CALLED, with seven of its premises paid. One statement with its proof.

Paid here: hC1 (Law/K6PubInScope.lean: k6Pub_in_scope) · hB, hRB (Law/TablesPlanInScope.lean) · hTT,
hVV (sizes_five) · planeCols (Law/HeadFsWritten.lean, Law/HeadPlanWritten.lean, calls_place) · of
hLv: LeavesReady and "the slot of the bits' value is filled" (Law/LeavesReadyPaid.lean's
leavesReady_item off the promise's own sentence, Law/K6FrontSays.lean's left_front).

WHAT IT IS NOT. An implication. Nothing on soundness. The four tests are totalities. WHAT IS LEFT:
(B) the scope (hZ, hR, hX: UNDER THE LIBRARY's publicOf); planB; two tests with code that read more
    than the public part X (hC2: readsRoomC; hC3: seatsK6C); treesB; sorts.
(L) ON THE IOP AS WRITTEN IN LEAN, AT ONE LIST OF ROUNDS Lk: KS, KB, runs2, back2, readers.
(F) ON REACHED STATES: hReach, hFold, hwords, htok, and hStart (every slot that the starting form
    of the sumcheck over the leaves names is filled: Johnson/Top/H/Keep/K3LeftWindow.lean:
    LeavesFilled).
AND hLeft. No values are shown at which the premises hold together.
LETTERS. No letter stands under "there is" in the conclusion. In htok: y0: pinned by either
equation.

-/
import Johnson.Desc.Kinds.Law.K6PubBehindFour
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Desc.Kinds.Law.TablesPlanInScope
import Johnson.Desc.Kinds.Law.LeavesReadyPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning Pub pubFit)
open VerifiableInference.Desc.Sound (Piece Frame MsgT MgData mgAll onQ linksFull)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
  (Fr : Frame) (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (Lp : K12.Door.Laid)
  (Mm : List OracleShape)

set_option quotPrecheck false in
/-- The composed meaning. -/
local notation "MGA" => mgAll D Mg

/-- The driver's list of places, at the full chain. -/
local notation "PS" => First.flatPlacesOf linksFull true

/-- **THE FIELD pubBehind, IN THE GOALS' SCOPE.** -/
theorem pubBehind_scope {bef : List (ℕ × ℕ)} {B bS : Block S Claim}
    {q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
    {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok Wp)
    (Hs : Seated Wp .two Fr q 24 bef B bS)
    (hp : PS[341]? = some { chain := 1, link := some 24, piece := 4, kind := .K6 })
    (hfit : pubFit (MGA).more linksFull PS = true) (hplan : planB Wp = true)
    (hC2 : readsRoomC Wp lay6 (D.sent.arrayOf.getD 24 #[]) = true)
    (hC3 : AtFold.seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS Lp Mm
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[341]?) = true)
    (treesB : First.FillSent.treesAt D.built 24 = First.FillSent.looksOf Wp.H.Fp)
    (sorts : D.links[24]? = some .head)
    (piece6 : ℕ) (Lk : Link S Claim) (small : S → Option K9.Read)
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (KB : K6Back Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) 24 piece6 (K9.statesOfLink Lk) 3)
    (runs2 : PlanesStates (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (back2 : PlanesBack (readsOf Wp) Wp.hS.lmbH (K9.statesOfLink Lk) 2)
    (readers : D.Rd 24 = K9.readersOfLink ⟨small, k6Silent (p8K6 Wp 24) (K9.statesOfLink Lk)⟩ Lk)
    (hLeft : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → a.1.2.failed = none →
      K6Left Wp a.1.2)
    (hReach : ∀ a, Rch 341 a → a.1.2.failed = none → AtFold.K6Reached a.1.2)
    (hFold : ∀ a, Rch 341 a → a.1.2.failed = none →
      AtFold.FoldAt Lp Mm D.cs D.shape lay6 a.1.2)
    (hwords : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → a.1.2.req = OnBytes.Flat.requestWordsOf (D.H.req a.1).val)
    (htok : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → ∃ y0, Reply.token (seatAt Wp.hS (readsOf Wp)).toSeat a.1.2 = some y0 ∧
        a.1.2.replyTok? = some y0)
    (hStart : ∀ a, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → VerifiableInference.OnPublicFiles.LeavesFilled a.1.2) :
    ∀ a τ b, onQ (Fr := Fr) D.N MGA linksFull PS (fun a => a) 341 a → Rch 341 a →
      a.1.2.failed = none → q.ior.red.out a τ = some b → K6After Wp b.1.2 →
      ∀ i ∈ [First.Pub.lookIn 24 8, .formsInT 24 4 "own", .formsInT 24 3 "planes",
        .formsInT 24 4 "join"], (MGA).pub i b.1 = true := by
  obtain ⟨z1, _, z3, z4, _, _, _, z8⟩ := InScope.sizes_five hZ hR hX
  have Fw := InScope.fs_in_scope hZ hR hX
  have Pw := InScope.plan_in_scope hZ hR hX
  refine pubBehind_four D Mg lay6 num Fr Rch Lp Mm Hs hp hfit hplan hX
    (InScope.k6Pub_in_scope hZ hR hX) hC2 (InScope.tabsPlan_in_scope hZ hR hX)
    (InScope.readsPlan_in_scope hZ hR hX) hC3 treesB sorts z3 z8 ?_ piece6 Lk small KS KB runs2
    back2 readers hLeft hReach hFold hwords htok ?_
  · intro p3 h3 hp3 hs3
    obtain ⟨pc, ec, sc, _, _⟩ := InScope.calls_place hZ hX
    obtain rfl : p3 = pc := Option.some.inj (hp3.symm.trans ec)
    obtain rfl : Wp.HLy.fs = h3 := Option.some.inj (sc.symm.trans hs3)
    rw [Fw.NC, Fw.kT, z4, z1, Pw.mats]
    decide
  · intro a ha hrc hm Fs gk hF hg
    obtain ⟨p3, _, L3⟩ := AtFold.left_front D Mg Fr hfit hp a ha hm
    obtain ⟨F', g', w1, w2, v1, v2⟩ := leavesReady_item L3
    obtain rfl : Fs = F' := Option.some.inj (hF.symm.trans w1)
    obtain rfl : gk = g' := Option.some.inj (hg.symm.trans w2)
    exact ⟨v1, v2, fun x hx => (hStart a ha hrc hm gk Fs hg hF x hx).2⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.pubBehind_scope
