-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/KeysNoToken.lean: WHERE THE REQUEST's WINDOW ENDS BEFORE THE LAST POSITION
(e < T) THE OUTPUT HEAD's KEYS READ NO TOKEN; AND SO THE PART lookCalls OF Law/HeadCutsK6.lean's
FILLING CAN BE CLOSED FROM K6's ITEM AT THE HEARD TOKEN, AT BOTH ARMS OF OnBytes.Flat.putReq.
Statements and proofs.

WHY. The filling's parts stand at x := (put q t).val. putReq lays the token t into the
request only where that gives a request (e < T asks the reply 0); else it leaves q as it is: there
x.y is not t. The token stands in the keys through the winner of the last position alone, and that
position is checked only where e = T.

  topNum_token, keyAt_token, keyTable_token, lookCalls_token   at e < T and two tokens below V: the
                   top digit's number, the head's five keys at a corner, a call's table and the
                   lookup's sentence are the same.
  callsPart_of_heard   MAIN: LookCallsAt Wp tab s0 t.val (compCut ... w).1 at a record whose request
                   is q's, and an index that the stored table holds, give the part lookCalls at
                   (putReq q t).val: FOR EVERY TOKEN t.

  constr_heard_of_at, constr_rider_of_at   SO: the two items that the lookup's row at the head
                   closes in front (constr hd lookCallsHeard, constr hd rider), at the constrQAt
                   with putReq and this filling, from LookCallsAt at the heard token and RiderAt at
                   the record, the promise's clause on the request's words, and the stored table's
                   pin.

WHAT IT IS NOT. Implications. The tests on the plan, FullH, requestOf s0 = reqX q.val and "the
stored table holds the index" are premises. That any block holds LookCallsAt is not here. Nothing on
soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.Desc.Kinds.Law.CellsAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Norm (lt ls d lPd T S2)

section Classes

variable [Sizes] [Policy] [Request]

/-- At e < T the last position is not checked. -/
theorem unchecked_last (he : e < T) {t : Nat} (ht : ¬ t + 1 < T) : checked t = false := by
  unfold checked
  have : ¬ t < e := by omega
  simp [this]

/-- The top digit's number reads no token. -/
theorem topNum_token (he : e < T) (y1 y2 : Nat) (c : Cells) (x t : Nat) :
    (letI : Token := ⟨y1⟩
     topNum c x t) =
    (letI : Token := ⟨y2⟩
     topNum c x t) := by
  unfold topNum
  by_cases ht : t + 1 < T
  · unfold win
    simp only [if_pos ht]
  · rw [unchecked_last he ht]
    simp

/-- **The head's five keys at a corner read no token.** -/
theorem keyAt_token (he : e < T) (y1 y2 : Nat) (P : PlanFacts) (hreq : Request.ok = true)
    (h1 : y1 < V) (h2 : y2 < V) (c : Cells) (k : Key) {x t : Nat} (hx : x < len k) (ht : t < T) :
    (letI : Token := ⟨y1⟩
     keyAt c (corner x t) k) =
    (letI : Token := ⟨y2⟩
     keyAt c (corner x t) k) := by
  refine eq_of_rd (letI : Token := ⟨y1⟩; okE_keyAt _ _ _) (letI : Token := ⟨y2⟩; okE_keyAt _ _ _) ?_
  cases k with
  | marginTop =>
    have hx' : x < JV := hx
    have a1 := (letI : Token := ⟨y1⟩; rd_key_top (c := c) P hreq h1 hx' ht)
    have a2 := (letI : Token := ⟨y2⟩; rd_key_top (c := c) P hreq h2 hx' ht)
    rw [a1, a2, topNum_token he y1 y2]
  | marginMid =>
    have hx' : x < JV := hx
    have a1 := (letI : Token := ⟨y1⟩; rd_key_mid (c := c) P hx' ht)
    have a2 := (letI : Token := ⟨y2⟩; rd_key_mid (c := c) P hx' ht)
    rw [a1, a2]
  | marginLow =>
    have hx' : x < JV := hx
    have a1 := (letI : Token := ⟨y1⟩; rd_key_low (c := c) P hx' ht)
    have a2 := (letI : Token := ⟨y2⟩; rd_key_low (c := c) P hx' ht)
    rw [a1, a2]
  | tableA =>
    have hx' : x < JVa := hx
    have a1 := (letI : Token := ⟨y1⟩; rd_key_tableA (c := c) P hx' ht)
    have a2 := (letI : Token := ⟨y2⟩; rd_key_tableA (c := c) P hx' ht)
    rw [a1, a2]
  | tableB =>
    have hx' : x < JV - JVa := hx
    have a1 := (letI : Token := ⟨y1⟩; rd_key_tableB (c := c) P hx' ht)
    have a2 := (letI : Token := ⟨y2⟩; rd_key_tableB (c := c) P hx' ht)
    rw [a1, a2]

/-- **A call's table reads no token.** -/
theorem keyTable_token (he : e < T) (y1 y2 : Nat) (P : PlanFacts) (hreq : Request.ok = true)
    (h1 : y1 < V) (h2 : y2 < V) (c : NCells) (call col : Nat) {t : Nat} (ht : t < T) :
    (letI : Token := ⟨y1⟩
     keyTable c call col t) =
    (letI : Token := ⟨y2⟩
     keyTable c call col t) := by
  unfold keyTable callTable tableOf
  have key : entriesOf (List.map lenOf (callKeys call))
      (fun s x => (letI : Token := ⟨y1⟩; cornerKey c (slot (callKeys call) s) x t)) =
      entriesOf (List.map lenOf (callKeys call))
        (fun s x => (letI : Token := ⟨y2⟩; cornerKey c (slot (callKeys call) s) x t)) := by
    refine @entriesOf_same _ _ _ ⟨y1⟩ _ _ _ _ fun s x hs hx => ?_
    rw [List.length_map] at hs
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hs), List.getElem_map] at hx
    have hx2 : x < lenOf (slot (callKeys call) s) := by
      unfold slot
      rw [List.getD_eq_getElem _ _ hs]
      exact hx
    cases hk : slot (callKeys call) s with
    | inl k => rfl
    | inr k =>
      rw [hk] at hx2
      exact keyAt_token he y1 y2 P hreq h1 h2 c.toCells k hx2 ht
  exact congrArg (fun l => (List.lookup col l).getD ((padKey call : Nat) : E)) key

/-- **The lookup's sentence reads no token.** -/
theorem lookCalls_token (he : e < T) (y1 y2 : Nat) (P : PlanFacts) (hreq : Request.ok = true)
    (h1 : y1 < V) (h2 : y2 < V) (c : NCells) (floor : Nat) (tab : Nat → Nat)
    (hl : letI : Token := ⟨y1⟩
      ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
        InTable tab call (keyTable c call col t)) :
    letI : Token := ⟨y2⟩
    ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
      InTable tab call (keyTable c call col t) := fun call hc col hcol t ht => by
  rw [← keyTable_token he y1 y2 P hreq h1 h2 c call col ht]
  exact hl call hc col hcol t ht

end Classes

open Inst.Model (ppref Instance)
open VerifiableInference.OnPublicFiles.Flat (GE Holds)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
  (pl : Nat → Nat × Bool × Nat × Nat)

/-- **THE PART lookCalls AT (putReq q t).val, FROM THE HEAD's ITEM AT THE TOKEN t ITSELF: AT BOTH
ARMS OF putReq.** -/
theorem callsPart_of_heard (tab : Nat → Nat) (i : Cm.Idx) (q : P5J.TReq) (t : Fin ppref.V)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (s0 : S)
    (hF : OnBytes.Road.Hd.FullH Wp.hS) (hplan : (parOf Wp.hS (workOf Wp)).ok = true)
    (hq : requestOf s0 = reqX q.val) (hH : Holds w.cells i)
    (hl : LookCallsAt Wp tab s0 t.val (compCut cs arr msR N s seat Wp pl w).1) :
    partsAtX cs arr msR N s seat Wp pl tab i (OnBytes.Flat.putReq q t).val w .lookCalls := by
  by_cases h : q.val.e < ppref.T → t.val = 0
  · rw [OnBytes.Flat.putReq_val q t h]
    exact callsPart_of_at cs arr msR N s seat Wp pl tab i { q.val with y := t } w s0
      (hq.trans (reqX_congr _ _ rfl rfl rfl)) hH hl
  · have he : q.val.e < ppref.T := by
      by_contra hc
      exact h fun h' => absurd h' hc
    have ht : t.val ≠ 0 := fun h0 => h fun _ => h0
    rw [OnBytes.Flat.putReq_else q t he ht]
    unfold LookCallsAt at hl
    rw [hq] at hl
    refine ⟨hH, ?_⟩
    letI : Sizes := sizesOf Wp.hS
    letI : Policy := (parOf Wp.hS (workOf Wp)).policy
    letI : Request := reqX q.val
    have heT : e < T := by
      show q.val.e < 2 ^ Wp.hS.lt
      rw [hF.lt]
      exact he
    have hV : ∀ z : Fin ppref.V, z.val < V := fun z => by
      show z.val < Wp.hS.V
      rw [hF.V]
      exact z.isLt
    exact lookCalls_token heT t.val q.val.y.val
      (letI : Token := ⟨t.val⟩; planFacts (sT := Wp.hS.tabS) hplan)
      (okStart_atX Wp.hS (workOf Wp) q.val hF (Meaning.head3_of_req q)) (hV t) (hV q.val.y) _ _ tab
      hl

variable {P : Type} (tab : Nat → Nat)
  (H : P5J.HidAt Wp P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
  (tokH : P × P5J.TS → Fin ppref.V)
  (digitsPart : Nat → P × P5J.TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)

/-- **constr hd lookCallsHeard AT A RECORD, FROM THE HEAD's ITEM AT THE HEARD TOKEN THERE.** -/
theorem constr_heard_of_at (hd : Nat) (a : P × P5J.TS) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (hF : OnBytes.Road.Hd.FullH Wp.hS)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true)
    (hl : LookCallsAt Wp tab a.2 (tokH a).val (compCut cs arr msR N s seat Wp pl w).1)
    (hw : a.2.req = OnBytes.Flat.requestWordsOf (H.req a).val)
    (hpin : ∀ M, H.dec a y = some M → M = w.cells) :
    P5J.constrQAt hd OnBytes.Flat.putReq H
      (headPartK6 cs arr msR N s seat Wp pl tab OnBytes.Flat.putReq H tokH) digitsPart hd
      .lookCallsHeard a y w := by
  unfold P5J.constrQAt
  rw [if_neg (by decide)]
  refine ⟨fun h => absurd h (by decide), fun M i hM hi => ?_⟩
  rw [if_pos rfl]
  exact callsPart_of_heard cs arr msR N s seat Wp pl tab i (H.req a) (tokH a) w a.2 hF hplan
    (requestOf_words a.2 (H.req a).val hw) (hpin M hM ▸ hi) hl

/-- **constr hd rider AT A RECORD, FROM THE HEAD's ITEM THERE, AT ANY TOKEN.** -/
theorem constr_rider_of_at (hd : Nat) (a : P × P5J.TS) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT) (y0 : Nat)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true)
    (hl : RiderAt Wp a.2 y0 (compCut cs arr msR N s seat Wp pl w).1)
    (hw : a.2.req = OnBytes.Flat.requestWordsOf (H.req a).val) :
    P5J.constrQAt hd OnBytes.Flat.putReq H
      (headPartK6 cs arr msR N s seat Wp pl tab OnBytes.Flat.putReq H tokH) digitsPart hd
      .rider a y w := by
  unfold P5J.constrQAt
  rw [if_neg (by decide)]
  refine ⟨fun h => absurd h (by decide), fun M i _ _ => ?_⟩
  rw [if_pos rfl, headPartK6_at cs arr msR N s seat Wp pl tab _ H tokH .rider (by decide)]
  obtain ⟨k1, k2, k3⟩ := putReq_keeps (H.req a) (H.hid w).tok
  exact riderPart_of_at cs arr msR N s seat Wp pl tab i _ w a.2 y0 hplan
    ((requestOf_words a.2 (H.req a).val hw).trans (reqX_congr _ _ k1.symm k2.symm k3.symm)) hl

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.lookCalls_token
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.callsPart_of_heard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.constr_heard_of_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.constr_rider_of_at
