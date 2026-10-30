-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/TableWords.lean: the kind "the code switch" (K2): THE TABLE
NUMBER j OF THE SWITCH's OWN SENDING, AS A TERM (`switchTableAt`, Honest/K2/Seated.lean), HAS THE
LENGTH AND THE NUMBER OF WORDS OF THE j-TH OF THE HONEST SENDING's TREES; AT THE PLAN's NUMBERS: OF
THE j-TH ORACLE MESSAGE THAT THE NUMBERS STATE. FREE OF ANY THREAD. Three statements with their
proofs; no definition.

  `moveOne_says`          the part's first move says tables of the trees' shapes
  `switchTable_shape`     THE LAW, against `treeShapes`
  `switchTable_at_plan`   THE LAW AT THE PLAN's NUMBERS, against the stated oracle messages

Why: a later switch's second round opens trees that an earlier switch has sent; whoever lays the
frame's Script can have the widths of these tables from the sender's clause "which table stands at
that tree" and one law of the sender's own on its table: this is that law for this kind. IT IS NOT
YET ALL THAT THESE WIDTHS WANT: that the width which a later switch's numbers state for a tree that
it reads is the stated oracle message's of the earlier sender is a public fact on the plan's
numbers: not here.

THE PREMISES, ALL OF THEM. ON THE BOOK: it lends the part its coins (`lendPart` returns). PUBLIC, ON
THE PLACE: `Sizes.serves` · `Sizes.roomy` · `placeFits` · `closingOk`. ON THE FILLING AT THE INPUT's
PUBLIC INSTANCE: `publicOk`. At the plan's numbers also: the plan's sizes and numbers return; the
place is one of `switchPlaces`.

By: `core_tables_ok`, `tableAt_is` (Honest/K2/Law/PlaysSeated.lean) · `returnsLaw`
(Honest/K2/Law/SegmentAlike.lean) · `place_shapes` (Honest/K2/Law/PlaysAtPlan.lean). `moveOne_says`
IS THE FIRST HALF OF `moves_say` (Honest/K2/Law/PlaysSeated.lean), WITH ITS LINES: its first two
conjuncts are this law's end; it also asks four equations on a sub-protocol's two rounds and oracle
messages: a caller without a sub-protocol would have to make such rounds up, which is more text than
these lines typed again: so it is not called. The cleaner order, that law calling this one, wants a
file that has gone out to turn.

Limits. WHERE A PREMISE FAILS THE TERM IS A TABLE WITHOUT A WORD (`noTable`): nothing is said there;
nor at a number j beyond the list of trees. On a table's shape alone: nothing on what it holds. The
premises are shown met together nowhere here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysSeated
import Johnson.Desc.ProofFile.Honest.K2.Law.PlaysAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Sizes)

variable {W₀ Rc Xi Tr : Type}

/-- The part's first move says tables of the trees' shapes. -/
theorem moveOne_says (table : FreshTable) (Z : Sizes) (others : Array OnBytes.OracleNotice)
    (k : Nat) (carries : List (String × Due)) (c : SwitchCoins Z others k carries)
    (t : State SwitchAsk Unit) (hs : Z.serves = true) (hr : Z.roomy = true)
    (hf : K1.sendFits (sendingPar Z.codes (switchSent Z others))
      (rideOf (switchSent Z others) (switchFresh Z others k)) = true)
    (hl : (t.input.left t.heard (Stretch.carried carries c.2.2)).toOption.isSome = true) :
    ∃ Tb : List Table,
      (∀ s, (moveOne (coreSender table) Z others k carries).say c s t = .ok ⟨[], Tb⟩) ∧
      Tb.map (fun t => (t.logLength, t.words)) = treeShapes Z.codes (switchSent Z others) := by
  have hD : ∃ D, switchRowsAt Z carries c.2.2 t 0 = .ok D := by
    unfold switchRowsAt
    simp only [Nat.sub_zero, List.take_length]
    cases e : t.input.left t.heard (Stretch.carried carries c.2.2) with
    | ok L => exact ⟨_, rfl⟩
    | error s =>
      rw [e] at hl
      cases hl
  obtain ⟨D, hD⟩ := hD
  obtain ⟨Tb, hTb, sTb⟩ := core_tables_ok table Z.codes (switchSent Z others)
    (switchFresh Z others k) D c.1 hf
  refine ⟨Tb, fun s => ?_, sTb⟩
  show (if !Z.serves then _ else if !Z.roomy then _ else
    (switchRowsAt Z carries c.2.2 t 0).bind _) = _
  rw [hs, hr, hD]
  show ((coreSender table).tables Z.codes (switchSent Z others) (switchFresh Z others k) D
    c.1).map _ = _
  rw [hTb]
  rfl

/-- **THE LAW**: the table number j has the j-th tree's shape. -/
theorem switchTable_shape (Bk : ProverCoinCounts) (chain : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    (segs : List SegmentPub) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (h : List Fmt.Drawn) (c₀ : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (hc : lendPart Bk (Bk.rowsOf chain) (k.look chain) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) = .ok c₀)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (hcl : closingOk freshTable (segs.take p.link) p = true)
    (hv : publicOk D lay p (segs.take p.link) w.x = true) (j : Nat) (s : Nat × Nat)
    (hj : (treeShapes p.sizes.codes (switchSent p.sizes p.others))[j]? = some s) :
    ((switchTableAt Bk chain (coreSender freshTable) D readers (lotClosingAt lay segs) p k w h
        j).logLength,
      (switchTableAt Bk chain (coreSender freshTable) D readers (lotClosingAt lay segs) p k w h
        j).words) = s := by
  obtain ⟨Tb, hsay, sh⟩ := moveOne_says freshTable p.sizes p.others p.foldVars p.carries c₀
    ⟨switchWit D readers (lotClosingAt lay segs) p w, h, ()⟩ hs hr hf
    ((returnsLaw D readers lay segs p hcl w h c₀.2.2).trans hv)
  rw [tableAt_is Bk chain (coreSender freshTable) D readers (lotClosingAt lay segs) p k w h c₀ Tb
    hc (hsay ⟨[], none⟩) j]
  rw [← sh, List.getElem?_map] at hj
  obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 hj
  rw [ht]
  rfl

/-- **THE LAW AT THE PLAN's NUMBERS**: the table number j has the length and the words of the j-th
oracle message that the numbers state. -/
theorem switchTable_at_plan {Z : ProofFile.Pub} {G : ProofFile.Ground} {P : P1K2.Prep}
    (hP : P1K2.prepOf Z G = some P) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    {N : P1K2.Nums} (hN : P1K2.numsAt P p.place.link = some N)
    (Bk : ProverCoinCounts) (chain : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    (segs : List SegmentPub) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (h : List Fmt.Drawn) (c₀ : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (hc : lendPart Bk (Bk.rowsOf chain) (k.look chain) ⟨p.place, 0⟩
      (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries) = .ok c₀)
    (hs : p.sizes.serves = true) (hr : p.sizes.roomy = true) (hf : placeFits p = true)
    (hcl : closingOk freshTable (segs.take p.link) p = true)
    (hv : publicOk D lay p (segs.take p.link) w.x = true) (j : Nat)
    (o : VerifiableInference.Desc.Oracle)
    (hj : (P1K2.oraclesAt N.grp N.codes N.sent)[j]? = some o) :
    ((switchTableAt Bk chain (coreSender freshTable) D readers (lotClosingAt lay segs) p k w h
        j).logLength,
      (switchTableAt Bk chain (coreSender freshTable) D readers (lotClosingAt lay segs) p k w h
        j).words) = (o.logLength, o.words) :=
  switchTable_shape Bk chain D readers lay segs p k w h c₀ hc hs hr hf hcl hv j _ (by
    rw [← place_shapes hP hp hN, List.getElem?_map, hj]
    rfl)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.moveOne_says
#print axioms ProofFile.Honest.K2.Law.switchTable_shape
#print axioms ProofFile.Honest.K2.Law.switchTable_at_plan
