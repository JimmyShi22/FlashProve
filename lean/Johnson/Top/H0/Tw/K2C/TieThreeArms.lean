-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeArms.lean: code switching: hAt OF THE THIRD TIE AT A PLACE
(hAt_at_place, Tw/K2C/TieThreeAt.lean) IN ITS THREE ARMS: a code switch at a link, at the head, at
the finish. In each arm the two premises on the way out (hK, hKb) fall to the arm's own text, and
hD (T3At.carried · position) to what is owed on the numbers there. A JOINING: every step is a call.
NO SUB-PROTOCOL IMPORTS THIS FILE. Johnson/Loose/PVK2/ is not in this library.
  HAt          the binder hAt of k02_t3R, as one named sentence:
               that it IS the binder is Lean's comparison in Johnson/Loose/PVK2/TieThreeFits.lean
  leaves_link    a way out that, wherever it accepts, is OpenedKeeps (opened_keeps,
                 Walk/FrameOpened.lean; a guard that hands back what it is handed meets it too)
                 keeps the tables, every group's rows and the book
  leaves_head    the like where it is an acceptance of "H.1.quiet" (K2.headOpenQ) and then
                 OpenedKeeps: headOpenQ_kept (K2Caller/DoorKeeps.lean) · K2.headOpenQ_book
                 (Tw/K2C/BookKept.lean). BOTH OF THE HEAD's SEATS: "H.1.quiet" then a guard, and
                 "H.1.quiet" then a row's «opened»
  leaves_finish  the like at "F.0.quiet" (K2.finishBehindQ): finishBehindQ_kept · finishBehindQ_book
  hAt_link       hAt, from K2.LinkDebts at the front
  hAt_head · hAt_finish   hAt, from K2.SwitchDebts at the front
The halves on KeepsOut stand already, at the real ways out, in
Johnson/P1K2R/SitsDoor.lean (P1K2.out_head | out_finish …): THE BOOK's HALF IS WHAT IS NEW HERE.
LEFT IN EACH ARM, BY NAME. Closed, on public data: h32 · hL · hkA · hnd h0f hcs hpub · C · hgrp ·
hd : d = baseCount r.set .request r.g (the payers have the lot's n.positions for d). The arm's text:
hlv. At the front, under the table of joints' promise, Rch and «no mark»: hT1 · the debts, IN THE
PAYERS' OWN FORM: under «layTrees … = some lay» (d_link_scope | d_head_scope |
d_finish_scope, Johnson/P1K2R/HstInScope.lean) · hone · hS.
LIMITS. OF THE DEBTS' SIX FIELDS TWO ARE SPENT (carried · position): the arms ask MORE than
hAt_at_place's hD; they are its form at the payers, no payment. The arms part in the way out and in
the form of the debts alone; the way in stays the letter enter. That a seated sub-protocol's way out
IS the arm's text is a premise (hlv). TieThreeAt.lean's limits hold here too, the equation
t.book.trees.size = p.firstTree + t.roots first. No premise is shown met here. It is no soundness of
the protocol. On hiding nothing.
-/
import Johnson.Top.H0.Tw.K2C.TieThreeAt
import Johnson.Top.H0.Tw.K2C.BookKept
import Johnson.Top.H0.Tw.K2C.HandsLink
import Johnson.Top.H0.Tw.K2C.HandsCore
import Johnson.Top.H0.Walk.FrameOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open Johnson.Desc.First.Walk.Tied (OpenedKeeps)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

/-! ## 1 The three ways out -/

/-- A link's way out. -/
theorem leaves_link {leave : Rec → Rec → Except String Rec}
    (hlv : ∀ s t' s', leave s t' = .ok s' → OpenedKeeps t' s') :
    KeepsOut leave ∧ ∀ s t' s', leave s t' = .ok s' → s'.book = t'.book :=
  ⟨fun s t' s' e => kept_of_st (hlv s t' s' e).1, fun s t' s' e => (hlv s t' s' e).2.1⟩

/-- The head's way out. -/
theorem leaves_head {leave : Rec → Rec → Except String Rec}
    (hlv : ∀ s t' s', leave s t' = .ok s' →
      ∃ Pq u, K2.headOpenQ Pq t' = .ok u ∧ OpenedKeeps u s') :
    KeepsOut leave ∧ ∀ s t' s', leave s t' = .ok s' → s'.book = t'.book :=
  ⟨fun s t' s' e => by
      obtain ⟨Pq, u, hq, ho⟩ := hlv s t' s' e
      exact (headOpenQ_kept hq).trans (kept_of_st ho.1),
    fun s t' s' e => by
      obtain ⟨Pq, u, hq, ho⟩ := hlv s t' s' e
      exact ho.2.1.trans (K2.headOpenQ_book hq).1⟩

/-- The finish's way out. -/
theorem leaves_finish {leave : Rec → Rec → Except String Rec}
    (hlv : ∀ s t' s', leave s t' = .ok s' → K2.finishBehindQ t' = .ok s') :
    KeepsOut leave ∧ ∀ s t' s', leave s t' = .ok s' → s'.book = t'.book :=
  ⟨fun s t' s' e => finishBehindQ_kept (hlv s t' s' e),
    fun s t' s' e => (K2.finishBehindQ_book (hlv s t' s' e)).1⟩

/-! ## 2 The arms -/

section
variable {F : Frame} {P Cells Tok Cl Xi : Type} {r : SwRow} (h : r.ok = true)
  (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
      h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
      h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
  (G : FileDescription Xi) (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT) (p : K2.P2)
  (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
  (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
  (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart)
  (ps : List VerifiableInference.Desc.Place) (z : P) (Rch : ℕ → Rec × F.E.Str → Prop)
  (k m n0 grp : ℕ)

/-- **The third tie's binder hAt at a place** (k02_t3R), as one sentence. -/
def HAt : Prop :=
  ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
        seatN base d₁ F) p base
      idExt) B ext').ior.red.out a τ = some b →
    ∀ t t' x y S3 Y rws Gg c, enter a.1 = .ok t → leave a.1 t' = .ok b.1 →
      (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss.length = baseCount r.set .request r.g →
      K2.decideWith _root_.Tw.K2.sendByL8 p t [vN d₁ τ.1 τ.2.1, vN d₂ τ.2.2.1 τ.2.2.2.1]
        (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base d₁ F) p
            base idExt (t, a.2) τ) = .ok t' →
      K2.AtYes p t t' (vN d₁ τ.1 τ.2.1) (vN d₂ τ.2.2.1 τ.2.2.2.1)
        (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base d₁ F) p
            base idExt (t, a.2) τ) x y S3 Y rws Gg c →
      K2.SameTables t'.st b.1.st ∧
      (b.1.st.groups[x.f.group]?).map (·.rows) = (t'.st.groups[x.f.group]?).map (·.rows) ∧
      T3At (r.ok_says h) iJ iQ seatN N m n0 grp b.1 x rws (vN d₂ τ.2.2.1 τ.2.2.2.1) Gg

variable (h32 : p.logN ≤ 32) (hL : r.cs.lengthsOk = true)
  (f₀ : _root_.Tw.K2.Front) (W : SwitchFrame) (olds : List ℕ)
  (hnd : olds.Nodup) (h0f : K2.frameAt f₀ = some W) (hcs : f₀.st.codes = r.cs)
  (hpub : frontPubB r.l.length f₀ = true) (hkA : r.keptAt W = true)
  (C : ∀ W₀, Renumbered W W₀ → CallerAt (selR (Letters.plain r (r.ok_says h))) r.cs r.l iJ iQ memK
      rowK (plK W₀) W₀)
  (hT1 : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
      frontB2 f₀ W grp 0 n0 olds fx = true ∧ Tied r.l (switchNotices fx.T fx.others))
  (hgrp : N.groupAt m = grp) (d : ℕ) (hd : d = baseCount r.set .request r.g)
  (hone : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
      ∀ κ ∈ (placeFrame W n0 olds).kept,
        (fx.st.oracles.getD κ.old default).sampleRows.size = 1)
  (hS : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
    ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
      ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
        ∀ i : Fin r.l.length,
          seatN i = (p.firstTree + (t.roots + lay.tree.getD i.val 0), lay.part.getD i.val 0))

include h32 hL hnd h0f hcs hpub hkA C hT1 hgrp hd hone hS

/-- **hAt at a link's code switch.** -/
theorem hAt_link (hlv : ∀ s t' s', leave s t' = .ok s' → OpenedKeeps t' s')
    (hDl : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ W₀, K2.frameAt fx = some W₀ → ∃ pIn pOut s, K2.LinkDebts N m pIn pOut s d fx W₀ lay) :
    HAt h iJ iQ G seatN base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k m n0 grp :=
  hAt_at_place h iJ iQ G seatN base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k m n0 grp
    (leaves_link hlv).1 (leaves_link hlv).2 h32 hL f₀ W olds hnd h0f hcs hpub hkA C hT1 hgrp
    d hd (fun a ha hr hm t et fx hf lay hl W₀ hW => by
      obtain ⟨pIn, pOut, s, D⟩ := hDl a ha hr hm t et fx hf lay hl W₀ hW
      exact ⟨D.carried, D.position⟩) hone hS

/-- **hAt at the head's code switch.** -/
theorem hAt_head
    (hlv : ∀ s t' s', leave s t' = .ok s' →
      ∃ Pq u, K2.headOpenQ Pq t' = .ok u ∧ OpenedKeeps u s')
    (hDs : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ W₀, K2.frameAt fx = some W₀ →
            ∃ pIn pOut bs n, K2.SwitchDebts N m pIn pOut bs d n fx W₀ lay) :
    HAt h iJ iQ G seatN base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k m n0 grp :=
  hAt_at_place h iJ iQ G seatN base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k m n0 grp
    (leaves_head hlv).1 (leaves_head hlv).2 h32 hL f₀ W olds hnd h0f hcs hpub hkA C hT1 hgrp
    d hd (fun a ha hr hm t et fx hf lay hl W₀ hW => by
      obtain ⟨pIn, pOut, bs, n, D⟩ := hDs a ha hr hm t et fx hf lay hl W₀ hW
      exact ⟨D.carried, D.position⟩) hone hS

/-- **hAt at the finish's code switch.** -/
theorem hAt_finish (hlv : ∀ s t' s', leave s t' = .ok s' → K2.finishBehindQ t' = .ok s')
    (hDs : ∀ a, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      ∀ t, enter a.1 = .ok t → ∀ fx, K2.frontAt p t = some fx →
        ∀ lay, layTrees fx.st.codes (switchNotices fx.T fx.others) = some lay →
          ∀ W₀, K2.frameAt fx = some W₀ →
            ∃ pIn pOut bs n, K2.SwitchDebts N m pIn pOut bs d n fx W₀ lay) :
    HAt h iJ iQ G seatN base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k m n0 grp :=
  hAt_at_place h iJ iQ G seatN base d₁ d₂ p B enter leave ext' N Mg links ps z Rch k m n0 grp
    (leaves_finish hlv).1 (leaves_finish hlv).2 h32 hL f₀ W olds hnd h0f hcs hpub hkA C hT1 hgrp
    d hd (fun a ha hr hm t et fx hf lay hl W₀ hW => by
      obtain ⟨pIn, pOut, bs, n, D⟩ := hDs a ha hr hm t et fx hf lay hl W₀ hW
      exact ⟨D.carried, D.position⟩) hone hS

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.leaves_link
#print axioms VerifiableInference.Desc.First.K2Caller.leaves_head
#print axioms VerifiableInference.Desc.First.K2Caller.leaves_finish
#print axioms VerifiableInference.Desc.First.K2Caller.hAt_link
#print axioms VerifiableInference.Desc.First.K2Caller.hAt_head
#print axioms VerifiableInference.Desc.First.K2Caller.hAt_finish
