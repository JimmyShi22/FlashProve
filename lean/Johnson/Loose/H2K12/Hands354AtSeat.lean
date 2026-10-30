-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/Hands354AtSeat.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN:
THE SECOND TIE AT THE FILE's
OWN PIECE, sub-protocol number 354 of the written list. One call of t2_at (H2K12/Hands354.lean) at
what is in hand of that piece (Seat354, H2K12/TieAt354.lean). Statements and proofs.
Main names:
  laysOnly_outCore   the way out of the entry at that seat (outCore, H2K12/FirstSeatForm.lean) lays
                  the statement, the book and the count of roots, and turns nothing else (LaysOnly,
                  Johnson/Desc/K12/Coin/K12Grows.lean): by outCore_ok and laysOnly_finish.
  place_355, stand_355, open_355   three lines on the table's written lists, decided by the kernel:
                  number 355 is the place of the joining of the pending rows; the chain stands at
                  its finish there; just four items are open at that border. open_354_more: the
                  third line can fail: one border earlier eight items are open.
  hands_354       THE SECOND TIE (T2At, H2K12/Frame354.lean) at number 354 of
                  the written lists, at any piece q with Seat354 Z N D q. PAID HERE, against t2_at:
                  which sub-protocol the piece holds, that it puts no round back, "sits", the way
                  out (Seat354; laysOnly_outCore) · the plan's four tests (PublicAtLast;
                  early_of_planOk, answers_of_planOk: Johnson/Desc/K12/Law/Top.lean) · the five
                  lines on the written lists (place_written, pinI_open_written: K12's files'; the
                  three here) · "decodes rides" (dec_rides_354, H2K12/TieAt354.lean) · the piece's
                  base.
Limits. (1) A CALL: it pays no law of the kind. (2) WHAT STAYS, each a premise: on the meaning's
and the reader's texts: hII, hIT, hheld, hshown, hnc, hin, hd, hBl, hsmp · numbers of the plan: hL,
hft, hB, hfen · the table's list of public items: hQb · under the promise and the condition Rch,
without a mark: hFacts (five fields of FoldFacts, Johnson/Desc/First/FoldFacts.lean). (3) WHETHER
THEY CAN BE MET TOGETHER IS SHOWN NOWHERE HERE. hQb was evaluated at the composed meaning's closed
list of extra public tests; hB at sibling terms alone (another maker of the list, another filling
of the numbers); hL and hfen by nobody yet. (4) This file stands over H2K12/FirstSeatForm.lean,
in which FirstOut has one arm.
No soundness statement. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.Top
import Johnson.Loose.H2K12.TieAt354
import Johnson.Loose.H2K12.Hands354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound (Mem Sending strsOf)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (Numbers)

/-- The way out of the entry at the first chain's seat lays the statement, the book and the count of
roots, and turns nothing else. -/
theorem laysOnly_outCore
    (same : VerifiableInference.Desc.First.S → VerifiableInference.Desc.First.S → Bool) :
    VerifiableInference.Desc.K12.Coin.LaysOnly (H2K.JointK.outCore same) :=
  fun s t' s' h => VerifiableInference.Desc.K12.Coin.laysOnly_finish s t' s'
    ((H2K.JointK.outCore_ok same s t' s').1 h).1

/-- By the kernel: number 355 of the written list is the place of the joining of the pending
rows. -/
theorem place_355 : (VerifiableInference.Desc.First.flatPlacesOf
    VerifiableInference.Desc.Sound.linksFull true)[354 + 1]? = some ⟨1, none, 3, .K13⟩ := by
  decide +kernel

/-- By the kernel: at that place the chain stands at its finish. -/
theorem stand_355 : VerifiableInference.Desc.First.standAt VerifiableInference.Desc.Sound.linksFull
    ⟨1, none, 3, .K13⟩ = .fin := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: the items that are open at border 355 of the written lists. -/
theorem open_355 : (VerifiableInference.Desc.First.openSets VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
    (VerifiableInference.Desc.First.start VerifiableInference.Desc.Sound.linksFull))[354 + 1]?.getD
    [] = [.unmarked, .pinW, .pile, .pinI] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The line can fail: one border earlier eight items are open. -/
theorem open_354_more : ((VerifiableInference.Desc.First.openSets
    VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
    (VerifiableInference.Desc.First.start VerifiableInference.Desc.Sound.linksFull))[354]?.getD
    []).length = 8 := by decide +kernel

/-- **THE SECOND TIE AT THE WRITTEN LISTS, AT NUMBER 354, AT THE FILE's OWN PIECE.** -/
theorem hands_354 {Xi W Cells : Type} {Fr : VerifiableInference.Desc.Sound.Frame}
    (cs : OnBytes.Codes) (G : FileDescription Xi) (d : VerifiableInference.Desc.First.FoldData)
    (smp : ProofFile.InstPub × VerifiableInference.Desc.First.S → (s : Sending) →
      (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (Nn : Numbers) (Mg : VerifiableInference.Desc.First.Meaning ProofFile.InstPub W)
    (Z : ProofFile.Pub) (N : H2U.Places4) (D : OnBytes.Maker.WholeD)
    (q : VerifiableInference.Desc.Sound.Piece (_root_.Run.ckP .two) Fr
      (ProofFile.InstPub × VerifiableInference.Desc.First.S) ProofFile.Cl W)
    (hq : Seat354 Z N D q)
    (hII : ∀ x, Mg.pub .indexIs x = VerifiableInference.Desc.K13.indexIsC Nn.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = VerifiableInference.Desc.K13.indexThereC x.2)
    (hheld : Mg.held = fun j t x => VerifiableInference.Desc.smpHeld x.2.st x.2.book j t)
    (hL : d.L.places[Nn.indexNo]? = some Nn.index) (hft : d.ft = 0)
    (hsmp : ∀ a o x, ListedAt ms d.L.places o x → smp a x.1 x.2 =
      VerifiableInference.Desc.K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 a.2.st o)
    (hQb : (VerifiableInference.Desc.First.pubSets Mg.more VerifiableInference.Desc.Sound.linksFull
      (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull
        true))[354 + 1]?.getD [] = [])
    (hB : VerifiableInference.Desc.K12.Coin.goOnB Nn ⟨1, none, 2, .K12⟩ ⟨1, none, 3, .K13⟩
      (H2K.JointK.pL N) (VerifiableInference.Desc.K12.Door.toTree d.L) d.sent.codes = true)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × VerifiableInference.Desc.First.S →
      Option Cells)
    (hd : Mg.decodes = VerifiableInference.Desc.Sound.decodesOf decT)
    (hBl : ∀ y (x x' : ProofFile.InstPub × VerifiableInference.Desc.First.S), x'.1 = x.1 →
      decT y x' = decT y x)
    (hin : ∀ x y : ProofFile.InstPub × VerifiableInference.Desc.First.S, y.1 = x.1 →
      Mg.inOrder x = true → Mg.inOrder y = true)
    (hshown : Mg.shown = VerifiableInference.Desc.Sound.shownJT cs G ms)
    (hnc : Mg.noColl = VerifiableInference.Desc.Sound.noCollJT cs G smp ms)
    (hfen : Nn.index.1 < VerifiableInference.Desc.Sound.nTrees (D.ds₁.take 48237))
    (Rch : ℕ → (ProofFile.InstPub × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (hFacts : ∀ a : (ProofFile.InstPub × VerifiableInference.Desc.First.S) × Fr.E.Str,
      VerifiableInference.Desc.Sound.onQ Nn Mg VerifiableInference.Desc.Sound.linksFull
        (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
        (fun x : ProofFile.InstPub × VerifiableInference.Desc.First.S => x) 354 a → Rch 354 a →
      ¬ a.1.2.failed ≠ none → FactsF d a.1.2 ∧ a.1.2.st.codes = d.sent.codes) :
    T2At Nn Mg VerifiableInference.Desc.Sound.linksFull
      (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
      Rch 354 q := by
  obtain ⟨_, J, leave, _, hb, h0, hbase, ⟨_, _, rfl⟩, hS, hPub⟩ := hq
  obtain ⟨_, C, _, ho, _, _, _⟩ := hPub
  exact t2_at cs G (H2K.JointK.pL N) d smp ms Nn Mg _ _ 354 q _ _ hb h0 hS
    (laysOnly_outCore ProofFile.sameReply) (H2K.JointK.early_of_planOk _ C.plan)
    (H2K.JointK.answers_of_planOk _ C.plan) pinI_open_written hII hIT hheld hL hft hsmp C.plan ho
    ⟨1, none, 2, .K12⟩ ⟨1, none, 3, .K13⟩ Rid354.place_written place_355 stand_355 open_355 hQb hB
    (dec_rides_354 q _ Mg decT hb hS hd hBl) hin hshown hnc
    (by rw [hbase, Nat.zero_add]; exact hfen) Rch hFacts

end H2K12

#print axioms H2K12.laysOnly_outCore
#print axioms H2K12.place_355
#print axioms H2K12.stand_355
#print axioms H2K12.open_355
#print axioms H2K12.open_354_more
#print axioms H2K12.hands_354
