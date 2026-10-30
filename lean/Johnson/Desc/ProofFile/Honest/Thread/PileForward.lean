-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/PileForward.lean: the open item `pile` of the first chain's
invariant passes over a sub-protocol whose step changes the statement, as long as the step leaves
the pending rows and what they read. The item states that every pending row holds of the witness
(`K13.Law.RowsTrue` at the reader `K13.Law.rwBook`). RowPileRides.lean shows that it passes where
the step leaves the statement and the list of commitment trees as they were. That is false for a
sending of oracle messages (kind K1) and for the closing of a segment (kind K10). No definition.

What the pending rows read. Where the library's test `K13.pileMasksC` accepts, every mask entry that
a pending row names belongs to one oracle message, the message of the index masks. The reader finds
that message's entries through the table of codes, the message's shape, its place in the list of
commitment trees and the tree there. If the step leaves these four, the readers at the two states
agree on all that the rows read (`K13.Law.AgreeAt`, `K13.Law.holds_congr`).

The library shows the opposite direction for an accepting step of a sending
(`K13.Law.agreeCommit`, Johnson/Desc/K13/Law/ReaderAtCommit.lean; `K1.pileBack_book`,
Johnson/Desc/K1/Law/ReaderAtLater.lean) and for the code switch (`agree_left`,
Johnson/Top/H0/K2Ties/Pile.lean). The proof of `rwBook_agree` is the second half of the proof of
`agreeCommit`, with the four equations as hypotheses.

  1  `rwBook_agree`   the readers at the two states agree at a message
  2  `shape_of_extends`   a message of the statement before the step has the same shape after it
  3  `pile_older`   the item's statement passes, at the library's meaning `mgAll`
  4  `ridesPastAt_pile_older`   the hypothesis `RidesPastAt` (Honest/Thread/Shares.lean) for the
     item at `lettersHead`, at every sub-protocol number `b`

The hypothesis of 4 may use the invariant before the step (`Thr`).

Limits.
  * `ridesPastAt_pile_older`: full size only, and only under the library's hypothesis `AtMgA` at
    the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The hypotheses on the two states have to be shown for each kind. This file shows them for no
    kind and at no state.
  * The witness is the same before and after the step.
  * Nothing here shows that the item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.First.Close.Law.FillRowRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (S Item Meaning BookKept wordsFirst_older)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_pile CellsQ wordsFirst)
open VerifiableInference.Desc.K13 (pileMasksC)
open VerifiableInference.Desc.K13.Law (AgreeAt Holds holds_congr rwBook maskCut tableSize_of_shape
  pileMasksC_iff)
open OnBytes.Means (Extends)
open OnBytes.Slice (GE)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The readers at the two states agree at a message -/

/-- The readers at two states agree on the matrix and on the mask entries of message `o`, if the two
states have the same table of codes, the same shape of `o`, the same place of `o` and the same tree
there. -/
theorem rwBook_agree {Pp Cells Tok : Type} {nR k : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin k → Bool) → GE) (x x' : Pp × S) (w : Wit Cells Tok MsgT) (o : ℕ)
    (hc : x'.2.st.codes = x.2.st.codes)
    (hx : (x'.2.st.oracles[o]?).map (·.shape) = (x.2.st.oracles[o]?).map (·.shape))
    (hp : x'.2.book.place[o]? = x.2.book.place[o]?)
    (ht : ∀ q, x.2.book.place[o]? = some q → x'.2.book.trees[q.1]? = x.2.book.trees[q.1]?) :
    AgreeAt o (rwBook arr mat x' w) (rwBook arr mat x w) := by
  refine ⟨rfl, fun i => ?_⟩
  show maskCut x'.2.st (wordsFirst arr x'.2.st x'.2.book w) ⟨o, i⟩ =
    maskCut x.2.st (wordsFirst arr x.2.st x.2.book w) ⟨o, i⟩
  have hw : wordsFirst arr x'.2.st x'.2.book w o .mask i =
      wordsFirst arr x.2.st x.2.book w o .mask i :=
    wordsFirst_older arr x.2.st x'.2.st x.2.book x'.2.book w o hc hx hp ht .mask i
  unfold maskCut
  dsimp only
  rw [tableSize_of_shape hc hx, hw]

/-! ## 2 A message's shape -/

/-- A message of the statement before the step has the same shape after it. -/
theorem shape_of_extends {A B : OnBytes.Statement} (hE : Extends A B) {o : ℕ}
    (ho : o < A.oracles.size) :
    (B.oracles[o]?).map (·.shape) = (A.oracles[o]?).map (·.shape) := by
  obtain ⟨x', hx', e⟩ := hE.shape o _ (Array.getElem?_eq_getElem ho)
  rw [hx', Array.getElem?_eq_getElem ho, Option.map_some, Option.map_some, e]

/-! ## 3 At the library's meaning -/

section
variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {s s' : S}

/-- The statement of `pile` passes from `s` to `s'`. -/
theorem pile_older (hr : s'.rows = s.rows) (hOn : pileMasksC s = true)
    (hlt : s.out.indexMasks < s.st.oracles.size) (hE : Extends s.st s'.st) (hB : BookKept s s')
    (z : P) (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT)
    (h0 : (mgAll 𝔇 Mg).pile (z, s) y w) : (mgAll 𝔇 Mg).pile (z, s') y' w := by
  rw [mgAll_pile] at h0 ⊢
  have h1 : ∀ r ∈ s.rows, Holds _ (rwBook 𝔇.arr 𝔇.mat13 (z, s) w) r := h0
  show ∀ r ∈ s'.rows, Holds _ (rwBook 𝔇.arr 𝔇.mat13 (z, s') w) r
  intro r hm
  rw [hr] at hm
  exact (holds_congr _ ((pileMasksC_iff s).1 hOn r hm)
    (rwBook_agree 𝔇.arr 𝔇.mat13 (z, s) (z, s') w s.out.indexMasks hE.codes
      (shape_of_extends hE hlt) (hB _ hlt).1 (hB _ hlt).2)).2 (h1 r hm)

end

/-! ## 4 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `pile` passes over sub-protocol `b` if, wherever the invariant holds before the step,
the step leaves the pending rows, these name mask entries of the message of the index masks alone,
that message is there, the statement after the step extends the one before it, and every message
keeps its place and the tree there. -/
theorem ridesPastAt_pile_older {b : Nat}
    (hk : ∀ k s mm E s',
      Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b k s mm E →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      s'.rows = s.rows ∧ pileMasksC s = true ∧ s.out.indexMasks < s.st.oracles.size ∧
        Extends s.st s'.st ∧ BookKept s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile := by
  intro k s mm E s' ps v hA hK h0
  obtain ⟨h1, h2, h3, h4, h5⟩ := hk k s mm E s' hA hK
  exact pile_older { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase
    h1 h2 h3 h4 h5 mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h0

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rwBook_agree
#print axioms ProofFile.Honest.FirstThread.shape_of_extends
#print axioms ProofFile.Honest.FirstThread.pile_older
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pile_older
