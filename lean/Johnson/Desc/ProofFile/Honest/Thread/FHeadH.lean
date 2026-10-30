-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadH.lean: one more layer of the condition `keeps` of the
first chain's invariant at the full size. `fHeadH` is `fHeadG` (FHeadG.lean) with one relation
beside it at the kinds K2, K7 and K12: what the item `pile` reads of the verifier's state is after
the step what it was before (`PileKept`). The clauses of `fHeadG` at these kinds do not say that:
K2's says nothing of the book of trees, K7's nothing of the rows on the table, and K12's keeps of an
older tree only the source. With the relation the item `pile` passes over these 27 sub-protocols.
Every statement at `fHeadG` stays as it is; `cellH_of_G` carries a cell of the column `hR` of the
gathering from `fHeadG` to `fHeadH`.

  1  `PileKept`, `relsBook`, `fHeadH`   three definitions
  2  `kpBy_fHeadH`   `fHeadH` implies `fHeadG`
  3  `pile_kept`   at the library's meaning: the statement of `pile` passes from one state to
     another under `PileKept`, if the rows on the table name mask entries of the message of the
     index masks alone
  4  `ridesPastAt_pile_kept`   so at the invariant
  5  `cellH_of_G`, `cellH_pile`   cells of the column `hR` at `fHeadH`

Why `PileKept` and not more. `pile_older` (PileForward.lean) asks that the statement after the step
extends the one before and that every message keeps its place in the book and the tree there. At
K2 and K12 that is false in general: a reading adds 1 to the field `lists` of each older tree that
it opens. But the item's reader reads the book at one message alone, the message of the index masks,
and of that message's tree only the number. The library says so: `agree_across`
(Johnson/Loose/H2K12/Rides354.lean) proves that the reader answers alike at two states with the same
table of codes, the same shape of the message and the same seat. `PileKept` asks these three and the
rows. They are four fields of that file's own record `Across`.

Is the relation true at a sub-protocol's accepting step? By reading, not proved here. At K2, by its
authors' reading: the switch writes the book twice, at a receiving and at the reading of the old
rows, which adds 1 to the field `lists` of each tree that it opens. So an older tree need not stay
as a whole there either. The library's `K2.yes_seated` (Johnson/Top/H0/Tw/K2C/SeatedAt.lean) says
that every older place stays and that every older tree keeps its number, source, shape and parts.
At K7: the clause leaves the statement and the book (`k7KeepsAt_pile`, PileCellsEqK7.lean); that the
rows stay is asked of its authors. At K12, by its authors' reading: the table of codes stays
(`OutK.codes`, Johnson/Desc/K12/Law/OutK.lean), and of every older tree the shape, the number and
the parts stay, and every place (`OutK.book`).

Limits.
  * That `keeps` := `fHeadH` holds after a sub-protocol's accepting step is not proved here.
  * Full size only, under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHeadG
import Johnson.Desc.ProofFile.Honest.Thread.RowPileForwardKinds
import Johnson.Desc.ProofFile.Honest.Thread.KeepsMono
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes
import Johnson.Loose.H2K12.Rides354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item Meaning)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_pile CellsQ seatBy noFirst)
open VerifiableInference.Desc.K13 (pileMasksC)
open VerifiableInference.Desc.K13.Law (Holds holds_congr rwBook pileMasksC_iff)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The definitions -/

/-- **What the item `pile` reads of the state is after the step what it was before**: the rows on
the table, the table of codes, and of the message of the index masks its shape and its seat by the
book, which is its tree's number and its place among that tree's parts (`seatBy`, `noFirst`:
Johnson/Desc/Sound/TabAt.lean). It is a definition: a part of a clause of `keeps`. -/
def PileKept (s s' : S) : Prop :=
  s'.rows = s.rows ∧ s'.st.codes = s.st.codes ∧
    (s'.st.oracles[s.out.indexMasks]?).map (·.shape) =
      (s.st.oracles[s.out.indexMasks]?).map (·.shape) ∧
    seatBy noFirst s'.book s.out.indexMasks = seatBy noFirst s.book s.out.indexMasks

/-- What the item `pile` needs of `keeps` beyond `fHeadG`, kind by kind: `PileKept` at K2, K7 and
K12; everywhere else it is "True". It is a definition: a part of a clause of `keeps`. -/
def relsBook : KindName → TS → TS → Prop
  | .K2 | .K7 | .K12 => PileKept
  | _ => fun _ _ => True

/-- `fHeadG` with this relation beside it. It is a definition: it fills an argument of the
invariant. -/
def fHeadH (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (D : VerifiableInference.Desc.First.PubData) :
    KindName → Place → TS → TS → Prop :=
  fun κ p s s' => fHeadG Zp cF G take P11 p12 P13 D κ p s s' ∧ relsBook κ s s'

/-- `fHeadH` implies `fHeadG`. -/
theorem kpBy_fHeadH {Zp : ProofFile.Pub} {cF : Chain TS ProofFile.Cl} (G : ProofFile.Ground) (take : Nat → Bool)
    (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
    (P13 : VerifiableInference.Desc.K13.Where) (Dp : VerifiableInference.Desc.First.PubData) :
    ∀ p s s', kpBy (fHeadH Zp cF G take P11 p12 P13 Dp) p s s' →
      kpBy (fHeadG Zp cF G take P11 p12 P13 Dp) p s s' :=
  fun _ _ _ hk => hk.1

/-! ## 2 At the library's meaning -/

section
variable {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  {s s' : S}

/-- The statement of `pile` passes from `s` to `s'`. -/
theorem pile_kept (hk : PileKept s s') (hOn : pileMasksC s = true) (z : P) (y y' : Strs)
    (w : Wit (CellsQ rows cols) Tok MsgT) (h0 : (mgAll 𝔇 Mg).pile (z, s) y w) :
    (mgAll 𝔇 Mg).pile (z, s') y' w := by
  rw [mgAll_pile] at h0 ⊢
  have h1 : ∀ r ∈ s.rows, Holds _ (rwBook 𝔇.arr 𝔇.mat13 (z, s) w) r := h0
  show ∀ r ∈ s'.rows, Holds _ (rwBook 𝔇.arr 𝔇.mat13 (z, s') w) r
  intro r hm
  rw [hk.1] at hm
  exact (holds_congr _ ((pileMasksC_iff s).1 hOn r hm)
    (H2K12.Rid354.agree_across 𝔇.arr 𝔇.mat13 (z, s) (z, s') s.out.indexMasks w w hk.2.1 hk.2.2.1
      hk.2.2.2 rfl fun _ _ => ⟨rfl, rfl⟩)).2 (h1 r hm)

end

/-! ## 3 At the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)

/-- The item `pile` passes over sub-protocol `b` if `keeps` gives `PileKept`. -/
theorem ridesPastAt_pile_kept (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {b : Nat}
    (hb : b ≤ cF.blocksInOrder.length)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps b s s' →
      PileKept s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread b Item.pile := by
  intro k s mm E s' ps v hA hK h0
  exact pile_kept { h.𝔇 with decT := fun _ _ => some (Q.cells mm.st.input), cr1 := carryX } mgBase
    (hk s s' hK) (head_pileMasks h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA)
    mm.st.input.x.pub
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs E)
    ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.strs (E.add ps)) v h0

variable (w : Local W₀ Rc ProofFile.Inst Tr) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- A cell of the column `hR` at `fHeadG` is one at `fHeadH`. -/
theorem cellH_of_G {b : Nat} {i : Item}
    (hc : RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b i) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b i :=
  head_ridesPastAtS_mono h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w
    (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD))
    (kpBy_fHeadH G take P11 p12 P13 h.𝔇.pubD) Said hc

/-- **The item `pile` at a place of the kind K2, K7 or K12**, where `keeps` is `fHeadH`. -/
theorem cellH_pile {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K2 ∨ p.kind = KindName.K7 ∨ p.kind = KindName.K12) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b Item.pile := by
  have hlen : b ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    omega
  refine ridesPastAtS_of _ _ (ridesPastAt_pile_kept h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hlen fun s s' hK => ?_)
  have a : fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD p.kind p s s' :=
    (head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadH Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp s s').1 hK
  have a2 : relsBook p.kind s s' := a.2
  rcases hk with hk | hk | hk <;> rw [hk] at a2 <;> exact a2

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.kpBy_fHeadH
#print axioms ProofFile.Honest.FirstThread.pile_kept
#print axioms ProofFile.Honest.FirstThread.ridesPastAt_pile_kept
#print axioms ProofFile.Honest.FirstThread.cellH_of_G
#print axioms ProofFile.Honest.FirstThread.cellH_pile
