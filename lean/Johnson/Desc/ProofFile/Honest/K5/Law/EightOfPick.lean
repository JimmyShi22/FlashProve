-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/EightOfPick.lean: CONDITIONAL: AN ATTENTION SEGMENT's OWN
ROUNDS (kind K5): THE JOINED LAW AT THE BOOK THAT onlineProverFromPublicFiles RETURNS, WITH ONE PREMISE ON THE BOOK's
MAKER, hPWA, WHERE ITS FORM OF RECORD (k5_owes_all_joined_nine, RidesOnCs.lean) HAS THE PREMISE ON
THE LENDING. A step toward Eight.lean, which pays hPWA. Two statements with their proofs: calls. No
definition.

  k5_lends_at_pure              CONDITIONAL: under h, hg, hA and hPWA: **at each plan a of group g:
                                lendsRow A.B 0 ‹the seat's place› (k5Row ‹the seat›) = true**
  k5_owes_all_joined_eight_of   CONDITIONAL: k5_owes_all_joined_nine at Bk := A.B, with hPWA where
                                that has hLends

hPWA: at all sendings p0 p1 p2 at which bookWhole returns A.B at the head's description and
mergesByName of its first chain: the premise hPW of k5_lends_of_pick (LendsOfPick.lean) at B := A.B:
the form in which other authors' pick_whole (Honest/BookRowStretch.lean; not imported here) ends.

Called: atPure_ok · parts_of_atPure (ReturnsOf.lean): what onlineProverFromPublicFiles returns holds a return of
bookWhole · atPure_at_laid_ground: its description is the head's · k5_lends_of_pick ·
k5_owes_all_joined_nine.

The second statement was made by a program out of the theorem that it calls: the name; the letter Bk
for A.B; hLends' binder for hPWA's. Nothing else parts.

Limits. Conditional. hPWA is proved nowhere that this file imports. AT Bk := A.B ALONE: at another
book hLends stays (RidesOnCs.lean). All Limits of RidesOnCs.lean and LendsOfPick.lean hold here too:
the ends may hold emptily. Through its imports the file stands above the library's folder
ThirdParty/. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsOfPick
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesOnCs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

include h in
/-- **THE FRAME's TEST ON THE LENDING AT K5's PLACES, AT THE BOOK THAT onlineProverFromPublicFiles RETURNS.**
CONDITIONAL: h; g is below 12; hA; hPWA, which is proved nowhere that this file imports. -/
theorem k5_lends_at_pure {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hPWA : ∀ p0 p1 p2 : Johnson.G.ChainSends,
      bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2
        (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B →
      ∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder,
      (∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") →
      ∃ (idx : MsgAt) (a : List Want × Nat),
        ownerOf indexMaskRun (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder p0
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
          isIndexMaskMsg = some idx ∧
        linksWants (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder p0
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) idx
          (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).ends
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
            .ok a ∧
        wantsFree (a.1 ++ (loneWants idx
          (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).lone
          (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filter fun x =>
            x.place.link.isNone).flatMap planParts) a.2).1) = true ∧
        ∀ j, BookRow.pick ⟨b.place, j⟩ A.B.ahead =
          ((a.1 ++ (loneWants idx
            (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).lone
            (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filter fun x =>
              x.place.link.isNone).flatMap planParts) a.2).1).filter
                fun w => w.spender == ⟨b.place, j⟩).map (·.entry)) :
    ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow A.B 0 (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Row (seatOf keyOfK3 Zp A.G cF g a)) = true := by
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  obtain ⟨_, _, _, _, p0, p1, p2, -, hB⟩ := (parts_of_atPure hA).1.book
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := (atPure_at_laid_ground h.laid hG hA).2.2
  rw [eF] at hB
  exact fun a ha => k5_lends_of_pick h hg hB (hPWA p0 p1 p2 hB) keyOfK3 A.G ha

/-- **ALL OF THE MEMBER's DEBTS AT THE BOOK THAT onlineProverFromPublicFiles RETURNS, WITH ONE PREMISE ON THE BOOK's
MAKER IN THE STEAD OF THE PREMISE ON THE LENDING.** -/
theorem k5_owes_all_joined_eight_of {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hPWA : ∀ p0 p1 p2 : Johnson.G.ChainSends,
      bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2
        (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B →
      ∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder,
      (∀ r ∈ b.rounds, r.entry.name ≠ "FOLD epsilon") →
      ∃ (idx : MsgAt) (a : List Want × Nat),
        ownerOf indexMaskRun (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder p0
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
          isIndexMaskMsg = some idx ∧
        linksWants (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder p0
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) idx
          (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).ends
          ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filterMap (·.place.link)).eraseDups 0 =
            .ok a ∧
        wantsFree (a.1 ++ (loneWants idx
          (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).lone
          (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filter fun x =>
            x.place.link.isNone).flatMap planParts) a.2).1) = true ∧
        ∀ j, BookRow.pick ⟨b.place, j⟩ A.B.ahead =
          ((a.1 ++ (loneWants idx
            (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder).lone
            (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.filter fun x =>
              x.place.link.isNone).flatMap planParts) a.2).1).filter
                fun w => w.spender == ⟨b.place, j⟩).map (·.entry))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
          (ridersOf (csHead ν st R)) (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_nine h Q test carryX item n₁ n₂ Vd ν st R f w hg hA hO hfix hf
    (k5_lends_at_pure h hg hA hPWA) HQ hH

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_lends_at_pure
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_eight_of
