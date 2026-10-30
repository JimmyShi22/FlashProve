-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FiveAtBookOfReturn.lean: CONDITIONAL: THE FIVE SENTENCES OF THE KIND K5
AT THE PROVER AND THE BOOK THAT onlineProverFromPublicFiles RETURNS, WITH THE FILLING A LETTER P AND THE PREMISE ON THE
BOOK's LENDING PAID. No filling is named. One statement with its proof.

  k5_five_at_filling_book_of_return   k5_five_at_filling_written_riders (FillRoad.lean in this
  folder) at Bk := A.B, with hLends from k5_lends_paid_fill (FillFoot.lean)

The premises. h: the library's head on the public input · hg: g is below 12 · hA: onlineProverFromPublicFiles returns A
at the head's three files and P · hex: some lot of the filling's list has, at A's public part and
ground, the halves of K5's lot · ho: every lot of that list has there either no half at a place of
the kind K5, or these halves (at cells := id and the reader keyOfK3) · hfix: the Script's trees are
fixed in time · hf: the keeper at the kind K5 · HQ: K5ScriptQ · hH: a valid input's cells hold.

Limits. Conditional: none of the premises that the statements still bear is paid here. EACH OF THE
FIVE ENDS IS AN IMPLICATION FROM THE THREAD's INVARIANT IN FRONT OF THE STEP (Thr): no state that
meets it at one of the kind's borders is laid here or beneath, and where none does the ends say
nothing.
hf IS AN EQUATION OF FUNCTIONS: at a thread whose clause at the kind says more than K5KeepsAt, as
the first thread's does, it cannot be met: call the form with the letter Kp (FiveAtClauseLetter.lean).
A FILLING WITH FEW LOTS IS NOT THE HONEST PROVER: P is a free variable, and a filling whose one lot
is K5's meets hex and ho.
At b₀ := b0Head, the rider of csHead and Bk := A.B alone. That onlineProverFromPublicFiles returns at any filling is not
proved here.
At the library's full size and the format's second hash function alone: h is typed there.
NOT IN FRONT OF A LAW OVER COINS: the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. This file's ground, in the rule's sense of the word. Of
the first kind, tied to the coins: the run's coins k, the state s, the mid-run m and the strings E
under the invariant Thr inside each end, and the input under the predicate Vd, a letter that may
read the input's coins: m's input in Thr, w in hH, v in HQ. Of the second kind, on the Script: hfix;
hH, which names no coin; and HQ, which binds the run's coins and every input under Vd by "for all",
so by itself picks among none, though its first equation says that the witness's messages hold the
row's coins: a law over coins names these in its own statement. Of neither kind: h, hg, hA, hex, ho
and hf. What lifts the bar: none: the bar is flat.
h is a hypothesis; on whether it can be met see the head of Honest/K5/Law/Member.lean. It is said
whether the lending returns: nothing on what is lent. The three arguments of csHead are letters:
what its clauses say is not looked at, and a rider that is a conjunction of this list with a further
sentence is not spoken of. Beneath what is called lie closed facts that Lean's kernel has decided by
evaluation at the library's written lists: K4.W.onePass_full, and b0Head_closed
(Honest/Thread/ReplyAt.lean). Through its imports the file stands above the library's folder
ThirdParty/. No property of a prover or a protocol is claimed.

Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FillRoad

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
  {W₀ X₀ X : Type} {P : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ X} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells X₀ X}
  (Q : Script A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **THE FIVE SENTENCES AT THE BOOK OF WHAT onlineProverFromPublicFiles RETURNS, WITH THE LENDING PAID.** CONDITIONAL:
as `k5_five_at_filling_written_riders` at Bk := A.B, without hLends. hf cannot be met at the first
thread. NOT IN FRONT OF A LAW OVER COINS, A FILLING WITH FEW LOTS IS NOT THE HONEST PROVER (the
grounds: this file's head). -/
theorem k5_five_at_filling_book_of_return {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K5) ∨
      M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
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
  k5_five_at_filling_written_riders h Q test carryX item n₁ n₂ Vd ν st R f w hg hA hex ho hfix hf
    (k5_lends_paid_fill h hg hA) HQ hH

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_five_at_filling_book_of_return
