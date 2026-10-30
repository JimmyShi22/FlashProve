-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FillRoad.lean: CONDITIONAL: THE FIVE SENTENCES OF THE KIND K5
(it plays; behind its yes; the exchange; it rides past; it is accepted, for every fall: at the
border of each of the twelve groups) AT THE PROVER THAT onlineProverFromPublicFiles RETURNS, WITH THE FILLING A LETTER P.
No filling is named. Four statements with their proofs.

  k5_five_at_filling_border_and_fit_left_open   the base law k5_owes_all_joined_kind₅_lent
  (AllJoined5.lean in this folder) at H := A.H, with LotLaid paid by lotLaid_fill_head
  (FillFoot.lean)
  k5_five_at_filling_ground_of_return   the ground is A.G; the thread's fit from hfix
  k5_five_at_filling_lending_test   hLends, the frame's Bool, in hLent's stead
  k5_five_at_filling_written_riders   at the riders of csHead: hRdM is paid

The premises. h: the library's head on the public input · hg: g is below 12 · hG (the first law
alone): G, a value of the type Ground, is the one made of the head's public part · hA: onlineProverFromPublicFiles
returns A at the head's three files and P · hex: some lot of the filling's list has, at A's public
part and ground, the halves of K5's lot · ho: every lot of that list has there either no half at a
place of the kind K5, or these halves (at cells := id and the reader keyOfK3) · hfit (the first law
alone): the thread fits the description's length · hb₀ (the first law alone): b₀ is not the border
behind the kind's · hfix: the Script's trees are fixed in time · hf: the keeper at the kind K5 ·
hRdM: the riders ride on · hLent | hLends: the book's lending to the kind's row returns · HQ:
K5ScriptQ · hH: a valid input's cells hold.

Limits. Conditional: none of the premises that the statements still bear is paid here. EACH OF THE
FIVE ENDS IS AN IMPLICATION FROM THE THREAD's INVARIANT IN FRONT OF THE STEP (Thr): no state that
meets it at one of the kind's borders is laid here or beneath, and where none does the ends say
nothing.
hf IS AN EQUATION OF FUNCTIONS: at a thread whose clause at the kind says more than K5KeepsAt, as
the first thread's does, it cannot be met: call the form with the letter Kp (FiveAtClauseLetter.lean).
A FILLING WITH FEW LOTS IS NOT THE HONEST PROVER: P is a free variable, and a filling whose one lot
is K5's meets hex and ho.
b₀ is b0Head in the last three statements alone, and the rider is csHead's in the last alone. That
onlineProverFromPublicFiles returns at any filling is not proved here.
At the library's full size and the format's second hash function alone: h is typed there.
NOT IN FRONT OF A LAW OVER COINS: the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. This file's ground, in the rule's sense of the word. Of
the first kind, tied to the coins: the run's coins k, the state s, the mid-run m and the strings E
under the invariant Thr inside each end, and the input under the predicate Vd, a letter that may
read the input's coins: m's input in Thr, w in hH, v in HQ. Of the second kind, on the Script: hfix;
hH, which names no coin; and HQ, which binds the run's coins and every input under Vd by "for all",
so by itself picks among none, though its first equation says that the witness's messages hold the
row's coins: a law over coins names these in its own statement. Of neither kind: h, hg, hG, hA, hex,
ho, hfit, hb₀, hf, hRdM, hLent, which is bound over all coins, and hLends. What lifts the bar: none:
the bar is flat.
h is a hypothesis; on whether it can be met see the head of Honest/K5/Law/Member.lean. The three
arguments of csHead are letters: what its clauses say is not looked at, and a rider that is a
conjunction of this list with a further sentence is not spoken of, in the last statement. Beneath
what is called lie closed facts that Lean's kernel has decided by evaluation at the library's
written lists: K4.W.onePass_full, and b0Head_closed (Honest/Thread/ReplyAt.lean). Through its
imports the file stands above the library's folder ThirdParty/. No property of a prover or a
protocol is claimed.

Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OnePassFull
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoined5
import Johnson.Desc.ProofFile.Honest.K5.Law.FillFoot
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesFree
import Johnson.Desc.ProofFile.Honest.Thread.FitsHead
import Johnson.Desc.ProofFile.Honest.Thread.ReplyIs

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
  {W₀ X₀ X : Type} {P : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ X} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells X₀ X} {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat)

section
variable (b₀ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (RdL : Nat → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **THE FIVE SENTENCES AT THE PROVER THAT onlineProverFromPublicFiles RETURNS AT A FILLING THAT HOLDS THE KIND's LOT**,
the reply's border b₀ and the thread's fit left to the caller. CONDITIONAL: the premises of
k5_owes_all_joined_kind₅_lent at H := A.H and cells := id, with hA, hex and ho in hL's stead. hf
cannot be met at the first thread. NOT IN FRONT OF A LAW OVER COINS, A FILLING WITH FEW LOTS IS NOT
THE HONEST PROVER (the grounds: this file's head). -/
theorem k5_five_at_filling_border_and_fit_left_open {g : Nat} (hg : g < 12) {G : Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K5) ∨
      M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (hfit : (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread.fits
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.length = true)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hb₀ : b₀ ≠ borderOf g + 1)
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst X Bk (id : Cells → Cells) (seatOf keyOfK3 Zp G cF g a))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_owes_all_joined_kind₅_lent h A.H Q test carryX item n₁ n₂ b₀ Vd RdL f w hg hG
    (lotLaid_fill_head h hG hA hex ho) hfit hf hb₀ hRdM hLent HQ hH

end

section
variable (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (RdL : Nat → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **THE FIVE SENTENCES, AT A's OWN GROUND**: the thread fits by hfix. CONDITIONAL: every premise
stands, by name, in the file's head. hf cannot be met at the first thread. NOT IN FRONT OF A LAW
OVER COINS, A FILLING WITH FEW LOTS IS NOT THE HONEST PROVER (the grounds: this file's head). -/
theorem k5_five_at_filling_ground_of_return {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K5) ∨
      M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLent : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      Lends5 W₀ IndexCommitterCoins ProofFile.Inst X Bk (id : Cells → Cells) (seatOf keyOfK3 Zp A.G cF g a))
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        fall (borderOf g) := by
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  exact k5_five_at_filling_border_and_fit_left_open h Q test carryX item n₁ n₂ b0Head Vd RdL f w hg hG hA hex ho
    (FirstThread.fits_head h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w
      K4.W.onePass_full hfix) hf (FirstThread.b0Head_ne_k5 g) hRdM hLent HQ hH

/-- **THE FIVE SENTENCES WITH THE FRAME's Bool IN THE STEAD OF THE PREMISE ON THE LENDING.**
CONDITIONAL: as `k5_five_at_filling_ground_of_return`, with hLends where that has hLent. hf cannot
be met at the first thread. NOT IN FRONT OF A LAW OVER COINS, A FILLING WITH FEW LOTS IS NOT THE
HONEST PROVER (the grounds: this file's head). -/
theorem k5_five_at_filling_lending_test {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K5) ∨
      M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hLends : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow Bk 0 (seatOf keyOfK3 Zp A.G cF g a).place (k5Row (seatOf keyOfK3 Zp A.G cF g a)) =
        true)
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp A.G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    (Plays (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Behind (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g) ∧
      RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        (borderOf g)) ∧
      ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd RdL (kpBy f) w).thread
        fall (borderOf g) :=
  k5_five_at_filling_ground_of_return h Q test carryX item n₁ n₂ Vd RdL f w hg hA hex ho hfix hf hRdM
    (fun a ha => (lends5_iff Bk _ _).2 (hLends a ha)) HQ hH

end

variable (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **THE FIVE SENTENCES AT THE WRITTEN LIST OF RIDERS.** CONDITIONAL: as
`k5_five_at_filling_lending_test`, without hRdM. hf cannot be met at the first thread. NOT IN FRONT
OF A LAW OVER COINS, A FILLING WITH FEW LOTS IS NOT THE HONEST PROVER (the grounds: this file's
head). -/
theorem k5_five_at_filling_written_riders {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K5) ∨
      M.halves A.Z A.G = (k5LotK id keyOfK3).halves A.Z A.G)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hLends : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow Bk 0 (seatOf keyOfK3 Zp A.G cF g a).place (k5Row (seatOf keyOfK3 Zp A.G cF g a)) =
        true)
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
  k5_five_at_filling_lending_test h Q test carryX item n₁ n₂ Vd (ridersOf (csHead ν st R)) f w hg
    hA
    hex ho hfix hf (fun a _ => k5_rides_on_csHead ν st R hg a.own) hLends HQ hH

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_five_at_filling_border_and_fit_left_open
#print axioms ProofFile.Honest.K5.k5_five_at_filling_ground_of_return
#print axioms ProofFile.Honest.K5.k5_five_at_filling_lending_test
#print axioms ProofFile.Honest.K5.k5_five_at_filling_written_riders
