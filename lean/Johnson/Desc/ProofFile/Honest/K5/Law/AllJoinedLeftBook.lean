-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AllJoinedLeftBook.lean: CONDITIONAL: k5_owes_all_joined_left
(Honest/K5/Law/AllJoinedLeft.lean: all of the debts of the member of an attention segment's own
rounds, kind K5, at the prover that onlineProverFromPublicFiles returns at the filling of record widerFillAt) AT THE BOOK
THAT onlineProverFromPublicFiles RETURNS, WITH A TEST WITH CODE ON THAT BOOK IN THE STEAD OF hLent. One statement with
its proof: calls.

  k5_owes_all_joined_left_book   CONDITIONAL: the same end

WHAT IS LEFT, ALL OF IT: h · hg · hA · hO · hfix · hf · hRdM · HQ · hH: each as in
AllJoinedLeft.lean's head, with the Script typed at the book A.B · hBook: at the plan of the group
g: rowNamed (Honest/K5/Law/LendsOfBook.lean) accepts at A.B, K5's place and K5's parts: five
clauses, of which the first two are true by the parts' text (k5_parts_plain); the three that are
left: the book's table has no coin of these parts' own · every entry whose spender is one of them is
one that is spent · these entries are, by name and count, the runs that the part states.

WHAT IS PAID INSIDE, AND BY WHAT: the book passes its own tests: parts_of_atPure
(Honest/K5/Law/ReturnsOf.lean) and bookWhole_word (Honest/AtPureLaw.lean) · the description's test
on its places accepts: A's description is the head's (atPure_at_laid_ground,
Honest/AtHeadGround.lean), whose tests on the plan accept under h; placesOk_of_planOk
(Johnson/RunOne/Sound/KeyListsAtFK.lean) · K5's place stands in the first chain's list: k5_member
(Honest/K5/Law/Member.lean) · then lends5_of_named.

Limits. Conditional. hLent IS EXCHANGED, NOT PAID: hBook gives hLent; every book has a run's coins
(the type Coins is inhabited, Honest/Frame.lean), so by the lending's text the converse should hold
too, and the two be equivalent at this book: not shown. What is won is the form: "at all coins there
is …" becomes a Bool on the book and the parts' public fields. THE BOOK IS NO FREE LETTER ANY MORE:
the statement speaks of Scripts typed at A.B alone. hBook is no closed test: A is a letter. THAT
rowNamed ACCEPTS AT A.B IS SHOWN NOWHERE. All Limits of AllJoinedLeft.lean hold here too. Through
its imports the file stands above the library's folder ThirdParty/. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.AllJoinedLeft
import Johnson.Desc.ProofFile.Honest.K5.Law.LendsOfBook
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf
import Johnson.RunOne.Sound.KeyListsAtFK

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
  (RdL : Nat → (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → TS → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

/-- **THE SAME AT THE BOOK THAT onlineProverFromPublicFiles RETURNS, WITH A TEST ON THAT BOOK IN hLent's STEAD.**
CONDITIONAL: every premise stands, by name, in the file's head. -/
theorem k5_owes_all_joined_left_book {g : Nat} (hg : g < 12)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hRdM : ∀ a, (P5J.At.X Zp).A[g]? = some a → ∀ v s s', RdL (borderOf g) v s →
      K5KeepsM a.own s s' → RdL (borderOf g + 1) v s')
    (hBook : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      rowNamed A.B (A.B.rowsOf 0) (seatOf keyOfK3 Zp A.G cF g a).place
        (k5Half (W₀ := W₀) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) (id : Cells → Cells)
          (seatOf keyOfK3 Zp A.G cF g a)).parts 0 = true)
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
  obtain ⟨_, _, _, _, _, _, _, -, hB⟩ := (parts_of_atPure hA).1.book
  have hw : A.B.word A.F = none := bookWhole_word hB
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := (atPure_at_laid_ground h.laid hG hA).2.2
  have hp : A.F.placesOk = true := by
    rw [eF]
    exact Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hpl : (⟨1, some (2 * g + 1), 3, .K5⟩ : Place) ∈ A.F.first.blocksInOrder.map (·.place) := by
    rw [eF]
    obtain ⟨blk, a, hm, -, Dc⟩ := k5_member h hg
    exact List.mem_map.2 ⟨blk, List.mem_of_getElem? hm, Dc.place⟩
  exact k5_owes_all_joined_left h Q test carryX item n₁ n₂ Vd RdL f w hg hA hO hfix hf hRdM
    (fun a ha => lends5_of_named hw hp hpl (hBook a ha)) HQ hH

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.k5_owes_all_joined_left_book
