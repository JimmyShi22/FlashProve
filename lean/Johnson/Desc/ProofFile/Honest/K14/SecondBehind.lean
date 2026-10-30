-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondBehind.lean: kind K14: WHAT IS PROVED: FormKeeps (wherever
the thread holds in front of a member and the member's step returns, the form holds behind it and
the step has left what keeps names) AT THE MEMBER 0 OF THE LAST CHAIN's THREAD
(Honest/Thread/Last.lean): under four premises on the thread's letters (its free arguments) in
second_formKeeps; with no premise, at three letters laid, at the IOP as written in Lean in
second_at_last. THE LIMIT: with the form laid as fillZ, the thread in front of the member asks
fillZ's test at border 0; wherever that test is false the claim holds vacuously; it is false at
every shape whose masks are not sent ahead and at every setting with more than one answer to a
sample, and fillZ has been evaluated at no state (see «What is not claimed»).

The member is "K14, second part" (Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean: batchLinearConstraintsSecondPart), the first member of
a proof file's last chain, at the kind's seventh place, ⟨3, none, 0, .K14⟩. (The other six places of
the kind are in the shared chain: the pieces 1, 3, 4, 6, 7 and 8.) The member has no round: nobody
sends, no challenge comes, no column is read: so no part of a prover is meant to stand at it, and no
simulator. Its decide function takes Omega over from the shared chain's end, joins it to the
request's own group and lays the row (Dot). Definitions, and statements with their proofs.

  LikeSecond blk p   blk declares no round and has batchLinearConstraintsSecondPart p's decide function: all that a step
                  reads of it
  SecondLaid p s s'   **the clause for keeps at that place**: the library's own relation
                  VerifiableInference.Desc.Third.Laid (Johnson/Desc/Third/Law/LaidDef.lean) at some
                  border, Omega, own group and row
  kpSecond p Kp   the letter Kp of lettersLast (Honest/Thread/LastHead.lean) with that clause laid
                  at the place ⟨3, none, 0, .K14⟩; Kp elsewhere
  second_formKeeps   **FormKeeps at the member 0, GENERAL IN THE LETTERS**, under four premises: the
                  form is the library's closed test fillZ (Johnson/Desc/Last/ShapeRowZero.lean)
                  (hPL); whatever stands at the number 0 of the thread's list declares no round and
                  has batchLinearConstraintsSecondPart p's decide function (hblk: LikeSecond); keeps at 0 is implied by
                  SecondLaid (hK); and the letter order follows from that form at border 1 (hO)
  inOrder_of_form fillZ's test at border 1 gives that the statement is in order (Means.InOrder): it
                  asks that the statement is tidy
  first_of_last   the first member of the last chain of the IOP as written in Lean, over ANY first
                  chain cF, is batchLinearConstraintsSecondPart at the library's parameters, carried to the file's type of
                  claims: by the library's last_blocks_in (Johnson/ToldDescR/LastBlocks.lean)
  second_at_last  **so FormKeeps at the member 0 of lettersLast's own thread, WITH NO PREMISE**, at
                  three letters laid: PL := fillZ, Kp := kpSecond, order := "the statement is in
                  order"; it holds vacuously wherever fillZ's test at border 0 is false

BOTH HALVES ARE CALLS: the form behind is the library's step_zero
(Johnson/Desc/Last/ShapeGives.lean), through shapeAt_of_fill and fill_of_shapeAt; keeps is the
library's laid_k14Second (Johnson/Desc/Third/Law/Laid.lean). Each has the form "a step's .ok gives":
nothing here says that the member accepts.

FormKeeps (Honest/K14/Debts2.lean) IS Behind (Honest/Thread/Pays.lean) WITHOUT ITS CLAUSE ON rides.
LACKING FOR Behind AT THE MEMBER 0: that the letter rides holds at border 1 at the state behind. At
lettersLast rides is a letter (Rd); the frame's behind_of_keeps (Honest/Thread/Riders.lean) wants it
as a list of clauses: one that spans the member must be shown to stay over it, and one that begins
at border 1 must be shown to be laid by the member: two things would have to be shown; no file does
so, and no file calls second_formKeeps or second_at_last.

What is not claimed. That the thread holds at any run: with the form laid as fillZ its clause on the
form at border 0 asks that the shared chain has ended, and is false at every shape whose masks are
not sent ahead and at every setting with more than one answer to a sample
(Johnson/Desc/Last/ShapeAt.lean, its limits (2) and (8)): where it is false FormKeeps holds
vacuously. THAT THE TEST CAN BE MET: no file of this folder evaluates fillZ, or shapeAt, the test
beneath it, at any state, and ShapeAt.lean's own limit (1) says that shapeAt has been evaluated at
none. (In a file that is not part of this tree shapeAt was evaluated to true at border 0 at one
small synthetic state; fillZ itself at none.) That the member accepts (Accepted): under premises of
their own, Honest/K14/SecondYes.lean and Honest/K14/SecondDoor.lean. The exchange of items (the row
owes rows and shuts ev and dot). That the three pins go past it (RidesPast). fs, the reader of the
first chain's last state, and R, the own test's declared rounds, are letters of fillZ. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.LastHead
import Johnson.Desc.ProofFile.Honest.K14.Debts2
import Johnson.Desc.Last.ShapeRowZero
import Johnson.Desc.Third.Law.Laid
import Johnson.ToldDescR.LastBlocks
import Johnson.Desc.K14.Law.Step
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place Chain OpenedColumn)
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart)
open VerifiableInference.Desc.Third.Law (laid_k14Second)
open VerifiableInference.Desc.Last (fillZ fillAt shapeAt shapeAt_of_fill fill_of_shapeAt step_zero
  behindOk_of_one lastPlaces MeaningL PromMeaningL)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St)

/-- blk declares no round and has batchLinearConstraintsSecondPart p's decide function. -/
structure LikeSecond {Cl : Type} (blk : Block S₃ Cl) (p : P₁₄) : Prop where
  rounds : blk.rounds = []
  decide : blk.decide = (batchLinearConstraintsSecondPart (Cl := Cl) p).decide

/-- **The clause for keeps at the place ⟨3, none, 0, .K14⟩**: what the member has laid. -/
def SecondLaid (p : P₁₄) (s s' : S₃) : Prop :=
  ∃ b y G dot, VerifiableInference.Desc.Third.Laid p.S s s' b y G dot

/-- The letter Kp with that clause laid at the kind's place in the last chain. -/
def kpSecond (p : P₁₄) (Kp : Place → S₃ → S₃ → Prop) (q : Place) (s s' : S₃) : Prop :=
  if q = ⟨3, none, 0, .K14⟩ then SecondLaid p s s' else Kp q s s'

section general
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P S₁ Wt : Type}
  (L : LastThread.Letters Bk St S₃ Cl W₀ Rc Xi Tr X (P × S₁) Wt) (p : P₁₄)
  (R : List Fmt.DeclaredRound) (fs : P × S₁ → VerifiableInference.Desc.First.S)

/-- **FormKeeps at the member 0, general in the letters**, under four premises: the form is fillZ
(hPL); whatever stands at the number 0 of the thread's list declares no round and has batchLinearConstraintsSecondPart p's
decide function (hblk); SecondLaid implies keeps at 0 (hK); fillZ's test at border 1 implies the
letter order (hO). Where the list is empty, or the thread holds at no state in front of the member,
it holds vacuously. -/
theorem second_formKeeps (hPL : L.PL = fillZ p R fs)
    (hblk : ∀ blk, L.bs[0]? = some blk → LikeSecond blk p)
    (hK : ∀ s s', SecondLaid p s s' → L.keeps 0 s s')
    (hO : ∀ x e s', (fillZ p R fs).shape 1 x e s' = true → L.order s') :
    FormKeeps L.thread 0 := by
  intro blk hb k s m E ds y cols s' hA hds hS
  obtain ⟨-, -, ⟨hF, -⟩, -, -, -, -⟩ := hA
  obtain ⟨hM, hst⟩ := hS
  obtain ⟨gs, hd⟩ := Desc.K14.Law.step_decides _ blk s s' _ cols _ hst
  rw [(hblk blk hb).decide] at hd
  have hL : SecondLaid p s s' := laid_k14Second p s s' _ gs hd
  -- the member has no round: no challenge comes: what was handed to the chain is read as in front
  rw [(hblk blk hb).rounds] at hds
  obtain rfl : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => cases hds
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  have ei := (play_mid _ _ _ _ _ hy).1
  have eh := play_heard _ _ _ _ _ hy
  rw [List.append_nil] at eh
  have es : L.thread.seat k y.2 s' = ((L.thread.seat k m s).1, s') := by
    unfold Thread.seat
    rw [ei, eh]
  have hF' : (L.PL.shape 0 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
      (!decide (lastPlaces.length ≤ 0) || L.PL.nothingLeft s)) = true := hF
  rw [Bool.and_eq_true] at hF'
  have h0 := hF'.1
  rw [hPL] at h0
  obtain ⟨f, o, hf, ho, hs0⟩ := shapeAt_of_fill p R _ _ h0
  have h1 := fill_of_shapeAt p R _ _ hf ho (step_zero (Cl := Cl) hs0 _ gs hd)
  refine ⟨⟨?_, ?_⟩, hK s s' hL⟩
  · rw [es]
    show (L.PL.shape 1 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s' &&
        (!decide (lastPlaces.length ≤ 1) || L.PL.nothingLeft s')) = true
    rw [Bool.and_eq_true]
    refine ⟨?_, rfl⟩
    rw [hPL]
    exact h1
  · rw [es]
    exact hO _ _ s' h1

end general

/-- fillZ's test at border 1 gives that the statement is in order: it asks that the statement is
tidy. -/
theorem inOrder_of_form {P S₁ : Type} (p : P₁₄) (R : List Fmt.DeclaredRound)
    (fs : P × S₁ → VerifiableInference.Desc.First.S) (x : P × S₁) (e : St) (s' : S₃)
    (h : (fillZ p R fs).shape 1 x e s' = true) : OnBytes.Means.InOrder s'.st := by
  obtain ⟨f, o, -, -, hs⟩ := shapeAt_of_fill p R _ _ h
  obtain ⟨_, B⟩ := behindOk_of_one hs
  exact B.tidy.inOrder

/-- **The first member of the last chain of the IOP as written in Lean**, over any first chain cF,
is batchLinearConstraintsSecondPart at the library's parameters, carried to the file's type of claims. -/
theorem first_of_last (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) :
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder[0]? =
      some ((batchLinearConstraintsSecondPart (ToldDesc.p14At Zp) : Block S₃ Unit).retype) := by
  have h := ToldDesc.last_blocks_in OnBytes.secondHashFunction ProofFile.pureRoad.links Zp
    (Desc.K14.Law.seatN Zp Np) Np cF
  have h' : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = _ := h
  rw [h']
  rfl

section atLast
variable (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : NumbersS) (Mg : Local W₀ Rc ProofFile.Inst Tr → MeaningS St (ProofFile.InstPub × P5J.TS) Wt)
  (ML : MeaningL S₃ Wt) (taken : List Fmt.TreeSource)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (ProofFile.InstPub × P5J.TS) × St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table)
  (fixed : Fmt.TreeSource → Nat) (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop) (Kp : Place → S₃ → S₃ → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr) (R : List Fmt.DeclaredRound)
  (fs : ProofFile.InstPub × P5J.TS → VerifiableInference.Desc.First.S)

/-- **FormKeeps at the member 0 of the last chain's letters at the IOP as written in Lean, WITH NO
PREMISE**, at three letters laid: the form as the library's closed test fillZ at the library's own
parameters, keeps at the kind's place as SecondLaid, order as "the statement is in order". It holds
vacuously wherever fillZ's test at border 0 is false, and fillZ has been evaluated at no state: see
the head. -/
theorem second_at_last :
    FormKeeps (LastThread.lettersLast Zp Np cF H N Mg ML (fillZ (ToldDesc.p14At Zp) R fs)
      (fun s => OnBytes.Means.InOrder s.st) taken ends wit table fixed item n₁ n₂ Vd Rd
      (kpSecond (ToldDesc.p14At Zp) Kp) w).thread 0 := by
  refine second_formKeeps _ (ToldDesc.p14At Zp) R fs rfl ?_ ?_
    (fun x e s' h => inOrder_of_form _ R fs x e s' h)
  · intro blk hb
    have hb' : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder[0]? = some blk := hb
    obtain rfl := Option.some.inj ((first_of_last Zp Np cF).symm.trans hb')
    exact ⟨rfl, rfl⟩
  · intro s s' hL q hq
    obtain rfl : (⟨3, none, 0, .K14⟩ : Place) = q := Option.some.inj hq
    show (if (⟨3, none, 0, .K14⟩ : Place) = ⟨3, none, 0, .K14⟩ then _ else _)
    rw [if_pos rfl]
    exact hL

end atLast

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.inOrder_of_form
#print axioms ProofFile.Honest.K14.second_formKeeps
#print axioms ProofFile.Honest.K14.first_of_last
#print axioms ProofFile.Honest.K14.second_at_last
