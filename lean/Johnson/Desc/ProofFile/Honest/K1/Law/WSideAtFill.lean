-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/WSideAtFill.lean: THE SHARED "SENDING" (the kind K1): W's SIDE
LAID IN A FILLING: the half of K1 at W's place ⟨1, none, 4, .K1⟩ (number 356 of the first chain), at
the data K13.wDataAt O.pile (Honest/K13/WData.lean), one lot more behind the lots of
widerFillOwnCPUOW (Honest/K12/AtProof/HalfWAtPure.lean). Four definitions, seven statements with
their proofs.

E2E/TheHonestProver.lean lays this filling, read through tableCoins, as the honest
prover's own (onlineFilling). This file states nothing on what a proof hides.






  K1.wSideNo           W's side with its number off the public part: what K1.dataSideNo is to K1's
                       own lot: HLot.byPub hands a lot the reader, not the public part, and wSide
                       takes one number. The number is idle (wSide_any_no, Honest/K1/HalvesFree.lean)
  wLotAt               the lot, in the shape of the lots of widerFillOwn: the reader by public part
  widerFillOwnCPUOWM, onlineProverPartsInUse   the two fillings: widerFillOwnCPUOW with that lot last
  wLotAt_name          the lot's name is wSide's own, which is K13.lot4's: lotsLacking reads names
  wLotAt_halves        what the lot holds, by rfl: by text the job term of jobRealW
                       (Honest/K12/AtProof/HalfW.lean) at secondW's letters: the same pile, input,
                       message and number. No statement here names jobRealW
  widerFillAtCPUOWM_lots   the filling's lots: widerFillAt's ten, the closings', the proximity
                       test's, this lot
  wider_none_at_w      no half of the ten stands at W's place: H2's widerKinds, and at K1's own lot
                       k1_linked. No premise
  hex_wM, ho_wM        THE TWO PREMISES OF half_w_of_lots (Honest/K1/Law/HalfAtW.lean) ARE MET AT
                       THIS FILLING. No premise
  half_w_wM            so the search at W's place in the prover that onlineProverFromPublicFiles returns at this filling
                       finds placeHalf of W's job, under the head h and hA

Why. At a filling that does not lay wSide the pair at the last chain's test reads a sending that
nobody sends
(HalfWAtPure.lean's Limits).

Limits. THAT onlineProverFromPublicFiles RETURNS AT THIS FILLING IS A PREMISE (hA). By reading, not typed: the added lot
costs onlineProverFromPublicFiles nothing under the head: one side, at number 356's place, so no stray; names are read
by onlineProverFromPublicFiles's report alone. THAT onlineProverFromPublicFiles RETURNS AT THE FILLING BENEATH (widerFillAtCPUOW) IS STATED IN
NO FILE OF THIS LIBRARY. AT THIS FILLING IT RETURNS UNDER THE HEAD, WHERE THE LIBRARY's TEST ON THE
PUBLIC FILES ACCEPTS AND THE INDEX TYPE's NAMED MEMBER IS IN RANGE (atPure_returns_fillW_at,
AtFullSide/K12/ReturnsAtAnyIndex.lean): there half_w_wM is not idle. Its kin one filling back: H2's
widerC_none_356 (Honest/Thread/WiderNoneW.lean): under the head, where onlineProverFromPublicFiles returns at widerFillAtC
the search at 356 finds nothing.
o is free in half_w_wM; secondW lays F0T o Z N c: for a join with it o := OnBytes.secondHashFunction is the
case that matters. pile is a letter of OnlineProverArguments: nothing is said of what it yields, and
RowData.readyAt at a run's list is not named. ONE NAMED FILLING, at LongLots.plain: a law at one
filling carries over to no wider one. wDataAt lays nothing where the pile has one row: W's place is
another there. Nothing on what a half plays. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfWAtPure
import Johnson.Desc.ProofFile.Honest.K1.Law.HalfAtW
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12Places
import Johnson.Desc.ProofFile.Honest.K13.WData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Place KindName Chain)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

namespace K1

variable {V W X : Type}

/-- **W's side with its number off the public part**: to wSide what dataSideNo is to K1's own lot.
The number is idle (wSide_any_no). -/
def wSideNo (wit : W → PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument) (D : Pub → Ground → RowDataOf ProofFile.Inst) :
    HLot V W X :=
  { name := (wSide (V := V) (X := X) wit (fun _ => 0) D).name
    halves := fun Z G => wHalves wit (lotNo o Z) D Z G }

end K1

variable {W₀ X : Type}

/-- **W's lot**, in the shape of widerFillOwn's lots: the reader by public part; the data
K13.wDataAt O.pile. -/
def wLotAt (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) :
    HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X :=
  HLot.byPub I.weights fun wt =>
    K1.wSideNo (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.x, ⟨w.trace, wt w.w₀, w.rc⟩⟩) o
      (K13.wDataAt O.pile)

/-- **widerFillOwnCPUOW with W's lot behind its lots.** The arguments are widerFillOwn's. -/

def widerFillOwnCPUOWM (own₀ : X) (L : LongLots W₀ X) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) : OnlineProverParts W₀ IndexCommitterCoins Cells Unit X :=
  { widerFillOwnCPUOW own₀ L I o S O with
    lots := (widerFillOwnCPUOW own₀ L I o S O).lots ++ [wLotAt I o O] }

/-- **widerFillAtCPUOW's sister with W's lot.** -/

def onlineProverPartsInUse (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    OnlineProverParts W₀ IndexCommitterCoins Cells Unit Unit :=
  widerFillOwnCPUOWM () (LongLots.plain o S O) I o S O

/-- **THE LOT's NAME IS W's SIDE's OWN**, which is the lot K13.lot4's: lotsLacking (Honest/AtPure.lean)
reads names. -/
theorem wLotAt_name (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) (Z : Pub) :
    (wLotAt (X := X) I o O).name = (VerifiableInference.Desc.K13.lot4 Z).name := rfl

/-- **WHAT THE LOT HOLDS**: by text the job term of jobRealW at secondW's letters: the same pile,
input, message and number. -/
theorem wLotAt_halves (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    (wLotAt (X := X) I o O).halves Z G =
      ((OnBytes.linMessageW Z.first.lin).map fun msg =>
        K1.placeHalf (fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.x, ⟨w.trace, I.weights Z w.w₀, w.rc⟩⟩)
          (K1.wJobAt Z.first (K1.wGp Z) 4 msg (K1.lotNo o Z ⟨1, none, 4, .K1⟩)
            (K13.wDataAt O.pile Z G))).toList := rfl

/-- **THE FILLING's LOTS.** -/
theorem widerFillAtCPUOWM_lots (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) :
    (onlineProverPartsInUse I o S O).lots =
      (((widerFillAt I o S O).lots ++ [closeLotAt I S]) ++ [proxLotAt I S]) ++ [wLotAt I o O] :=
  rfl

/-- **NO HALF OF THE TEN STANDS AT W's PLACE.** No premise. -/
theorem wider_none_at_w (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ M ∈ (widerFillAt I o S O).lots, ∀ g ∈ M.halves Zq G, g.place ≠ ⟨1, none, 4, .K1⟩ := by
  intro M hM g hg e
  rw [widerFillAt_lots] at hM
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hM
  have hk := (FirstFill.widerKinds I o S O Zq G).all q hq g hg
  by_cases k : q.2 = .K1
  · have e' : q = (HLot.byPub I.weights (LongLots.plain o S O).k1, .K1) :=
      List.inj_on_of_nodup_map widerPairs_nodup hq (List.Mem.head _) k
    rw [e'] at hg
    have hg' : g ∈ (K1.dataSideNo S (fun w : Local W₀ IndexCommitterCoins Inst Cells =>
        ⟨w.x, ⟨w.trace, I.weights Zq w.w₀, w.rc⟩⟩) o :
        HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit).halves Zq G := hg
    have hl := FirstFill.k1_linked S _ o Zq G g hg'
    rw [e] at hl
    exact hl rfl
  · rw [e] at hk
    exact k hk.symm

/-- **hex AT THIS FILLING**: some lot has W's side's halves. No premise. -/
theorem hex_wM (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∃ M ∈ (onlineProverPartsInUse I o S O).lots, M.halves Zq G =
      K1.wHalves (fun v : Local W₀ IndexCommitterCoins Inst Cells => ⟨v.x, ⟨v.trace, I.weights Zq v.w₀, v.rc⟩⟩)
        (K1.lotNo o Zq) (K13.wDataAt O.pile) Zq G := by
  refine ⟨wLotAt I o O, ?_, rfl⟩
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_right _ (.head _)

/-- **ho AT THIS FILLING**: every lot has no half at W's place, or these halves. No premise. -/
theorem ho_wM (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ g ∈ M.halves Zq G, g.place ≠ ⟨1, none, 4, .K1⟩) ∨
      M.halves Zq G =
        K1.wHalves (fun v : Local W₀ IndexCommitterCoins Inst Cells => ⟨v.x, ⟨v.trace, I.weights Zq v.w₀, v.rc⟩⟩)
          (K1.lotNo o Zq) (K13.wDataAt O.pile) Zq G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · exact .inl (wider_none_at_w I o S O Zq G M h)
  · refine .inl fun g hg e => ?_
    have hk := closeLotAt_kinds I S Zq G g hg
    rw [e] at hk
    have hk' : KindName.K1 = KindName.K10 := hk
    cases hk'
  · refine .inl fun g hg e => ?_
    have hk := proxLotAt_kinds I S Zq G g hg
    rw [e] at hk
    have hk' : KindName.K1 = KindName.K12 := hk
    cases hk'
  · exact .inr rfl

/-- **THE SEARCH AT W's PLACE, AT THE PROVER OF THIS FILLING**: half_w_of_lots at hex_wM and ho_wM.
Under the head h and hA: both hypotheses. -/
theorem half_w_wM {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o S O) = .ok A)
    {J : K1.SendJob (K1.PlaceIn ProofFile.Inst) Unit}
    (hJ : J = K1.wJobAt Zp.first (K1.wGp Zp) 4 wMsgFull
      (K1.lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩) (K13.wDataAt O.pile Zp A.G)) :
    (A.H.first.find? fun g => g.place == J.P.place) =
      some (K1.placeHalf
        (fun v : Local W₀ IndexCommitterCoins Inst Cells => ⟨v.x, ⟨v.trace, I.weights A.Z v.w₀, v.rc⟩⟩) J) :=
  K1.half_w_of_lots h hA _ (K1.lotNo o A.Z) (K13.wDataAt O.pile) (hex_wM I o S O A.Z A.G)
    (ho_wM I o S O A.Z A.G) hJ

end ProofFile.Honest

#print axioms ProofFile.Honest.K1.wSideNo
#print axioms ProofFile.Honest.wLotAt
#print axioms ProofFile.Honest.widerFillOwnCPUOWM
#print axioms ProofFile.Honest.onlineProverPartsInUse
#print axioms ProofFile.Honest.wLotAt_name
#print axioms ProofFile.Honest.wLotAt_halves
#print axioms ProofFile.Honest.widerFillAtCPUOWM_lots
#print axioms ProofFile.Honest.wider_none_at_w
#print axioms ProofFile.Honest.hex_wM
#print axioms ProofFile.Honest.ho_wM
#print axioms ProofFile.Honest.half_w_wM
