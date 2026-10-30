-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheG.lean: G AT NAMES. The sides at a return of the maker, at any filling: the letters are the
three chains' threads, the rows those that the kinds lay, the falls the lists at the term.

  ThreadParts            what the three threads take from outside
  theLetters             the letters of the three threads
  theG                   G at a return of the maker at a filling
  theG_prover            its prover is the return's
  theGOfReturn           the same at the description that the return holds; castSides_of carries
                         every statement on G to it
  theGAtBase, theGAtBase_prover   at the base filling
  theGAtTerm, theGAtTerm_prover   at the filling that the online prover reads

Limits. The kinds' rows are an argument. A place where no kind has laid a row holds the filling's own
side, beside a simulator that tells nothing. Nothing here ties G at the base to G at the term. This
file proves nothing about completeness, soundness or zero knowledge.
-/
import E2E.TheFalls
import E2E.BaseMaker
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.TheG
open OnBytes (TableKey)
open ProofFile.Honest (OnlineProverWithDescription ProverCoinCounts OnlineProverParts Sides SaidOk onlineProverFromPublicFiles)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts SharedThreadParts LastThreadParts
  IndexReaders firstThread sharedThread lastThread)
open VerifierAndGoals (PublicFiles)
open AtPublicFiles.TheSides AtPublicFiles.TheFalls

variable {W₀ Rc Tr X₀ X Wt : Type} {files : PublicFiles}

/-- **What the three threads take from outside.** -/
structure ThreadParts (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (Wt : Type) where
  first : FirstThreadParts A
  reads : IndexReaders W₀ Rc
  shared : SharedThreadParts A Wt
  last : LastThreadParts A

variable {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The letters of the three threads.** -/
def theLetters (h : HeadAtReturn files A) (T : ThreadParts A Wt) :
    Letters h.description A.B W₀ Rc TableKey Tr X₀ X :=
  Letters.ofThreads _ (firstThread h T.first) (sharedThread h T.reads T.shared)
    (lastThread h T.first T.reads T.last) (fun _ => SaidOk) (fun _ => SaidOk) (fun _ => SaidOk)

variable {P : OnlineProverParts W₀ Rc Tr X₀ X}

/-- **G at a return of the maker at a filling.** -/
def theG (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows P A.Z A.G) :
    Sides h.description A.B W₀ Rc TableKey Tr X₀ X :=
  theSides h.description (theLetters h T) K.slots.rows
    (theFalls₁ A.Z h.places h.firstChain A.G (FallSlots.nothing _))
    (theFalls₂ A.Z h.places h.firstChain (FallSlots.nothing _))
    (theFalls₃ A.Z h.places h.firstChain (FallSlots.nothing _))

/-- **Its prover is the return's.** -/
theorem theG_prover {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    (made : onlineProverFromPublicFiles o pol lay KL P = .ok A) (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows P A.Z A.G) : (theG h T K).prover A.H = A.H :=
  theSides_prover (K.slots.fit made)

/-- **G at the description that the return holds**, by the equation that the head gives. -/
def theGOfReturn {P : OnlineProverParts W₀ Rc Tr X₀ X}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows P A.Z A.G) :
    Sides A.F A.B W₀ Rc TableKey Tr X₀ X :=
  castSides (ProofFile.Honest.atPure_at_laid h.head.laid made).2 (theG h T K)

theorem theGOfReturn_prover {P : OnlineProverParts W₀ Rc Tr X₀ X}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt) (K : KindRows P A.Z A.G) :
    (theGOfReturn made h T K).prover A.H = A.H :=
  (castSides_prover _ _ _).trans (theG_prover made h T K)

end AtPublicFiles.TheG

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.TheG AtPublicFiles.TheSides
open ProofFile.Honest (OnlineProverWithDescription)
open ProofFile.Honest.FirstThread (HeadAtReturn)

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type}

/-- **G at the base filling.** The kinds' lots and the simulators stand here. -/
abbrev theGAtBase {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins ProofFile.Honest.Cells Unit Unit} (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G) :=
  theG h T K

theorem theGAtBase_prover {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins ProofFile.Honest.Cells Unit Unit}
    (made : baseMaker files = .ok A) (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G) : (theGAtBase h T K).prover A.H = A.H :=
  theG_prover made h T K

/-- **G at the filling that the online prover reads.** -/
abbrev theGAtTerm {A : OnlineReturn files} (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (onlineFilling files) A.Z A.G) :=
  theG h T K

theorem theGAtTerm_prover {A : OnlineReturn files} (made : onlineMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (onlineFilling files) A.Z A.G) : (theGAtTerm h T K).prover A.H = A.H :=
  theG_prover made h T K

end ProofFile.Honest.Term

#print axioms AtPublicFiles.TheG.theG_prover
#print axioms AtPublicFiles.TheG.theGOfReturn_prover
#print axioms ProofFile.Honest.Term.theGAtBase_prover
#print axioms ProofFile.Honest.Term.theGAtTerm_prover
