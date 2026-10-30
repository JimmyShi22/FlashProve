-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheOneObjectLastLine.lean: the last line of TheOneObject.lean under the name of the
premise that completeness takes, at any sides, and that premise's law called at it.

The protocol has three parts, named by what a user holds. offline: the proof in the key file, on the
committed table. link: from a further encoding to the first. online: the proof for a request (the
proof file). This file is on the online part. The sides G are a letter: any sides whose prover is the
online return's and whose three lists of falls are the stated ones (SidesFit).
tied_reads_no_sides: the relation on the inputs is the same at all such sides.
baseThreads_at_any_sides: BaseThreadsJAt (E2E/CompleteAsIOPByBase.lean), at the base prover.
yes_at_any_sides: yesZ_of_base_threadsJ called at it; its end is the field yes of OnlineDebts.
All are implications from the fields of TheOneObject, which are hypotheses.
-/
import AtFullSide.Honest.TheOneObject
import E2E.CompleteAsIOPByBase
import E2E.CompleteAsIOPOffline

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles InScope asDescriptionFiles)
open LPFD.Full (instanceAsPlainRecord)
open FlashProve (protocolDataWellFormed allZeroDigest committerCoinCountLessOne)
open AtPublicFiles.TheFalls (theFalls₁)
open scoped ENNReal

local instance (priority := high) nonemptyPadZ_theLastLine : Nonempty PadZ :=
  pads_nonempty frS 402653181

/- Given by hand, as in E2E/TheHonestProver.lean: the search for these runs out of its budget. -/
local instance (priority := high) nonemptyRunValue_theLastLine : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_theLastLine : Inhabited RunValue := ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A}
  {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp}

/-- **The inputs of which something is said, at sides G.** At theSides it is TiedRequest. -/
abbrev TiedRequestAt (h : HeadAtReturn Z A) (hr : readFiles Z = .ok pp)
    (G : OnlineSides (onlineReturn Z A) h.places h.firstChain) : ℕ → WZ Z → ProofFile.Inst → Prop :=
  TiedOut Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes runValueBytes
    (onlineReturn Z A).B G (onlineReturn Z A).H (ServedRequest committerCoinCountLessOne Z hr) fun _ _ => ∅

/-- **What is asked of the sides**: their prover is the online return's, and they hold the stated
lists of falls. -/
structure SidesFit (h : HeadAtReturn Z A)
    (G : OnlineSides (onlineReturn Z A) h.places h.firstChain) : Prop where
  prover : G.prover (onlineReturn Z A).H = (onlineReturn Z A).H
  falls₁ : G.falls₁ = theFalls₁ (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).G
    (theSlots (onlineReturn Z A) h.places h.firstChain)
  falls₂ : G.falls₂ = []
  falls₃ : G.falls₃ = []

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **One value**: the sides that TheOneObject.lean stands at fit. -/
theorem theSides_fit : SidesFit h (theSides h) where
  prover := sidesForCompleteness_prover (onlineReturn Z A) h.places h.firstChain
    (theSlots (onlineReturn Z A) h.places h.firstChain)
  falls₁ := rfl
  falls₂ := no_later_fall.1
  falls₃ := no_later_fall.2

variable {G : OnlineSides (onlineReturn Z A) h.places h.firstChain}

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The prover that runs is the same at all sides whose prover is the online return's.** -/
theorem running_prover_reads_no_sides
    (hG : G.prover (onlineReturn Z A).H = (onlineReturn Z A).H) :
    provG Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B G (onlineReturn Z A).H =
      provG Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B (theSides h)
        (onlineReturn Z A).H := by
  show (cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 (G.prover (onlineReturn Z A).H) =
    (cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 ((theSides h).prover (onlineReturn Z A).H)
  rw [hG, (theSides_fit (h := h)).prover]

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The relation reads of the sides their prover alone**: at sides that fit it is TiedRequest. -/
theorem tied_reads_no_sides (hG : G.prover (onlineReturn Z A).H = (onlineReturn Z A).H) :
    TiedRequestAt h hr G = TiedRequest h hr := by
  have e : G.prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 (onlineReturn Z A).H) =
      (theSides h).prover ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 (onlineReturn Z A).H) :=
    running_prover_reads_no_sides hG
  funext n w x
  unfold TiedRequestAt TiedRequest TiedOut TiedYes TiedG
  rw [e]

/-- **THE LAST LINE: the premise of completeness, at the online prover of honestProvers, at any
sides that fit.** -/
theorem baseThreads_at_any_sides (F : SidesFit h G)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheOneObject h hr) :
    BaseThreadsJAt Z (onlineReturn Z A).Z h.places h.firstChain (R₂ := RunValue) (R₃ := RunValue)
      (onlineReturn Z A).B G id (tableCoins Z) A.H (TiedRequestAt h hr G) := by
  intro n w x c hx
  rw [tied_reads_no_sides F.prover] at hx
  obtain ⟨R, hR, hP, T, f₁, f₂, f₃⟩ := atEveryTiedRun made O n w x c hx
  exact ⟨R, hR, hP, T, f₁.trans F.falls₁.symm, (f₂.trans no_later_fall.1).trans F.falls₂.symm,
    (f₃.trans no_later_fall.2).trans F.falls₃.symm⟩

/-- The last line at the sides of TheOneObject.lean. -/
theorem baseThreads_of_theOneObject
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheOneObject h hr) :
    BaseThreadsJAt Z (onlineReturn Z A).Z h.places h.firstChain (R₂ := RunValue) (R₃ := RunValue)
      (onlineReturn Z A).B (theSides h) id (tableCoins Z) A.H (TiedRequest h hr) :=
  baseThreads_at_any_sides theSides_fit made O

/-- **The field yes of OnlineDebts, from a value of the object, at any sides that fit.** What stands
beside the object are the called law's own premises. Two more of them, on the named member's range
and on the sides' prover, are proved here. Its premise on the trace is the object's own field
traceAtTied, a hypothesis like the others. -/
theorem yes_at_any_sides (F : SidesFit h G) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheOneObject h hr)
    (h₀ : ∃ z₀, (descZ (onlineReturn Z A).Z h.places h.firstChain).okStart (instanceAsPlainRecord z₀) = true)
    (Q : PlainAt Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B G
      (A.H.thru id (tableCoins Z) matrixInput.dummy))
    (hk : (cmAlong (AZ Z) PadZ (holdZ Z)).key = A.H.key)
    (hcols : ∀ n w x, TiedRequestAt h hr G n w x →
      CommittedColumns (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H id (tableCoins Z) w.1 w.2.1) :
    YesZ allZeroDigest [] Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes runValueBytes
      (onlineReturn Z A).B G (onlineReturn Z A).H (TiedRequestAt h hr G) :=
  yesZ_of_base_threadsJ allZeroDigest [] Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes
    runValueBytes (onlineReturn Z A).B G id (tableCoins Z) matrixInput.dummy A.H scope live
    h.head.laid (fun _ _ => ∅) h₀ Q
    (by rw [(inRange_of_atPure made).2]; rfl)
    F.prover hk hcols
    (fun n w x hx => O.traceAtTied n w x
      (Eq.mp (congrFun (congrFun (congrFun (tied_reads_no_sides (hr := hr) F.prover) n) w) x) hx))
    (baseThreads_at_any_sides F made O)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The end of yes_at_any_sides is the field yes of OnlineDebts, to the letter**: the equation has a
type only if the two statements are one. -/
theorem the_end_is_the_field {zB z pF : ℝ≥0∞}
    (D : OnlineDebts (onlineReturn Z A) h.places h.firstChain G (ServedRequest committerCoinCountLessOne Z hr) zB z
      pF)
    (y : YesZ allZeroDigest [] Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes runValueBytes
      (onlineReturn Z A).B G (onlineReturn Z A).H (TiedRequestAt h hr G)) :
    D.yes = y := rfl

end AtFullSide.Honest

#print axioms AtFullSide.Honest.theSides_fit
#print axioms AtFullSide.Honest.running_prover_reads_no_sides
#print axioms AtFullSide.Honest.tied_reads_no_sides
#print axioms AtFullSide.Honest.baseThreads_at_any_sides
#print axioms AtFullSide.Honest.baseThreads_of_theOneObject
#print axioms AtFullSide.Honest.yes_at_any_sides
#print axioms AtFullSide.Honest.the_end_is_the_field
