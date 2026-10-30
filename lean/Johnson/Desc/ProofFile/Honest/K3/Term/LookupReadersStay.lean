-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupReadersStay.lean: the kind "lookup" (K3): behind the step
of a lookup on the digits, at the first chain's thread of `lettersHead`
(Honest/Thread/FirstHead.lean), the readers' answers at the runs of every item "forms" that is open
on both sides of the lookup are what they were in front of it.

What is shown.
  `digitsPlaceIsWritten`: at the lookup's number the written list of places holds the lookup's
    place.
  `borderOfTheDigitsPlace`: the table's number of the border in front of that place is the lookup's
    number.
  `readersStayBehindTheDigitsStep`: the statement above. Its end is written in the table's own
    terms at the place `IM.k3Place l true`: the two lists of open items at
    `borderOf P5J.At.ps (some p)` and the next number, the runs and readers of `h.𝔇.pubD`, and the
    library's `Fwd` (Johnson/Desc/Reads/FormsPass.lean).

How. `P5J.k3_digits_readers_head_on` (Johnson/P5J/K03ReadersHeadAsk.lean) has it from the table's
promise in front, "reached", "reached by the wrapped sub-protocols' steps" and the step's
acceptance. The promise is the second half of the thread's clause `Form`; the two reaches are
`thr_reach` (Honest/Thread/ReachFacts.lean) and `thrS_reach_below` (Honest/Thread/ReachAtHead.lean).

Hypotheses that remain. `h`: the library's hypothesis `P5J.AtMgA` at the hash function `secondHashFunction`. Every
letter of `lettersHead` is a variable. `saidGivesWordsBelowThePrime`: the letter `Said` gives
`SaidOk`. l < 25; the member at the border; the invariant in front; the member's step.

Limits. An implication. Nothing here shows that the invariant or the step holds at any run. At the
full size alone.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupFormBehind
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.P5J.K03ReadersHeadAsk
import Johnson.P5J.FoldJ3
import Johnson.IMR.BorderW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Strs Block Place)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf places_are_k3)
open VerifiableInference.Desc.First (Item onAt)
open VerifiableInference.OnPublicFiles (k3K)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest ProofFile.Honest.FirstThread

/-- At the lookup's number the written list of places holds the lookup's place. -/
theorem digitsPlaceIsWritten {l : Nat} (linkBelow : l < 25) :
    P5J.At.ps[k3K l true]? = some (IM.k3Place l true) := places_are_k3 linkBelow true

/-- The table's number of the border in front of the lookup's place is the lookup's number. -/
theorem borderOfTheDigitsPlace {l : Nat} (linkBelow : l < 25) :
    VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true)) = k3K l true := by
  have hk : k3K l true ≤ 358 := by
    have hlt := (List.getElem?_eq_some_iff.1 (digitsPlaceIsWritten linkBelow)).1
    rw [← P5J.placesW_at, IM.places_len] at hlt
    omega
  have e := IM.border_W (k3K l true) hk
  rw [P5J.placesW_at, digitsPlaceIsWritten linkBelow] at e
  exact e

-- from here on the closed lists are not unfolded
attribute [local irreducible] IM.openAt VerifiableInference.Desc.First.flatPlacesOf

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The readers stay behind the step of a lookup on the digits.** Conditional on what this file's
head lists. -/
theorem readersStayBehindTheDigitsStep (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    {l : Nat} (linkBelow : l < 25) {blk : Block TS ProofFile.Cl}
    (memberAtBorder : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[borderOf l
      true]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (invariantInFront : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (borderOf l true) k s m E)
    (memberStepped : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s
      m E ds y cols s') :
    ∀ mm kk ρ,
      Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps
        (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true))) →
      Item.forms mm kk ρ ∈ IM.openAt P5J.At.links P5J.At.ps
        (VerifiableInference.Desc.First.borderOf P5J.At.ps (some (IM.k3Place l true)) + 1) →
      ∀ q ∈ h.𝔇.pubD.runs mm kk ρ,
        VerifiableInference.Reads.Pass.Fwd (h.𝔇.pubD.Rd mm) q.1 q.2 s s' := by
  have hb : cF.blocksInOrder[k3K l true]? = some blk := memberAtBorder
  have hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk
      (k3K l true) k s m E := thrS_mono _ saidGivesWordsBelowThePrime invariantInFront
  have hF := hT.1.2.2.1
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hlen : k3K l true ≤ cF.blocksInOrder.length := by
    have := (List.getElem?_eq_some_iff.1 hb).1
    omega
  have hreach := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT.1
  have hbelow := thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT
  have hy : IM.Yes 0 blk s s' := ⟨_, _, _, memberStepped.2⟩
  have hon : onAt _ _ _ _ _ _ _ _ := hF.2
  intro mm kk ρ ho ho'
  rw [borderOfTheDigitsPlace linkBelow, ← P5J.linksW_at, ← P5J.placesW_at] at ho ho'
  exact P5J.k3_digits_readers_head_on h linkBelow hb
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP rfl rfl rfl _ _ _ 0 hreach h0 hon
    (fun _ => hbelow) hy mm kk ρ ho ho'

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.digitsPlaceIsWritten
#print axioms ProofFile.Honest.K3.Term.borderOfTheDigitsPlace
#print axioms ProofFile.Honest.K3.Term.readersStayBehindTheDigitsStep
