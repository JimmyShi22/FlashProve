-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupFormBehind.lean: the kind "lookup" (K3): at the first
chain's thread of `lettersHead` (Honest/Thread/FirstHead.lean) the thread's clause `Form` holds
behind the accepting step of each of the lookups' fifty members.

What is shown.
  `borderIsTheLookupNumber`: the written number of the border in front of a lookup (`borderOf`,
    Johnson/Desc/Sound/MgAt/K3Open.lean) is the library's number of that lookup in the list of
    places (`k3K`, Johnson/Desc/First/Look/K3Base.lean). By unfolding.
  `lookupFormHoldsBehindTheStep`: from the thread's invariant with a letter `Said` beside it in
    front of the lookup of link l (on the calls, d = false; on the digits, d = true) and the
    member's step from s to s', the form holds at the next border, at s'.

How. The form in front gives "no mark", the six tests, "the samples are held" and what the open
public items say (`xk_of_form`, Honest/Thread/FormXK.lean, and the form's own clause). The
invariant with `SaidOk` gives that s is reached by the wrapped sub-protocols' steps
(`thrS_reach_below`, Honest/Thread/ReachAtHead.lean). `step_calls_top` and `step_digits_top`
(Honest/K3/Law/Total/NoMarkBehind.lean) carry the four over the step. `form_behind_of_xk` ends in
the form.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` at the hash function `secondHashFunction`.
  Every letter of `lettersHead` is a variable: the prover H, Q, test, carryX, item, n₁, n₂, b₀, Vd,
    Rd, Kp, w.
  `saidGivesWordsBelowThePrime`: the letter `Said` gives `SaidOk`.
  `linkBelow`: l < 25. `memberAtBorder`: blk is the thread's member at the border.
  `invariantInFront`, `memberStepped`: the invariant in front; the member's step.

Limits. An implication. Nothing here shows that the invariant or the step holds at any run. Nothing
on `rides` or `keeps`. At the full size alone.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.NoMarkBehind
import Johnson.Desc.ProofFile.Honest.Thread.FormXK
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.Desc.ProofFile.Honest.Thread.SaidMono

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain Strs Wit Block)
open VerifiableInference.Desc.Sound (MsgT below)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.Desc.First (samplesHeld onAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.Walk.Tied (Reach RchAt)
open ProofFile.Honest ProofFile.Honest.FirstThread ProofFile.Honest.K3.Law.Total
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound VerifiableInference.OnPublicFiles

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The written number of the border in front of a lookup is the library's number of that lookup in
the list of places. -/
theorem borderIsTheLookupNumber (l : Nat) (d : Bool) : borderOf l d = k3K l d := rfl

/-- **The form holds behind a lookup's step, at the first chain's thread of `lettersHead`.** d:
false: the lookup on the calls; true: on the digits. Conditional on what this file's head lists. -/
theorem lookupFormHoldsBehindTheStep (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (saidGivesWordsBelowThePrime : ∀ b k m, Said b k m → SaidOk b k m)
    {l : Nat} (linkBelow : l < 25) (d : Bool) {blk : Block TS ProofFile.Cl}
    (memberAtBorder : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[borderOf l
      d]? = some blk)
    {k : Coins Bk} {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (invariantInFront : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (borderOf l d) k s m E)
    (memberStepped : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s
      m E ds y cols s') :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Form (borderOf l d + 1) k s'
      y.2 := by
  have hb : cF.blocksInOrder[k3K l d]? = some blk := memberAtBorder
  have hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread SaidOk (k3K l d) k
      s m E := thrS_mono _ saidGivesWordsBelowThePrime invariantInFront
  have hF := hT.1.2.2.1
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hlen : k3K l d ≤ cF.blocksInOrder.length := by
    have := (List.getElem?_eq_some_iff.1 hb).1
    omega
  have hr := thrS_reach_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT
  have hy : IM.Yes 0 blk s s' := ⟨_, _, _, memberStepped.2⟩
  have hx := xk_of_form _ hF
  have ha : onAt _ _ _ _ _ _ _ _ := hF.2
  obtain ⟨-, hHeld, -, hPP⟩ := ha.2.resolve_left (fun e => e h0)
  cases d with
  | false =>
    obtain ⟨a0, a1, a2, a3⟩ := step_calls_top h linkBelow hb _ hr hy h0 hx hHeld
    exact form_behind_of_xk _ memberStepped a0 a1 a2 a3
  | true =>
    obtain ⟨a0, a1, a2, a3⟩ := step_digits_top h linkBelow hb _ hr hy h0 hx hHeld hPP
    exact form_behind_of_xk _ memberStepped a0 a1 a2 a3

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.borderIsTheLookupNumber
#print axioms ProofFile.Honest.K3.Term.lookupFormHoldsBehindTheStep
