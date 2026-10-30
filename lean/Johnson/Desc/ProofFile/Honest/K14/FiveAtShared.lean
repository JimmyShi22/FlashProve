-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/FiveAtShared.lean: the linear claim's shared rounds (kind K14):
THE FIVE STATEMENTS ON ONE SUB-PROTOCOL (PlaysS, BehindS, ExchangeS, RidesPastS, AcceptedS,
Honest/Thread/PaysS.lean) AT EACH OF THE MEMBERS 1 TO 8 OF THE SHARED CHAIN, in these five forms
themselves, from the one structure K14Asks (Honest/K14/Asks.lean) and premises on the letter rides.
They hold at every second condition `Said` and at every `fall`: the kind reads nothing of the first
and has none of the second.

  k14_five        **the five at a member b, 1 ≤ b ≤ 8**, where the letter rides is a sentence R₀ and
                  a list of clauses
  k14_five_quiet  the same where the letter rides holds everywhere: no premise on it is left
  k14_owes, k14_yes   the share of OwesS and YesS at these eight members

THE PREMISES ON THE LETTER rides, in k14_five. Of the clause of BehindS that speaks of rides this
file shows nothing: it hands that clause on to the caller in four premises. hr: the letter is a
sentence R₀ and a list of clauses cs; both are the caller's choice. h₀: R₀ holds behind the member's
accepted step. hst: each clause of cs that speaks on both sides of the member stays by what the
member keeps. hl: each clause of cs that begins at the border behind the member holds behind the
member's accepted step (LaysAtS, Honest/Thread/SharesS.lean).

What is not claimed. That K14Asks holds at any letters. That `Said` is carried from border to border
(SaidNext, Honest/Thread/Said.lean): that is a statement on `Said`, not on this kind. Nothing on the
members 0, 9, 10 and 11 of the chain; but K14Asks' field letters fixes the thread's form at the
borders 2 to 9, so also in front of the member 9. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0. A side
is the prover's list of parts at one place (Placed, Honest/Frame.lean).
-/
import Johnson.Desc.ProofFile.Honest.K14.AsksS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block)
open Desc.K14 (P14 St)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Cl Wt : Type} {ℓ : WitLens Wt}
  {L : SharedThread.Letters Bk St Cl W₀ Rc TableKey X₀ P₁ Wt} {Q : P14}
  {sentU : Array OracleNotice} {layO : TreeLay} {c : Model.Verify.Chains}
  {tests : List (Block St Unit)} {last : List (Block St Unit) → Block St Unit} {A : Data}
  {weights : W₀ → Weights} {rand : Rc → TableRand}

/-- **The five statements at a member b of the eight**, at every `Said` and every `fall`. The
premises on the letter rides: the file's head. -/
theorem k14_five (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String)
    {R₀ : Nat → Common W₀ Rc TableKey → St → Prop}
    {cs : List (RiderCl (Common W₀ Rc TableKey) St)}
    (hr : ∀ b w s, L.thread.rides b w s ↔ R₀ b w s ∧ ridersOf cs b w s) (b : Nat) (h1 : 1 ≤ b)
    (h8 : b ≤ 8)
    (h₀ : ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ x ∈ cs, x.lo ≤ b → b + 1 ≤ x.hi → StaysBy L.thread b x)
    (hl : ∀ x ∈ cs, x.lo = b + 1 → LaysAtS L.thread Said b x) :
    PlaysS L.thread Said b ∧ BehindS L.thread Said b ∧ ExchangeS L.thread Said b ∧
      RidesPastS L.thread Said b ∧ AcceptedS L.thread Said fall b := by
  obtain ⟨p, fk, ex, rp, ac⟩ := k14_asks h fall b h1 h8
  exact ⟨playsS_of _ _ p,
    behindS_of_keeps_and L.thread Said hr (formKeepsS_of Said fk) h₀ hst hl, exchangeS_of _ _ ex,
    ridesPastS_of _ _ rp, acceptedS_of _ _ ac⟩

/-- **The five where the letter rides holds everywhere.** -/
theorem k14_five_quiet (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String)
    (hr : ∀ b w s, L.thread.rides b w s) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) :
    PlaysS L.thread Said b ∧ BehindS L.thread Said b ∧ ExchangeS L.thread Said b ∧
      RidesPastS L.thread Said b ∧ AcceptedS L.thread Said fall b :=
  k14_five h Said fall (R₀ := fun _ _ _ => True) (cs := [])
    (fun b w s => ⟨fun _ => ⟨trivial, fun _ hc => nomatch hc⟩, fun _ => hr b w s⟩) b h1 h8
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ hx => nomatch hx) fun _ hx => nomatch hx

/-- The share of OwesS (Honest/Thread/PaysS.lean) at the eight members. -/
theorem k14_owes (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    {R₀ : Nat → Common W₀ Rc TableKey → St → Prop}
    {cs : List (RiderCl (Common W₀ Rc TableKey) St)}
    (hr : ∀ b w s, L.thread.rides b w s ↔ R₀ b w s ∧ ridersOf cs b w s)
    (h₀ : ∀ b, 1 ≤ b → b ≤ 8 → ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ b, 1 ≤ b → b ≤ 8 → ∀ x ∈ cs, x.lo ≤ b → b + 1 ≤ x.hi → StaysBy L.thread b x)
    (hl : ∀ b, 1 ≤ b → b ≤ 8 → ∀ x ∈ cs, x.lo = b + 1 → LaysAtS L.thread Said b x) (b : Nat)
    (h1 : 1 ≤ b) (h8 : b ≤ 8) :
    PlaysS L.thread Said b ∧ BehindS L.thread Said b ∧ ExchangeS L.thread Said b ∧
      RidesPastS L.thread Said b := by
  obtain ⟨p, bh, ex, rp, -⟩ := k14_five h Said (fun _ _ _ => none) hr b h1 h8 (h₀ b h1 h8)
    (hst b h1 h8) (hl b h1 h8)
  exact ⟨p, bh, ex, rp⟩

/-- The share of YesS (Honest/Thread/PaysS.lean) at the eight members, at every fall. Of the letter
rides nothing is asked. -/
theorem k14_yes (h : K14Asks ℓ L Q sentU layO c tests last A weights rand)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8) :
    AcceptedS L.thread Said fall b :=
  acceptedS_of _ _ (k14_asks h fall b h1 h8).2.2.2.2

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.k14_five
#print axioms ProofFile.Honest.K14.k14_five_quiet
#print axioms ProofFile.Honest.K14.k14_owes
#print axioms ProofFile.Honest.K14.k14_yes
