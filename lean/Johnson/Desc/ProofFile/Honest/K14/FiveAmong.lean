-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K14/FiveAmong.lean: the linear claim's shared rounds (kind K14): THE
FIVE STATEMENTS ON ONE SUB-PROTOCOL (PlaysS, BehindS, ExchangeS, RidesPastS, AcceptedS,
Honest/Thread/PaysS.lean) AT THE MEMBERS 1 TO 8 OF THE SHARED CHAIN, AT THE THREAD OF THE PROOF
FILE's OWN DESCRIPTION (lettersShared, Honest/Thread/SharedHead.lean), for any prover whose list of
the shared chain's sides begins with this kind's six sides. One theorem: asks_among
(Honest/K14/AsksAtShared.lean) and k14_five (Honest/K14/FiveAtShared.lean), joined.

WHAT IS A PREMISE.
  h                   the library's hypothesis at the full size (P5J.AtMgA,
                      Johnson/P5J/MgAtAll.lean)
  hs, apart, off      on the prover's list: the six sides, then sides at other places, each once
  letters             nine equations on the thread's letters (Asked, Honest/K14/LettersVar.lean)
  tenant              no two of the three sampled messages have the same tree's number and the same
                      number in that tree
  treesU, treesO      the trees of the two sendings are the thread's tables
  five                five facts on the committed table and its key, at the run's own input w, under
                      the caller's sentence Vd on it. EACH IS TO BE SHOWN OF THE COMMITTER's TABLE
                      AND KEY; it is not met by laying the fact into Vd, and at a Vd that holds of
                      nothing the theorem says nothing (the rule of use at the letter valid,
                      Honest/Thread/Thr.lean's head)
  book                every entry of the book of coins by which "SPLIT" spends coins (its spender is
                      that part, its field once is true) names the second sending's part as owner
                      and starts at the first coin of the split's mask message. That there is such
                      an entry is not asked
  hr, h₀, hst, hl     on the letter rides (Honest/K14/FiveAtShared.lean's head)
The thread's other letters, the book, the second condition `Said` and the `fall` are free.

What is not claimed. That any premise holds. That the thread's invariant holds at any state: each of
the five starts from it. Nothing on the members 0, 9, 10, 11; but the premise letters fixes the
thread's form at the borders 2 to 9, so also in front of the member 9. Nothing on completeness,
soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0. A side
is the prover's list of parts at one place (Placed, Honest/Frame.lean).
-/
import Johnson.Desc.ProofFile.Honest.K14.AsksAtShared
import Johnson.Desc.ProofFile.Honest.K14.FiveAtShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12.Seat (tests last)
open ProofFile.Honest.SharedThread (lettersShared)
open P5J (TS)
open Desc.K14 (St)

variable {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} {ℓ : WitLens Wt} {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X}
  {N : NumbersS} {Mg : Common W₀ Rc TableKey → MeaningS St P₁ Wt}
  {shape : Nat → St → Bool} {nothingLeft : St → Bool} {order : St → Prop}
  {wit : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt}
  {table : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table}
  {fixed : Fmt.TreeSource → Nat} {n₁ n₂ : Nat} {Vd : Common W₀ Rc TableKey → Prop}
  {Rd : Nat → Common W₀ Rc TableKey → St → Prop} {Kp : Place → St → St → Prop}
  {w : Common W₀ Rc TableKey} {weights : W₀ → Weights} {rand : Rc → TableRand}

/-- **The five statements at a member b, 1 ≤ b ≤ 8, of the shared chain's thread at the proof file's
own description.** The premises: the file's head. -/
theorem five_among {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {o : ProofFile.SecondHashFunctionArgument}
    (h : P5J.AtMgA o Z D r Zp Np cF x₀)
    {more : List (Placed Empty (Common W₀ Rc TableKey) X₀)}
    (hs : H.shared = proverSidesOfSharedRounds (planData (qAt Zp Np)) weights ++
      proverSidesOfSharedSendings ⟨qAt Zp Np, 0⟩ weights rand ++ more)
    (apart : (more.map (·.place)).Nodup) (off : ∀ g ∈ more, g.place ∉ sixPlaces)
    (letters : Asked ℓ (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w) (qAt Zp Np) (sentWithU Zp Np) Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) weights rand))
    (tenant : Function.Injective N.tenant)
    (treesU : TreesLaid (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w).thread 2 (jobU ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand))
    (treesO : TreesLaid (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂
      Vd Rd Kp w).thread 5 (jobOmega ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand))
    (five : FiveFields (qAt Zp Np) (fun v => v = w ∧ Vd v) (fun v => H.storedWords v.w₀ v.rc)
      weights rand)
    (book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨qAt Zp Np, 0⟩).sort 1⟩)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String)
    {R₀ : Nat → Common W₀ Rc TableKey → St → Prop}
    {cs : List (RiderCl (Common W₀ Rc TableKey) St)}
    (hr : ∀ b v s, Rd b v s ↔ R₀ b v s ∧ ridersOf cs b v s) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8)
    (h₀ : ∀ blk, (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd
        Kp w).thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
        w).thread Said b k s m E → drawsFit blk.rounds ds = true →
      (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
        w).thread.Stepped blk k s m E ds y cols s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ x ∈ cs, x.lo ≤ b → b + 1 ≤ x.hi → StaysBy (lettersShared Zp Np cF H N Mg shape
      nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).thread b x)
    (hl : ∀ x ∈ cs, x.lo = b + 1 → LaysAtS (lettersShared Zp Np cF H N Mg shape nothingLeft order
      wit table fixed n₁ n₂ Vd Rd Kp w).thread Said b x) :
    PlaysS (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
        w).thread Said b ∧
      BehindS (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
        w).thread Said b ∧
      ExchangeS (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd
        Kp w).thread Said b ∧
      RidesPastS (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd
        Kp w).thread Said b ∧
      AcceptedS (lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd
        Kp w).thread Said fall b := by
  obtain ⟨layO, a⟩ := asks_among h hs apart off letters tenant treesU treesO five book
  exact k14_five a Said fall hr b h1 h8 h₀ hst hl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.five_among
