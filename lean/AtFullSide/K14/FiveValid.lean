-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/FiveValid.lean: the linear claim's shared rounds (kind K14): THE FIVE FACTS ON THE
COMMITTED TABLE AND ITS KEY (FiveFields, Johnson/Desc/ProofFile/Honest/K14/FiveFields.lean) AT THE
PROVER THAT THE MAKER onlineProverFromPublicFiles RETURNS AT THE FILLING onlineProverPartsInUse, at any type of index, FROM
ONE SENTENCE ON THE RUN's OWN INPUT: its key is the key that the committer makes of its index and
coins, at some seed (validAt, Johnson/Bind/ForProver/FiveAt.lean). And so the five statements on one
sub-protocol at the members 1 to 8 of the shared chain with that sentence in the place of the
premise `five` of AtFullSide/K14/FiveJoined.lean.

  five_of_validAt     **FiveFields at that prover**: the library's fiveFieldsK14_inScope
                      (Johnson/Bind/ForProver/FiveFieldsAt.lean), read through the reader of the
                      index (fiveFields_thru), narrowed to the run's own input (fiveFields_of_imp);
                      the prover's stored columns are the library's storedW (atPure_storedW,
                      Honest/AtPureStoredW.lean)
  validAt_made        **hv at the committer's made input**: where the explicit input is the
                      library's xiAt at the matrix read off the index, the coins and a seed, the key
                      that the prover reads of it is the committer's: at every index, all coins,
                      every seed
  five_at_base_valid  **the five at a member b, 1 ≤ b ≤ 8**: five_at_base_late with five_of_validAt

NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head), of
five_of_validAt and five_at_base_valid. The ground: the run's input w is a letter for a value, and
the premise hv ties its key to its coins: at a fixed key it holds at some coins and fails at others
(the first kind of premise), so at a letter w nobody can show it. Vd is a letter for a predicate in
front of each field; where it is laid as "the index is in range" it reads the hidden index and no
coin (the second kind: a law over coins would have to name it). THE BAR LIFTS AT THE MADE INPUT:
there the key is the term oodSh that the committer makes of index, coins and seed, and validAt_made
shows hv at every index, all coins and every seed, by the library's key_atPure
(Johnson/Bind/ForProver/XiAt.lean) and validAt's own text. A bound on the probability that an honest
proof is rejected is no law over coins by that rule, and these statements are made to feed one.

What is not claimed. That any premise holds; that a run's explicit input is such an xiAt. What
AtFullSide/K14/FiveJoined.lean does not claim. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's blocksInOrder list, numbered from 0.
-/
import AtFullSide.K14.FiveJoined
import Johnson.Bind.ForProver.FiveFieldsAt
import Johnson.Bind.ForProver.XiAt
import Johnson.Desc.ProofFile.Honest.AtPureStoredW
import Johnson.Desc.ProofFile.Honest.K14.FiveFieldsThru

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open ProofFile (SecondHashFunctionArgument)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.AtFile (tableShared)
open ProofFile.Honest.SharedThread (lettersShared)
open Bind.ForProver (validAt shapeOf fiveFieldsK14_inScope fiveFields_of_imp)
open P5J (AtMgA TS)
open Desc.K14 (St beforePointOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {P₁ Wt : Type} {ℓ : WitLens Wt} {N : NumbersS} {nothingLeft : St → Bool}
  {fixed : Fmt.TreeSource → Nat} {n₁ n₂ : Nat}

/-- **FiveFields at the prover that onlineProverFromPublicFiles returns at the filling**, at the run's own input w under
the caller's sentence Vd. hv: under Vd the key of w is the key that the committer makes of the
matrix read off w's index and of w's coins, at some seed.
NOT IN FRONT OF A LAW OVER COINS: w is a letter and hv ties its key to its coins (the file's head).
-/
theorem five_of_validAt {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A)
    {Vd : Common W₀ IndexCommitterCoins TableKey → Prop} {w : Common W₀ IndexCommitterCoins TableKey}
    (hv : Vd w → validAt (shapeOf Zp) Zp ⟨I.weights Zp w.w₀, w.rc, w.key⟩) :
    FiveFields (qAt Zp Np) (fun v => v = w ∧ Vd v) (fun v => A.H.storedWords v.w₀ v.rc)
      (I.weights Zp) (randNow (qAt Zp Np)) := by
  have F := fiveFields_thru (I.weights Zp) (id : IndexCommitterCoins → IndexCommitterCoins)
    (fiveFieldsK14_inScope h.scope h.laid.pub (beforePointOf Np))
  have eZ := atPure_pub_at_head h hA
  refine fiveFields_of_imp (valid' := fun v => v = w ∧ Vd v)
    (stored' := fun v => A.H.storedWords v.w₀ v.rc) F (fun v hv' => ?_) (fun v _ y => ?_)
  · obtain ⟨rfl, hd⟩ := hv'
    exact hv hd
  · show A.H.storedWords v.w₀ v.rc _ y = Bind.ForProver.storedW Zp (I.weights Zp v.w₀) v.rc _ y
    rw [atPure_storedW hA (I.weights A.Z) (fun _ => rfl) v.w₀, eZ]

/-- **hv at the committer's made input.** At every filling, every index, all coins and every seed:
the key that the returned prover reads of the explicit input xiAt is the key that the committer
makes. -/
theorem validAt_made {W₀ Tr X₀ X : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {Φ : OnlineProverParts W₀ IndexCommitterCoins Tr X₀ X} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL Φ = .ok A)
    (weights : W₀ → Weights) (w₀ : W₀) (rc : IndexCommitterCoins) (sd : Bind.ForProver.Seed (shapeOf A.Z) × ℕ)
    (bytes : ByteArray × ByteArray) :
    validAt (shapeOf A.Z) A.Z ⟨weights w₀, rc,
      A.H.key (Bind.ForProver.xiAt (shapeOf A.Z) A.Z ⟨weights w₀, rc, sd⟩ bytes)⟩ :=
  ⟨sd, Bind.ForProver.key_atPure hA (shapeOf A.Z) ⟨weights w₀, rc, sd⟩ bytes⟩

/-- **The five at a member b, 1 ≤ b ≤ 8, at the prover and the book that onlineProverFromPublicFiles returns at the
filling**, with hv in the place of the five facts on the committed table and its key; the letter
rides is a list of clauses that all begin at border 10 or later. L stands for the letters, by the
equation hL. hN: the three sampled messages' tenants are those of the library's own table of
numbers. h0, h1: fixed is 1 at own 0, and 4 at own 1 and 2. hv: under Vd the key of w is the
committer's. hr, late: the form of the letter rides. NOT IN FRONT OF A LAW OVER COINS: w is a letter
and hv ties its key to its coins (the file's head).
-/
theorem five_at_base_valid {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A)
    {JU JO : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit}
    {Mg₀ : Common W₀ IndexCommitterCoins TableKey → MeaningS St P₁ Wt} {shape₀ : Nat → St → Bool}
    {rest : Coins A.B → Common W₀ IndexCommitterCoins TableKey → List Fmt.Drawn → Wt}
    {Kp₀ : Place → St → St → Prop}
    {Vd : Common W₀ IndexCommitterCoins TableKey → Prop} {Rd : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop}
    {w : Common W₀ IndexCommitterCoins TableKey}
    {L : SharedThread.Letters A.B St ProofFile.Cl W₀ IndexCommitterCoins TableKey Unit P₁ Wt}
    (hL : L = lettersShared Zp Np cF A.H N (fun v => mgWords ℓ (qAt Zp Np) N (Mg₀ v))
      (form2 (qAt Zp Np) shape₀) nothingLeft (fun s => OnBytes.Means.InOrder s.st)
      (witL ℓ (qAt Zp Np) (sentWithU Zp Np)
        (holds2 (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))) rest)
      (tableShared (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np)) JU JO ()) fixed n₁ n₂ Vd Rd
      (kp2 (qAt Zp Np) (sentWithU Zp Np) Kp₀) w)
    (hN : N.tenant = (IM.Seats.nsA OnBytes.secondHashFunction Zp Np cF).tenant)
    (h0 : fixed (.own 0) = 1) (h1 : ∀ i, i < 2 → fixed (.own (1 + i)) = 4)
    (hv : Vd w → validAt (shapeOf Zp) Zp ⟨I.weights Zp w.w₀, w.rc, w.key⟩)
    (Said : Nat → Coins A.B → Mid (Common W₀ IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String)
    {cs : List (RiderCl (Common W₀ IndexCommitterCoins TableKey) St)}
    (hr : ∀ b v s, Rd b v s ↔ ridersOf cs b v s) (late : ∀ c ∈ cs, 10 ≤ c.lo) (b : Nat)
    (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    PlaysS L.thread Said b ∧ BehindS L.thread Said b ∧ ExchangeS L.thread Said b ∧
      RidesPastS L.thread Said b ∧ AcceptedS L.thread Said fall b :=
  five_at_base_late h I o' S O hA hL hN h0 h1 (five_of_validAt h I o' S O hA hv) Said fall hr late
    b hb1 hb8

end AtFullSide.K14

#print axioms AtFullSide.K14.five_of_validAt
#print axioms AtFullSide.K14.validAt_made
#print axioms AtFullSide.K14.five_at_base_valid
