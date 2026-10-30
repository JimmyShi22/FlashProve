-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/FiveAtBase.lean: the linear claim's shared rounds (kind K14): AT THE PROVER THAT THE
MAKER onlineProverFromPublicFiles RETURNS AT THE FILLING onlineProverPartsInUse
(Johnson/Desc/ProofFile/Honest/K1/Law/WSideAtFill.lean), at any type of index (I : WiderIn W₀): all
that the kind's statements ask of the shared chain's thread (K14Asks, Honest/K14/Asks.lean), and the
five statements on one sub-protocol (PlaysS, BehindS, ExchangeS, RidesPastS, AcceptedS,
Honest/Thread/PaysS.lean) at the members 1 to 8 of the shared chain. Calls of asks_among
(Honest/K14/AsksAtShared.lean) and five_among (Honest/K14/FiveAmong.lean), with their three premises
on the prover's list shown (AtFullSide/K14/SixAtBase.lean).

  found_at_base     the search at the place of each of the six sides in that prover's list finds
                    that side. It is stated side by side: which side stands at which member's place
                    is halves_eq and sendHalves_eq's to say (Honest/K14/PartsPlay.lean,
                    SendingsPlay.lean); the members 3 and 6 have no side, and nothing is said of a
                    search at their places
  asks_at_base      **K14Asks at that prover's thread**
  five_at_base      **the five at a member b, 1 ≤ b ≤ 8, of that prover's thread**

The readers of the prover's input are I.weights Zp (the matrix off the index) and randNow (qAt Zp
Np) (the committed table's pads and tails off the committer's randomness).

WHAT STAYS A PREMISE.
  h, hA               the library's hypothesis at the full size (P5J.AtMgA,
                      Johnson/P5J/MgAtAll.lean), at the format's second hash function; onlineProverFromPublicFiles
                      returns A
  letters             nine equations on the thread's letters (Asked, Honest/K14/LettersVar.lean)
  tenant              no two of the three sampled messages have the same tree's number and the same
                      number in that tree
  treesU, treesO      the trees of the two sendings are the thread's tables
  five                five facts on the committed table and its key, at the run's own input w, under
                      the caller's sentence Vd on it: to be shown of the committer's table and key,
                      not laid into Vd (Honest/K14/FiveAmong.lean's head)
  book                on the entries of the book of coins by which "SPLIT" spends coins (its spender
                      is that part, its field once is true)
  hr, h₀, hst, hl     in five_at_base: on the letter rides (Honest/K14/FiveAtShared.lean's head)
The book Bk is a letter, and so are the thread's other letters, `Said` and `fall`. The book that
onlineProverFromPublicFiles returns with the prover is A.B.

What is not claimed. That any premise holds. That the thread's invariant holds at any state: each of
the five starts from it. Nothing on the members 0, 9, 10, 11; but the premise letters fixes the
thread's form at the borders 2 to 9, so also in front of the member 9. Nothing on the prover at the
filling read through a pair of maps but what AtFullSide/K14/SixAtBase.lean says of its list. Nothing
on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's blocksInOrder list, numbered from 0. A side
is the prover's list of parts at one place (Placed, Honest/Frame.lean).
-/
import AtFullSide.K14.SixAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12.Seat (tests last)
open ProofFile (Pub Ground SecondHashFunctionArgument)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.SharedThread (lettersShared)
open P5J (AtMgA TS)
open Desc.K14 (St)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {W₀ : Type} {Bk : ProverCoinCounts} {P₁ Wt : Type} {ℓ : WitLens Wt} {N : NumbersS}
  {shape : Nat → St → Bool} {nothingLeft : St → Bool} {order : St → Prop}
  {fixed : Fmt.TreeSource → Nat} {n₁ n₂ : Nat} {Kp : Place → St → St → Prop}

/-- **The search at the place of each of the six sides finds that side**, in the list of the prover
that onlineProverFromPublicFiles returns at the filling. -/
theorem found_at_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A) :
    ∀ g ∈ (proverSidesOfSharedRounds (planData (qAt Zp Np)) (I.weights Zp) ++
        proverSidesOfSharedSendings ⟨qAt Zp Np, 0⟩ (I.weights Zp) (randNow (qAt Zp Np)) :
        List (Placed Empty (Common W₀ IndexCommitterCoins TableKey) Unit)),
      (A.H.shared.find? fun y => y.place == g.place) = some g := by
  intro g hg
  have e := base_shared h I o' S O hA
  refine find_of_mem _ g ?_ (e ▸ List.mem_append_left _ hg)
  rw [e, List.map_append]
  obtain ⟨nd, among⟩ := six_apart (Ky := TableKey) (X := Unit) (planData (qAt Zp Np))
    ⟨qAt Zp Np, 0⟩ (I.weights Zp) (randNow (qAt Zp Np))
  refine List.pairwise_append.2 ⟨nd, (testSides_places I Zp).1, fun a ha b hb e' => ?_⟩
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ha
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hb
  have e'' : u.place = v.place := e'
  exact (testSides_places I Zp).2 v hv (e'' ▸ among u hu)

/-- **K14Asks at the thread of the prover that onlineProverFromPublicFiles returns at the filling.** The premises: the
file's head. -/
theorem asks_at_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A)
    {Mg : Common W₀ IndexCommitterCoins TableKey → MeaningS St P₁ Wt}
    {wit : Coins Bk → Common W₀ IndexCommitterCoins TableKey → List Fmt.Drawn → Wt}
    {table : Fmt.TreeSource → Coins Bk → Common W₀ IndexCommitterCoins TableKey → List Fmt.Drawn → Place × Table}
    {Vd : Common W₀ IndexCommitterCoins TableKey → Prop} {Rd : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop}
    {w : Common W₀ IndexCommitterCoins TableKey}
    (letters : Asked ℓ (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w) (qAt Zp Np) (sentWithU Zp Np) Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))))
    (tenant : Function.Injective N.tenant)
    (treesU : TreesLaid (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w).thread 2 (jobU ⟨qAt Zp Np, 0⟩)
      (witOf (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))))
    (treesO : TreesLaid (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w).thread 5 (jobOmega ⟨qAt Zp Np, 0⟩)
      (witOf (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))))
    (five : FiveFields (qAt Zp Np) (fun v => v = w ∧ Vd v) (fun v => A.H.storedWords v.w₀ v.rc)
      (I.weights Zp) (randNow (qAt Zp Np)))
    (book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨qAt Zp Np, 0⟩).sort 1⟩) :
    ∃ layO, K14Asks ℓ
      (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w)
      (qAt Zp Np) (sentWithU Zp Np) layO Zp.p.chains (tests Np) last (planData (qAt Zp Np))
      (I.weights Zp) (randNow (qAt Zp Np)) :=
  asks_among h (base_shared h I o' S O hA) (testSides_places I Zp).1 (testSides_places I Zp).2
    letters tenant treesU treesO five book

/-- **The five at a member b, 1 ≤ b ≤ 8, at the prover that onlineProverFromPublicFiles returns at the filling.** The
premises: the file's head. -/
theorem five_at_base (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A)
    {Mg : Common W₀ IndexCommitterCoins TableKey → MeaningS St P₁ Wt}
    {wit : Coins Bk → Common W₀ IndexCommitterCoins TableKey → List Fmt.Drawn → Wt}
    {table : Fmt.TreeSource → Coins Bk → Common W₀ IndexCommitterCoins TableKey → List Fmt.Drawn → Place × Table}
    {Vd : Common W₀ IndexCommitterCoins TableKey → Prop} {Rd : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop}
    {w : Common W₀ IndexCommitterCoins TableKey}
    (letters : Asked ℓ (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w) (qAt Zp Np) (sentWithU Zp Np) Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))))
    (tenant : Function.Injective N.tenant)
    (treesU : TreesLaid (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w).thread 2 (jobU ⟨qAt Zp Np, 0⟩)
      (witOf (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))))
    (treesO : TreesLaid (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁
      n₂ Vd Rd Kp w).thread 5 (jobOmega ⟨qAt Zp Np, 0⟩)
      (witOf (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))))
    (five : FiveFields (qAt Zp Np) (fun v => v = w ∧ Vd v) (fun v => A.H.storedWords v.w₀ v.rc)
      (I.weights Zp) (randNow (qAt Zp Np)))
    (book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨qAt Zp Np, 0⟩).sort 1⟩)
    (Said : Nat → Coins Bk → Mid (Common W₀ IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String)
    {R₀ : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop}
    {cs : List (RiderCl (Common W₀ IndexCommitterCoins TableKey) St)}
    (hr : ∀ b v s, Rd b v s ↔ R₀ b v s ∧ ridersOf cs b v s) (b : Nat) (h1 : 1 ≤ b) (h8 : b ≤ 8)
    (h₀ : ∀ blk, (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd
        Rd Kp w).thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
        w).thread Said b k s m E → drawsFit blk.rounds ds = true →
      (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
        w).thread.Stepped blk k s m E ds y cols s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy (lettersShared Zp Np cF A.H N Mg shape
      nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w).thread b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAtS (lettersShared Zp Np cF A.H N Mg shape nothingLeft order
      wit table fixed n₁ n₂ Vd Rd Kp w).thread Said b c) :
    PlaysS (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp
        w).thread Said b ∧
      BehindS (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd
        Kp w).thread Said b ∧
      ExchangeS (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd
        Rd Kp w).thread Said b ∧
      RidesPastS (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd
        Rd Kp w).thread Said b ∧
      AcceptedS (lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd
        Rd Kp w).thread Said fall b :=
  five_among h (base_shared h I o' S O hA) (testSides_places I Zp).1 (testSides_places I Zp).2
    letters tenant treesU treesO five book Said fall hr b h1 h8 h₀ hst hl

end AtFullSide.K14

#print axioms AtFullSide.K14.found_at_base
#print axioms AtFullSide.K14.asks_at_base
#print axioms AtFullSide.K14.five_at_base
