-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/FiveJoined.lean: the linear claim's shared rounds (kind K14): THE FIVE STATEMENTS ON
ONE SUB-PROTOCOL (PlaysS, BehindS, ExchangeS, RidesPastS, AcceptedS,
Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean) AT THE MEMBERS 1 TO 8 OF THE SHARED CHAIN, at the
prover A.H and the book A.B that the maker onlineProverFromPublicFiles returns at the filling onlineProverPartsInUse, at any
type of index. One theorem: five_at_base_laid (AtFullSide/K14/FiveTabled.lean) with two more of its
premises shown: the one on the book of coins (book_at_made, AtFullSide/K14/BookSplitAtMade.lean) and
the one on the table's numbers (tenant_at_head, Honest/K14/TenantAtHead.lean).

  five_at_base_joined the five, with the clause on the letter rides handed on in four premises
  five_at_base_late   the five where the letter rides is a list of clauses that all begin at border
                      10 or later: the four premises hold at these eight members for want of a case

WHAT STAYS A PREMISE.
  h, hA               the library's hypothesis at the full size (P5J.AtMgA,
                      Johnson/P5J/MgAtAll.lean), at the format's second hash function; onlineProverFromPublicFiles
                      returns A
  hL                  the thread's letters have this form: this kind's makers laid at Mg, shape,
                      order, wit, keeps, over Mg₀, shape₀, rest, Kp₀ that stay free, at the
                      filling's two readers I.weights Zp and randNow (qAt Zp Np); table is
                      tableShared at these readers
  hN                  the three sampled messages' tenants are those of the library's own table of
                      numbers (IM.Seats.nsA)
  h0, h1              fixed is 1 at the chain's own tree 0, and 4 at its own trees 1 and 2
  five                five facts on the committed table and its key, at the run's own input w, under
                      the caller's sentence Vd on it: to be shown of the committer's table and key,
                      not laid into Vd (Honest/K14/FiveAmong.lean's head)
  hr, h₀, hst, hl     on the letter rides (Honest/K14/FiveAtShared.lean's head)

What is not claimed. That any premise holds. That the thread's invariant holds at any state: each of
the five starts from it. Nothing on the members 0, 9, 10, 11; but hL fixes the thread's form at the
borders 2 to 9, so also in front of the member 9. Nothing on completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's blocksInOrder list, numbered from 0.
-/
import AtFullSide.K14.FiveTabled
import AtFullSide.K14.BookSplitAtMade
import Johnson.Desc.ProofFile.Honest.K14.TenantAtHead

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
open P5J (AtMgA TS)
open Desc.K14 (St)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {P₁ Wt : Type} {ℓ : WitLens Wt} {N : NumbersS} {nothingLeft : St → Bool}
  {fixed : Fmt.TreeSource → Nat} {n₁ n₂ : Nat}

/-- **The five at a member b, 1 ≤ b ≤ 8, at the prover and the book that onlineProverFromPublicFiles returns at the
filling.** L stands for the letters, by the equation hL: this kind's makers laid at Mg, shape,
order, wit, keeps; table is tableShared at the filling's two readers. hN: the three sampled
messages' tenants are those of the library's own table of numbers. h0, h1: fixed is 1 at own 0, and
4 at own 1 and 2. five: the five facts on the committed table and its key at the run's own input.
hr, h₀, hst, hl: the clause of BehindS on the letter rides, handed on to the caller. -/
theorem five_at_base_joined {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
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
    (five : FiveFields (qAt Zp Np) (fun v => v = w ∧ Vd v) (fun v => A.H.storedWords v.w₀ v.rc)
      (I.weights Zp) (randNow (qAt Zp Np)))
    (Said : Nat → Coins A.B → Mid (Common W₀ IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String)
    {R₀ : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop}
    {cs : List (RiderCl (Common W₀ IndexCommitterCoins TableKey) St)}
    (hr : ∀ b v s, Rd b v s ↔ R₀ b v s ∧ ridersOf cs b v s) (b : Nat) (hb1 : 1 ≤ b) (hb8 : b ≤ 8)
    (h₀ : ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy L.thread b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAtS L.thread Said b c) :
    PlaysS L.thread Said b ∧ BehindS L.thread Said b ∧ ExchangeS L.thread Said b ∧
      RidesPastS L.thread Said b ∧ AcceptedS L.thread Said fall b :=
  five_at_base_laid h I o' S O hA hL h0 h1 (tenant_at_head h.toAtMg hN) five (book_at_made h hA)
    Said fall hr b hb1 hb8 h₀ hst hl

/-- **The five where the letter rides is a list of clauses that all begin at border 10 or later.**
No clause then speaks at a border 1 to 9, so at the members 1 to 8 nothing is to be shown of the
letter. The other premises are five_at_base_joined's. -/
theorem five_at_base_late {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
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
    (five : FiveFields (qAt Zp Np) (fun v => v = w ∧ Vd v) (fun v => A.H.storedWords v.w₀ v.rc)
      (I.weights Zp) (randNow (qAt Zp Np)))
    (Said : Nat → Coins A.B → Mid (Common W₀ IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String)
    {cs : List (RiderCl (Common W₀ IndexCommitterCoins TableKey) St)}
    (hr : ∀ b v s, Rd b v s ↔ ridersOf cs b v s) (late : ∀ c ∈ cs, 10 ≤ c.lo) (b : Nat)
    (hb1 : 1 ≤ b) (hb8 : b ≤ 8) :
    PlaysS L.thread Said b ∧ BehindS L.thread Said b ∧ ExchangeS L.thread Said b ∧
      RidesPastS L.thread Said b ∧ AcceptedS L.thread Said fall b :=
  five_at_base_joined h I o' S O hA hL hN h0 h1 five Said fall (R₀ := fun _ _ _ => True)
    (fun b v s => ⟨fun g => ⟨trivial, (hr b v s).1 g⟩, fun g => (hr b v s).2 g.2⟩) b hb1 hb8
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun c hc g _ => absurd (late c hc) (by omega))
    (fun c hc g => absurd (late c hc) (by omega))

end AtFullSide.K14

#print axioms AtFullSide.K14.five_at_base_joined
#print axioms AtFullSide.K14.five_at_base_late
