-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ExchangeAtHead.lean.
WHAT IT IS NOT. CONDITIONAL ON ONE SHARE THAT IS PAID NOWHERE: THE DEBT's SHARE AT THE ITEM
formsT 24 3 "planes" (hPlanes): that item speaks of the lookup argument's run on the planes; the
relation that the output head's own law opens does not read them. SO THE DEBT ExchangeS AT BORDER
341 IS NOT SHOWN: IT IS BROUGHT DOWN TO THAT ONE SHARE AND FIVE MORE PREMISES, EACH SHOWN HERE OF
NOTHING: the library's hypothesis P5J.AtMgA; BehindS at the border (hB); that the letter Kp at the
sub-protocol's place IS the sub-protocol's own clause of what its step keeps (hKp, hKp'); K6HalfAt
(on the prover's halves); K6Script (seven sentences that tie the prover's cells, coins and letters
to what the law reads off the thread's witness: ALL THE CONTENT ON VALUES LIES THERE). (Of the
hypothesis the library has a member under four premises on the three public files:
P5J.head_exists_at_name, Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) That the
thread holds at any run is shown nowhere. ExchangeS is a definition (Honest/Thread/PaysS.lean): a
premise's form: none of the library's goals. That the verifier accepts is that debt's own premise:
nothing here shows it. A JOIN: NO NEW MATHEMATICS: ONE CALL. The full size, the format's second
hash function and border 341 alone. Nothing on soundness, on completeness or on what a proof hides.
WHAT IT IS. THE SUB-PROTOCOL "the output head's own rounds": THE DEBT ExchangeS AT ITS BORDER, AT
THE FIRST CHAIN's THREAD AT THE LIBRARY's OWN LETTERS (lettersHead, Honest/Thread/FirstHead.lean),
at every letter Said: all seven items that the row owes (owes_341, Honest/K6/Law/RidesPast.lean).
  k6_exchangeS_at_head   THE TOP
WHO PAYS WHAT. The gathering over the row's list: k6_exchangeS_of_four (Honest/K6/Law/
RidesPast.lean), which pays pin 24 0, pinW and constr 24 small itself, under hB and hKp'.
formsT 24 4 "own", "join" and "weights": k6_exchange_at_head_keeps (Honest/K6/Law/ShareAtHead.lean),
under hKp, K6HalfAt and K6Script. formsT 24 3 "planes": the premise hPlanes. hB: where the letter
for the riders is a list of clauses and Kp is laid by the places' kinds, k6_behindS and
k6_behindS_sorts (Honest/K6/Law/Behind.lean) have it under premises on these clauses, on the letter
b₀ and on the kind's clause; they are not called here.
OF THE FOLDER Johnson/Goal/ it names nothing, and no module of it is imported by name
(cutAtHead, which it names, holds Meaning.sizesOf: Honest/K6/Law/ShareAtHead.lean says so).
Over files that have not yet landed in the library: the two that it imports and what they import.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.ShareAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.RidesPast

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps plK6)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.X)
open ProofFile.Honest (BehindS ExchangeS ExchangeAtS ProverCoinCounts Coins Local Mid Prover)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (HeadAsk K6Script K6HalfAt k6_exchangeS_of_four)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE DEBT ExchangeS AT THE OUTPUT HEAD's OWN ROUNDS, AT THE LIBRARY's OWN LETTERS, FROM ONE
SHARE THAT IS NOT PAID**, at every letter Said. CONDITIONAL on the hypothesis that ties the table's
letters to the IOP as written in Lean; on hPlanes: the debt's share at the item formsT 24 3
"planes"; on hB: the debt BehindS at the border; on hKp and hKp': at the sub-protocol's place the
letter Kp is the sub-protocol's own clause of what its step keeps (K6Keeps,
Johnson/Desc/K6/Honest/Law/Keeps.lean); and on the two named premises on the prover's halves and on
what ties the prover's cells, coins and letters to what the law reads off the witness. -/
theorem k6_exchangeS_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (hKp : ∀ s s', K6Keeps s s' → Kp plK6 s s') (hKp' : ∀ s s', Kp plK6 s s' → K6Keeps s s')
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (hH : K6HalfAt Zp H wit)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Hc : K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) wit IM.k6Place (cutAtHead h Q carryX))
    (hB : BehindS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
    (hPlanes : ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      341 (Item.formsT 24 3 "planes")) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 := by
  obtain ⟨hOwn, hJoin, hWeights⟩ :=
    k6_exchange_at_head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hKp wit hH Said Hc
  exact k6_exchangeS_of_four h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hB hKp' hOwn hPlanes
    hJoin hWeights

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchangeS_at_head
