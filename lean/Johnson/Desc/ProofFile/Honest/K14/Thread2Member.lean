-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Thread2Member.lean: kind K14: the public premises of the shared
chain's thread HAVE TYPED MEMBERS (at every list bp that is not empty), and the letters of
Honest/K14/Thread2.lean ARE APPLIED ONCE, at a term that is no honest prover's: much of what is
shown there is met vacuously (see «What is not claimed»).

Main names:
  plan2_key, plan2_real   **Plan2 at the two typed shapes**: the typed sizes of a key of full size,
                      and those over a proof file's own codes (Johnson/Desc/K14/Honest/YesAt.lean:
                      planFacts_key, planFacts_real; ChainWitness.lean: planOwn_of): at every item
                      and every list bp THAT IS NOT EMPTY (a premise); sentU and layO are had by
                      "there is", not written out
  noCoins, others0, others0_tenant   **a term of Others**, at any book, any planner's chains, any
                      committed table (stored) and any test on inputs (valid): the least at every
                      other field; the witness is a family of words. IT IS NO HONEST PROVER's: no
                      half, holdings that are 0
  debts_at_key        at the first typed shape (bp not empty) and that term: the form behind and
                      keeps (FormKeeps) at 2 to 8, «RidesPast» at 1 to 8, «Exchange» at 6 and 7:
                      what asks none but public premises
  behind_at_key       a whole «Behind» at 2 to 8 at that term (bp not empty): by Debts2.lean's
                      behind_of_formKeeps at the list of no clause

The term others0 is an instance. Honest/K14/Debts2.lean's head names behind_at_key as the term at
which the premises of behind_of_formKeeps are met together. plan2_key and plan2_real are called
(Honest/K14/Thread2Full.lean).

What is not claimed. THAT THE THREAD HOLDS AT ANY RUN. debts_at_key shows that the letters can be
applied by type, and no more. (The border b: in front of the member number b; a stand: the coins,
the two states and the tables at hand of which the thread's sentence Thr speaks.) TWO WAYS IN WHICH
ITS SENTENCES ARE MET VACUOUSLY. (1) Where stored hands "LOC" no column, the thread holds at no
stand from the border 5 on, and ten of the seventeen sentences are met vacuously there. (2) AT EVERY
stored, by a reading of the definitions that no theorem states: others0 has no half, so each round
of a member is played with no item shown (chainSteps and Step.tell, Honest/Frame.lean: no move, and
no run to fall back on), while the member's own step asks that each round shows just the items that
it declares, but for the roots (roundsFit in Block.step, Johnson/Desc/Block.lean). So wherever a
member's round declares such an item its step returns at no play, and FormKeeps and «Behind» at that
member are met vacuously: at "SPLIT" (8), whose round declares one element under Plan2, and at the
two sendings (2 and 5) wherever the second round declares an answer (not evaluated at the key's full
size). So ten is a lower count. That a planner's chains are there. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Exchange2
import Johnson.Desc.ProofFile.Honest.K14.Rides2
import Johnson.Desc.K14.Honest.ChainWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)
open OnBytes.Means (Words)
open Desc.K14 (frontBlock)
open Desc.K14.Honest

/-! ## The public premises at the two typed shapes -/

/-- **Plan2 at the typed sizes of a key of full size**, at every item and every list bp that is not
empty; sentU and layO are had by "there is", not written out. -/
theorem plan2_key : ∃ (sentU : Array OracleNotice) (layO : TreeLay),
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] →
      Plan2 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU layO := by
  obtain ⟨sentU, layO, hf⟩ := planFacts_key
  refine ⟨sentU, layO, fun item bp hbp => ?_⟩
  obtain ⟨hBU, hBO⟩ := planOwn_of (Desc.K14.Law.k14_key item bp hbp) (hf item bp hbp).goes
  exact ⟨hf item bp hbp, hBU, hBO⟩

/-- **Plan2 at the typed sizes over a proof file's own codes**, at every item and every list bp that
is not empty; the sizes x, sentU and layO are had by "there is", not written out. -/
theorem plan2_real : ∃ (x : LinSized) (sentU : Array OracleNotice) (layO : TreeLay),
    realSized = some (x, codesFull2) ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] →
      Plan2 ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ sentU layO := by
  obtain ⟨x, sentU, layO, a1, _, hf⟩ := planFacts_real
  obtain ⟨x', b1, _, hC⟩ := Desc.K14.Law.k14_real
  obtain rfl : x = x' := congrArg Prod.fst (Option.some.inj (a1.symm.trans b1))
  refine ⟨x, sentU, layO, a1, fun item bp hbp => ?_⟩
  obtain ⟨hBU, hBO⟩ := planOwn_of (hC item bp hbp) (hf item bp hbp).goes
  exact ⟨hf item bp hbp, hBU, hBO⟩

/-! ## A term of Others -/

/-- Random values that are all 0. -/
noncomputable def noCoins : MsgCoins := ⟨fun _ _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-- **A TERM OF Others**, at any book, any planner's chains, any committed table (stored) and any
test on inputs (valid): the least at every other field: no proximity test, the front sub-protocol
once more as the closing, no half, tests that pass and sentences that hold everywhere, holdings that
are 0. It is no honest prover's. -/
noncomputable def others0 (Bk : ProverCoinCounts) (c : Model.Verify.Chains)
    (stored : Common Unit Unit TableKey → Nat → Nat → Option (List UInt64))
    (valid : Common Unit Unit TableKey → Prop) :
    Others Bk Unit Unit Unit Unit (Words Cb.Gl.E) where
  lens := WitLens.words
  c := c
  tests := []
  last := fun _ => frontBlock c
  N := ⟨0, fun m => (0, num m), (0, 0), (0, 0)⟩
  Mg₀ := fun _ => ⟨fun _ _ _ _ _ => True, fun _ _ _ => True, fun _ _ _ _ _ => True,
    fun _ _ _ => True, fun _ _ => True, fun _ _ => True, fun _ _ _ => True, fun _ _ _ => True,
    fun _ _ _ _ => True, fun _ _ _ => True, fun _ => True⟩
  shape := fun _ _ => true
  nothingLeft := fun _ => true
  hs := []
  table := fun _ _ _ _ => (⟨2, none, 0, .K14⟩, ⟨0, 0, fun _ i => i.elim0⟩)
  fixed := fun _ => 0
  stored := stored
  n₁ := 0
  n₂ := 0
  valid := valid
  keeps := fun _ _ _ => True
  rides := fun _ _ _ => True
  holds := fun _ _ => ⟨fun _ _ _ => 0, fun _ _ => 0, noCoins, noCoins, noCoins, noCoins⟩
  rest := fun _ _ _ _ _ _ => 0

/-- No two messages have one tenant there. -/
theorem others0_tenant (Bk : ProverCoinCounts) (c : Model.Verify.Chains)
    (stored : Common Unit Unit TableKey → Nat → Nat → Option (List UInt64))
    (valid : Common Unit Unit TableKey → Prop) :
    Function.Injective (others0 Bk c stored valid).N.tenant := by
  intro a b h
  have h2 : num a = num b := congrArg Prod.snd h
  cases a <;> cases b <;> first | rfl | cases h2

/-- **The letters applied**: at the typed sizes of a key of full size, AT THE sentU THAT GOES OUT
WITH o_u AT THAT SHAPE (withU: it binds sentU to the letter), at a list bp that is not empty, and
this term of Others: those of the thread's sentences that ask none but public premises. That the
thread holds at a run is not said; how far the sentences are met vacuously: see the head. -/
theorem debts_at_key : ∃ sentU : Array OracleNotice,
    Desc.K14.withU keyFull.once.shape = some sentU ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] → ∀ (Bk : ProverCoinCounts) (c : Model.Verify.Chains)
      (stored : Common Unit Unit TableKey → Nat → Nat → Option (List UInt64))
      (valid : Common Unit Unit TableKey → Prop) (Cl : Type),
      (∀ b, 2 ≤ b → b ≤ 8 → FormKeeps (letters2
        ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU
        (others0 Bk c stored valid) Cl).thread b) ∧
      (∀ b, 1 ≤ b → b ≤ 8 → RidesPast (letters2
        ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU
        (others0 Bk c stored valid) Cl).thread b) ∧
      Exchange (letters2 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU
        (others0 Bk c stored valid) Cl).thread 6 ∧
      Exchange (letters2 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU
        (others0 Bk c stored valid) Cl).thread 7 := by
  obtain ⟨sentU, layO, hp⟩ := plan2_key
  refine ⟨sentU, (hp 0 [(0, 0)] (List.cons_ne_nil _ _)).facts.goes,
    fun item bp hbp Bk c stored valid Cl => ⟨fun b h2 h8 => ?_, fun b h1 h8 => ?_, ?_, ?_⟩⟩
  · have hQ := hp item bp hbp
    match b, h2, h8 with
    | 2, _, _ => exact formKeeps2 hQ _ Cl
    | 3, _, _ => exact formKeeps3 hQ _ Cl
    | 4, _, _ => exact formKeeps4 hQ _ Cl
    | 5, _, _ => exact formKeeps5 hQ _ Cl
    | 6, _, _ => exact formKeeps6 hQ _ Cl
    | 7, _, _ => exact formKeeps7 hQ _ Cl
    | 8, _, _ => exact formKeeps8 hQ _ Cl
  · match b, h1, h8 with
    | 1, _, _ => exact ridesPast1 _ Cl
    | 2, _, _ => exact ridesPast2 _ Cl
    | 3, _, _ => exact ridesPast3 _ Cl
    | 4, _, _ => exact ridesPast4 _ Cl
    | 5, _, _ => exact ridesPast5 _ Cl
    | 6, _, _ => exact ridesPast6 _ Cl
    | 7, _, _ => exact ridesPast7 _ Cl
    | 8, _, _ => exact ridesPast8 _ Cl
  · exact exchange6 _ Cl
  · exact exchange7 (hp item bp hbp) _ Cl (others0_tenant Bk c stored valid)

/-- **A WHOLE «Behind» at 2 to 8, at that term**, at the same sentU (withU), at a list bp that is
not empty: its letter rides says nothing: it is the list of no clause: so the three premises of
behind_of_formKeeps (Debts2.lean) are met together. At 8, and at 2 and 5 wherever the sending's
second round declares an answer, it is met vacuously whatever stored is, since the term has no half:
see the head, (2). -/
theorem behind_at_key : ∃ sentU : Array OracleNotice,
    Desc.K14.withU keyFull.once.shape = some sentU ∧
    ∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] → ∀ (Bk : ProverCoinCounts) (c : Model.Verify.Chains)
      (stored : Common Unit Unit TableKey → Nat → Nat → Option (List UInt64))
      (valid : Common Unit Unit TableKey → Prop) (Cl : Type) (b : Nat), 2 ≤ b → b ≤ 8 →
      Behind (letters2 ⟨recordSet, .once, keyFull.codes, keyFull.once.shape, item, bp⟩ sentU
        (others0 Bk c stored valid) Cl).thread b := by
  obtain ⟨sentU, hU, h⟩ := debts_at_key
  exact ⟨sentU, hU, fun item bp hbp Bk c stored valid Cl b h2 h8 =>
    behind_of_formKeeps (cs := [])
      (fun _ _ _ => ⟨fun _ x hx => absurd hx (List.not_mem_nil), fun _ => trivial⟩)
      ((h item bp hbp Bk c stored valid Cl).1 b h2 h8)
      (fun x hx => absurd hx (List.not_mem_nil)) fun x hx => absurd hx (List.not_mem_nil)⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.plan2_key
#print axioms ProofFile.Honest.K14.plan2_real
#print axioms ProofFile.Honest.K14.others0_tenant
#print axioms ProofFile.Honest.K14.debts_at_key
#print axioms ProofFile.Honest.K14.behind_at_key
