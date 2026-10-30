-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Join15.lean: ROW 1.15 OF THE KEY FILE's TABLES: THE TWO FACTS (shape) AND (free) OF fwd_of_facts' hdec (Johnson/RunOne/Law/K12FwdFacts.lean), JOINED, IN THAT PREMISE's OWN FORM: at every yes of the held block. Statements with proofs.
OBJECT. The third and fourth conjuncts of fwd_of_facts' hdec. USER. Whoever fills hdec.
LETTERS. The tables' own. WHAT IS PAID HERE, OFF THE DESCRIPTION's OWN TEST ON THE FILE ((descriptionFromSource X N P).fileOk = true): the test's number of stages is the plan's (the clause "stages.rng") · the codes' lengths are in order (the clause "lengths"). WHAT IS PAID BY Johnson/RunOne/Law/K12Order.lean: the statement stays in order.
PREMISES LEFT, EACH OVER ALL YESES OF THE BLOCK, WITH WHO CAN PAY IT:
  hp     the block's test on the plan: rng_planOk (Johnson/RunOne/KeySmpStay.lean) has it off (descriptionFromSource X N P).planOk (another cone).
  hS     the sampled messages stay (K1.SmpStay): ranges_smpStay (KeySmpStay.lean): PROVED, in another cone: a call at the joining.
  htr    how many trees stand behind the test: PAID HERE (trees_fact) over Johnson/RunOne/Law/K12Trees.lean's count along the stages, UNDER ONE PREMISE ON layTrees: OneTree at the plan's codes: each switch's prover's message lays one tree: oneTree_all (Johnson/RunOne/Law/K12OneTree.lean) has it, for all codes.
  hft    the place's first tree's number is 0: PUBLIC; no test of the description asks it; the maker of the place's numbers lays 0 (Johnson/Desc/Key/Ranges.lean): to be had where N is the maker's.
  hrec   the reading's recOf says the same of both records: on the tables' letter B.h₁.
  hcoll  a collision is read off the cells alone: what CellOnly coll gives.

  nums_of_ne: where the test's parameters have a stage they are the place's numbers. stages_of_fileOk | lengths_of_fileOk: the two clauses.
  trees_fact: the trees behind the test. shape_fact | free_fact: the two facts. shape_fact': shape_fact with htr paid.
Limits. A block that says no to all meets every statement. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Free15
import Johnson.RunOne.Law.K12Order
import Johnson.RunOne.Law.K12Trees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12Join15
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open VerifiableInference.Desc.K1 (SmpStay)
open Johnson.RunOne.KeyRows23 (BaseSt Fk oneAt fileOk_all)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ open₁ free₁ plan₁ readers₁ book₁ slots₁)
open Johnson.RunOne.Law.K12Shape15 (out_of_yes front15 shape_15_16)
open Johnson.RunOne.Law.K12Free15 (free_15_16)
open Johnson.RunOne.Law.K12Order (ranges_inOrder)
open Johnson.RunOne.Law.K12Trees (OneTree k12_trees)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)

/-- Where the test's parameters have a stage they are the place's numbers. -/
theorem nums_of_ne {N : H2U.PlaceNums} (h : (rangesParams N).nums.stages ≠ []) : (rangesParams N).nums = N.nums := by
  unfold rangesParams H2U.proximityTestParametersAt at h ⊢
  by_cases c : (rangesPlace.chain != N.chain) = true
  · rw [if_pos c] at h
    exact absurd rfl h
  · rw [if_neg c] at h ⊢
    cases e : H2U.testOracles5 N.nums N.firstGroup with
    | none =>
      rw [e] at h
      exact absurd rfl h
    | some os => rfl

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- The clause "stages.rng" of the description's test on the file: its first conjunct. -/
theorem stages_of_fileOk (h : (descriptionFromSource X N P).fileOk = true) : N.nums.stages.length = X.Y.k.oneTime.ranges.stages.length := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  have h4 : stagesAsSized X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.stages N = true :=
    List.all_eq_true.1 ha ("stages.rng", stagesAsSized X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.stages N)
      (List.mem_append.2 (Or.inr (List.mem_of_getElem? (i := 4) rfl)))
  unfold stagesAsSized at h4
  simp only [Bool.and_eq_true, beq_iff_eq] at h4
  exact h4.1.1

/-- The clause "lengths". -/
theorem lengths_of_fileOk (h : (descriptionFromSource X N P).fileOk = true) : X.Y.k.oneTime.codes.lengthsOk = true := by
  obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P h
  exact List.all_eq_true.1 ha ("lengths", X.Y.k.oneTime.codes.lengthsOk)
    (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
      (List.mem_of_getElem? (l := sourceClauses X.Y) (i := 9) rfl)))))))

/-- **The fact (shape)**, in the letter of fwd_of_facts' hdec. -/
theorem shape_fact (hf : (descriptionFromSource X N P).fileOk = true) (hl : (lookupsOf X.Y.k.oneTime).length = 2) (hft : N.nums.firstTree = 0)
    (hp : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk = true)
    (hS : ∀ s rs gs s', (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).decide s rs gs = .ok s' → SmpStay s.d.st s'.d.st)
    (htr : ∀ s rs gs s', (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).decide s rs gs = .ok s' →
      shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 15 s = true →
      s'.d.book.trees.size = X.Y.k.oneTime.ranges.stages.length + 1)
    (a b : Xi × FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b) :
    shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true →
      shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 16 b.2 = true := by
  have hn : n₁ (oneAt X) = 2 := hl
  rw [hn]
  intro h15
  have hy : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).decide a.2 rs gs = .ok b.2 := (held_decide _ a rs gs b hd).2
  obtain ⟨_, _, _, _, _, _, _, hne⟩ := out_of_yes hp hy
  have hst : (rangesParams N).nums.stages.length = X.Y.k.oneTime.ranges.stages.length := by
    rw [nums_of_ne hne]
    exact stages_of_fileOk X N P hf
  exact shape_15_16 hp hy hst (by rw [nums_of_ne hne]; exact hft) (hS _ _ _ _ hy) (htr _ _ _ _ hy h15) h15

/-- **How many trees stand behind the test**: the plan's stages and one. -/
theorem trees_fact (hf : (descriptionFromSource X N P).fileOk = true)
    (hp : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk = true)
    (hone : OneTree X.Y.k.oneTime.codes) :
    ∀ s rs gs s', (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).decide s rs gs = .ok s' →
      shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 15 s = true →
      s'.d.book.trees.size = X.Y.k.oneTime.ranges.stages.length + 1 := by
  intro s rs gs s' h h15
  obtain ⟨_, _, hC, _, _, hRd, _, _, _, _, hT, _, _⟩ := front15 h15
  obtain ⟨_, he, ha, _, _⟩ := Johnson.RunOne.Law.RngAsked.planOk_ok (Johnson.RunOne.Law.RngAnyCl.plan_unit hp)
  obtain ⟨_, _, _, _, _, _, _, hne⟩ := out_of_yes hp h
  obtain ⟨tE, _, _, _, hd, _, e⟩ := Johnson.RunOne.Law.RngAtKeyD.keyD_yes h
  have hd' : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (Johnson.RunOne.Law.RngAtKeyD.recD s) rs gs = .ok tE := by
    rw [(Johnson.RunOne.Law.RngAnyCl.same_k12 (A := Unit) (B := Key.Claim) guardedProximityTestParts (rangesParams N)).decide]
    exact hd
  have hone' : OneTree (Johnson.RunOne.Law.RngAtKeyD.recD s).st.codes := by
    show OneTree s.d.st.codes
    rw [hC]
    exact hone
  have k := k12_trees (rangesParams N) he ha _ tE rs gs hd' hone' 2 hRd
  have k' : tE.book.trees.size = s.d.book.trees.size + ((rangesParams N).nums.stages.length - 1) := k
  have hst : (rangesParams N).nums.stages.length = X.Y.k.oneTime.ranges.stages.length := by
    rw [nums_of_ne hne]
    exact stages_of_fileOk X N P hf
  have hpos : 1 ≤ (rangesParams N).nums.stages.length := Nat.pos_of_ne_zero fun h0 => hne (List.length_eq_zero_iff.1 h0)
  have e' : s'.d.book.trees.size = tE.book.trees.size := by rw [e]
  omega

/-- **The fact (shape), with the trees' count paid.** -/
theorem shape_fact' (hf : (descriptionFromSource X N P).fileOk = true) (hl : (lookupsOf X.Y.k.oneTime).length = 2) (hft : N.nums.firstTree = 0)
    (hp : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk = true)
    (hS : ∀ s rs gs s', (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).decide s rs gs = .ok s' → SmpStay s.d.st s'.d.st)
    (hone : OneTree X.Y.k.oneTime.codes)
    (a b : Xi × FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b) :
    shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true →
      shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 16 b.2 = true :=
  shape_fact X N P hf hl hft hp hS (trees_fact X N P hf hp hone) a b rs gs hd

variable {Cells M Smp Rec : Type} (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (coll : Strs → Rec → Prop)

/-- **The fact (free)**: fwd_of_facts' hdec's fourth conjunct UNDER THE BOOK-KEEPING IN FRONT (h15): ONE PREMISE MORE THAN THAT CONJUNCT HAS: the order's law wants the codes' lengths in order at the STATE's codes; that these are the plan's is said by the ties in shape₁ 15, not by free₁ 15. In the promise onAt the two stand side by side: so the caller's rule must hand the first to the second. -/
theorem free_fact (hf : (descriptionFromSource X N P).fileOk = true) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hp : (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim).planOk = true)
    (hrec : ∀ a rs gs b, (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b → B.h₁.recOf b = B.h₁.recOf a)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r)
    (a b : Xi × FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hd : (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b)
    (h15 : shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true) :
    ∀ y y', StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) y y' → free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 15 a y →
      free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 16 b y' := by
  have hn : n₁ (oneAt X) = 2 := hl
  rw [hn] at h15
  have hc : a.2.d.st.codes = X.Y.k.oneTime.codes := (front15 h15).2.2.1
  exact free_15_16 X N P B at_ R coll hl hp a b rs gs hd (hrec a rs gs b hd) hcoll
    (ranges_inOrder _ N a.2 b.2 rs gs (held_decide _ a rs gs b hd).2 (by rw [hc]; exact lengths_of_fileOk X N P hf))

end Johnson.RunOne.Law.K12Join15

#print axioms Johnson.RunOne.Law.K12Join15.nums_of_ne
#print axioms Johnson.RunOne.Law.K12Join15.stages_of_fileOk
#print axioms Johnson.RunOne.Law.K12Join15.lengths_of_fileOk
#print axioms Johnson.RunOne.Law.K12Join15.shape_fact
#print axioms Johnson.RunOne.Law.K12Join15.free_fact
#print axioms Johnson.RunOne.Law.K12Join15.trees_fact
#print axioms Johnson.RunOne.Law.K12Join15.shape_fact'
