-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/StepSide15.lean: THE STATE's SIDE OF THE FIRST CHAIN's PROMISE ACROSS THE RANGES' PROXIMITY TEST: at border 15 in front gives at border 16 behind, at the block's yes: ON THE STATE ALONE: no strings, no witness, no reading. Statements with proofs; each proof is a joining of calls.
OBJECT. The tables' files' "state's side" ASide one at_ k s (THE TEXT OF ASide IN Johnson/RunOne/KeyASide.lean, the form in which the step is wanted; typed out here because that file is not beneath this one): the book-keeping shape₁ at k · the book places the pinned messages where at_ says · the statement is in order · from border 2 to 15: message 2 lies in message 1's tree, the next part. And the block Key.rangesTest (Key.enterRanges one) Key.leaveRanges N, bare or not (baring turns the test on the plan alone).
USER. The tables' files' fold of "the state's side at k gives it at k + 1, at the k-th block's yes" along the first chain's history: its step at k = 15.
LETTERS. one N at_: free. PUBLIC PREMISES: hp: the block's own test on the plan · hst: the place's number of stages is the plan's · hft: the place's first tree's number is 0 · hlen: the plan's codes' lengths are in order. (Off (descriptionFromSource X N P).planOk: hp · hst · hlen: Johnson/RunOne/Law/K12Facts15.lean | K12Join15.lean; hft: the maker's literal.) roundsFit is not spent.
  ASide · step_15: the step, written out in the asked form. book_15: the lighter one: the yes keeps BookStep 0 s.d.book s.d.roots.
Limits. A block that says no to all meets every statement. AT THE TABLES' TEXT THAT HOLDS «THE BOOK IS IN ORDER» (moreB's last conjunct, Johnson/RunOne/KeyReaders1.lean). Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Shape15
import Johnson.RunOne.Law.K12Free15
import Johnson.RunOne.Law.K12Order
import Johnson.RunOne.Law.K12Keeps
import Johnson.RunOne.Law.K12Trees
import Johnson.RunOne.Law.K12OneTree
import Johnson.RunOne.Law.K12Join15

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.StepSide15
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (FirstState Claim enterRanges leaveRanges)
open VerifiableInference.Desc.K1 (SmpStay groundKeeps_smpStay beginRun_smpStay)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Sound (BookStep bookStepB bookStep_iff)
open Johnson.RunOne.KeyRows1 (open₁ plan₁ readers₁ book₁ slots₁)
open Johnson.RunOne.Law.K12Shape15 (out_of_yes front15 shape_15_16 book_of_yes)
open Johnson.RunOne.Law.K12Free15 (pins_sub)
open Johnson.RunOne.Law.K12Order (ranges_inOrder)
open Johnson.RunOne.Law.K12Keeps (ranges_keeps)
open Johnson.RunOne.Law.K12Trees (k12_trees)
open Johnson.RunOne.Law.K12OneTree (oneTree_all)
open Johnson.RunOne.Law.K12Join15 (nums_of_ne)

/-- **The state's side of the first chain's promise at border k**: KeyASide.lean's text. -/
def ASide (one : OneTime) (at_ : Where) (k : Nat) (s : FirstState) : Prop :=
  shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) k s = true ∧
    Placed (plan₁ one).orc (fun o => s.d.book.place[o]?) id at_ (pinned (open₁ 2 k)) ∧ Means.InOrder s.d.st ∧
    (2 ≤ k ∧ k ≤ 15 → MaskWith (fun o => s.d.book.place[o]?) 1 2)

variable (one : OneTime) (N : H2U.PlaceNums) (at_ : Where)

/-- How many trees stand behind the test, on the state alone. -/
theorem trees_15 (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true)
    (hst : N.nums.stages.length = one.ranges.stages.length) (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s')
    (h15 : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 15 s = true) :
    s'.d.book.trees.size = one.ranges.stages.length + 1 := by
  obtain ⟨_, _, _, _, _, hRd, _, _, _, _, hT, _, _⟩ := front15 h15
  obtain ⟨_, he, ha, _, _⟩ := Johnson.RunOne.Law.RngAsked.planOk_ok (Johnson.RunOne.Law.RngAnyCl.plan_unit hp)
  obtain ⟨_, _, _, _, _, _, _, hne⟩ := out_of_yes hp h
  obtain ⟨tE, _, _, _, hd, _, e⟩ := Johnson.RunOne.Law.RngAtKeyD.keyD_yes h
  have hd' : (proximityTestKind guardedProximityTestParts (rangesParams N) : Block T12 Unit).decide (Johnson.RunOne.Law.RngAtKeyD.recD s) rs gs = .ok tE := by
    rw [(Johnson.RunOne.Law.RngAnyCl.same_k12 (A := Unit) (B := Claim) guardedProximityTestParts (rangesParams N)).decide]
    exact hd
  have k : tE.book.trees.size = s.d.book.trees.size + ((rangesParams N).nums.stages.length - 1) :=
    k12_trees (rangesParams N) he ha _ tE rs gs hd' (fun nx last lay h => oneTree_all _ nx last lay h) 2 hRd
  have hst' : (rangesParams N).nums.stages.length = one.ranges.stages.length := by
    rw [nums_of_ne hne]
    exact hst
  have hpos : 1 ≤ (rangesParams N).nums.stages.length := Nat.pos_of_ne_zero fun h0 => hne (List.length_eq_zero_iff.1 h0)
  have e' : s'.d.book.trees.size = tE.book.trees.size := by rw [e]
  omega

/-- **The step at k = 15.** b: any block that decides as the ranges' test (the bare one does, by rfl). -/
theorem step_15 (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true)
    (hst : N.nums.stages.length = one.ranges.stages.length) (hft : N.nums.firstTree = 0) (hlen : one.codes.lengthsOk = true)
    (b : Block FirstState Claim) (hb : b.decide = (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide) :
    ∀ (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), roundsFit b.rounds rs = true →
      b.decide s (rs.map noDigest) gs = .ok s' → ASide one at_ 15 s → ASide one at_ 16 s' := by
  intro s s' rs gs _ h ⟨h15, hpl, hI, _⟩
  rw [hb] at h
  obtain ⟨_, _, hC, _, _, _, _, _, _, _, _, _, _⟩ := front15 h15
  obtain ⟨tE, G, e, _, k1, _, _, hne⟩ := out_of_yes hp h
  have eb : s'.d.book = tE.book := by rw [e]
  refine ⟨?_, ?_, ?_, fun h => absurd h.2 (by omega)⟩
  · exact shape_15_16 hp h (by rw [nums_of_ne hne]; exact hst) (by rw [nums_of_ne hne]; exact hft)
      (ranges_keeps groundKeeps_smpStay (fun d d' g run hb => beginRun_smpStay d d' g run hb) one N s s' _ gs h)
      (trees_15 one N hp hst s s' _ gs h h15) h15
  · intro k hk
    obtain ⟨o, t, h1, h2, h3⟩ := hpl k (pins_sub k hk)
    refine ⟨o, t, h1, ?_, h3⟩
    show s'.d.book.place[o]? = some t
    rw [eb]
    exact k1.book.place o t h2
  · exact ranges_inOrder one N s s' _ gs h (by rw [hC]; exact hlen) hI

/-- **The lighter one**: the yes keeps "the book is in order". -/
theorem book_15 (hp : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).planOk = true) (hft : N.nums.firstTree = 0)
    (s s' : FirstState) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).decide s rs gs = .ok s')
    (hB : BookStep 0 s.d.book s.d.roots) : BookStep 0 s'.d.book s'.d.roots := by
  obtain ⟨_, _, _, _, _, _, _, hne⟩ := out_of_yes hp h
  exact (bookStep_iff 0 _ _).1 (book_of_yes hp h (by rw [nums_of_ne hne]; exact hft) ((bookStep_iff 0 _ _).2 hB))

end Johnson.RunOne.Law.StepSide15

#print axioms Johnson.RunOne.Law.StepSide15.trees_15
#print axioms Johnson.RunOne.Law.StepSide15.step_15
#print axioms Johnson.RunOne.Law.StepSide15.book_15
