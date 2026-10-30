-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/QuietMore.lean: THE COUNT AT THE QUIET SEAT (Honest/K9/Quiet.lean), IN THE FORMS IN
WHICH IT IS SPENT: "s is good" as a proposition on s · where the gatherer never answers · on machine words.
Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

  `goodS p g s n`      **"s is good"**: at SOME challenge the draw and the gatherer return, and the Bool `goodAt` is
                       true of what they yield. A PROPOSITION ON s, no Bool: under `RunsLaw.same` the Bool has one
                       value wherever they return (`goodAt_congr`), so whoever holds a run's own chi reads it there
  `goodS_iff`          under the laws, where they return at x: "s is good" is the Bool at x
  `FallsAt`            the set that is counted: the challenges x, as words, at which a member b' says yes from s and
                       the quiet seat's test speaks at the state behind
  `decide_of_step`, `falls_of_step`   FROM THE FRAME's WALK, which goes by `Block.step`, TO `FallsAt`, which speaks
                       of the block's decision: at a round that reads no column (a premise; for the
                       description's own seated block Honest/K9/AtStep.lean goes another road)
  `quiet_few_good`     **the laws, and s good ⟹ at most n * (P - 1) READINGS of such x**: P: the plan's number of
                       claims, wherever draw and gatherer return
  `quiet_none`         where draw and gatherer return at NO challenge, no challenge is counted: the batching
                       refuses at all of them (another share's matter)
  `quiet_few_words`    **ON MACHINE WORDS**: in any finite set of words on which the reading is one-to-one: at most
                       n * (P - 1) such words. `quiet_few_canon`: so in any finite set of elements whose words are
                       below the prime (`K9L.gl_injOn`, Johnson/Desc/First/Batch/Law/Count.lean)

WHAT IS NOT CLAIMED. That a drawn element's words are below the prime: the block's test on a round does not ask
it: a debt of whoever types the space of challenges. That s is good at any state of a run (the laws:
Honest/K9/AtSeatAll.lean). No probability. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.Quiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS Where batch)

/-- **"s is good."** -/
def goodS (p : Where) (g : S → Except String (List Claim × S)) (s : S) (n : Nat) : Prop :=
  ∃ x₀ y₀, gathered p g s x₀ = some y₀ ∧ goodAt n y₀ = true

/-- Under the laws, where draw and gatherer return at x: "s is good" is the Bool there. -/
theorem goodS_iff (p : Where) (g : S → Except String (List Claim × S)) (s : S) (laws : RunsLaw p g s)
    (n : Nat) (x : E) (y : S × VerifiableInference.Desc.K9.Part × List Claim)
    (hy : gathered p g s x = some y) : goodS p g s n ↔ goodAt n y = true :=
  ⟨fun ⟨x₀, y₀, h₀, hb⟩ => by rw [goodAt_congr p g s laws n x x₀ y y₀ hy h₀]; exact hb,
    fun hb => ⟨x, y, hy, hb⟩⟩

/-- The challenges, as words, at which b' says yes from s and the quiet seat's test speaks behind. -/
def FallsAt {Cl : Type} (b' : Block S Cl) (s : S) (n : Nat) (k4 : Option Nat) (x : E) : Prop :=
  ∃ s₁, b'.decide s [⟨[], drawnOne x⟩] [] = .ok s₁ ∧
    (quietFallTest n k4 (fun _ => none) s₁ []).isSome = true

/-- From the frame's walk to `decide`: a yes of `Block.step` at rounds that read no column is a yes of the block's
decision at these rounds without their sealed digests. -/
theorem decide_of_step {Cl : Type} (ft : Nat) (b' : Block S Cl) (s s₁ : S) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (k : Nat) (h : b'.step ft s rs cols = .ok (s₁, k))
    (hg : VerifiableInference.Desc.groupsOf ft b'.rounds (rs.map (·.drawn)) = []) :
    b'.decide s (rs.map VerifiableInference.Desc.noDigest) [] = .ok s₁ := by
  unfold VerifiableInference.Desc.Block.step at h
  obtain ⟨_, _, h⟩ := bind_ok h
  rw [hg] at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨s', hs', h⟩ := bind_ok h
  have e : s' = s₁ := congrArg (·.1) (Except.ok.inj h)
  rw [← e]
  exact hs'

/-- **FROM THE FRAME's WALK TO `FallsAt`**: the member's own step says yes at one round in which nothing is sent and
one element t is drawn (with or without a sealed digest), that round reads no column, and the quiet seat's test
speaks at the state behind: then the element is counted. -/
theorem falls_of_step {Cl : Type} (ft : Nat) (b' : Block S Cl) (s s₁ : S)
    (t : UInt64 × UInt64 × UInt64) (dg : Option ByteArray) (cols : List VerifiableInference.Desc.OpenedColumn) (k : Nat)
    (h : b'.step ft s [⟨[], ⟨[t], [], [], dg⟩⟩] cols = .ok (s₁, k))
    (hg : VerifiableInference.Desc.groupsOf ft b'.rounds [⟨[t], [], [], dg⟩] = [])
    (n : Nat) (k4 : Option Nat) (hq : (quietFallTest n k4 (fun _ => none) s₁ []).isSome = true) :
    FallsAt b' s n k4 (E.ofTriple t) :=
  ⟨s₁, decide_of_step ft b' s s₁ [⟨[], ⟨[t], [], [], dg⟩⟩] cols k h hg, hq⟩

/-- **The count, at "s is good".** -/
theorem quiet_few_good {Cl : Type} (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : Nat) (hg : goodS p g s n) (P : Nat)
    (hP : ∀ x y, gathered p g s x = some y → y.2.1.F.planClaimsF = P)
    (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t → (batch atS p g).decide s rs [] = .ok t) :
    Prob.cnt (fun y : Cb.Gl.E => ∃ x : E, Reading.gl.val x = y ∧ FallsAt b' s n k4 x) ≤ n * (P - 1) := by
  obtain ⟨x₀, y₀, h₀, hb⟩ := hg
  have h := quiet_few_of p g s laws n x₀ y₀ h₀ hb k4 hk b' hb'
  rw [hP x₀ y₀ h₀] at h
  refine le_trans (Prob.cnt_mono fun y hy => ?_) h
  obtain ⟨x, e, s₁, hd, hq⟩ := hy
  exact ⟨x, s₁, e, hd, hq⟩

/-- Where draw and gatherer return at no challenge, nothing is counted. -/
theorem quiet_none {Cl : Type} (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (hn : ∀ x, gathered p g s x = none) (n : Nat) (k4 : Option Nat) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t → (batch atS p g).decide s rs [] = .ok t) (x : E) :
    ¬ FallsAt b' s n k4 x := by
  rintro ⟨s₁, hd, _⟩
  obtain ⟨e, a, cls, G, hy, _, _⟩ := batch_split p g s s₁ x (hb' _ _ hd)
  rw [hn x] at hy
  exact nomatch hy

/-- **The count on machine words.** -/
theorem quiet_few_words {Cl : Type} (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : Nat) (hg : goodS p g s n) (P : Nat)
    (hP : ∀ x y, gathered p g s x = some y → y.2.1.F.planClaimsF = P)
    (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t → (batch atS p g).decide s rs [] = .ok t)
    (T : Finset E) (hT : Set.InjOn Reading.gl.val (T : Set E)) :
    Nat.card {x : E // x ∈ T ∧ FallsAt b' s n k4 x} ≤ n * (P - 1) := by
  refine le_trans ?_ (quiet_few_good p g s laws n hg P hP k4 hk b' hb')
  apply Nat.card_le_card_of_injective
    (fun c : {x : E // x ∈ T ∧ FallsAt b' s n k4 x} =>
      (⟨Reading.gl.val c.1, c.1, rfl, c.2.2⟩ :
        {y : Cb.Gl.E // ∃ x : E, Reading.gl.val x = y ∧ FallsAt b' s n k4 x}))
  intro a b hab
  have h1 : Reading.gl.val a.1 = Reading.gl.val b.1 := congrArg Subtype.val hab
  exact Subtype.ext (hT a.2.1 b.2.1 h1)

/-- In any finite set of elements whose words are below the prime. -/
theorem quiet_few_canon {Cl : Type} (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : Nat) (hg : goodS p g s n) (P : Nat)
    (hP : ∀ x y, gathered p g s x = some y → y.2.1.F.planClaimsF = P)
    (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t → (batch atS p g).decide s rs [] = .ok t)
    (T : Finset E) (hT : ∀ x ∈ T, okE x = true) :
    Nat.card {x : E // x ∈ T ∧ FallsAt b' s n k4 x} ≤ n * (P - 1) :=
  quiet_few_words p g s laws n hg P hP k4 hk b' hb' T
    (VerifiableInference.Desc.K9L.gl_injOn.mono fun x hx => hT x hx)

namespace Toy

/-! ## Each of them called, at the second segment of Honest/K9/FallGoodOfToy.lean (claims that hang on chi; a
gatherer that refuses at chi = 3; a claim under a higher power; a merge) -/

theorem goodC : goodS pwC gatC sC 3 := by
  have hb := bool'
  cases hq : gathered pwC gatC sC oneE with
  | none => rw [hq] at hb; exact nomatch hb
  | some y => rw [hq] at hb; exact ⟨oneE, y, hq, Option.some.inj hb⟩

theorem planC (x : E) (y : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h : gathered pwC gatC sC x = some y) : y.2.1.F.planClaimsF = 3 := by
  rw [(yieldsC x y h).1]
  rfl

/-- `quiet_few_good`, called: at the batching with the guard on marks, with K4's share at K9's own number. -/
theorem fewC : Prob.cnt (fun y : Cb.Gl.E => ∃ x : E, Reading.gl.val x = y ∧
    FallsAt (guardMark (batch atS pwC gatC)) sC 3 (some 3) x) ≤ 3 * (3 - 1) :=
  quiet_few_good pwC gatC sC laws' 3 goodC 3 planC (some 3) (Or.inr rfl) _
    fun rs t h => guardMark_bare _ sC t rs [] h

/-- It bites: chi = 1 is counted. -/
theorem fallsC : FallsAt (guardMark (batch atS pwC gatC)) sC 3 (some 3) oneE := by
  have h : ((guardMark (batch atS pwC gatC)).decide sC [⟨[], drawnOne oneE⟩] []).toOption.map
      (fun s₁ => (quietFallTest 3 (some 3) (fun _ => none) s₁ []).isSome) = some true := by
    decide +kernel
  cases hq : (guardMark (batch atS pwC gatC)).decide sC [⟨[], drawnOne oneE⟩] [] with
  | error m => rw [hq] at h; exact nomatch h
  | ok s₁ => rw [hq] at h; exact ⟨s₁, hq, Option.some.inj h⟩

/-- `quiet_few_canon`, called: among the eight elements 0 … 7 of the base field at most six fall. (A call, to show
that the premises can be held together: six of eight shows no bite.) -/
theorem wordsC : Nat.card {x : E // x ∈ ((Finset.range 8).image fun i => e i.toUInt64) ∧
    FallsAt (guardMark (batch atS pwC gatC)) sC 3 (some 3) x} ≤ 3 * (3 - 1) :=
  quiet_few_canon pwC gatC sC laws' 3 goodC 3 planC (some 3) (Or.inr rfl) _
    (fun rs t h => guardMark_bare _ sC t rs [] h) _ (by decide +kernel)

/-- `falls_of_step`, called: the toy's own step at chi = 1, with a sealed digest in the round. -/
theorem stepC : FallsAt (guardMark (batch atS pwC gatC)) sC 3 (some 3) (E.ofTriple (1, 0, 0)) := by
  have h : ((guardMark (batch atS pwC gatC)).step 0 sC [⟨[], ⟨[(1, 0, 0)], [], [], some ⟨#[7]⟩⟩⟩] []).toOption.map
      (fun y => (quietFallTest 3 (some 3) (fun _ => none) y.1 []).isSome) = some true := by
    decide +kernel
  cases hq : (guardMark (batch atS pwC gatC)).step 0 sC [⟨[], ⟨[(1, 0, 0)], [], [], some ⟨#[7]⟩⟩⟩] [] with
  | error m => rw [hq] at h; exact nomatch h
  | ok y => rw [hq] at h; exact falls_of_step 0 _ sC y.1 (1, 0, 0) _ [] y.2 hq rfl 3 (some 3) (Option.some.inj h)

/-- `quiet_none`, called: a gatherer that always refuses. -/
theorem noneC (x : E) : ¬ FallsAt (batch atS pwC fun _ => .error "never") sC 3 none x :=
  quiet_none pwC _ sC (fun x => by
    unfold gathered
    rw [draw_C]) 3 none _ (fun _ _ h => h) x

end Toy

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.goodS_iff
#print axioms ProofFile.Honest.K9.decide_of_step
#print axioms ProofFile.Honest.K9.falls_of_step
#print axioms ProofFile.Honest.K9.Toy.stepC
#print axioms ProofFile.Honest.K9.quiet_few_good
#print axioms ProofFile.Honest.K9.quiet_none
#print axioms ProofFile.Honest.K9.quiet_few_words
#print axioms ProofFile.Honest.K9.quiet_few_canon
#print axioms ProofFile.Honest.K9.Toy.goodC
#print axioms ProofFile.Honest.K9.Toy.fewC
#print axioms ProofFile.Honest.K9.Toy.fallsC
#print axioms ProofFile.Honest.K9.Toy.wordsC
#print axioms ProofFile.Honest.K9.Toy.noneC
#print axioms ProofFile.Honest.K9.goodS
#print axioms ProofFile.Honest.K9.FallsAt
#print axioms ProofFile.Honest.K9.Toy.planC
