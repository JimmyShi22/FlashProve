-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/CutLaw.lean: FROM "THE SEGMENT's LIST IS: WRITTEN CLAIMS · THE LIST
"K8.equations" · WRITTEN CLAIMS" TO THE LAW `KeysSame` AND TO A BOOL ON WRITTEN LISTS. Statements and proofs ON THE
VERIFIER's TEXT; no prover is in this file, and no goal is stated.

The protocol's order of a segment's claims has three stretches (`orderCuts`, Johnson/Desc/First/Driver/Chain.lean); the
smallness test's list ends the second. WHERE the claims in front of that list and behind it, and the list's first
four, can be written off the state IN FRONT of the batching draw (shown elsewhere at a feed-forward segment;
here a premise), the rest follows: the list's ties and reads hang on chi, but name no slot
(`K9H.k8_noSlot`, Johnson/Desc/K9/Honest/K8NoSlot.lean).
  `Cut p g s FR FOUR N BK M`   THE PREMISE: wherever draw and gatherer return: the list is FR ++ k8 ++ BK, where k8 is
                    the answer of "K8.equations" at some data, its first four claims are FOUR and its length is N;
                    and the merge's slot is M. FR, FOUR, N, BK, M STAND OUTSIDE THE CHALLENGE
  `cutKeys`         the keys of such a list, written out: those of FR, of FOUR, N - 4 times the key of a claim
                    without a slot, those of BK
  `keys_of_cut`     the list's keys are these
  `keysSame_of_cut` **so `KeysSame`** (Honest/K9/LedgerOf.lean)
  `blank`, `cutList`   a written list with the same keys: N - 4 claims without form in place of the ties and reads
  `slotsLive_of_cut`   **the Bool `goodAt`'s first half, `slotsLive`, at what `gathered` yields, IS `slotsLive` at the
                    written list**: a Bool on data in front of the draw
  `k8Len tl funs`   the length of the list "K8.equations" at its data: 4, the ties, the reads
  `goodCut`         **THE BOOL "GOOD", ON WRITTEN LISTS**: `slotsLive` at the written list, and that list's length
                    within the plan's number of claims
  `goodS_of_cut`    the cut, no claim counted and the plan's number P behind every gathering, the Bool true, and
                    draw and gatherer return somewhere ⟹ "s is good" (`goodS`, Honest/K9/QuietMore.lean)
  `free_few_cut`, `free_few_cut_canon`   **THE COUNT OUT OF THE CUT**, in readings and on machine words; where draw and
                    gatherer never return, nothing is counted

WHAT IS NOT CLAIMED. That `Cut` holds at any segment: it is what a walk through the segment's runs yields. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.LedgerOf
import Johnson.Desc.ProofFile.Honest.K9.QuietMore
import Johnson.Desc.K9.Honest.K8NoSlot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.K9 (Where mergeOf atS batch)
open OnBytes.Tie.Pv.Tail.Port (readsList)
open VerifiableInference.Desc.K9H (slotsLive k8_drop NoSlot)

/-- **The premise**: the list's cut, wherever draw and gatherer return. -/
def Cut (p : Where) (g : S → Except String (List Claim × S)) (s : S) (FR FOUR : List Claim) (N : Nat)
    (BK : List Claim) (M : Option Nat) : Prop :=
  ∀ x y, gathered p g s x = some y →
    ∃ (k8 : List Claim) (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F' : Fork),
      y.2.2 = FR ++ k8 ++ BK ∧ equations front tl funs F = .ok (tl', F', k8) ∧
      k8.take 4 = FOUR ∧ k8.length = N ∧ mergeOf y.1 = M

/-- The keys of such a list. -/
def cutKeys (FR FOUR : List Claim) (N : Nat) (BK : List Claim) : List (Option Nat × List (Nat × E)) :=
  FR.map slotKey ++ (FOUR.map slotKey ++ List.replicate (N - 4) (none, [])) ++ BK.map slotKey

theorem keys_noSlot : ∀ (l : List Claim), (∀ c ∈ l, NoSlot c) →
    l.map slotKey = List.replicate l.length (none, [])
  | [], _ => rfl
  | c :: l, h => by
    have hc : c.form.slots.toList = [] := by
      have := h c List.mem_cons_self
      unfold NoSlot at this
      rw [this]
    rw [List.map_cons, slotKey_empty c hc, keys_noSlot l fun d hd => h d (List.mem_cons_of_mem _ hd),
      List.length_cons, List.replicate_succ]

/-- The list's keys, written out. -/
theorem keys_of_cut (FR FOUR k8 BK : List Claim) (N front : Nat) (tl tl' : HTailF2) (funs : Array HFun)
    (F F' : Fork) (he : equations front tl funs F = .ok (tl', F', k8)) (h4 : k8.take 4 = FOUR)
    (hN : k8.length = N) : (FR ++ k8 ++ BK).map slotKey = cutKeys FR FOUR N BK := by
  have hk : k8 = FOUR ++ k8.drop 4 := by rw [← h4, List.take_append_drop]
  have hd : (k8.drop 4).map slotKey = List.replicate (N - 4) (none, []) := by
    rw [keys_noSlot _ (k8_drop he), List.length_drop, hN]
  unfold cutKeys
  rw [List.map_append, List.map_append]
  congr 2
  calc k8.map slotKey = (FOUR ++ k8.drop 4).map slotKey := congrArg (List.map slotKey) hk
    _ = FOUR.map slotKey ++ List.replicate (N - 4) (none, []) := by rw [List.map_append, hd]

/-- **`KeysSame` out of the cut.** -/
theorem keysSame_of_cut (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (FR FOUR : List Claim) (N : Nat) (BK : List Claim) (M : Option Nat)
    (h : Cut p g s FR FOUR N BK M) : KeysSame p g s := by
  intro x x' y y' hy hy'
  obtain ⟨k8, fr, tl, tl', funs, F, F', e, he, h4, hN, hM⟩ := h x y hy
  obtain ⟨k8', fr', tl2, tl2', funs', F2, F2', e', he', h4', hN', hM'⟩ := h x' y' hy'
  exact ⟨by rw [e, e', keys_of_cut FR FOUR k8 BK N fr tl tl' funs F F' he h4 hN,
    keys_of_cut FR FOUR k8' BK N fr' tl2 tl2' funs' F2 F2' he' h4' hN'], by rw [hM, hM']⟩

/-- A claim without form. -/
def blank : Claim := {}

/-- A written list with the same keys. -/
def cutList (FR FOUR : List Claim) (N : Nat) (BK : List Claim) : List Claim :=
  FR ++ (FOUR ++ List.replicate (N - 4) blank) ++ BK

theorem cutList_keys (FR FOUR : List Claim) (N : Nat) (BK : List Claim) :
    (cutList FR FOUR N BK).map slotKey = cutKeys FR FOUR N BK := by
  unfold cutList cutKeys
  rw [List.map_append, List.map_append, List.map_append, List.map_replicate]
  rfl

/-- **`slotsLive` at what `gathered` yields is `slotsLive` at the written list.** -/
theorem slotsLive_of_cut (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (FR FOUR : List Claim) (N : Nat) (BK : List Claim) (M : Option Nat)
    (h : Cut p g s FR FOUR N BK M) (n : Nat) (x : E)
    (y : S × VerifiableInference.Desc.K9.Part × List Claim) (hy : gathered p g s x = some y) :
    slotsLive n (mergeOf y.1) y.2.2 = slotsLive n M (cutList FR FOUR N BK) := by
  obtain ⟨k8, fr, tl, tl', funs, F, F', e, he, h4, hN, hM⟩ := h x y hy
  rw [hM]
  apply slotsLive_congr
  rw [e, keys_of_cut FR FOUR k8 BK N fr tl tl' funs F F' he h4 hN, cutList_keys]

/-- The length of the list "K8.equations" at its data. -/
def k8Len (tl : HTailF2) (funs : Array HFun) : Nat := 4 + (tl.NM + (readsList tl funs).length)

/-- **The Bool "good", on written lists.** n: the number of slots asked; M: the merge's slot; plan: the plan's
number of claims. -/
def goodCut (n : Nat) (M : Option Nat) (FR FOUR : List Claim) (N : Nat) (BK : List Claim) (plan : Nat) : Bool :=
  slotsLive n M (cutList FR FOUR N BK) && decide ((cutList FR FOUR N BK).length ≤ plan)

/-- The gathered list is as long as the written one. -/
theorem length_of_cut (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (FR FOUR : List Claim) (N : Nat) (BK : List Claim) (M : Option Nat)
    (h : Cut p g s FR FOUR N BK M) (x : E)
    (y : S × VerifiableInference.Desc.K9.Part × List Claim) (hy : gathered p g s x = some y) :
    y.2.2.length = (cutList FR FOUR N BK).length := by
  obtain ⟨k8, fr, tl, tl', funs, F, F', e, he, h4, hN, _⟩ := h x y hy
  have h1 := congrArg List.length (keys_of_cut FR FOUR k8 BK N fr tl tl' funs F F' he h4 hN)
  have h2 := congrArg List.length (cutList_keys FR FOUR N BK)
  rw [List.length_map] at h1 h2
  rw [e, h1, h2]

/-- **"s is good" out of the cut.** -/
theorem goodS_of_cut (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (FR FOUR : List Claim) (N : Nat) (BK : List Claim) (M : Option Nat)
    (h : Cut p g s FR FOUR N BK M) (n P : Nat)
    (facts : ∀ x y, gathered p g s x = some y → y.2.1.F.nClaim = 0 ∧ y.2.1.F.planClaimsF = P)
    (good : goodCut n M FR FOUR N BK P = true) (x₀ : E)
    (y₀ : S × VerifiableInference.Desc.K9.Part × List Claim) (h₀ : gathered p g s x₀ = some y₀) :
    goodS p g s n := by
  unfold goodCut at good
  rw [Bool.and_eq_true, decide_eq_true_eq] at good
  refine ⟨x₀, y₀, h₀, ?_⟩
  unfold goodAt
  rw [Bool.and_eq_true, decide_eq_true_eq, slotsLive_of_cut p g s FR FOUR N BK M h n x₀ y₀ h₀,
    (facts x₀ y₀ h₀).1, (facts x₀ y₀ h₀).2, length_of_cut p g s FR FOUR N BK M h x₀ y₀ h₀, Nat.zero_add]
  exact good

/-- **The count out of the cut**, in readings. -/
theorem free_few_cut {Cl : Type} (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (FR FOUR : List Claim) (N : Nat) (BK : List Claim) (M : Option Nat)
    (h : Cut p g s FR FOUR N BK M) (n P : Nat)
    (facts : ∀ x y, gathered p g s x = some y → y.2.1.F.nClaim = 0 ∧ y.2.1.F.planClaimsF = P)
    (good : goodCut n M FR FOUR N BK P = true)
    (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t → (batch atS p g).decide s rs [] = .ok t) :
    Prob.cnt (fun z : Cb.Gl.E => ∃ x : E, Reading.gl.val x = z ∧ FallsAt b' s n k4 x) ≤ n * (P - 1) := by
  by_cases hyes : ∃ x₀ y₀, gathered p g s x₀ = some y₀
  · obtain ⟨x₀, y₀, h₀⟩ := hyes
    exact quiet_few_good p g s laws n (goodS_of_cut p g s FR FOUR N BK M h n P facts good x₀ y₀ h₀) P
      (fun x y hy => (facts x y hy).2) k4 hk b' hb'
  · have hn : ∀ x, gathered p g s x = none := by
      intro x
      cases hq : gathered p g s x with
      | none => rfl
      | some y => exact absurd ⟨x, y, hq⟩ hyes
    rw [Prob.cnt_false fun z hz => by
      obtain ⟨x, _, hx⟩ := hz
      exact quiet_none p g s hn n k4 b' hb' x hx]
    exact Nat.zero_le _

/-- **The count out of the cut**, on machine words below the prime. -/
theorem free_few_cut_canon {Cl : Type} (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (FR FOUR : List Claim) (N : Nat) (BK : List Claim) (M : Option Nat)
    (h : Cut p g s FR FOUR N BK M) (n P : Nat)
    (facts : ∀ x y, gathered p g s x = some y → y.2.1.F.nClaim = 0 ∧ y.2.1.F.planClaimsF = P)
    (good : goodCut n M FR FOUR N BK P = true)
    (k4 : Option Nat) (hk : k4 = none ∨ k4 = some n) (b' : Block S Cl)
    (hb' : ∀ rs t, b'.decide s rs [] = .ok t → (batch atS p g).decide s rs [] = .ok t)
    (T : Finset E) (hT : ∀ x ∈ T, okE x = true) :
    Nat.card {x : E // x ∈ T ∧ FallsAt b' s n k4 x} ≤ n * (P - 1) := by
  refine le_trans ?_ (free_few_cut p g s laws FR FOUR N BK M h n P facts good k4 hk b' hb')
  apply Nat.card_le_card_of_injective
    (fun c : {x : E // x ∈ T ∧ FallsAt b' s n k4 x} =>
      (⟨Reading.gl.val c.1, c.1, rfl, c.2.2⟩ :
        {y : Cb.Gl.E // ∃ x : E, Reading.gl.val x = y ∧ FallsAt b' s n k4 x}))
  intro a b hab
  have h1 : Reading.gl.val a.1 = Reading.gl.val b.1 := congrArg Subtype.val hab
  exact Subtype.ext (VerifiableInference.Desc.K9L.gl_injOn (hT a.1 a.2.1) (hT b.1 b.2.1) h1)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.length_of_cut
#print axioms ProofFile.Honest.K9.goodS_of_cut
#print axioms ProofFile.Honest.K9.free_few_cut
#print axioms ProofFile.Honest.K9.free_few_cut_canon
#print axioms ProofFile.Honest.K9.keys_noSlot
#print axioms ProofFile.Honest.K9.keys_of_cut
#print axioms ProofFile.Honest.K9.keysSame_of_cut
#print axioms ProofFile.Honest.K9.cutList_keys
#print axioms ProofFile.Honest.K9.slotsLive_of_cut
#print axioms ProofFile.Honest.K9.Cut
#print axioms ProofFile.Honest.K9.cutKeys
#print axioms ProofFile.Honest.K9.blank
#print axioms ProofFile.Honest.K9.cutList
#print axioms ProofFile.Honest.K9.k8Len
#print axioms ProofFile.Honest.K9.goodCut
