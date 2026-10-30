-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallGoodOf.lean: FROM A BOOL WITH CODE, AND TWO LAWS ON THE RUNS OF
CLAIMS, TO THE PREMISES OF `batFall_few` (Honest/K9/FallFew.lean). Definitions with code, statements
and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

  `slotKey cl`       what of a claim the slots' coefficients hang on: its form's pairs (slot, coefficient), and,
                     IF IT HAS SUCH A PAIR, under which power it is added (eqFirst). A claim that names no slot
                     has the key (none, []), whatever its power: so of K8's ties and reads, which name none
                     (`K9H.k8_noSlot`, Johnson/Desc/K9/Honest/K8NoSlot.lean), `same` asks their NUMBER alone
  `slotPoly_congr`   two lists of claims with the same keys have the same polynomial at every slot
  `RunsLaw p g s`    THE TWO LAWS, premises here:
      ledger   where the draw and the gatherer return at x, the ledger in front of the adding holds x,
               has one coefficient for each slot, and every coefficient is the word 0
      same     at any two challenges at which they return: the claims' keys, the plan's number of
               claims, the number of claims added so far and the merge's slot are the same: ON THE
               SLOTS NOTHING HANGS ON chi (a claim's constant, entries and runs may)
  `goodAt n y`       **THE BOOL**, of what `gathered` yields at one challenge: `K9H.slotsLive`
                     (Johnson/Desc/K9/Honest/SlotsLive.lean) at its claims and merge's slot, and the
                     claims' numbers stay below the plan's number
  `goodAt_congr`     under `same` the Bool has one value at all challenges at which `gathered` answers:
                     so it may be read at the run's own chi. IT IS A BOOL OF WHAT `gathered` YIELDS AT
                     SOME CHALLENGE, NOT OF THE STATE s: "s is good", as a spender has it, is: there
                     are x₀, y₀ with gathered p g s x₀ = some y₀ and goodAt n y₀: a proposition. Where
                     `gathered` answers at no challenge nothing is said here: every chi is then the
                     share's in front
  `fallGood_of`      **the two laws, and the Bool true at one such challenge, give `FallGood`**, at
                     d := the plan's number of claims - 1
  `batFall_few_bool` so at most n * d elements of the field are readings of a chi at which K9's share
                     of the fall's test speaks
  `behindBat_fit`    a challenge in which one element and nothing else is drawn, with or without a
                     sealed digest, is `drawnOne` of that element to `behindBat`
  `batFallTest_cases`  where the whole test speaks, the share in front speaks, or K9's, or the share
                     behind the adding

WHAT IS COUNTED, AND WHAT NOT. READINGS IN THE FIELD, NOT WORDS: several triples of words can have one
reading; whoever counts challenges as they are drawn needs that a drawn element's words are below the
prime, where the reading is one-to-one. IT IS NOT THE COUNT OF THE ROUND "BAT-sigma": at some chi the
gatherer itself refuses (another kind's test on values inside its run of claims): there `gathered`
answers nothing and nothing is counted here: that is the share in front.
WHAT IS NOT CLAIMED HERE. That `RunsLaw` holds at any state (at the description's own segments:
Honest/K9/AtSeatAll.lean). That the Bool is true at any state: it hangs on what the claims' makers
lay into a slot's coefficient (Johnson/Desc/K9/Honest/SlotsFew.lean's head names what the verifier's
text says of that). No probability. Nothing on any property.
AT K9's BARE BATCHING (`K9.batch atS p g`): for the member as the description's makers wrap it:
Honest/K9/Quiet.lean, `quiet_few_of`.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallFew
import Johnson.Desc.K9.Honest.SlotsLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS Where mergeOf batch)
open VerifiableInference.Desc.K9L (expo)
open VerifiableInference.Desc.K9H (SlotsGood slotPoly slotCoef slotsLive liveAt plainAt unnamedAt
  unnamedIn live_of_bool unnamed_of_bool)

/-- What of a claim the slots' coefficients hang on: its form's pairs (slot, coefficient), and, IF IT HAS SUCH A
PAIR, under which power it is added. -/
def slotKey (cl : Claim) : Option Nat × List (Nat × E) :=
  (if cl.form.slots.toList.isEmpty then none else cl.eqFirst, cl.form.slots.toList)

/-- A claim without a pair: its key. -/
theorem slotKey_empty (cl : Claim) (h : cl.form.slots.toList = []) : slotKey cl = (none, []) := by
  unfold slotKey
  rw [h]
  rfl

/-- A claim with a pair: its key. -/
theorem slotKey_some (cl : Claim) (h : cl.form.slots.toList ≠ []) :
    slotKey cl = (cl.eqFirst, cl.form.slots.toList) := by
  unfold slotKey
  have : cl.form.slots.toList.isEmpty = false := by simpa using h
  rw [this]
  rfl

theorem slotPoly_congr {K : Type} [CommRing K] (ρ : Reading K) (n j : Nat) :
    ∀ (l l' : List Claim) (c : Nat), l.map slotKey = l'.map slotKey →
      slotPoly ρ n c l j = slotPoly ρ n c l' j
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h
  | a :: l, b :: l', c, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    have h2 : a.form.slots.toList = b.form.slots.toList := congrArg (·.2) h.1
    have e2 : slotCoef ρ a j = slotCoef ρ b j := by unfold slotCoef; rw [h2]
    show Polynomial.monomial (expo n c a) (slotCoef ρ a j) + slotPoly ρ n (c + 1) l j =
      Polynomial.monomial (expo n c b) (slotCoef ρ b j) + slotPoly ρ n (c + 1) l' j
    rw [slotPoly_congr ρ n j l l' (c + 1) h.2]
    by_cases he : a.form.slots.toList = []
    · have z : slotCoef ρ a j = 0 := by unfold slotCoef; rw [he]; rfl
      rw [← e2, z, map_zero, map_zero]
    · have h1 : a.eqFirst = b.eqFirst := by
        have h3 := h.1
        rw [slotKey_some a he, slotKey_some b (h2 ▸ he)] at h3
        exact congrArg (·.1) h3
      have e1 : expo n c a = expo n c b := by unfold expo; rw [h1]
      rw [e1, e2]

/-- **The two laws on the runs of claims.** -/
structure RunsLaw (p : Where) (g : S → Except String (List Claim × S)) (s : S) : Prop where
  ledger : ∀ x y, gathered p g s x = some y →
    y.2.1.F.theta = x ∧ y.2.1.F.LS.size = y.2.1.F.ns ∧ ∀ j, y.2.1.F.LS.getD j zeroE = zeroE
  same : ∀ x x' y y', gathered p g s x = some y → gathered p g s x' = some y' →
    y.2.2.map slotKey = y'.2.2.map slotKey ∧ y.2.1.F.planClaimsF = y'.2.1.F.planClaimsF ∧
      y.2.1.F.nClaim = y'.2.1.F.nClaim ∧ mergeOf y.1 = mergeOf y'.1

/-- **The Bool**, of what `gathered` yields at one challenge. -/
def goodAt (n : Nat) (y : S × VerifiableInference.Desc.K9.Part × List Claim) : Bool :=
  slotsLive n (mergeOf y.1) y.2.2 && decide (y.2.1.F.nClaim + y.2.2.length ≤ y.2.1.F.planClaimsF)

/-- The three Bools read a claim through its key alone. -/
theorem liveAt_key (l : List Claim) (j : Nat) : liveAt l j = (l.map slotKey).any fun k =>
    k.1.isNone && VerifiableInference.Desc.K9H.notZero
      (k.2.foldl (fun a x => if x.1 == j then addE a x.2 else a) zeroE) := by
  unfold liveAt
  rw [List.any_map]
  congr 1
  funext cl
  by_cases he : cl.form.slots.toList = []
  · have z : VerifiableInference.Desc.K9H.slotWord cl j = zeroE := by
      unfold VerifiableInference.Desc.K9H.slotWord
      rw [he]
      rfl
    have nz : VerifiableInference.Desc.K9H.notZero zeroE = false := rfl
    simp only [Function.comp, slotKey_empty cl he, z, nz, Bool.and_false, List.foldl_nil]
  · simp only [Function.comp, slotKey_some cl he]
    rfl

theorem plainAt_key (l : List Claim) (j : Nat) : plainAt l j = (l.map slotKey).all fun k =>
    k.1.isNone || k.2.all fun x => x.1 != j := by
  unfold plainAt
  rw [List.all_map]
  congr 1
  funext cl
  by_cases he : cl.form.slots.toList = []
  · have u : unnamedIn cl j = true := by
      unfold unnamedIn
      rw [he]
      rfl
    simp only [Function.comp, slotKey_empty cl he, u, Bool.or_true, List.all_nil]
  · simp only [Function.comp, slotKey_some cl he]
    rfl

theorem unnamedAt_key (l : List Claim) (j : Nat) : unnamedAt l j = (l.map slotKey).all fun k =>
    k.2.all fun x => x.1 != j := by
  unfold unnamedAt
  rw [List.all_map]
  rfl

theorem slotsLive_congr (n : Nat) (merge : Option Nat) (l l' : List Claim)
    (h : l.map slotKey = l'.map slotKey) : slotsLive n merge l = slotsLive n merge l' := by
  unfold slotsLive
  simp only [liveAt_key, plainAt_key, unnamedAt_key, h]

/-- **Under `same` the Bool has one value wherever `gathered` answers.** -/
theorem goodAt_congr (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : Nat) (x x' : E)
    (y y' : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h : gathered p g s x = some y) (h' : gathered p g s x' = some y') :
    goodAt n y = goodAt n y' := by
  obtain ⟨k, e1, e2, e3⟩ := laws.same x x' y y' h h'
  have el : y.2.2.length = y'.2.2.length := by
    have := congrArg List.length k
    simpa using this
  unfold goodAt
  rw [slotsLive_congr n _ _ _ k, e1, e2, e3, el]

/-- **The two laws and the Bool give the premises of `batFall_few`.** -/
theorem fallGood_of (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : Nat) (x₀ : E)
    (y₀ : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h₀ : gathered p g s x₀ = some y₀) (hb : goodAt n y₀ = true) :
    FallGood p g s n (mergeOf y₀.1) (y₀.2.1.F.planClaimsF - 1)
      (fun j => slotPoly Reading.gl y₀.2.1.F.planClaimsF y₀.2.1.F.nClaim y₀.2.2 j) := by
  unfold goodAt at hb
  rw [Bool.and_eq_true, decide_eq_true_eq] at hb
  have hall := List.all_eq_true.1 hb.1
  -- what `gathered` yields at a challenge at which it answers
  have get : ∀ x, (gathered p g s x).isSome = true → ∃ y, gathered p g s x = some y := by
    intro x hx
    cases hq : gathered p g s x with
    | none => rw [hq] at hx; exact nomatch hx
    | some y => exact ⟨y, rfl⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := get x hx
    rw [hy]
    exact (laws.ledger x y hy).1
  · intro x hx
    obtain ⟨y, hy⟩ := get x hx
    rw [hy]
    exact (laws.ledger x y hy).2.1
  · intro x hx j
    obtain ⟨y, hy⟩ := get x hx
    rw [hy]
    exact (laws.ledger x y hy).2.2 j
  · intro x hx j _ _
    obtain ⟨y, hy⟩ := get x hx
    obtain ⟨k, e1, e2, _⟩ := laws.same x x₀ y y₀ hy h₀
    rw [hy]
    show slotPoly Reading.gl y.2.1.F.planClaimsF y.2.1.F.nClaim y.2.2 j = _
    rw [e1, e2, slotPoly_congr Reading.gl _ j _ _ _ k]
  · intro j hj hm
    have h1 := hall j (List.mem_range.2 hj)
    have hne : (mergeOf y₀.1 == some j) = false := by simpa using hm
    rw [hne] at h1
    simp only [Bool.false_eq_true, if_false, Bool.and_eq_true] at h1
    exact live_of_bool _ _ j _ hb.2 h1.1 h1.2
  · intro x hx j hj hm cl hcl z hz
    obtain ⟨y, hy⟩ := get x hx
    obtain ⟨k, _, _, _⟩ := laws.same x x₀ y y₀ hy h₀
    rw [hy] at hcl
    have hcl' : cl ∈ y.2.2 := hcl
    have h1 := hall j (List.mem_range.2 hj)
    have he : (mergeOf y₀.1 == some j) = true := by simpa using hm
    rw [he] at h1
    simp only [if_true] at h1
    rw [unnamedAt_key, ← k, ← unnamedAt_key] at h1
    exact unnamed_of_bool _ j h1 cl hcl' z hz
  · intro x y hy
    exact (laws.same x x₀ y y₀ hy h₀).2.2.2

/-- **From the Bool to the count.** -/
theorem batFall_few_bool (p : Where) (g : S → Except String (List Claim × S)) (s : S)
    (laws : RunsLaw p g s) (n : Nat) (x₀ : E)
    (y₀ : S × VerifiableInference.Desc.K9.Part × List Claim)
    (h₀ : gathered p g s x₀ = some y₀) (hb : goodAt n y₀ = true) :
    Prob.cnt (fun y : Cb.Gl.E => ∃ x : E, Reading.gl.val x = y ∧
      (batFallTest (batch atS p g) n (fun _ _ => none) (fun _ => none) s [drawnOne x]).isSome
        = true) ≤ n * (y₀.2.1.F.planClaimsF - 1) :=
  batFall_few p g s n _ _ _ (fallGood_of p g s laws n x₀ y₀ h₀ hb)

/-- A challenge in which one element and nothing else is drawn is `drawnOne` of it to `behindBat`. -/
theorem behindBat_fit {T Cl : Type} (b : Block T Cl) (s : T) (t : UInt64 × UInt64 × UInt64)
    (dg : Option ByteArray) :
    behindBat b s [⟨[t], [], [], dg⟩] = behindBat b s [drawnOne (E.ofTriple t)] := rfl

/-- Where the whole test speaks, one of the three shares speaks. -/
theorem batFallTest_cases {Cl : Type} (b : Block S Cl) (n : Nat)
    (front : S → List Fmt.Drawn → Option String) (other : S → Option String) (s : S)
    (ds : List Fmt.Drawn) (h : (batFallTest b n front other s ds).isSome = true) :
    (front s ds).isSome = true ∨
      (batFallTest b n (fun _ _ => none) (fun _ => none) s ds).isSome = true ∨
      ((behindBat b s ds).bind other).isSome = true := by
  unfold batFallTest at h ⊢
  cases hf : front s ds with
  | some _ => exact Or.inl rfl
  | none =>
    rw [hf] at h
    refine Or.inr ?_
    cases hb : behindBat b s ds with
    | none => rw [hb] at h; exact nomatch h
    | some s₁ =>
      rw [hb] at h
      cases hk : freeSlotShare n s₁ with
      | some _ => exact Or.inl (by show ((freeSlotShare n s₁).or none).isSome = true; rw [hk]; rfl)
      | none =>
        refine Or.inr ?_
        have h' : ((freeSlotShare n s₁).or (other s₁)).isSome = true := h
        rw [hk] at h'
        exact h'

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.slotPoly_congr
#print axioms ProofFile.Honest.K9.slotsLive_congr
#print axioms ProofFile.Honest.K9.goodAt_congr
#print axioms ProofFile.Honest.K9.fallGood_of
#print axioms ProofFile.Honest.K9.batFall_few_bool
#print axioms ProofFile.Honest.K9.behindBat_fit
#print axioms ProofFile.Honest.K9.batFallTest_cases
#print axioms ProofFile.Honest.K9.slotKey
#print axioms ProofFile.Honest.K9.slotKey_empty
#print axioms ProofFile.Honest.K9.slotKey_some
#print axioms ProofFile.Honest.K9.RunsLaw
#print axioms ProofFile.Honest.K9.goodAt
#print axioms ProofFile.Honest.K9.liveAt_key
#print axioms ProofFile.Honest.K9.plainAt_key
#print axioms ProofFile.Honest.K9.unnamedAt_key
