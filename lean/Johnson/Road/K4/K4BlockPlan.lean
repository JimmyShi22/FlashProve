-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4BlockPlan.lean: K4's sub-protocol passes its own test on the plan and is shaped.

Words. The code's `Block` is a sub-protocol at one place; `FileDescription` is the written-out protocol of
one file: three chains of sub-protocols. K4: the feed-forward layers' own rounds.

What it is for. A `FileDescription` passes the tests on the plan (`FileDescription.planOk`,
Johnson/Desc/Block.lean) only if every `Block` of its three chains passes its own test on the plan
and is shaped (`blocksOk`). This file says when that holds of K4's, as the proof file's `FileDescription`
seats them (`ProofFile.k4Block`, Johnson/Desc/ProofFile/Lot/K4.lean).

What it says.
  `k4Block_shaped`   every `Block` of the lot is shaped: it sends no root and names no oracle
                     message. No premise.
  `k4Block_planOk`   its test on the plan is `covers x.2.P && x.1`, by unfolding.
  `k4Block_refused`  where x.1 is false that test is false.
  `k4From_fst`       the Bool x.1 of every pair that `k4From` lays is true, if `sentB` is true at
                     the name of every layers' segment in the list and at the name handed in.
  `k4From_fst_of`    every pair that `k4From` lays stems from a segment X of kind 0 in the list, of
                     the pair's group, and x.1 = true gives `sentB` at X's name.
  `layers_named`     in the goals' scope a segment X of kind 0 has X.g < 12 and the name
                     "G" ++ toString X.g.
  `k4Block_ok`       in the goals' scope, where the public part and the blank ground are returned
                     and `k4SentB Z` is true: every `Block` of the lot passes its test, is shaped.
  `k4_blocks_ok`     the same of the `Block` that stands at link 2 g, third in front of the
                     batching, in the first chain of an opening (`IM.Open`).
  `k4SentB_iff`      at an opening in scope: `k4SentB Z` is true if and only if x.1 is true at every
                     pair of the lot: the test says what the twelve Bools say, no more, no less.
  `k4SentB_rejects`  so where it rejects, some `Block` of the lot fails its test on the plan.

The one test that is left. `k4SentB Z`: `sentB Z` at each of the twelve names "G0" … "G11".
`sentB Z name`, by `ProofFile.k4Sent`: the table of steps `Z.cuts` has a step «‹name›.0.call»; with k
the rounds in front of that step and n the rounds of all steps whose names begin «‹name›.0.», the n
declared rounds of `Z.D.1` from number k on send at least one root. (`k4Sent`'s own caution: these n
rounds are those steps' rounds only if the steps stand in a row that begins with «‹name›.0.call».)
It has code and reads `Z.cuts` and `Z.D.1` alone. IT IS THE x.1 HALF OF THE TEST ON THE PLAN,
CARRIED FROM THE LOT's PAIRS TO THE NAMES: A RESTATEMENT, NOT A PAYMENT. NO THEOREM HERE SHOWS IT
TRUE ANYWHERE.

Limits. `covers` in scope is the proved `refPub_in_scope` (Johnson/Road/K4/RefInScope.lean); the
seat is `IM.k4_of` (Johnson/IMR/K4Seat.lean). At the second hash function
`OnBytes.secondHashFunction` alone. Nothing on soundness.
-/
import Johnson.IMR.K4Seat
import Johnson.Road.K4.RefInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Desc.First.K4 (covers entries entryOf Par)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-! ### Shaped -/

/-- A test holds at every pair of a list of rounds made from entries alone, each beside the empty
list, if it holds at each such pair. -/
theorem all_zip_nil (q : Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle → Bool) :
    ∀ es : List Fmt.Entry, (∀ e ∈ es, q ({ entry := e }, []) = true) →
      (((es.map fun e => ({ entry := e } : Fmt.DeclaredRound)).zip
        (es.map fun _ => ([] : List VerifiableInference.Desc.Oracle))).all q) = true
  | [], _ => rfl
  | e :: es, h => by
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
    exact ⟨h e (List.Mem.head _), all_zip_nil q es fun a ha => h a (List.Mem.tail _ ha)⟩

/-- **A `Block` whose rounds are made from entries without roots, and which names no oracle message,
is shaped.** -/
theorem shaped_of_noRoots {T C : Type} (b : Block T C) (es : List Fmt.Entry)
    (hr : b.rounds = es.map fun e => { entry := e }) (ho : b.oracles = es.map fun _ => [])
    (h0 : ∀ e ∈ es, e.roots = 0) : b.shaped = true := by
  unfold VerifiableInference.Desc.Block.shaped
  rw [hr, ho, List.length_map, List.length_map, beq_self_eq_true, Bool.true_and]
  exact all_zip_nil _ es fun e he => by simp [h0 e he]

/-- Two `Block`s with the same rounds and the same oracle messages are shaped together. -/
theorem shaped_congr {T C T' C' : Type} {b : Block T C} {b' : Block T' C'}
    (hr : b.rounds = b'.rounds) (ho : b.oracles = b'.oracles) : b.shaped = b'.shaped := by
  unfold VerifiableInference.Desc.Block.shaped
  rw [hr, ho]

/-- No entry of K4's table sends a root. -/
theorem entries_noRoots (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) :
    ∀ e ∈ entries P hp g, e.roots = 0 := by
  intro e he
  unfold OnBytes.Desc.First.K4.entries at he
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
  rfl

/-- **Every `Block` of K4's lot is shaped.** No premise. -/
theorem k4Block_shaped (x : Bool × Par) : (ProofFile.k4Block x).shaped = true :=
  shaped_of_noRoots (ProofFile.k4Block x) (entries x.2.P x.2.hp x.2.g) rfl rfl
    (entries_noRoots x.2.P x.2.hp x.2.g)

/-! ### The test on the plan -/

/-- **The test on the plan of a `Block` of K4's lot**: K4's text covers the plan, and the pair's
Bool. -/
theorem k4Block_planOk (x : Bool × Par) : (ProofFile.k4Block x).planOk = (covers x.2.P && x.1) := rfl

/-- Where the pair's Bool is false the `Block`'s test on the plan is false. -/
theorem k4Block_refused (x : Bool × Par) (h : x.1 = false) : (ProofFile.k4Block x).planOk = false := by
  rw [k4Block_planOk, h, Bool.and_false]

/-- By the table of steps, the first place of the segment of that name sends an oracle message. -/
def sentB (Z : ProofFile.Pub) (name : String) : Bool := (ProofFile.k4Sent Z name).any fun m => !m.isEmpty

/-- `sentB` at the twelve layers' segments' names. -/
def k4SentB (Z : ProofFile.Pub) : Bool := (List.range 12).all fun g => sentB Z ("G" ++ toString g)

/-- **The Bool of every pair that `k4From` lays is true**, if `sentB` is true at the name of every
segment of kind 0 in the list and at the name handed in. -/
theorem k4From_fst (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ (L : List LinkH) (l : ℕ) (last : Option String),
      (∀ X ∈ L, X.kind = 0 → sentB Z X.name = true) →
      (∀ n, last = some n → sentB Z n = true) →
      ∀ x ∈ ProofFile.k4From Z G L l last, x.1 = true
  | [], _, _, _, _, x, h => by
    simp [ProofFile.k4From] at h
  | X :: rest, l, last, hL, hl, x, h => by
    unfold ProofFile.k4From at h
    split at h
    · rename_i hk
      have hk0 : X.kind = 0 := by simpa using hk
      have hX : sentB Z X.name = true := hL X (List.Mem.head _) hk0
      rcases List.mem_append.1 h with h1 | h2
      · split at h1
        · obtain rfl := List.mem_singleton.1 h1
          show (sentB Z X.name &&
            last.all fun _ => (last.elim (some []) (ProofFile.k4Sent Z)).any fun m => !m.isEmpty) = true
          rw [hX, Bool.true_and]
          cases last with
          | none => rfl
          | some n => exact hl n rfl
        · cases h1
      · exact k4From_fst Z G rest (l + 1) (some X.name) (fun Y hY => hL Y (List.Mem.tail _ hY))
          (fun n hn => by cases hn; exact hX) x h2
    · exact k4From_fst Z G rest (l + 1) last (fun Y hY => hL Y (List.Mem.tail _ hY)) hl x h

/-- **Every pair that `k4From` lays stems from a segment of kind 0 in the list**, of the pair's
group, and where the pair's Bool is true `sentB` is true at that segment's name. -/
theorem k4From_fst_of (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ (L : List LinkH) (l : ℕ) (last : Option String) (x : Bool × Par),
      x ∈ ProofFile.k4From Z G L l last →
      ∃ X ∈ L, X.kind = 0 ∧ x.2.g = X.g ∧ (x.1 = true → sentB Z X.name = true)
  | [], _, _, x, h => by
    simp [ProofFile.k4From] at h
  | X :: rest, l, last, x, h => by
    unfold ProofFile.k4From at h
    split at h
    · rename_i hk
      have hk0 : X.kind = 0 := by simpa using hk
      rcases List.mem_append.1 h with h1 | h2
      · split at h1
        · obtain rfl := List.mem_singleton.1 h1
          refine ⟨X, List.Mem.head _, hk0, rfl, fun ht => ?_⟩
          simp only [Bool.and_eq_true] at ht
          exact ht.1
        · cases h1
      · obtain ⟨Y, hY, a, b, c⟩ := k4From_fst_of Z G rest (l + 1) _ x h2
        exact ⟨Y, List.Mem.tail _ hY, a, b, c⟩
    · obtain ⟨Y, hY, a, b, c⟩ := k4From_fst_of Z G rest (l + 1) _ x h
      exact ⟨Y, List.Mem.tail _ hY, a, b, c⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- **In the goals' scope a segment X of kind 0 has X.g < 12 and the name "G" ++ toString X.g.** -/
theorem layers_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) :
    ∀ X ∈ G₀.built.toList, X.kind = 0 → X.g < 12 ∧ X.name = "G" ++ toString X.g := by
  intro X hX hk
  obtain ⟨j, e⟩ := List.mem_iff_getElem?.1 hX
  rw [Array.getElem?_toList] at e
  obtain ⟨sz, -⟩ := IM.ground_gets hS hR hZ hG
  obtain ⟨nam, l24, e24, k24, -⟩ := IM.ground_named hS hR hZ hG
  have hj : j < 25 := by
    rw [← sz]
    exact (Array.getElem?_eq_some_iff.1 e).1
  by_cases h24 : j = 24
  · subst h24
    obtain rfl : l24 = X := Option.some.inj (e24.symm.trans e)
    rw [hk] at k24
    cases k24
  · obtain ⟨l, l', a, ka, ga, Na, b, kb, gb, Nb⟩ := nam (j / 2) (by omega)
    by_cases he : j % 2 = 0
    · have ej : 2 * (j / 2) = j := by omega
      rw [ej] at a
      obtain rfl : l = X := Option.some.inj (a.symm.trans e)
      rw [ga]
      exact ⟨by omega, Na.name⟩
    · have ej : 2 * (j / 2) + 1 = j := by omega
      rw [ej] at b
      obtain rfl : l' = X := Option.some.inj (b.symm.trans e)
      rw [hk] at kb
      cases kb

/-- `k4SentB` gives `sentB` at each of the twelve names. -/
theorem sentB_of_all (hs : k4SentB Z = true) {g : ℕ} (hg : g < 12) :
    sentB Z ("G" ++ toString g) = true :=
  List.all_eq_true.1 hs g (List.mem_range.2 hg)

/-- **In the goals' scope the Bool of every pair of K4's lot is true, where `k4SentB Z` is.** -/
theorem k4Lot_fst (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (hs : k4SentB Z = true)
    {x : Bool × Par} (hx : x ∈ ProofFile.k4From Z G₀ G₀.built.toList 0 none) : x.1 = true :=
  k4From_fst Z G₀ G₀.built.toList 0 none
    (fun X hX hk => by
      obtain ⟨hg, e⟩ := layers_named hS hR hZ hG X hX hk
      rw [e]
      exact sentB_of_all hs hg)
    (fun n hn => nomatch hn) x hx

/-- **K4's SUB-PROTOCOL PASSES ITS OWN TEST ON THE PLAN AND IS SHAPED, IN THE GOALS' SCOPE**, where
the public part and the blank ground are returned and `k4SentB Z` is true: of every `Block` of the
lot. -/
theorem k4Block_ok (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (hs : k4SentB Z = true)
    {x : Bool × Par} (hx : x ∈ ProofFile.k4From Z G₀ G₀.built.toList 0 none) :
    ((ProofFile.k4Block x).planOk && (ProofFile.k4Block x).shaped) = true := by
  have hc : covers x.2.P = true := by
    rw [(IM.k4_seated hZ hG hx).1]
    exact (refPub_in_scope hS hR (IM.ground_publicK hZ hG) (g := 0) (by decide)).covers
  have h1 : x.1 = true := k4Lot_fst hS hR hZ hG hs hx
  simp only [k4Block_shaped, k4Block_planOk, hc, h1, Bool.and_self]

/-- **The same of the `Block` that stands in the first chain of an opening**, at link 2 g, third in
front of the batching, for each of the twelve groups. -/
theorem k4_blocks_ok {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : VerifiableInference.Desc.Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hs : k4SentB Z = true) :
    ∀ g < 12, ∃ (Lk : VerifiableInference.Desc.Link S Cl) (b : Block S Cl),
      c.links[2 * g]? = some Lk ∧ Lk.hear[2]? = some b ∧ b.place = IM.k4Place g ∧
      (b.planOk && b.shaped) = true := by
  intro g hg
  obtain ⟨Lk, b, x, e1, e2, hx, la, -⟩ := IM.k4_of hS hR O g hg
  refine ⟨Lk, b, e1, e2, IM.alone_place la, ?_⟩
  rw [IM.alone_planOk la, shaped_congr (IM.alone_rounds la) (IM.alone_oracles la)]
  exact k4Block_ok hS hR O.pub O.blank hs hx

/-- **`k4SentB Z` says what the lot's twelve Bools say, no more and no less**: at an opening, in the
goals' scope. -/
theorem k4SentB_iff {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : VerifiableInference.Desc.Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    k4SentB Z = true ↔ ∀ x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none, x.1 = true := by
  constructor
  · intro hs x hx
    exact k4Lot_fst hS hR O.pub O.blank hs hx
  · intro h
    refine List.all_eq_true.2 fun g hg => ?_
    obtain ⟨Lk, b, x, -, -, hx, -, -, eg, -⟩ := IM.k4_of hS hR O g (List.mem_range.1 hg)
    obtain ⟨X, hX, hk, e, hh⟩ := k4From_fst_of Z Bs.G₀ _ 0 none x hx
    obtain ⟨-, en⟩ := layers_named hS hR O.pub O.blank X hX hk
    have hs : sentB Z X.name = true := hh (h x hx)
    rw [en, ← e, eg] at hs
    exact hs

/-- **Where `k4SentB Z` rejects, some `Block` of the lot fails its own test on the plan**: at an
opening, in the goals' scope. -/
theorem k4SentB_rejects {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : VerifiableInference.Desc.Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h : k4SentB Z = false) :
    ∃ x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none, (ProofFile.k4Block x).planOk = false := by
  by_contra hn
  have hall : ∀ x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none, x.1 = true := fun x hx => by
    by_contra hx1
    exact hn ⟨x, hx, k4Block_refused x (eq_false_of_ne_true hx1)⟩
  rw [(k4SentB_iff hS hR O).2 hall] at h
  cases h

#print axioms OnBytes.Road.K4.all_zip_nil
#print axioms OnBytes.Road.K4.shaped_of_noRoots
#print axioms OnBytes.Road.K4.shaped_congr
#print axioms OnBytes.Road.K4.entries_noRoots
#print axioms OnBytes.Road.K4.k4Block_shaped
#print axioms OnBytes.Road.K4.k4Block_planOk
#print axioms OnBytes.Road.K4.k4Block_refused
#print axioms OnBytes.Road.K4.k4From_fst
#print axioms OnBytes.Road.K4.k4From_fst_of
#print axioms OnBytes.Road.K4.layers_named
#print axioms OnBytes.Road.K4.sentB_of_all
#print axioms OnBytes.Road.K4.k4Lot_fst
#print axioms OnBytes.Road.K4.k4Block_ok
#print axioms OnBytes.Road.K4.k4_blocks_ok
#print axioms OnBytes.Road.K4.k4SentB_iff
#print axioms OnBytes.Road.K4.k4SentB_rejects

end OnBytes.Road.K4
