-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/FallsHead.lean: the first chain's list of falls at the full size,
as one definition. A fall (`Fall`, Honest/Side.lean) is a record with a place, a test on the
verifier's state and the place's own challenges, and a stated number. It names an event on the
challenges at which the honest prover's run is rejected. The authors of three kinds of sub-protocol
have each written their own records. The theorems that bound the chance of a fall (`falls_asks`,
Honest/Law/CoverAsks.lean) and the rule for acceptance take the chain's list of falls as an
argument. Here that list is laid: each record is its authors' own, at the parameters at which the
chain's sub-protocols are made from the public part `Zp` and the ground `G₀`.

The records, in the list's order.
  * In each of the 25 segments, three:
    `K8.k8FrontFall` (Honest/K8/Falls.lean), at the batching: a column of the smallness test's drawn
    matrix has the weight 0 at the batching element;
    `K9.quietFall` (Honest/K9/Falls.lean), at the sub-protocol without a round after the batching:
    the verifier's test on the free slots rejects;
    `K8.k8ShareFall` (Honest/K8/Falls.lean), at the same sub-protocol: one of seven tests of the
    smallness test on the ledger's weights rejects.
  * In each of the twelve feed-forward segments, one: `K4.k4Fall` (Honest/K4/Part.lean), at the
    segment's own rounds: a sampled element is 0.

  1  `oAt`, `linkFalls`, `fallsHead`   the definitions
  2  `fallsHead_front`, `fallsHead_quiet`, `fallsHead_share`, `fallsHead_k4`   each named record is
     in the list, where the look-up that gives its parameters returns
  3  `length_flatMap_range`, `length_filterMap_range`, `linkFalls_length`, `fallsHead_length`
     where all four look-ups return, the list has 87 records

Limits.
  * Where a look-up does not return (`IM.k9At`, `testsWhere`, `G₀.built[l]?`, `G₀.W.G[g]?`), the
    text leaves the record out and says nothing. So a statement about every record of the list is
    the weaker for each record that is left out. `fallsHead_length` takes as hypotheses that the
    look-ups return. They are not proved here.
  * Five arguments are stated numbers or a field that no test reads: `cols`, `tau`, `share`,
    `notGood`, `r0` (see `fallsHead`). No test reads any of them.
  * Two of the three tests at a batching take a test of the verifier whole, a comparison with it
    that no challenge excuses (see Honest/Law/SilentFree.lean and Honest/Law/SilentTail.lean).
  * The fall of K4's own test on the free slots is not in the list. That no run is rejected by that
    test while `quietFall` is silent rests on a lemma that lies outside this tree:
    `valuesJ_behind_lay` (Johnson/AtFull/Shape/ValuesOfFalls.lean), of the authors of the table of
    steps.
  * Nothing holds a stated number against its test.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K8.Falls
import Johnson.Desc.ProofFile.Honest.K9.Falls
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.IMR.LinkSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S)

/-! ## 1 The list -/

/-- The output head's segment, number 24, has two more sub-protocols before its batching than the
others. -/
def oAt (l : Nat) : Nat := if l = 24 then 1 else 0

/-- The falls of one segment's batching: at the batching itself the fall of the smallness test's
columns; at the sub-protocol without a round after it the fall of the free slots and the smallness
test's share. Each is its authors' own record. The four arguments `cols`, `tau`, `share` and
`notGood` are explained at `fallsHead`. -/
def linkFalls (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (cols tau : Nat → Nat) (share notGood : Nat → Odds)
    (l : Nat) : List (Fall S) :=
  [K8.k8FrontFall l (oAt l) (cols l) (tau l)] ++
    (match IM.k9At Zp l, VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 with
      | some p, some u => [K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l)]
      | _, _ => []) ++
    (match G₀.built[l]? with
      | some Xl => [K8.k8ShareFall l (oAt l) (ProofFile.k8ParW Zp G₀ Xl l).nU (share l)]
      | none => [])

/-- The first chain's list of falls at the full size: the falls of the 25 segments' batchings, then
the fall "coin-zero" of each of the twelve feed-forward segments. Five arguments are left open.
  * `cols l`, `tau l`: the two numbers of which `k8FrontFall`'s stated number is made. K8's authors
    give them as `K8.k8ColsAt G₀ l` and `K8.k8TauAt G₀ l`, in a file that is not imported here.
  * `share l`: `k8ShareFall`'s stated number. K8's authors give it as `P1K8.k8ShareAt Zp G₀ l`, in a
    file that is not imported here. They say that `k8FallShare`, which their file with the record
    names, is not meant any more.
  * `notGood l`: the second half of `quietFall`'s stated number: the chance that the state before
    the batching is not good. K9's authors say: "it has no payer", and "0 of 1 makes the total too
    small".
  * `r0 g`: the number of rounds before K4's first. It is a field of K4's public data that the
    fall's test does not read. -/
def fallsHead (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (cols tau : Nat → Nat) (share notGood : Nat → Odds)
    (r0 : Nat → Nat) : List (Fall S) :=
  (List.range 25).flatMap (linkFalls Zp G₀ cols tau share notGood) ++
    (List.range 12).filterMap fun g => (G₀.W.G[g]?).map fun hp =>
      K4.k4Fall ⟨G₀.W.layers, hp, g, 2 * g, 3, r0 g, 2 * g⟩

variable {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground} {cols tau : Nat → Nat} {share notGood : Nat → Odds}
  {r0 : Nat → Nat}

/-! ## 2 The named records are in the list -/

/-- A record of a segment's falls is in the list. -/
theorem fallsHead_link {l : Nat} (hl : l < 25) {F : Fall S}
    (h : F ∈ linkFalls Zp G₀ cols tau share notGood l) :
    F ∈ fallsHead Zp G₀ cols tau share notGood r0 := by
  unfold fallsHead
  exact List.mem_append_left _ (List.mem_flatMap.2 ⟨l, List.mem_range.2 hl, h⟩)

/-- The fall of the smallness test's columns, at each segment. -/
theorem fallsHead_front {l : Nat} (hl : l < 25) :
    K8.k8FrontFall l (oAt l) (cols l) (tau l) ∈ fallsHead Zp G₀ cols tau share notGood r0 :=
  fallsHead_link hl (by
    unfold linkFalls
    exact List.mem_append_left _ (List.mem_append_left _ List.mem_cons_self))

/-- The fall of the free slots, at each segment at which the two look-ups return. -/
theorem fallsHead_quiet {l : Nat} (hl : l < 25) {p : VerifiableInference.Desc.K9.Where}
    {u : VerifiableInference.Desc.K9.SegSort × Nat × VerifiableInference.Desc.K9.TWhere}
    (hp : IM.k9At Zp l = some p)
    (hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u) :
    K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l) ∈
      fallsHead Zp G₀ cols tau share notGood r0 :=
  fallsHead_link hl (by
    unfold linkFalls
    rw [hp, hu]
    exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))

/-- The smallness test's share, at each segment whose planned link is there. -/
theorem fallsHead_share {l : Nat} (hl : l < 25) {Xl : OnBytes.Model.Stages.LinkH}
    (hX : G₀.built[l]? = some Xl) :
    K8.k8ShareFall l (oAt l) (ProofFile.k8ParW Zp G₀ Xl l).nU (share l) ∈
      fallsHead Zp G₀ cols tau share notGood r0 :=
  fallsHead_link hl (by
    unfold linkFalls
    rw [hX]
    exact List.mem_append_right _ List.mem_cons_self)

/-- The fall "coin-zero", at each feed-forward segment whose plan is there. -/
theorem fallsHead_k4 {g : Nat} (hg : g < 12) {hp : OnBytes.Model.Layer.HPlan2}
    (hh : G₀.W.G[g]? = some hp) :
    (K4.k4Fall ⟨G₀.W.layers, hp, g, 2 * g, 3, r0 g, 2 * g⟩ : Fall S) ∈
      fallsHead Zp G₀ cols tau share notGood r0 := by
  unfold fallsHead
  refine List.mem_append_right _ (List.mem_filterMap.2 ⟨g, List.mem_range.2 hg, ?_⟩)
  rw [hh]
  rfl

/-! ## 3 How many -/

/-- Lists of one length, laid in a row. -/
theorem length_flatMap_range {α : Type} (f : Nat → List α) (c : Nat) :
    ∀ n, (∀ l, l < n → (f l).length = c) → ((List.range n).flatMap f).length = c * n
  | 0, _ => by simp
  | n + 1, h => by
    have e : [n].flatMap f = f n := by simp
    rw [List.range_succ, List.flatMap_append, List.length_append,
      length_flatMap_range f c n (fun l hl => h l (by omega)), e, h n (Nat.lt_succ_self n),
      Nat.mul_succ]

/-- Where the function returns at every number, nothing is left out. -/
theorem length_filterMap_range {α : Type} (k : Nat → Option α) :
    ∀ n, (∀ g, g < n → (k g).isSome = true) → ((List.range n).filterMap k).length = n
  | 0, _ => by simp
  | n + 1, h => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (h n (Nat.lt_succ_self n))
    have e : [n].filterMap k = [a] := by simp [ha]
    rw [List.range_succ, List.filterMap_append, List.length_append,
      length_filterMap_range k n (fun g hg => h g (by omega)), e, List.length_singleton]

/-- Where its three look-ups return, a segment has three falls. -/
theorem linkFalls_length {l : Nat} (h1 : (IM.k9At Zp l).isSome = true)
    (h2 : (VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0).isSome = true)
    (h3 : (G₀.built[l]?).isSome = true) :
    (linkFalls Zp G₀ cols tau share notGood l).length = 3 := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h2
  obtain ⟨Xl, hX⟩ := Option.isSome_iff_exists.1 h3
  unfold linkFalls
  rw [hp, hu, hX]
  rfl

/-- Where all look-ups return, the list has 87 records: three in each of 25 segments, and twelve. -/
theorem fallsHead_length
    (h1 : ∀ l, l < 25 → (IM.k9At Zp l).isSome = true)
    (h2 : ∀ l, l < 25 → (VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0).isSome = true)
    (h3 : ∀ l, l < 25 → (G₀.built[l]?).isSome = true)
    (h4 : ∀ g, g < 12 → (G₀.W.G[g]?).isSome = true) :
    (fallsHead Zp G₀ cols tau share notGood r0).length = 87 := by
  have a := length_flatMap_range (linkFalls Zp G₀ cols tau share notGood) 3 25
    (fun l hl => linkFalls_length (h1 l hl) (h2 l hl) (h3 l hl))
  have b := length_filterMap_range (fun g => (G₀.W.G[g]?).map fun hp =>
      (K4.k4Fall ⟨G₀.W.layers, hp, g, 2 * g, 3, r0 g, 2 * g⟩ : Fall S)) 12
    (fun g hg => by
      obtain ⟨hp, hh⟩ := Option.isSome_iff_exists.1 (h4 g hg)
      show (Option.map _ (G₀.W.G[g]?)).isSome = true
      rw [hh]
      rfl)
  unfold fallsHead
  calc _ = 3 * 25 + 12 := by rw [List.length_append, a, b]
    _ = 87 := rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.fallsHead_link
#print axioms ProofFile.Honest.fallsHead_front
#print axioms ProofFile.Honest.fallsHead_quiet
#print axioms ProofFile.Honest.fallsHead_share
#print axioms ProofFile.Honest.fallsHead_k4
#print axioms ProofFile.Honest.length_flatMap_range
#print axioms ProofFile.Honest.length_filterMap_range
#print axioms ProofFile.Honest.linkFalls_length
#print axioms ProofFile.Honest.fallsHead_length
