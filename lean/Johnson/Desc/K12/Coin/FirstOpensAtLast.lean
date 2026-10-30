-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/FirstOpensAtLast.lean: THE PROMISE `FirstOpens` AT THE LAST CHAIN, ASSEMBLED: from what
the test on taken sources says, the description's data and tests on the plan, and FOUR NAMED PREMISES.

The pieces. `firstOpens_of` (FirstOpensOf.lean) · `taken_of_first` (FirstOpensTaken.lean) ·
`tk_eq_places` (FirstOpensSets.lean) · `all_taken` (FirstOpensAll.lean) · `sets_of_tied`
(Johnson/Desc/Sound/FirstOpensOfSets.lean).
  `firstOpens_at_last`  **FirstOpens π (numAt F.t₁ F.t₂ 2) (fun z => wholeNo F.t₁ F.t₂ (plOf t.book ω z))
                        base t**
PAID BY OTHERS' YES. (a), (b): the two clauses of the last chain's test on taken sources, at the pairs
tk that it has read off the book. h: `F.data`'s yes. hk: `F.treeSharingOk`. hp: the block's test on the plan.
THE NAMED PREMISES, NONE PAID HERE.
  `seated`  the block's rounds are rounds of the description's last chain (the seat)
  `first`   every member of the place's list π.nums.first is taken over (at the planner's road: the head
            of `secondOpens`: Johnson/G/SecondOpensTaken.lean), with no own mask and two stages at least
  `alone`   of the group's members and the mask, Omega alone lies in Omega's tree
  `up`      along D.ts the places rise strictly: the book's make
  `firstOpens_at_book`  the same with "no" said of ONE PUBLIC BOOK B₀: a fifth named premise `book`: the
                        record's book agrees with B₀ on the place of Omega's tree and on the numbers
                        of the trees at D.ts
Limits. THAT THE PREMISES HOLD TOGETHER AT THE RELEASE's PLAN AND A RECORD THAT RUNS HAS NOT BEEN TESTED BY
LEAN (by eye, against a print at both sizes, not shown here: they look met). hm: the mask has
come: a plan without masks ahead is shut out.
WHAT THE NUMBERS ARE. In a source "taken c n" the n is spent as AN INDEX
INTO THE SENDING CHAIN's LIST OF ROOTS (`taken_sent_of_data`). `plOf`'s second member is the field
`number` of a tree OFF THE BOOK. That the two are one, that is: THAT A TREE's NUMBER IN THE BOOK IS ITS
PLACE IN ITS CHAIN's ORDER OF SENDING, is said by no law: `up` and `book` must carry it. UNTIL THEN
THIS THEOREM TIES NUMBERS IN ORDER, NOT TREES.
TWO TIES BESIDE THE PREMISES, both by Lean on another ground (Johnson/ToldDescR/TiesAtSeat.lean, over
the description's cone): the list that the last chain's test reads off its record is, at the seat's
record, A COPY OF `tkOf` typed on that ground (the two definitions' texts, and the record types' that
they name, are the same bytes: held by program, not by Lean); the rounds that it reads are this
block's, at one π.
Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.FirstOpensSets
import Johnson.Desc.K12.Coin.FirstOpensTaken
import Johnson.Desc.K12.Coin.FirstOpensAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- **The promise at the last chain, assembled.** -/
theorem firstOpens_at_last {Xi : Type} {F : FileDescription Xi} {file : String} {D₀ : WholeD}
    (h : F.data file = .ok D₀) (hk : F.treeSharingOk = true) (π : P12)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (seated : ∀ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, r ∈ F.roundsDeclaredByBlocks.2.2)
    (base : ℕ) (hb : F.t₁ + F.t₂ ≤ base) (t : T12) {id : ℕ} (hm : t.mask = some id) (ω : ℕ)
    (tk : List (ℕ × ℕ)) (htk : tkOf t ω = some tk)
    (a : ∀ x ∈ tk, ∃ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, ∃ o ∈ r.opens,
      o.2 = .taken x.1 x.2)
    (b : ∀ r ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds, ∀ o ∈ r.opens, ∀ c n,
      o.2 = .taken c n → (c, n) ∈ tk)
    (ho : π.nums.ownMask = false) (h2 : 2 ≤ π.nums.stages.length)
    (first : ∀ o ∈ π.nums.first, ∃ c n, o.2 = .taken c n)
    (alone : ∀ G0, t.st.groups[t.g]? = some G0 → ∀ i ∈ G0.members.toList ++ t.mask.toList,
      ∀ q p z, t.book.place[ω]? = some q → t.book.place[i]? = some (z, p) → q.1 = z → i = ω)
    (up : ∀ s rest G0 Ly D, Fixes π t s rest G0 Ly D →
      (D.ts.map (plOf t.book ω)).Pairwise Before) :
    FirstOpens π (VerifiableInference.Desc.numAt F.t₁ F.t₂ 2)
      (fun z => Three.wholeNo F.t₁ F.t₂ (plOf t.book ω z)) base t := by
  have tkn := taken_of_first π hp ho h2 first
  refine firstOpens_of h hk π hp seated (plOf t.book ω) base hb t tkn up ?_
  intro s rest G0 Ly D hF x
  have hs := hF.1
  have hO : D.opens = H2K.First.opensOf π s.k :=
    (H2K.First.made_of _ _ _ _ _ (hF.2.2.2 { group := 0 })).opens
  obtain ⟨dS, dC, hc, -, -, -, -, hC⟩ :=
    H2K.First.cut_of_ok π s rest hs (H2K.JointK.cut_of_planOk π hp)
  have hr : dC ∈ (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds :=
    cut_mem π hp s.k dC (by rw [hc]; simp)
  rw [hO]
  exact (sets_of_tied _ (H2K.First.opensOf π s.k) tk a b
    (fun o hoo => ⟨dC, hr, by rw [hC]; exact hoo⟩) (tkn s rest hs) (all_taken π hp s rest hs) x).trans
    (tk_eq_places hF hm ω tk htk (alone G0 hF.2.1) x)

/-- The promise reads its letter "no" at the places D.ts alone. -/
theorem FirstOpens.congr_no {π : P12} {num : Fmt.TreeSource → ℕ} {no no' : ℕ → ℕ} {base : ℕ} {t : T12}
    (h : FirstOpens π num no base t)
    (e : ∀ s rest G0 Ly D, Fixes π t s rest G0 Ly D → ∀ z ∈ D.ts, no' z = no z) :
    FirstOpens π num no' base t := by
  intro s rest G0 Ly D hF
  obtain ⟨h1, h2⟩ := h s rest G0 Ly D hF
  refine ⟨h1.trans (List.map_congr_left fun z hz => (e s rest G0 Ly D hF z hz).symm), fun z hz => ?_⟩
  rw [e s rest G0 Ly D hF z hz]
  exact h2 z hz

/-- Two books that agree on the place of Omega's tree and on the number of the tree at z give z one
place. -/
theorem plOf_congr {B B₀ : TreeBook} {ω z : ℕ}
    (h₁ : (B₀.place[ω]?).map (·.1) = (B.place[ω]?).map (·.1))
    (h₂ : (B₀.trees[z]?).map (·.number) = (B.trees[z]?).map (·.number)) :
    plOf B₀ ω z = plOf B ω z := by
  unfold plOf
  rw [h₁, h₂]

/-- **The same with the letter "no" said of ONE PUBLIC BOOK B₀**, from a fifth named premise `book`:
the record's book agrees with B₀ on the place of Omega's tree and on the numbers of the trees at
D.ts. -/
theorem firstOpens_at_book {π : P12} {num : Fmt.TreeSource → ℕ} {t₁ t₂ base ω : ℕ} {t : T12}
    (B₀ : TreeBook)
    (h : FirstOpens π num (fun z => Three.wholeNo t₁ t₂ (plOf t.book ω z)) base t)
    (book₁ : (B₀.place[ω]?).map (·.1) = (t.book.place[ω]?).map (·.1))
    (book₂ : ∀ s rest G0 Ly D, Fixes π t s rest G0 Ly D → ∀ z ∈ D.ts,
      (B₀.trees[z]?).map (·.number) = (t.book.trees[z]?).map (·.number)) :
    FirstOpens π num (fun z => Three.wholeNo t₁ t₂ (plOf B₀ ω z)) base t :=
  h.congr_no fun s rest G0 Ly D hF z hz => by
    show Three.wholeNo t₁ t₂ (plOf B₀ ω z) = Three.wholeNo t₁ t₂ (plOf t.book ω z)
    rw [plOf_congr book₁ (book₂ s rest G0 Ly D hF z hz)]

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.FirstOpens.congr_no
#print axioms VerifiableInference.Desc.K12.Coin.firstOpens_at_book
#print axioms VerifiableInference.Desc.K12.Coin.firstOpens_at_last
