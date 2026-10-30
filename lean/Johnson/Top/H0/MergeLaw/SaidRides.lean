-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/SaidRides.lean: K11's SECOND TIE: WHAT THE OPEN PUBLIC ITEMS SAY BESIDE
THEIR TESTS WITH CODE (`Meaning.pubP`) PASSES THE MERGE's ACCEPTING STEP: the premise hPP of
`merge_t2` (Johnson/Top/H0/MergeLaw/TieOneTwo.lean), at the composed filling `mgAll 𝔇 Mg₀`
(Johnson/Desc/Sound/MgAll.lean). Theorems.

What is said.
  `merge_leftOn`: **what is said of "leftOn m" rides** (its test with code is "true" outright, so
    all that is said of it is said here): the sentence is `k3LeftOnItemAt X m` (what
    the lookup on the calls left, in the form that stands at every later state); it rides by their
    own `leftOn_stays`: what was heard stays (`isLocal`); the ledger behind is later
    (`decide_later`); it has its sizes (`merge_ledger`, from the sizes in front, which the sentence
    itself holds).
  `merge_said`: one item's sentence rides, if the item is not the sharp "left m": at "leftOn m" by
    the above; at the pending claim's own item it is "True"; elsewhere it is Mg₀'s, which is asked
    not to read what the step turns (hblind).
  `merge_hPP_all`: **hPP to the letter at Q := the open public set in front and r := the row**,
    under: hblind; no item that stays open past the step is a "left m" (hnl: "none is open in front"
    gives it, and so does "none is open behind"); what the row makes AND WAS NOT OPEN IN FRONT holds
    behind (hmk). AN ITEM THAT WAS OPEN IN FRONT IS PAID HERE, whether or not the row makes it anew:
    so "leftOn m" never falls to hmk where it is open on both sides.

Limits. Implications. THE SHARP ITEM "left m" DOES NOT RIDE (it says that the ledger IS the one
behind the hearing): that none is open at the merge's border is a fact on the written table, taken
as given. hblind holds outright at a Mg₀ whose sentence reads no state. What the row makes is taken
as given. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.LedgerBehind
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Later)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn Here Pub PubRow Meaning pubStep)
open VerifiableInference.Desc.First.Look (fillK3 fill_pubP_other)
open VerifiableInference.Desc.First.FillP1 (fillP1 p1Item fillP1_pubP_own fillP1_pubP_else)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt k3LeftOnItem leftOn_stays laterFo_of_psc)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **WHAT IS SAID OF "leftOn m" RIDES PAST THE MERGE's ACCEPTING STEP.** -/
theorem merge_leftOn (X : Verify.Public) (m : ℕ) (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (L : k3LeftOnItemAt X m s) : k3LeftOnItemAt X m s' := by
  obtain ⟨p, hp, L⟩ := L
  refine ⟨p, hp, ?_⟩
  obtain ⟨a, a', ha, ha', ho, ho', H⟩ := merge_ledger P h
  obtain ⟨a₁, a₁', e1, e1', _, ea, _⟩ := isLocal P s rs s' h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  obtain ⟨a₂, a₂', f1, f1', hl⟩ := decide_later h
  obtain rfl : a₂ = a₁ := by
    rw [ha] at f1
    exact (Here.head.inj f1).symm
  obtain rfl : a₂' = a₁' := by
    rw [ha'] at f1'
    exact (Here.head.inj f1').symm
  have eF : s.fork? = some a₂.F := by
    unfold S.fork?
    rw [ha]
    simp only [ho, if_true]
  have eF' : s'.fork? = some a₂'.F := by
    unfold S.fork?
    rw [ha']
    simp only [ho', if_true]
  have hh : s'.lookHeard? = s.lookHeard? := by
    have e : a₂'.lookHeard = a₂.lookHeard := by rw [ea]
    unfold S.lookHeard?
    rw [ha, ha']
    simp only [ho, ho', if_true, e]
  have hz : Sized a₂.F := by
    obtain ⟨⟨_, _, _, _, G, _, _, _, _, _, _, hG, _, hs⟩, _⟩ := L
    obtain rfl : G = a₂.F := Option.some.inj (hG.symm.trans eF)
    exact hs
  exact leftOn_stays hh eF eF' (laterFo_of_psc hl) (H hz).2.2.1 L

/-- A member of the open public set behind a sub-protocol was open in front, or the row makes it. -/
theorem mem_pubStep {Q : List Pub} {r : PubRow} {q : Pub} (h : q ∈ pubStep Q r) :
    q ∈ Q ∨ q ∈ r.makes := by
  unfold pubStep at h
  rcases List.mem_append.1 h with h | h
  · exact Or.inl (List.mem_filter.1 h).1
  · exact Or.inr (List.mem_filter.1 h).1

section
variable {Xi Pp Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  (𝔇 : MgData Xi Pp Tok rows cols nR X) (Mg₀ : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT))

/-- **One item's sentence rides past the step**, if it is not the sharp item "left m". -/
theorem merge_said (P : HeadMergeP) (z : Pp) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s')
    (hblind : ∀ q, Mg₀.pubP q (z, s) → Mg₀.pubP q (z, s')) (q : Pub) (hq : ∀ m, q ≠ .left m)
    (h0 : (mgAll 𝔇 Mg₀).pubP q (z, s)) : (mgAll 𝔇 Mg₀).pubP q (z, s') := by
  rw [mgAll_pubP] at h0 ⊢
  by_cases hl : ∃ m, q = .leftOn m
  · obtain ⟨m, rfl⟩ := hl
    exact merge_leftOn X m P h h0
  · have h2 : ∀ m, q ≠ .leftOn m := fun m e => hl ⟨m, e⟩
    rw [fill_pubP_other X 𝔇.sent _ q _ hq h2] at h0 ⊢
    cases hp : p1Item q with
    | true => exact fillP1_pubP_own _ _ _ _ _ q hp _
    | false =>
      rw [fillP1_pubP_else _ _ _ _ _ q hp] at h0 ⊢
      exact hblind q h0

/-- **hPP OF `merge_t2` AT THE COMPOSED FILLING.** Q: the open public set in front; r: the row. -/
theorem merge_hPP_all (Q : List Pub) (r : PubRow) (P : HeadMergeP) (z : Pp) {s s' : S}
    (hy : ∃ rs, headMergeDecide P s rs = .ok s')
    (hblind : ∀ q, Mg₀.pubP q (z, s) → Mg₀.pubP q (z, s'))
    (hnl : ∀ q ∈ Q, q ∈ pubStep Q r → ∀ m, q ≠ .left m)
    (hmk : ∀ q ∈ r.makes, q ∉ Q → (mgAll 𝔇 Mg₀).pubP q (z, s')) :
    (∀ q ∈ Q, (mgAll 𝔇 Mg₀).pubP q (z, s)) →
      ∀ q ∈ pubStep Q r, (mgAll 𝔇 Mg₀).pubP q (z, s') := by
  obtain ⟨rs, hy⟩ := hy
  intro hQ q hq
  by_cases hin : q ∈ Q
  · exact merge_said 𝔇 Mg₀ P z hy hblind q (hnl q hin hq) (hQ q hin)
  · rcases mem_pubStep hq with h | h
    · exact absurd h hin
    · exact hmk q h hin

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_leftOn
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_said
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_hPP_all
