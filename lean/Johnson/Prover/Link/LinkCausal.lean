-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkCausal.lean: WHAT linkAll (Johnson/Prover/Link/LinkAll.lean) SHOWS IN A
ROUND HANGS ON THE DRAWS IN FRONT OF THAT ROUND ALONE; so linkNext, at the draws so far, gives the
round's own message. Statements and proofs.

  lMem_congr ... lT_congr   equal draws, equal pieces
  linkAll_causal   two families of draws that agree below i: round i shows the same items and sends
                   the same tree
  linkNext_at      linkNext i (the first i draws of a list) is round i's message of linkAll at the
                   whole list

Not shown here: that any block says yes. Nothing on soundness; nothing on what any value that is
sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkAll
import Johnson.Prover.Link.BodyCausal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.JointK (laidOf)

variable (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D D' : ℕ → Fmt.Drawn)

theorem lMem_congr (h0 : D 0 = D' 0) : lMem S X C D = lMem S X C D' := by
  unfold lMem lGam
  rw [h0]

theorem lPS_congr (h0 : D 0 = D' 0) : lPS P S X C D = lPS P S X C D' := by
  unfold lPS
  rw [lMem_congr S X C D D' h0]

theorem lCol_congr (h0 : D 0 = D' 0) : lCol P S X C D = lCol P S X C D' := by
  unfold lCol
  rw [lMem_congr S X C D D' h0]

theorem lSeed_congr (h1 : D 1 = D' 1) : lSeed S D = lSeed S D' := by
  unfold lSeed
  rw [h1]

theorem lFront_congr (h : ∀ n, n < 5 → D n = D' n) : lFront S t X C D = lFront S t X C D' := by
  unfold lFront
  rw [lMem_congr S X C D D' (h 0 (by omega)), lSeed_congr S D D' (h 1 (by omega)),
    h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega)]

theorem lT_congr (h : ∀ n, n < 6 → D n = D' n) : lT P S t X C D = lT P S t X C D' := by
  unfold lT lStoredCols
  rw [lFront_congr S t X C D D' fun n hn => h n (by omega), h 3 (by omega), h 5 (by omega)]

theorem linkAll_rs (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of P).nums.stages = first :: rest) :
    (linkAll P S t X C D).rs = lFront S t X C D ++ [⟨[], D 5⟩] ++
      (bodyAll (p12Of P) C.body rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D)
        (lPS P S X C D) (lCol P S X C D) D).rs := by
  unfold linkAll
  rw [hs]

theorem linkAll_tr (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of P).nums.stages = first :: rest) :
    (linkAll P S t X C D).tr =
      [fun _ => [], lCol P S X C D] ++ [fun _ => [], fun _ => [], fun _ => [], fun _ => []] ++
      (bodyAll (p12Of P) C.body rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t X C D)
        (lPS P S X C D) (lCol P S X C D) D).tr := by
  unfold linkAll
  rw [hs]
  rfl

theorem linkAll_nil (hs : (p12Of P).nums.stages = []) : linkAll P S t X C D = ⟨[], [], []⟩ := by
  unfold linkAll
  rw [hs]

/-- The two answers. -/
def lAns : List Fmt.ItemValue :=
  [.answer (ofE (smAt S t (lSeed S D) (mu0 S t (lMem S X C D)) false)),
    .answer (ofE (smAt S t (lSeed S D) (mu0 S t (lMem S X C D)) true))]

theorem lFront_map : (lFront S t X C D).map (·.vals) = [[], [], lAns S t X C D, [], []] := rfl

theorem five_get {α : Type} (e u u' : α) (i : ℕ) (h : i < 2 ∨ u = u') :
    [e, e, u, e, e][i]? = [e, e, u', e, e][i]? := by
  rcases h with h | h
  · match i, h with
    | 0, _ => rfl
    | 1, _ => rfl
  · rw [h]

theorem lFront_vals (i : ℕ) (h : ∀ n, n < i → D n = D' n) :
    ((lFront S t X C D)[i]?).map (·.vals) = ((lFront S t X C D')[i]?).map (·.vals) := by
  rw [← List.getElem?_map, ← List.getElem?_map, lFront_map, lFront_map]
  refine five_get _ _ _ i ?_
  by_cases c : i < 2
  · exact Or.inl c
  · refine Or.inr ?_
    unfold lAns
    rw [lMem_congr S X C D D' (h 0 (by omega)), lSeed_congr S D D' (h 1 (by omega))]

theorem two_get {α : Type} (e u u' : α) (i : ℕ) (h : i < 1 ∨ u = u') :
    [e, u][i]? = [e, u'][i]? := by
  rcases h with h | h
  · match i, h with
    | 0, _ => rfl
  · rw [h]

/-- **What a round shows hangs on the draws in front of it alone.** -/
theorem linkAll_causal (i : ℕ) (h : ∀ n, n < i → D n = D' n) :
    ((linkAll P S t X C D).rs[i]?).map (·.vals) = ((linkAll P S t X C D').rs[i]?).map (·.vals) ∧
      (linkAll P S t X C D).tr[i]? = (linkAll P S t X C D').tr[i]? := by
  cases hs : (p12Of P).nums.stages with
  | nil => rw [linkAll_nil P S t X C D hs, linkAll_nil P S t X C D' hs]; exact ⟨rfl, rfl⟩
  | cons first rest =>
    rw [linkAll_rs P S t X C D first rest hs, linkAll_rs P S t X C D' first rest hs,
      linkAll_tr P S t X C D first rest hs, linkAll_tr P S t X C D' first rest hs]
    have l5 : ∀ E : ℕ → Fmt.Drawn, (lFront S t X C E).length = 5 := fun _ => rfl
    by_cases c1 : i < 5
    · constructor
      · rw [get3_left _ _ _ i (by rw [l5]; exact c1), get3_left _ _ _ i (by rw [l5]; exact c1)]
        exact lFront_vals S t X C D D' i h
      · by_cases c0 : i < 2
        · rw [get3_left [fun _ => [], lCol P S X C D] _ _ i c0,
            get3_left [fun _ => [], lCol P S X C D'] _ _ i c0]
          refine two_get _ _ _ i ?_
          by_cases c : i < 1
          · exact Or.inl c
          · exact Or.inr (lCol_congr P S X C D D' (h 0 (by omega)))
        · rw [get3_mid _ _ _ i (by show 2 ≤ i; omega) (by show i < 2 + 4; omega),
            get3_mid _ _ _ i (by show 2 ≤ i; omega) (by show i < 2 + 4; omega)]
          simp only [List.length_cons, List.length_nil]
    · by_cases c2 : i = 5
      · subst c2
        constructor
        · rw [get3_mid _ _ _ 5 (by rw [l5]) (by rw [l5]; show 5 < 5 + 1; omega),
            get3_mid _ _ _ 5 (by rw [l5]) (by rw [l5]; show 5 < 5 + 1; omega), l5, l5]
          rfl
        · rw [get3_mid _ _ _ 5 (by show 2 ≤ 5; omega) (by show 5 < 2 + 4; omega),
            get3_mid _ _ _ 5 (by show 2 ≤ 5; omega) (by show 5 < 2 + 4; omega)]
          simp only [List.length_cons, List.length_nil]
      · have ih := bodyAll_causal (p12Of P) C.body rest 0 first ((laidOf (p12Of P)).drop 1) 6
          (lT P S t X C D) (lPS P S X C D) (lCol P S X C D) D D' (i - 6) fun n hn => h n (by omega)
        rw [← lT_congr P S t X C D D' fun n hn => h n (by omega),
          ← lPS_congr P S X C D D' (h 0 (by omega)), ← lCol_congr P S X C D D' (h 0 (by omega))]
        constructor
        · rw [get3_right _ _ _ i (by rw [l5]; show 5 + 1 ≤ i; omega),
            get3_right _ _ _ i (by rw [l5]; show 5 + 1 ≤ i; omega), l5, l5]
          exact ih.1
        · rw [get3_right _ _ _ i (by show 2 + 4 ≤ i; omega),
            get3_right _ _ _ i (by show 2 + 4 ≤ i; omega)]
          exact ih.2

/-- **linkNext at the draws so far gives the round's own message.** Ds: a whole list of draws. -/
theorem linkNext_at (Ds : List Fmt.Drawn) (i : ℕ) :
    (linkNext P S t X C i (Ds.take i)).vals =
        (((linkAll P S t X C fun j => Ds.getD j ⟨[], [], [], none⟩).rs[i]?).map (·.vals)).getD [] ∧
      (linkNext P S t X C i (Ds.take i)).col = fun _ =>
        ((linkAll P S t X C fun j => Ds.getD j ⟨[], [], [], none⟩).tr[i]?).getD fun _ => [] := by
  have h := linkAll_causal P S t X C (fun j => (Ds.take i).getD j ⟨[], [], [], none⟩)
    (fun j => Ds.getD j ⟨[], [], [], none⟩) i fun n hn => by
      show (Ds.take i).getD n _ = Ds.getD n _
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hn]
  unfold linkNext
  exact ⟨congrArg (·.getD []) h.1, funext fun _ => congrArg (·.getD fun _ => []) h.2⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.lT_congr
#print axioms Johnson.Prover.Link.linkAll_causal
#print axioms Johnson.Prover.Link.linkNext_at
