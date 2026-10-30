-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkWords.lean: EVERY WORD THAT linkNext SHOWS OR WRITES INTO A TREE IS BELOW
THE PRIME: the two premises hV | hC of okViewW_run (Johnson/Prover/Link/LinkFrameView.lean), at
every round, every history, all letters and inputs. Statements and proofs: all that is shown is
written by ofE, and every column by this folder's writers.

  OkRV, OkCol           every item of a round passes okGot · every word of a column is below the
                        prime
  okRV_showRV ... okRV_linkAll     at the rounds
  okCol_sCol ... okCol_linkAll     at the trees
  linkNext_vals, linkNext_cols     hV and hC

Not shown here. The drawn elements and the stored columns (ViewWords.lean has them). Nothing on a
decision, on soundness or on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkCausal
import Johnson.Prover.Link.LinkFrameView

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open _root_.Desc.K15 (P15 p12Of)
open H2K.JointK (laidOf)

/-- Every item that a round shows passes okGot (Johnson/Prover/Link/LinkFrameView.lean). -/
def OkRV (r : Fmt.RoundView) : Prop := ∀ g ∈ r.vals, okGot g = true
/-- Every word of a column, at every position, is below the prime. -/
def OkCol (c : ℕ → List UInt64) : Prop := ∀ x, ∀ w ∈ c x, w < fieldPrimeWord

theorem okCol_nil : OkCol fun _ => [] := fun _ _ h => by cases h
theorem okRV_nil (d : Fmt.Drawn) : OkRV ⟨[], d⟩ := fun _ h => by cases h

theorem okRV_showRV : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    ∀ r ∈ showRV k q D, OkRV r
  | 0, _, _, _, h => by cases h
  | k + 1, q, D, r, h => by
    rcases List.mem_cons.1 h with rfl | h
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact lt_ofE _
      · rw [List.mem_singleton.1 hg]; exact lt_ofE _
    · exact okRV_showRV k _ _ r h

theorem okRV_foldRV (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : ∀ r ∈ foldRV s v μ W D, OkRV r := by
  intro r h
  rcases List.mem_cons.1 h with rfl | h
  · intro g hg
    rw [List.mem_singleton.1 hg]; exact lt_ofE _
  · exact okRV_showRV _ _ _ r h

theorem okCol_lastCol (s : Sg) (P : PS) : OkCol (lastCol s P) :=
  fun x => lt_words12 _ _ _ _ _ _ _ _ _ _ x

theorem okCol_sCol (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (o : ℕ) (P : PS)
    (row : GroupRow) (D : ℕ → Fmt.Drawn) : OkCol (sCol K last j cur next o P row D) := by
  cases last
  · exact fun x => lt_stageColW _ _ _ _ _ _ _ x
  · exact okCol_lastCol _ _

theorem ok_bodyAll (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64),
      (∀ r ∈ (bodyAll p K rest j cur l o t P col D).rs, OkRV r) ∧
        ∀ c ∈ (bodyAll p K rest j cur l o t P col D).tr, OkCol c
  | [], j, cur, l, o, t, P, col => by
    constructor
    · intro r h
      rcases List.mem_cons.1 h with rfl | h
      · intro g hg
        rw [List.mem_singleton.1 hg]; exact lt_tauSW _ _ _ _ _ _
      · rw [List.mem_singleton.1 h]
        intro g hg
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
        unfold shownAll at he
        rcases List.mem_append.1 he with he | he
        · exact lt_wr _ _ e he
        · rcases List.mem_append.1 he with he | he
          · exact lt_wr _ _ e he
          · rcases List.mem_append.1 he with he | he
            · exact lt_wr _ _ e he
            · exact lt_wr _ _ e he
    · intro c h
      rcases List.mem_cons.1 h with rfl | h
      · exact okCol_nil
      · rw [List.mem_singleton.1 h]; exact okCol_nil
  | next :: rest, j, cur, l, o, t, P, col => by
    obtain ⟨ih1, ih2⟩ := ok_bodyAll p K D rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D)
    constructor
    · intro r h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · exact okRV_foldRV _ _ _ _ _ r h
        · rcases List.mem_cons.1 h with rfl | h
          · exact okRV_nil _
          · rw [List.mem_singleton.1 h]
            intro g hg
            rw [List.mem_singleton.1 hg]; exact lt_ofE _
      · exact ih1 r h
    · intro c h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · obtain ⟨_, _, rfl⟩ := List.mem_map.1 h
          exact okCol_nil
        · rcases List.mem_cons.1 h with rfl | h
          · exact okCol_sCol _ _ _ _ _ _ _ _ _
          · rw [List.mem_singleton.1 h]; exact okCol_nil
      · exact ih2 c h

variable (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)

theorem okCol_lCol : OkCol (lCol P S X C D) := fun x => lt_firstColW S _ _ _ _ x

theorem ok_linkAll : (∀ r ∈ (linkAll P S t X C D).rs, OkRV r) ∧
    ∀ c ∈ (linkAll P S t X C D).tr, OkCol c := by
  cases hs : (p12Of P).nums.stages with
  | nil =>
    rw [linkAll_nil P S t X C D hs]
    exact ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩
  | cons first rest =>
    obtain ⟨b1, b2⟩ := ok_bodyAll (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6
      (lT P S t X C D) (lPS P S X C D) (lCol P S X C D)
    rw [linkAll_rs P S t X C D first rest hs, linkAll_tr P S t X C D first rest hs]
    constructor
    · intro r h
      rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h
        · unfold lFront at h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact okRV_nil _
          · exact okRV_nil _
          · intro g hg
            rcases List.mem_cons.1 hg with rfl | hg
            · exact lt_ofE _
            · rw [List.mem_singleton.1 hg]; exact lt_ofE _
          · exact okRV_nil _
          · exact okRV_nil _
        · rw [List.mem_singleton.1 h]; exact okRV_nil _
      · exact b1 r h
    · intro c h
      rcases List.mem_append.1 h with h | h
      · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl
        · exact okCol_nil
        · exact okCol_lCol P S X C D
        · exact okCol_nil
        · exact okCol_nil
        · exact okCol_nil
        · exact okCol_nil
      · exact b2 c h

/-- **Every item that linkNext shows passes okGot**, at every round and every history: the premise
hV of okViewW_run (Johnson/Prover/Link/LinkFrameView.lean). -/
theorem linkNext_vals (i : ℕ) (h : List Fmt.Drawn) :
    ∀ g ∈ (linkNext P S t X C i h).vals, okGot g = true := by
  intro g hg
  unfold linkNext at hg
  cases e : (linkAll P S t X C fun j => h.getD j ⟨[], [], [], none⟩).rs[i]? with
  | none => simp only [e] at hg; cases hg
  | some r =>
    simp only [e] at hg
    exact (ok_linkAll P S t X C _).1 r (List.mem_of_getElem? e) g hg

/-- **Every word of every column that linkNext writes is below the prime**, at every round and every
history: the premise hC of okViewW_run (Johnson/Prover/Link/LinkFrameView.lean). -/
theorem linkNext_cols (i : ℕ) (h : List Fmt.Drawn) (n x : ℕ) :
    ∀ w ∈ (linkNext P S t X C i h).col n x, w < fieldPrimeWord := by
  intro w hw
  unfold linkNext at hw
  cases e : (linkAll P S t X C fun j => h.getD j ⟨[], [], [], none⟩).tr[i]? with
  | none => simp only [e] at hw; cases hw
  | some c =>
    simp only [e] at hw
    exact (ok_linkAll P S t X C _).2 c (List.mem_of_getElem? e) x w hw

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.ok_bodyAll
#print axioms Johnson.Prover.Link.ok_linkAll
#print axioms Johnson.Prover.Link.linkNext_vals
#print axioms Johnson.Prover.Link.linkNext_cols
