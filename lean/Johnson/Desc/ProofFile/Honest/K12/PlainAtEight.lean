-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PlainAtEight.lean

What it proves. Each of the eight sub-protocols of the linear claim's shared rounds
(Desc.K14.blocks, Johnson/Desc/K14/Blocks.lean) keeps the mark "no row of the statement has a
written-out factor" (stPlainB, Johnson/Desc/Ground/Shape/Marks.lean), wherever its decision
returns; so does the fold over the eight; and the chain's first state has the mark. So wherever the
fold over the eight returns from the chain's first state, at whatever key, rounds and columns, the
statement behind has the mark. The one premise is that the plan makes its eight
(blocks Q = some bs).

Names.
  sampleRow_plain   a sending's sample row is plain.
  layRows_plain, decideSend_plain   the laying of the sample rows and a sending's decision keep the
      mark.
  PlainStay   the relation: the mark in front gives the mark behind.
  sendAt_plain   a sending at the shared chain's state.
  blocks_plain   each of the eight: its decision keeps the mark.
  fold_plain_eight   the fold over the eight keeps the mark.
  plain_behind_eight   from the chain's first state.

By what. PlainAtSix.lean in this folder for the six that send no oracle message; recv_plain,
admit_plain and start_plain (Marks.lean); the library's foldBlocks_keeps
(Johnson/Desc/FoldKeeps.lean). The library's rule for relations that the ground's functions keep
(GroundQuiet, Johnson/Desc/GroundQuiet.lean; blocks_steps, Johnson/Desc/K14/Quiet.lean) does not
serve here: it speaks of the adding of every row, and a row with a written-out factor breaks the
mark.

Limits.
- Three lemmas have likes in two files of ours that are not in the library and stand over the key
  file's own files: sampleRow_plain (sample_noDense, E2E/KeyRowsNoDense.lean: the same as a Bool),
  layRows_plain (k1rows_plain, E2E/KeyMarksWalk.lean; that file's own layRows_plain is another
  theorem) and decideSend_plain (the same name, there). They are proved here once more so that this
  file stands over the library and PlainAtSix.lean.
- The mark is on the form of rows alone. One direction: from a return to the mark behind.
- Steps of the verifier's: nothing is shown of any prover. Nothing on completeness, on soundness or
  on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlainAtSix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain Desc.K14
open VerifiableInference.Desc VerifiableInference.Desc.Ground VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.Keeps

/-! ## 1 A sending -/

/-- A term without a written-out factor, added to a plain row. -/
theorem add_plain (r : Row) (o : ℕ) (part : Part) (v : Tensor) (hv : v.denseVars = [])
    (h : PlainRow r) : PlainRow (r.add o part v) := by
  refine ⟨fun t ht => ?_, h.2⟩
  have ht' : t ∈ (r.terms.push ⟨o, part, v⟩).toList := ht
  rw [Array.toList_push] at ht'
  rcases List.mem_append.1 ht' with ht' | ht'
  · exact h.1 t ht'
  · rw [List.mem_singleton.1 ht']
    exact hv

/-- A sending's sample row is plain. -/
theorem sampleRow_plain (m : K1.Msg) (o : ℕ) (z : List E) (β : E) (i : ℕ) (y : E) :
    PlainRow (K1.sampleRow m o z β i y) := by
  have key : ∀ (r₀ : Row) (c1 c2 : Prop) [Decidable c1] [Decidable c2] (v1 v2 : Tensor),
      PlainRow r₀ → v1.denseVars = [] → v2.denseVars = [] →
      PlainRow { (if c2 then (if c1 then r₀.add o .main v1 else r₀).add o .mask v2
        else (if c1 then r₀.add o .main v1 else r₀)) with target := y } := by
    intro r₀ c1 c2 _ _ v1 v2 h0 h1 h2
    have k1 : PlainRow (if c1 then r₀.add o .main v1 else r₀) := by
      split
      · exact add_plain _ _ _ _ h1 h0
      · exact h0
    have k2 : PlainRow (if c2 then (if c1 then r₀.add o .main v1 else r₀).add o .mask v2
        else (if c1 then r₀.add o .main v1 else r₀)) := by
      split
      · exact add_plain _ _ _ _ h2 k1
      · exact k1
    exact ⟨k2.1, k2.2⟩
  unfold K1.sampleRow
  refine key _ _ _ _ _ ?_ rfl rfl
  refine foldl_plain _ ?_ _ _ (plainRow_of_empty { kind := .sample } rfl rfl)
  intro r _ hr
  exact ⟨hr.1, hr.2⟩

/-- The laying of the sample rows keeps the mark. -/
theorem layRows_plain {L : Type} {codes : Codes} {seeds : List (List E × E)} :
    ∀ (l : List (ℕ × OracleShape)) (ys : List E) (d d' : DState L),
      K1.layRows codes seeds l ys d = .ok d' → stPlainB d.st = true → stPlainB d'.st = true
  | [], ys, d, d', e, hp => by
    unfold K1.layRows at e
    split at e
    · cases e
      exact hp
    · cases e
  | (o, s) :: l, ys, d, d', e, hp => by
    unfold K1.layRows at e
    split at e
    · exact layRows_plain l ys d d' e hp
    · split at e
      · cases e
      · split at e
        · cases e
        · dsimp only at e
          obtain ⟨d₁, ha, e'⟩ := ebind_ok e
          refine layRows_plain l _ d₁ d' e'
            (admit_plain _ _ _ _ (named_ok ha) hp fun r hr => ?_)
          rw [List.toList_toArray] at hr
          obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
          exact rowPlainB_iff.2 (sampleRow_plain _ _ _ _ _ _)

/-- A sending's decision keeps the mark. -/
theorem decideSend_plain {L : Type} {P : K1.Par} {owed : Option ℕ} {d d' : DState L}
    {rs : List Fmt.RoundView} {ns : Array ℕ} (e : K1.decideSend P owed d rs = .ok (ns, d'))
    (hp : stPlainB d.st = true) : stPlainB d'.st = true := by
  unfold K1.decideSend at e
  split at e
  · obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨x, hx, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨_, -, e⟩ := ebind_ok e
    obtain ⟨d₂, hl, e⟩ := ebind_ok e
    obtain ⟨ns', d₁⟩ := x
    have hr := named_ok hx
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
    exact layRows_plain _ _ d₁ _ hl (recv_plain _ _ _ _ _ hr hp)
  · cases e

/-! ## 2 The eight -/

/-- The mark in front gives the mark behind. -/
def PlainStay (a b : St) : Prop := stPlainB a.st = true → stPlainB b.st = true

/-- A sending at the shared chain's state: its decision keeps the mark, where what the kind notes
behind it leaves the statement. -/
theorem sendAt_plain (P : P14) (n : String) (Q : K1.Par) (inFront : Option Fmt.Entry)
    (groups : List (List ℕ)) (behind : St → Array ℕ → Option St)
    (hb : ∀ d ids d', behind d ids = some d' → d'.st = d.st) :
    Decides PlainStay (sendAt P n Q inFront groups behind) := by
  intro s rs gs s' h hp
  unfold sendAt at h
  dsimp only [Block.inside] at h
  obtain ⟨t, h0, h1⟩ := ebind_ok h
  obtain ⟨t', h2, h3⟩ := ebind_ok h1
  cases h0
  have h2' : (K1.decideSend Q none
      ({ st := s.st, book := s.book, roots := s.roots, opened := s.opened, loc := #[] } :
        DState (Array ℕ)) rs).map
      (fun x => ({ owed := none, held := { x.2 with loc := x.1 } } :
        K1.Owing (DState (Array ℕ)))) = .ok t' := h2
  obtain ⟨x, k1, k2⟩ := emap_ok h2'
  subst k2
  rw [hb _ _ _ (named_ok h3)]
  exact decideSend_plain (ns := x.1) (d' := x.2) k1 hp

/-- **Each of the eight: its decision keeps the mark.** -/
theorem blocks_plain (P : P14) (l : List (Block St Unit)) (h : blocks P = some l) :
    ∀ b ∈ l, Decides PlainStay b := by
  unfold blocks at h
  dsimp only at h
  obtain ⟨w, _, h⟩ := obind_ok h
  cases h
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun d rs _ d' hd => linPoint_plain _ d d' rs (why_some hd)
  · exact sendAt_plain _ _ _ _ _ _ fun d ids d' k => behindU_st _ d d' ids k
  · exact fun d rs _ d' hd => laysRec_plain _ d d' rs (why_some hd)
  · exact fun d rs gs d' hd => loc_plain _ d d' rs gs (why_some hd)
  · exact sendAt_plain _ _ _ _ _ _ fun d ids d' k => behindOmega_st _ d d' ids k
  · exact fun d rs _ d' hd => joins_plain _ d d' rs (why_some hd)
  · exact fun d rs _ d' hd => linZeta_plain d d' rs (why_some hd)
  · exact fun d rs _ d' hd => split_plain _ d d' rs (why_some hd)

/-- **The fold over the eight keeps the mark.** -/
theorem fold_plain_eight (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs) (ft : ℕ)
    (s : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs s rs cols = .ok r) (hp : stPlainB s.st = true) :
    stPlainB r.1.st = true :=
  foldBlocks_keeps PlainStay (fun _ x => x) (fun _ _ _ x y z => y (x z)) ft bs
    (blocks_plain Q bs hb) s rs cols r h hp

/-- **From the chain's first state**, at whatever key, rounds and columns. -/
theorem plain_behind_eight (Q : P14) (bs : List (Block St Unit)) (hb : blocks Q = some bs)
    (ft : ℕ) (key : TableKey) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (r : St × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft bs (first Q.codes key) rs cols = .ok r) : stPlainB r.1.st = true :=
  fold_plain_eight Q bs hb ft _ rs cols r h (start_plain Q.codes)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.add_plain
#print axioms ProofFile.Honest.K12.Light.sampleRow_plain
#print axioms ProofFile.Honest.K12.Light.layRows_plain
#print axioms ProofFile.Honest.K12.Light.decideSend_plain
#print axioms ProofFile.Honest.K12.Light.PlainStay
#print axioms ProofFile.Honest.K12.Light.sendAt_plain
#print axioms ProofFile.Honest.K12.Light.blocks_plain
#print axioms ProofFile.Honest.K12.Light.fold_plain_eight
#print axioms ProofFile.Honest.K12.Light.plain_behind_eight
