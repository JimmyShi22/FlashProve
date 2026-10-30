-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Reveal.lean: WHAT A REVEAL DOES IN THE MODE IN WHICH MARKED EVALUATIONS ARE
DEFERRED, as a function on states; a list of reveals; the reveal of one leaf's two tokens. General
in the family of oracles, but for the last section.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

  relL d ts, revI d ts   The entries that a reveal of ts writes (those of the evaluations that are
        not released and are charged to a shown token, in their order); the state after it.
        run_reveal: that is the run in mode I (Rom/Defer.lean), by release_lay
        (Compile/DeferRun/Proof.lean).
  What a reveal leaves alone: the store, the evaluations as entries, the count of ordinary queries,
        for each token the evaluations that are charged to it (as entries).
  Laid.revI   After a reveal the point of each released evaluation has an entry in the table.
  relL_shown  A reveal of tokens that are all shown already writes nothing, in a well-formed state.
  LeafChunk d ts en, lay_chunk   ts are two tokens; just one evaluation is charged to the first, and
        as an entry it is en; none is charged to the second; ts can be revealed. Then the reveal of
        ts does to the table what writing en (where there is no entry) does: if the evaluation was
        released before, its point has an entry and neither side moves.
  revAll, revAll_chunks   Reveals in turn: the table after the reveals of such chunks is the table
        with their entries written in turn.

-/
import Johnson.TokenRel.Trees
import Compile.DeferRun.Proof
import Rom.Handle.Laws

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRel
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRules
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1 val_of_prefix val_afterFresh markDue markDue_charged markDue_released markDue_point
    releaseAll_fst)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

section Generic
variable {S : OSpec} {sp : Split S} {Rl : Rules S} {α : Type}

/-! ## Tables -/

theorem lay_ne_none {T : Table S} {o : S.ι} {q : S.Dom o} (h : T o q ≠ none) (l : Trace S) :
    T.lay l o q ≠ none := by
  cases hT : T o q with
  | none => exact absurd hT h
  | some r => rw [Table.lay_of_some l hT]; exact fun h' => nomatch h'

theorem lay1_self_ne_none (T : Table S) (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    T.lay1 o q r o q ≠ none := by
  cases hT : T o q with
  | none =>
      rw [Table.lay1_of_none hT]
      simp [Table.set]
  | some r' =>
      rw [Table.lay1_of_some hT, hT]
      exact fun h' => nomatch h'

/-- After a log is written each of its points has an entry. -/
theorem lay_mem_ne_none : ∀ (l : Trace S) (T : Table S) (en : QA S), en ∈ l →
    T.lay l en.1 en.2.1 ≠ none
  | e :: l, T, en, h => by
      rw [Table.lay_cons]
      rcases List.mem_cons.mp h with rfl | h
      · exact lay_ne_none (lay1_self_ne_none T _ _ _) l
      · exact lay_mem_ne_none l _ en h

/-- Writing an entry at a point that has one is no move. -/
theorem lay_one_of_ne_none {T : Table S} {en : QA S} (h : T en.1 en.2.1 ≠ none) :
    T.lay [en] = T := by
  cases hT : T en.1 en.2.1 with
  | none => exact absurd hT h
  | some r => rw [Table.lay_cons, Table.lay1_of_some hT, Table.lay_nil]

/-! ## One reveal -/

/-- the entries that a reveal of ts writes in mode I, where the table has no entry -/
def relL (d : DSt S) (ts : List Tok) : Trace S :=
  (d.evs.filter fun e => !e.released && (d.shown ++ ts).contains e.charged).map qa

/-- the state after a reveal of ts in mode I -/
def revI (d : DSt S) (ts : List Tok) : DSt S := afterReveal d ts (d.table.lay (relL d ts))

theorem run_reveal (ts : List Tok) (k : List Bits → Step S sp α) (d : DSt S) :
    (Step.reveal ts k).run true d = (k (ts.map d.val)).run true (revI d ts) := by
  rw [Step.run]
  simp only [releaseAll_fst, DeferRun.release_lay S (d.shown ++ ts) d.evs d.table]
  rfl

theorem qa_markDue (sh : List Tok) (e : Ev S) : qa (markDue sh e) = qa e := by
  unfold markDue
  split <;> rfl

theorem revI_evs_qa (d : DSt S) (ts : List Tok) : (revI d ts).evs.map qa = d.evs.map qa := by
  show (d.evs.map (markDue (d.shown ++ ts))).map qa = _
  rw [List.map_map]
  exact List.map_congr_left fun e _ => qa_markDue _ e

theorem revI_filter (d : DSt S) (ts : List Tok) (s : Tok) :
    ((revI d ts).evs.filter fun e => e.charged == s) =
      (d.evs.filter fun e => e.charged == s).map (markDue (d.shown ++ ts)) := by
  show ((d.evs.map (markDue (d.shown ++ ts))).filter fun e => e.charged == s) = _
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun e _ => by simp [markDue_charged]

theorem revI_filter_qa (d : DSt S) (ts : List Tok) (s : Tok) :
    ((revI d ts).evs.filter fun e => e.charged == s).map qa =
      (d.evs.filter fun e => e.charged == s).map qa := by
  rw [revI_filter, List.map_map]
  exact List.map_congr_left fun e _ => qa_markDue _ e

theorem Laid.revI {d : DSt S} (h : Laid d) (ts : List Tok) : Laid (revI d ts) := by
  intro e' he' hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (show e' ∈ d.evs.map (markDue (d.shown ++ ts)) from he')
  refine (markDue_point _ e fun o q => (d.table.lay (relL d ts)) o q ≠ none).mpr ?_
  by_cases hre : e.released = true
  · exact lay_ne_none (h e he hre) _
  · have hc : e.charged ∈ d.shown ++ ts := ((markDue_released _ e).mp hr).resolve_left hre
    exact lay_mem_ne_none _ _ (qa e) (List.mem_map_of_mem (List.mem_filter.mpr ⟨he, by
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem]
      exact ⟨by simpa using hre, hc⟩⟩))

/-- In a well-formed state an evaluation that is not released is charged to no shown token. -/
theorem relL_eq {d : DSt S} (hd : TidyO Rl d) (ts : List Tok) :
    relL d ts = (d.evs.filter fun e => !e.released && ts.contains e.charged).map qa := by
  unfold relL
  congr 1
  refine List.filter_congr fun e he => ?_
  by_cases hr : e.released = true
  · simp [hr]
  · have hs : e.charged ∉ d.shown := fun h => hr (hd.released e he h)
    simp [hs]

/-- A reveal of tokens that are all shown writes nothing. -/
theorem relL_shown {d : DSt S} (hd : TidyO Rl d) {ts : List Tok} (h : ∀ u ∈ ts, u ∈ d.shown) :
    relL d ts = [] := by
  rw [relL_eq hd, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro e he hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hc
  have := hd.released e he (h _ hc.2)
  rw [hc.1] at this
  exact nomatch this

theorem closedO_shown {d : DSt S} (hd : TidyO Rl d) {ts : List Tok} (h : ∀ u ∈ ts, u ∈ d.shown) :
    ClosedO d ts where
  lt := fun t ht => hd.shown_lt t (h t ht)
  tail := fun e he hc => Or.inr (hd.closed_tail e he (hd.released e he (h _ hc)))
  others := fun e he hc u hu => Or.inr (hd.closed_others e he (hd.released e he (h _ hc)) u hu)

theorem ClosedO.revI {d : DSt S} {ts : List Tok} (h : ClosedO d ts) (ts' : List Tok) :
    ClosedO (revI d ts') ts :=
  h.grows (GrowsO.ofReveal (Ch := noTok) (e := zr) (M := zr) d ts' _) fun _ _ h => h

/-! ## The two tokens of a leaf -/

/-- See the head. -/
def LeafChunk (d : DSt S) (ts : List Tok) (en : QA S) : Prop :=
  ClosedO d ts ∧ ∃ s e, ts = [s, e] ∧ (d.evs.filter fun x => x.charged == s).map qa = [en] ∧
    (d.evs.filter fun x => x.charged == e) = []

theorem LeafChunk.revI {d : DSt S} {ts : List Tok} {en : QA S} (h : LeafChunk d ts en)
    (ts' : List Tok) : LeafChunk (revI d ts') ts en := by
  obtain ⟨hc, s, e, rfl, h1, h2⟩ := h
  exact ⟨ClosedO.revI hc ts', s, e, rfl, by rw [revI_filter_qa]; exact h1,
    by rw [revI_filter, h2]; rfl⟩

theorem lay_chunk {d : DSt S} (hd : TidyO Rl d) (hl : Laid d) {ts : List Tok} {en : QA S}
    (h : LeafChunk d ts en) : d.table.lay (relL d ts) = d.table.lay [en] := by
  obtain ⟨_, s, e, rfl, h1, h2⟩ := h
  have hne : ∀ x ∈ d.evs, x.charged ≠ e := fun x hx hc =>
    (List.filter_eq_nil_iff.mp h2) x hx (by simpa using hc)
  have hf : (d.evs.filter fun x => !x.released && [s, e].contains x.charged) =
      (d.evs.filter fun x => x.charged == s).filter fun x => !x.released := by
    rw [List.filter_filter]
    refine List.filter_congr fun x hx => ?_
    have := hne x hx
    by_cases hs : x.charged = s <;> simp [hs, this]
  rw [relL_eq hd, hf]
  obtain ⟨x₀, hx₀, hq⟩ : ∃ x₀, (d.evs.filter fun x => x.charged == s) = [x₀] ∧ qa x₀ = en := by
    cases hL : (d.evs.filter fun x => x.charged == s) with
    | nil => rw [hL] at h1; exact nomatch h1
    | cons x₀ l =>
        rw [hL] at h1
        cases l with
        | nil => exact ⟨x₀, rfl, (List.cons.inj h1).1⟩
        | cons _ _ => exact nomatch (List.cons.inj h1).2
  rw [hx₀]
  have hm : x₀ ∈ d.evs := (List.mem_filter.mp (hx₀ ▸ List.mem_singleton.mpr rfl :
    x₀ ∈ d.evs.filter fun x => x.charged == s)).1
  by_cases hr : x₀.released = true
  · rw [List.filter_cons_of_neg (by simp [hr]), List.filter_nil, List.map_nil, Table.lay_nil,
      ← hq]
    exact (lay_one_of_ne_none (en := qa x₀) (hl x₀ hm hr)).symm
  · rw [List.filter_cons_of_pos (by simpa using hr), List.filter_nil, List.map_cons, List.map_nil,
      hq]

/-! ## Reveals in turn -/

/-- the state after the reveals of the lists of l, in turn, in mode I -/
def revAll : List (List Tok) → DSt S → DSt S
  | [], d => d
  | ts :: l, d => revAll l (revI d ts)

theorem revAll_vals : ∀ (l : List (List Tok)) (d : DSt S), (revAll l d).vals = d.vals
  | [], _ => rfl
  | _ :: l, _ => revAll_vals l _

theorem revAll_nPlain : ∀ (l : List (List Tok)) (d : DSt S), (revAll l d).nPlain = d.nPlain
  | [], _ => rfl
  | _ :: l, _ => revAll_nPlain l _

theorem revAll_evs_qa : ∀ (l : List (List Tok)) (d : DSt S),
    (revAll l d).evs.map qa = d.evs.map qa
  | [], _ => rfl
  | ts :: l, d => (revAll_evs_qa l _).trans (revI_evs_qa d ts)

theorem revAll_shown : ∀ (l : List (List Tok)) (d : DSt S),
    (revAll l d).shown = d.shown ++ l.flatten
  | [], d => (List.append_nil _).symm
  | ts :: l, d => by
      rw [revAll, revAll_shown l, List.flatten_cons, ← List.append_assoc]
      rfl

theorem revAll_filter_qa : ∀ (l : List (List Tok)) (d : DSt S) (s : Tok),
    ((revAll l d).evs.filter fun e => e.charged == s).map qa =
      (d.evs.filter fun e => e.charged == s).map qa
  | [], _, _ => rfl
  | ts :: l, d, s => (revAll_filter_qa l _ s).trans (revI_filter_qa d ts s)

theorem Laid.revAll : ∀ (l : List (List Tok)) {d : DSt S}, Laid d → Laid (revAll l d)
  | [], _, h => h
  | ts :: l, _, h => Laid.revAll l (Laid.revI h ts)

/-- **The reveals of leaves' tokens, in turn, write the leaves' entries, in turn.** -/
theorem revAll_chunks : ∀ (cs : List (List Tok)) (ens : Trace S) (d : DSt S), TidyO Rl d → Laid d →
    List.Forall₂ (LeafChunk d) cs ens →
    (revAll cs d).table = d.table.lay ens ∧ TidyO Rl (revAll cs d)
  | [], [], d, hd, _, _ => ⟨rfl, hd⟩
  | ts :: cs, en :: ens, d, hd, hl, h => by
      obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
      obtain ⟨a, b⟩ := revAll_chunks cs ens (revI d ts) (hd.reveal h1.1 _) (Laid.revI hl ts)
        (h2.imp fun _ _ hc => hc.revI ts)
      refine ⟨?_, b⟩
      rw [revAll, a]
      show (d.table.lay (relL d ts)).lay ens = _
      rw [lay_chunk hd hl h1]
      rfl
  | [], _ :: _, _, _, _, h => nomatch h
  | _ :: _, [], _, _, _, h => nomatch h

end Generic

/-! ## At the token programs -/

section Twin
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

theorem run_revealsT : ∀ (l : List (List Tok)) (d : DSt (typedOracleFamily lam K L)),
    (revealsT (K := K) (L := L) l).run true d = PMF.pure ((), revAll l d)
  | [], _ => rfl
  | ts :: l, d => by
      rw [revealsT, run_reveal]
      exact run_revealsT l _

theorem LeafAt.revAll (l : List (List Tok)) {d : DSt (typedOracleFamily lam K L)} {T : TreeT lam L} {pv : Bits}
    (h : LeafAt d T pv) : LeafAt (revAll l d) T pv := by
  have hval : (OnBytes.TokenRel.revAll l d).val = d.val := by
    funext t
    unfold DSt.val
    rw [revAll_vals]
  refine ⟨h.1, fun j a hj => ⟨?_, ?_⟩⟩
  · rw [revAll_filter_qa, hval]
    exact (h.2 j a hj).1
  · have := revAll_filter_qa l d a.2
    rw [(h.2 j a hj).2] at this
    exact List.map_eq_nil_iff.mp this

end Twin

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.run_reveal
#print axioms OnBytes.TokenRel.lay_chunk
#print axioms OnBytes.TokenRel.revAll_chunks
