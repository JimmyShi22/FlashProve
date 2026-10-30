--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeLayRows.lean: "rng.0.rows", THE SUB-PROTOCOL THAT LAYS THE LOOKUPS' ROWS ONTO THE
RANGES' GROUP (`layRows`, Johnson/Desc/Key/Link.lean), ON THE FIRST CHAIN'S SHAPE
(E2E/KeyShapeFirst.lean). Definitions, statements and proofs. NOTHING IS SHOWN OF ANY PROVER.

What is shown.
  `addRows_tidy`: the adding of rows keeps the mark on the statement.
  `standB`, `stand_of_B`: the four clauses of `Stand` (E2E/KeyRowsFit.lean) ARE READ OFF THE SHAPE:
    the group's members and flag, the own message's rows and pad, its two tables' index bits
    (`tableBitsS`, Johnson/Desc/Ground/Shape/More.lean).
  `gLayRows`: the sub-protocol on the shape: it asks the marks tidy and plain, a count of rows for
    each lookup, that the group holds no open row and its test has not begun, and `standB`; then it
    adds as many rows of the kind "plain" as the counts say (`addRowsS`).
  **`layRows_exact`**: where `gLayRows` returns at a state's shape, the sub-protocol's decision
    returns a state of the shape that it returns: so (B1r) and (B2r) hold (`both_of_exact`) WITH NO
    TEST ON VALUES: the five clauses of the adding that read a row's summands (`rowRestB`), two of
    which read values, hold at every `LookupShapedRow` under `Stand` WHATEVER THE COEFFICIENTS ARE
    (`fits_of_plain`).

Limits.
- `gLayRows` asks more than the sub-protocol does (the two marks, `standB`): sufficient, not
  necessary.
- That the mark plain is laid where the rows are written is owed at the sub-protocol behind a
  lookup's rounds: it is not here.
- Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyShapeFirst

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyShape
open OnBytes
open OnBytes.Model (Fork Aff)
open ProofFile.Honest (CarriesR ReturnsR)
open VerifiableInference.Desc (Block named need Key.quietAt)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Ground (addRowP addRowsFrom addRowsP rowL ok)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.First.Shape (LedSh ledSh)
open _root_.Desc.Plain (DState)
open AtPublicFiles.KeyLookup AtPublicFiles.RowsFit

/-! ## 1. The adding of rows keeps the mark on the statement -/

section
variable {L : Type}

theorem addRowsFrom_tidy (g : ℕ) : ∀ (rows : List Row) (d d' : DState L),
    addRowsFrom g rows d = some d' → stTidyB d.st = true → stTidyB d'.st = true
  | [], d, d', h, ht => by
    obtain rfl := Option.some.inj h
    exact ht
  | r :: l, d, d', h, ht => by
    obtain ⟨e, he, h⟩ := Option.bind_eq_some_iff.1 h
    exact addRowsFrom_tidy g l e d' h (addRow_tidy d e g r he ht)

theorem addRows_tidy {d d' : DState L} {g : ℕ} {rows : List Row}
    (h : addRowsP d g rows = some d') (ht : stTidyB d.st = true) : stTidyB d'.st = true := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_tidy g rows d d' h ht
  · cases h

/-! ## 2. `Stand` on the shape -/

/-- The four clauses of `Stand` (E2E/KeyRowsFit.lean), read off the shape. -/
def standB (a : StSh) (g msg B P V : ℕ) : Bool :=
  ((a.groups[g]?).any fun G => G.members == [msg] && !G.inRun) &&
    ((a.oracles[msg]?).any fun x => decide (0 < x.shape.maskRows) &&
      decide (0 < x.shape.mainRows) && x.pad.all fun q => q.1 == Part.mask && decide (P ≤ q.2)) &&
    2 ^ tableBitsS a msg .mask == B && tableBitsS a msg .main == V

theorem stand_of_B {d : DState L} {g msg B P V : ℕ} (h : standB (stSh d.st) g msg B P V = true) :
    Stand d g msg B P V := by
  unfold standB at h
  simp only [Bool.and_eq_true, beq_iff_eq, tableBitsS_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [grp_get] at h1
  rw [orc_get] at h2
  refine ⟨?_, ?_, h3, h4⟩
  · cases hG : d.st.groups[g]? with
    | none => rw [hG] at h1; cases h1
    | some G =>
      rw [hG] at h1
      simp only [Option.map_some, Option.any_some, Bool.and_eq_true, beq_iff_eq,
        Bool.not_eq_true'] at h1
      refine ⟨G, rfl, ?_, h1.2⟩
      have : G.members.toList = [msg] := h1.1
      exact Array.toList_inj.1 this
  · cases hx : d.st.oracles[msg]? with
    | none => rw [hx] at h2; cases h2
    | some x =>
      rw [hx] at h2
      simp only [Option.map_some, Option.any_some, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true, beq_iff_eq] at h2
      exact ⟨x, rfl, h2.1.1, h2.1.2, fun q hq => h2.2 q hq⟩

end

/-! ## 3. "rng.0.rows" -/

variable (Q : Pub1) {Bk : Type} (bk : BackOf → Bk)

/-- "rng.0.rows", on the shape. -/
def gLayRows (a : Sh₁ Bk) : Except String (Sh₁ Bk) :=
  if a.2.tidy && a.2.look.plain && a.2.look.rows.length == (lookupsOf Q.one).length &&
      ((a.1.st.groups[a.2.grp]?).any fun G => G.kinds.isEmpty && !G.inRun) &&
      standB a.1.st a.2.grp (msgOf Q.one) (sizeB Q.one) (padP Q.one) (bitsV Q.one) then
    match addRowsS a.1 a.2.grp (List.replicate a.2.look.rows.sum .plain) with
    | some c => .ok (c, a.2)
    | none => .error "rng.0.rows: a row does not fit the ranges' group"
  else .error "rng.0.rows: a guard on the shape"

theorem kinds_plain {msg B P V : ℕ} : ∀ (rows : List Row), (∀ r ∈ rows, LookupShapedRow msg B P V r) →
    rows.map (·.kind) = List.replicate rows.length .plain
  | [], _ => rfl
  | r :: l, h => by
    rw [List.map_cons, List.length_cons, List.replicate_succ, (h r List.mem_cons_self).kind,
      kinds_plain l fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem layRows_exact (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (s : FirstState)
    (t : Sh₁ Bk) (h : gLayRows Q (sh₁ Q bk s) = .ok t) :
    ∃ s', (layRows Q.one).decide s rs gs = .ok s' ∧ sh₁ Q bk s' = t := by
  unfold gLayRows at h
  split at h
  case isFalse => cases h
  rename_i h0
  simp only [Bool.and_eq_true, beq_iff_eq] at h0
  obtain ⟨⟨⟨⟨ht, hp⟩, hn⟩, hg⟩, hS⟩ := h0
  have ht' : stTidyB s.d.st = true := ht
  have hp' : ∀ r ∈ s.base.rows.flatten,
      LookupShapedRow (msgOf Q.one) (sizeB Q.one) (padP Q.one) (bitsV Q.one) r := fun r hr =>
    plainRowB_iff.1 (List.all_eq_true.1 hp r hr)
  have hn' : s.base.rows.length = (lookupsOf Q.one).length := by
    have : (s.base.rows.map (·.length)).length = _ := hn
    rwa [List.length_map] at this
  have hst : Stand s.d s.grp (msgOf Q.one) (sizeB Q.one) (padP Q.one) (bitsV Q.one) :=
    stand_of_B hS
  have hg' : ((s.d.st.groups[s.grp]?).any fun G => G.rows.isEmpty && !G.inRun) = true := by
    have hg2 : (((stSh s.d.st).groups[s.grp]?).any fun G => G.kinds.isEmpty && !G.inRun) = true :=
      hg
    rw [grp_get] at hg2
    cases hG : s.d.st.groups[s.grp]? with
    | none => rw [hG] at hg2; cases hg2
    | some G =>
      rw [hG] at hg2
      simp only [Option.map_some, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at hg2 ⊢
      refine ⟨?_, hg2.2⟩
      have e : (G.rows.toList.map (·.kind)).isEmpty = true := hg2.1
      rw [List.isEmpty_iff, List.map_eq_nil_iff] at e
      rw [Array.isEmpty_iff]
      exact Array.toList_eq_nil_iff.1 e
  have hlen : (s.base.rows.map (·.length)).sum = s.base.rows.flatten.length :=
    List.length_flatten.symm
  cases e : addRowsS (sh₁ Q bk s).1 (sh₁ Q bk s).2.grp
      (List.replicate (sh₁ Q bk s).2.look.rows.sum .plain) with
  | none => rw [e] at h; cases h
  | some c =>
    rw [e] at h
    obtain rfl := Except.ok.inj h
    have e' : addRowsS (shD s.d) s.grp (s.base.rows.flatten.map (·.kind)) = some c := by
      rw [kinds_plain _ hp', ← hlen]
      exact e
    obtain ⟨d', hd⟩ := addRows_returns s.d s.grp s.base.rows.flatten c e' fun r hr => by
      have := fits_of_plain hst (hp' r hr)
      rw [addRowG_eq, Bool.and_eq_true] at this
      exact this.2
    have c' := addRows_carries s.d d' s.grp s.base.rows.flatten hd
    rw [e'] at c'
    obtain rfl := Option.some.inj c'
    have hdec : (layRows Q.one).decide s rs gs = .ok { s with d := d' } := by
      simp only [layRows, Key.quietAt, hn', hg', hd, named, need, beq_self_eq_true, bind,
        Except.bind, pure, Except.pure, if_true]
    refine ⟨_, hdec, ?_⟩
    unfold sh₁ locSh
    simp only [addRows_tidy hd ht', ht']
    rfl

end AtPublicFiles.KeyShape

#print axioms AtPublicFiles.KeyShape.addRows_tidy
#print axioms AtPublicFiles.KeyShape.stand_of_B
#print axioms AtPublicFiles.KeyShape.layRows_exact
