-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Say.lean: kind K5: what the claims say, member by member. The written
lists Fo.claim3T … Fo.claim8T at a plain record h, read in a world W under a reading ρ: "every form
of the list is worth 0" holds if and only if a written conjunction holds, in three groups: the rows
that the sumchecks leave; the end values' claims, as equations "the slot's worth = a written
reader's form's worth"; the linear claims on the other named scalars. First part: the tools, claims
3 and 4.

Main names:
  `AllZero ρ W l`: every member of l is worth 0.
  `PlanesSay`, `UnitAt`, `UnitSay`, `Say3`, `Say4`, with `say3`, `say4`: AllZero (Fo.claim3T h K) ↔
    Say3, and so on.
  `endsU h K k tb j`: the reader's form under a softmax-table unit's end value number j: 2 b: the
    query's head (readHead tQ atQ); 2 b + 1: the key's group (readGroup tK atK), at piece b's layer
    and head.
Used of OnBytes: plain records, pure functions and lemmas on them alone; no routine in a context and
no theorem on a run: the records that Johnson/Desc/First/Att/Claims/Top.lean names; Reading, World,
Aff.value with its lemmas value_slot, value_sub, value_add, value_scale, value_ofConst, value_addMul
(OnBytes/Model/HideLaws.lean); the written forms and lists Fo.…F and Fo.…T; Fo.planeMember.
Not claimed: that a claim holds; what an entry of a table means.

Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Model.HideLaws
import Johnson.Desc.First.Att.Claims.AnySeat

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention

variable {Kf : Type} [CommRing Kf] (ρ : Reading Kf) (W : World Kf)

/-- Every member is worth 0. -/
def AllZero (l : List Aff) : Prop := ∀ f ∈ l, f.value ρ W = 0

theorem allZero_nil : AllZero ρ W [] ↔ True := ⟨fun _ => trivial, fun _ _ h => by cases h⟩

theorem allZero_append (l m : List Aff) : AllZero ρ W (l ++ m) ↔ AllZero ρ W l ∧ AllZero ρ W m := by
  unfold AllZero
  simp only [List.mem_append]
  exact ⟨fun h => ⟨fun f hf => h f (.inl hf), fun f hf => h f (.inr hf)⟩,
    fun h f hf => hf.elim (h.1 f) (h.2 f)⟩

theorem allZero_single (f : Aff) : AllZero ρ W [f] ↔ f.value ρ W = 0 := by
  unfold AllZero
  simp only [List.mem_singleton, forall_eq]

theorem allZero_flatMap {α : Type} (xs : List α) (g : α → List Aff) :
    AllZero ρ W (xs.flatMap g) ↔ ∀ x ∈ xs, AllZero ρ W (g x) := by
  unfold AllZero
  simp only [List.mem_flatMap]
  exact ⟨fun h x hx f hf => h f ⟨x, hx, hf⟩, fun h f ⟨x, hx, hf⟩ => h x hx f hf⟩

theorem allZero_ite (c : Bool) (l : List Aff) :
    AllZero ρ W (if c = true then l ++ [] else []) ↔ (c = true → AllZero ρ W l) := by
  cases c
  · simp [allZero_nil]
  · simp

/-- A claim "slot − form". -/
theorem slot_sub (s : ℕ) (f : Aff) : (Aff.slot s - f).value ρ W = 0 ↔ W.slot s = f.value ρ W := by
  rw [Aff.value_sub, Aff.value_slot, sub_eq_zero]

/-- Over an array with its numbers. -/
theorem forall_zipIdx {α : Type} [Inhabited α] (v : Array α) (P : ℕ → α → Prop) :
    (∀ x ∈ v.toList.zipIdx, P x.2 x.1) ↔ ∀ b < v.size, P b (v.getD b default) := by
  constructor
  · intro h b hb
    have e : v.getD b default = v[b] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb]
      rfl
    rw [e]
    refine h (v[b], b) ?_
    rw [List.mem_zipIdx_iff_getElem?]
    simp [hb]
  · intro h x hx
    rw [List.mem_zipIdx_iff_getElem?] at hx
    simp only [Array.getElem?_toList] at hx
    obtain ⟨hb, e⟩ := Array.getElem?_eq_some_iff.1 hx
    have := h x.2 hb
    rw [Array.getD_eq_getD_getElem?, hx] at this
    exact this

/-- Pairs of places. -/
theorem forall_pairs (n : ℕ) (C : ℕ → Prop) :
    (∀ b < n, C (2 * b) ∧ C (2 * b + 1)) ↔ ∀ j < 2 * n, C j := by
  constructor
  · intro h j hj
    rcases Nat.even_or_odd' j with ⟨b, rfl | rfl⟩
    · exact (h b (by omega)).1
    · exact (h b (by omega)).2
  · intro h b hb
    exact ⟨h _ (by omega), h _ (by omega)⟩

variable (h : Attention.Heard) (K : ℕ)

/-! ### claim 3 -/

/-- Each plane value of a plane claim is the pieces' weighted sum of the plane's forms. -/
def PlanesSay (pc : PlaneClaim) : Prop := ∀ y < pc.np, (Fo.planeMember h K pc y).value ρ W = 0

theorem linPlanes_say (pc : PlaneClaim) : AllZero ρ W (Fo.linPlanesT h K pc) ↔ PlanesSay ρ W h K pc := by
  unfold Fo.linPlanesT PlanesSay Fo.planeMember
  simp only [allZero_flatMap, allZero_single, List.mem_range]

def Say3 : Prop :=
  ∀ x ∈ h.S.calls.toList.zipIdx, (x.1.kind == Table.kr) = true →
    ∀ pc ∈ h.planes.toList, (pc.call == x.2) = true → PlanesSay ρ W h K pc

theorem say3 : AllZero ρ W (Fo.claim3T h K) ↔ Say3 ρ W h K := by
  unfold Fo.claim3T Fo.callKRT Say3
  simp only [allZero_flatMap, allZero_ite, linPlanes_say]

/-! ### claim 4 -/

/-- The reader's form under a softmax-table unit's end value number j. -/
def endsU (k : Score) (tb : ScoreTables) (j : ℕ) : Aff :=
  if j % 2 = 0 then
    Fo.readHeadT h K tb.tQ h.S.atQ k.sc.r (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size)
      (k.pw.getD (j / 2) default).lam (k.pw.getD (j / 2) default).a
  else
    Fo.readGroupT h K tb.tK h.S.atK k.sc.r (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size)
      (k.pw.getD (j / 2) default).lam

/-- What a softmax-table unit's claims say, where its tables and its plane claim are there. -/
structure UnitAt (k : Score) (tb : ScoreTables) (pc : PlaneClaim) : Prop where
  planes : PlanesSay ρ W h K pc
  maximum : (Fo.lessF (Aff.slot (k.s0 + 5)) k.pw fun w =>
    Fo.readMaximumF h K tb.tM k.zg w.lam w.a).value ρ W = 0
  row : k.sc.rowU.value ρ W = 0
  ends : ∀ j < 2 * k.pw.size, W.slot (k.sc.sEnd + j) = (endsU h K k tb j).value ρ W

def UnitSay (n : ℕ) (k : Score) : Prop :=
  ∀ tb pc, h.t.score[n]? = some tb → h.planes[k.claim]? = some pc → UnitAt ρ W h K k tb pc

theorem unit_say (n : ℕ) (k : Score) : AllZero ρ W (Fo.unitKFDT h K n k) ↔ UnitSay ρ W h K n k := by
  unfold Fo.unitKFDT UnitSay
  cases h.t.score[n]? with
  | none => simp [allZero_nil]
  | some tb =>
    cases h.planes[k.claim]? with
    | none => simp [allZero_nil]
    | some pc =>
      simp only [Option.some.injEq]
      simp only [allZero_append, allZero_single, allZero_flatMap, linPlanes_say, Fo.endValuesT]
      rw [forall_zipIdx k.pw (fun b w =>
        (sc3A k.sc b - Fo.readHeadT h K tb.tQ h.S.atQ k.sc.r
          (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) w.lam w.a).value ρ W = 0 ∧
        (sc3B k.sc b - Fo.readGroupT h K tb.tK h.S.atK k.sc.r
          (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) w.lam).value ρ W = 0)]
      have e : (∀ b < k.pw.size,
          (sc3A k.sc b - Fo.readHeadT h K tb.tQ h.S.atQ k.sc.r
            (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) (k.pw.getD b default).lam
            (k.pw.getD b default).a).value ρ W = 0 ∧
          (sc3B k.sc b - Fo.readGroupT h K tb.tK h.S.atK k.sc.r
            (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size)
            (k.pw.getD b default).lam).value ρ W = 0) ↔
          ∀ j < 2 * k.pw.size, W.slot (k.sc.sEnd + j) = (endsU h K k tb j).value ρ W := by
        rw [← forall_pairs]
        refine forall₂_congr fun b _ => and_congr ?_ ?_
        · unfold sc3A endsU
          rw [slot_sub, if_pos (by omega), show 2 * b / 2 = b by omega]
        · unfold sc3B endsU
          rw [slot_sub, if_neg (by omega), show (2 * b + 1) / 2 = b by omega]
      rw [e]
      constructor
      · rintro ⟨a, b, c, d⟩ _ _ rfl rfl
        exact ⟨a, b, c, d⟩
      · intro H
        obtain ⟨a, b, c, d⟩ := H tb pc rfl rfl
        exact ⟨a, b, c, d⟩

def Say4 : Prop :=
  ∀ x ∈ h.S.calls.toList.zipIdx, (x.1.kind == Table.kfd) = true →
    ∀ y ∈ h.scores.toList.zipIdx, (y.1.call == x.2) = true → UnitSay ρ W h K y.2 y.1

theorem say4 : AllZero ρ W (Fo.claim4T h K) ↔ Say4 ρ W h K := by
  unfold Fo.claim4T Fo.callKFDT Say4
  simp only [allZero_flatMap, allZero_ite, unit_say]

end K5Law
