-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadTabsBelow.lean: the tables that the description's text makes for the
output head lie in the vector of reads, on matrices of the plan, and end at or below the plan's
number of reads.

The smallness test's sentence on the reads speaks of the entries that the closed list's tables name.
To spell it as the law of the reads (Fo.ReadsAll) one needs that every table's matrix is one of the
plan's and that every entry that a table names lies below the width of the array of the reads. The
layers' form of these two: Johnson/Meaning/ReadsPlan.lean (k4_mats_below) and
Johnson/Meaning/ReadsK4.lean (k4_entries_below, k4_places_below).

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  Below mats B t: every table of t lies in the vector of reads (tree = 2), on a matrix below number
      B, and ends at or below t.p, the length of the vector so far.
  partStart_le, below_step, below_fold: one ask, and a list of asks, keep Below.
  tables_below: after a yes of K8.ReadsQuiet.tables: Below at the plan's matrices and B = NHf + 4,
      and t.p is the plan's number of reads.
  step_grows, fold_le, fold_grows, tables_pos: an ask lengthens the vector; so after a yes the
      plan's number of reads is not 0.
  k6_mats_below, k6_entries_below, k6_places_below: the three facts in the letters of a record tl of
      the smallness test that has the plan's matrices and these tables.

Premises. hK: the plan's number of reads is at most K3, the width at which the law of the reads is
asked. hNM: the record has NHf + 4 matrices at least. Both are on public numbers; neither is shown
here.
Limits. Numbers of entries alone: nothing on what an entry is worth. That no entry lies in two
tables is not stated. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.HeadPlanesHost
import OnBytes.Tie.Pv.Tail.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law
open OnBytes OnBytes.Model Fo
open VerifiableInference.Desc.K8

/-- Every table lies in the vector of reads, on a matrix below number B, and ends at or below the
length of the vector so far. -/
def Below (mats : Array TMat) (B : Nat) (t : Model.Head.Tables) : Prop :=
  ∀ f ∈ t.funs.toList, f.tree = 2 ∧ f.mat < B ∧ f.start + partLen mats f.len f.mat ≤ t.p

/-- The parts of a table begin one behind the other. -/
theorem partStart_le (mats : Array TMat) (M0 Lf p0 p n : Nat) (h : p ≤ n) :
    partStart mats M0 Lf p0 p ≤ partStart mats M0 Lf p0 n := by
  induction n with
  | zero =>
    obtain rfl : p = 0 := Nat.le_zero.mp h
    exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.lt_or_ge p (n + 1) with h1 | h1
    · have e : partStart mats M0 Lf p0 (n + 1) =
          partStart mats M0 Lf p0 n + partLen mats Lf (M0 + n) := rfl
      rw [e]
      exact (ih (Nat.lt_succ_iff.mp h1)).trans (Nat.le_add_right _ _)
    · obtain rfl : p = n + 1 := Nat.le_antisymm h h1
      exact Nat.le_refl _

/-- One ask keeps it. -/
theorem below_step {mats : Array TMat} {B : Nat} {t t' : Model.Head.Tables} {a : Ask}
    (h : askStep mats t a = some t') (ha : a.1 + a.2.1 ≤ B) (Z : Below mats B t) :
    Below mats B t' := by
  obtain ⟨_, e2, e3⟩ := addFun_ok h
  intro f hf
  rw [e2, Array.toList_append, List.mem_append] at hf
  rcases hf with hf | hf
  · obtain ⟨z0, z1, z2⟩ := Z f hf
    refine ⟨z0, z1, z2.trans ?_⟩
    rw [e3]
    exact partStart_le mats a.1 a.2.2.1 t.p 0 a.2.1 (Nat.zero_le _)
  · have hf' : f ∈ (List.range a.2.1).map (partRec mats a.1 a.2.2.1 t.p a.2.2.2.1) := hf
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf'
    have hp' : p < a.2.1 := List.mem_range.mp hp
    refine ⟨rfl, ?_, ?_⟩
    · show a.1 + p < B
      omega
    · show partStart mats a.1 a.2.2.1 t.p (p + 1) ≤ t'.p
      rw [e3]
      exact partStart_le mats a.1 a.2.2.1 t.p (p + 1) a.2.1 hp'

/-- A list of asks keeps it. -/
theorem below_fold (mats : Array TMat) (B : Nat) :
    ∀ (l : List Ask) (t t' : Model.Head.Tables), l.foldlM (askStep mats) t = some t' →
      (∀ a ∈ l, a.1 + a.2.1 ≤ B) → Below mats B t → Below mats B t'
  | [], t, t', h, _, Z => by
    obtain rfl : t = t' := Option.some.inj h
    exact Z
  | a :: l, t, t', h, ha, Z => by
    rw [List.foldlM_cons] at h
    cases h1 : askStep mats t a with
    | none =>
      rw [h1] at h
      exact absurd h (by simp)
    | some t1 =>
      rw [h1] at h
      exact below_fold mats B l t1 t' h (fun b hb => ha b (List.mem_cons_of_mem _ hb))
        (below_step h1 (ha a (by simp)) Z)

/-- One ask lengthens the vector: an empty table is refused. -/
theorem step_grows {mats : Array TMat} {t t' : Model.Head.Tables} {a : Ask}
    (h : askStep mats t a = some t') : t.p < t'.p := by
  unfold askStep Model.Head.addFun at h
  rw [addFun_fold] at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i hn
    have e := Option.some.inj h
    rw [← e]
    show t.p < partStart mats a.1 a.2.2.1 t.p a.2.1
    have hle : t.p ≤ partStart mats a.1 a.2.2.1 t.p a.2.1 :=
      partStart_le mats a.1 a.2.2.1 t.p 0 a.2.1 (Nat.zero_le _)
    have hne : partStart mats a.1 a.2.2.1 t.p a.2.1 ≠ t.p := by simpa using hn
    omega

/-- A list of asks does not shorten it; a list with a member lengthens it. -/
theorem fold_le (mats : Array TMat) :
    ∀ (l : List Ask) (t t' : Model.Head.Tables), l.foldlM (askStep mats) t = some t' → t.p ≤ t'.p
  | [], t, t', h => by
    obtain rfl : t = t' := Option.some.inj h
    exact Nat.le_refl _
  | a :: l, t, t', h => by
    rw [List.foldlM_cons] at h
    cases h1 : askStep mats t a with
    | none =>
      rw [h1] at h
      exact absurd h (by simp)
    | some t1 =>
      rw [h1] at h
      exact (Nat.le_of_lt (step_grows h1)).trans (fold_le mats l t1 t' h)

@[inherit_doc fold_le] theorem fold_grows (mats : Array TMat) (a : Ask) (l : List Ask)
    (t t' : Model.Head.Tables) (h : (a :: l).foldlM (askStep mats) t = some t') : t.p < t'.p := by
  rw [List.foldlM_cons] at h
  cases h1 : askStep mats t a with
  | none =>
    rw [h1] at h
    exact absurd h (by simp)
  | some t1 =>
    rw [h1] at h
    exact Nat.lt_of_lt_of_le (step_grows h1) (fold_le mats l t1 t' h)

/-- **After a yes of the head's tables**: all lie in the vector of reads, on the plan's first
NHf + 4 matrices, and end at or below the plan's number of reads. -/
theorem tables_below {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    Below hp.tl.mats (h.NHf + 4) t ∧ t.p = hp.nU.getD 2 0 := by
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, _, _, _, _, _, _, ea⟩ := tables_asks e
  refine ⟨below_fold hp.tl.mats (h.NHf + 4) _ {} t ea (fun a ha => ?_)
    (fun f hf => absurd hf (by simp)), beq_iff_eq.mp (ReadsQuiet.tables_ok e).2⟩
  simp only [asksH, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> (dsimp only; omega)

section
variable {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
  {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}

/-- After a yes of the head's tables the plan's number of reads is not 0. -/
theorem tables_pos (e : ReadsQuiet.tables h L hp cov x = .ok t) : 0 < hp.nU.getD 2 0 := by
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, _, _, _, _, _, _, ea⟩ := tables_asks e
  rw [← (tables_below e).2]
  exact fold_grows hp.tl.mats _ _ {} t ea

/-- Every table's matrix is one of the record's. -/
theorem k6_mats_below (e : ReadsQuiet.tables h L hp cov x = .ok t) (tl : HTailF2)
    (hfun : tl.funs = t.funs) (hNM : h.NHf + 4 ≤ tl.NM) :
    ∀ f ∈ tl.funs.toList, f.mat < tl.NM := by
  intro f hf
  rw [hfun] at hf
  exact Nat.lt_of_lt_of_le ((tables_below e).1 f hf).2.1 hNM

/-- Every entry of a table lies below K3. -/
theorem k6_entries_below (e : ReadsQuiet.tables h L hp cov x = .ok t) (tl : HTailF2)
    (hfun : tl.funs = t.funs) (hmat : tl.mats = hp.tl.mats) {K3 : Nat}
    (hK : hp.nU.getD 2 0 ≤ K3) :
    ∀ f ∈ tl.funs.toList, ∀ c < (tl.mats.getD f.mat {}).k,
      ∀ sg < (tl.mats.getD f.mat {}).m / f.len,
        f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg < K3 := by
  intro f hf c hc sg hsg
  rw [hfun] at hf
  rw [hmat] at hc hsg ⊢
  obtain ⟨Z, ep⟩ := tables_below e
  have hb : f.start + (hp.tl.mats.getD f.mat {}).k * ((hp.tl.mats.getD f.mat {}).m / f.len) ≤ t.p :=
    (Z f hf).2.2
  have h1 : c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg <
      (hp.tl.mats.getD f.mat {}).k * ((hp.tl.mats.getD f.mat {}).m / f.len) :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hsg _)
      (by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hc)
  omega

/-- Every entry that a table of the closed list names lies below K3. -/
theorem k6_places_below (e : ReadsQuiet.tables h L hp cov x = .ok t) (tl : HTailF2)
    (hfun : tl.funs = t.funs) (hmat : tl.mats = hp.tl.mats) {K3 : Nat}
    (hK : hp.nU.getD 2 0 ≤ K3) :
    ∀ (n : Nat) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos,
      tl.tabAt Fn c sg = some pos → pos < K3 := by
  intro n Fn hn c sg pos hp'
  obtain ⟨_, g2, g3, rfl⟩ := OnBytes.Tie.Pv.Tail.tabAt_some tl hp'
  exact k6_entries_below e tl hfun hmat hK Fn
    (List.mem_iff_getElem?.mpr ⟨n, by rw [Array.getElem?_toList]; exact hn⟩) c g2 sg g3

end

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.tables_pos
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tables_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_mats_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_entries_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_places_below
