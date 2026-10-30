-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/KeyLookup/AdmAtPlan.lean: the conditions on the public record of a key file's lookup
(Lk6.Pub.Adm, Cb/Pv/KeyLookup/Letters.lean) hold at every lookup of every plan that the planner
returns. No number of a plan stands in a statement.

The soundness statement of the lookup whose keys come in parts asks one thing of its public record:
Pub.Adm p, thirteen clauses on numbers and shapes. The planner sizes a key's proof of the ranges in
Plan.rangesSized (OnBytes/Plan/Ranges.lean), whose last step refuses unless Wf.admitted holds
(OnBytes/Iop/Wf.lean). That test asks Wf.lookupOk and Wf.fitsMatrix of every lookup
(OnBytes/Key/Ranges.lean). Here: these two tests give all thirteen clauses at the record
pubOf (Wf.lookupOf id m l) (OnBytes/Tie/Pv/KeyLookup/PubOf.lean), at the characteristic Cb.Gl.p.

The way. Wf.lookupOf writes the padding part by part: the stretches of places between the part's
runs. Wf.runsOk says that the runs rise without overlap inside the part and cover a place each. So
the stretches lie inside the part, rise, have no place in common, and leave a place uncovered.

Main names.
  padL, paddingFrom_toList   a part's padding as a list, by recursion on the runs.
  Laid, laid_padL            such a list rises inside the part.
  Before, pairwise_parts     the order of two runs; it holds between all runs of all parts.
  no_common                  two runs in that order have no place in common.
  run_ok, padded_lt          the clauses on one run; a part's padding is less than the part.
  adm_of_clauses             Adm from two clauses of the program's test of form (sizes, order) and
                             three facts on the padding, for any public inputs.
  adm_of_tests               Adm at Wf.lookupOf id m l from Wf.lookupOk and Wf.fitsMatrix.
  adm_of_admitted            Adm at every member of Wf.lookupsOf x m from Wf.admitted codes x m.
  adm_at_keySized            at every lookup of what Plan.keySized returns, at the sizing's matrix.
  adm_at_keyOk               the same at the matrix that the blocks of a chain take (Wf.matrixOf of
                             the shape of the test on the table), from Plan.keyOk.
  adm_at_oneTime             the same at any parameters of a key's one-time chain that pass the test
                             of the check of a key file (Key.admitted).
  planned_keyOk              what Model.Verify.planned returns passes Plan.keyOk.
  adm_at_planned             at every lookup of the key's sizes in what Model.Verify.planned
                             returns from three public files, whatever the files are, at the matrix
                             that the blocks of a chain take. adm_at_planned_sizing: at the
                             sizing's own matrix.
  padRow_lookupOf            every run of padding of Wf.lookupOf id m l holds the record's one row.
  lookupsOf_ne_nil           an item that is admitted has a lookup.
  not_adm_noParts, not_adm_char (with adm_pubTiny), not_adm_apart, not_admitted_noLookups,
  not_lookupOk_default       controls: see below.

The program's whole test of form (Lkp.Public.ok) is not used and does not follow: it also asks that
there are at most 4096 runs of padding, which the two tests do not give. Adm does not read that
number.

Limits. One direction: from a planner that returns. That it returns at any files is not said here,
so by itself each statement "at what the planner returns" would also hold of a planner that always
refuses. The controls show only that the condition and the tests are no empty words: a record
without parts is not admissible; a small record is admissible at the characteristic 7 and not at 6;
a record with one run of padding twice is not admissible; an item "ranges" without a lookup is not
admitted; the default lookup fails Wf.lookupOk. That a description of the protocol takes its
lookups' records from these functions is not said here; nor that the parameters which a reader reads
back from a chain's parameter bytes are the planner's. Nothing on soundness.

-/
import OnBytes.KeyPlan.LookupOkA
import OnBytes.Params.Fit.SizedParts
import OnBytes.Model.Fit.PlanTestsPlanned
import OnBytes.Tie.Pv.Lookup.PendOkKeys
import OnBytes.Tie.Pv.KeyLookup.PubOf
import Cb.Pv.KeyLookup.PartsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes
open OnBytes.Params (WfRun WfPart WfLookup WfPublic)

/-! ## 1. A part's padding as a list -/

/-- The padding of part i from the place u on: the stretches between the runs, up to 2 ^ lp. -/
def padL (K i row lp : ℕ) : ℕ → List WfRun → List Lkp.Padding
  | u, [] => Wf.stretch K i row u (2 ^ lp)
  | u, r :: rs => Wf.stretch K i row u r.firstPlace ++ padL K i row lp (r.firstPlace + r.places) rs

theorem padL_nil (K i row lp u : ℕ) : padL K i row lp u [] = Wf.stretch K i row u (2 ^ lp) := rfl

theorem padL_cons (K i row lp u : ℕ) (r : WfRun) (rs : List WfRun) :
    padL K i row lp u (r :: rs) =
      Wf.stretch K i row u r.firstPlace ++ padL K i row lp (r.firstPlace + r.places) rs := rfl

/-- The program's routine appends that list. -/
theorem paddingFrom_toList (K i row lp : ℕ) :
    ∀ (rs : List WfRun) (u : ℕ) (acc : Array Lkp.Padding),
    (Wf.paddingFrom K i row lp u rs acc).toList = acc.toList ++ padL K i row lp u rs
  | [], u, acc => by rw [Wf.paddingFrom, Array.toList_appendList, padL_nil]
  | r :: rs, u, acc => by
    rw [Wf.paddingFrom, paddingFrom_toList K i row lp rs, Array.toList_appendList, padL_cons,
      List.append_assoc]

/-- What the test on the runs says of the first run. -/
theorem runsOk_cons {lp u : ℕ} {r : WfRun} {rs : List WfRun}
    (h : Wf.runsOk lp u (r :: rs) = true) :
    1 ≤ r.places ∧ u ≤ r.firstPlace ∧ r.firstPlace + r.places ≤ 2 ^ lp ∧
      Wf.runsOk lp (r.firstPlace + r.places) rs = true := by
  rw [Wf.runsOk] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, by omega, h5⟩

/-- Runs of padding of part i, step 1, that hold the row: each has a place, begins at or after the
end of the one before (at first: at or after u), and ends at or before top. In key numbers. -/
def Laid (i row top : ℕ) : ℕ → List Lkp.Padding → Prop
  | _, [] => True
  | u, q :: qs => q.part = i ∧ q.logStep = 0 ∧ q.row = row ∧ 1 ≤ q.length ∧ u ≤ q.first ∧
      q.first + q.length ≤ top ∧ Laid i row top (q.first + q.length) qs

theorem Laid.mono {i row top : ℕ} : ∀ {l : List Lkp.Padding} {u u' : ℕ}, u ≤ u' →
    Laid i row top u' l → Laid i row top u l
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, h, ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, Nat.le_trans h e, f, g⟩

/-- What holds of each member. -/
theorem Laid.mem {i row top : ℕ} : ∀ {l : List Lkp.Padding} {u : ℕ}, Laid i row top u l →
    ∀ q ∈ l, q.part = i ∧ q.logStep = 0 ∧ q.row = row ∧ 1 ≤ q.length ∧ u ≤ q.first ∧
      q.first + q.length ≤ top
  | [], _, _, _, hq => by cases hq
  | a :: l, u, ⟨h1, h2, h3, h4, h5, h6, h7⟩, q, hq => by
    rcases List.mem_cons.1 hq with e | hq'
    · rw [e]
      exact ⟨h1, h2, h3, h4, h5, h6⟩
    · obtain ⟨g1, g2, g3, g4, g5, g6⟩ := Laid.mem h7 q hq'
      exact ⟨g1, g2, g3, g4, by omega, g6⟩

/-- One stretch before a laid list. -/
theorem laid_stretch (K i row N lo hi : ℕ) (hN : hi ≤ N) (hlo : lo ≤ hi) {l : List Lkp.Padding}
    (hl : Laid i row (N * 2 ^ K) (hi * 2 ^ K) l) :
    Laid i row (N * 2 ^ K) (lo * 2 ^ K) (Wf.stretch K i row lo hi ++ l) := by
  unfold Wf.stretch
  by_cases hlt : lo < hi
  · rw [if_pos hlt]
    have e : lo * 2 ^ K + (hi - lo) * 2 ^ K = hi * 2 ^ K := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' hlo]
    simp only [List.cons_append, List.nil_append]
    refine ⟨rfl, rfl, rfl, Nat.mul_pos (Nat.sub_pos_of_lt hlt) (Nat.two_pow_pos K),
      Nat.le_refl _, ?_, ?_⟩
    · show lo * 2 ^ K + (hi - lo) * 2 ^ K ≤ N * 2 ^ K
      rw [e]
      exact Nat.mul_le_mul_right _ hN
    · show Laid i row (N * 2 ^ K) (lo * 2 ^ K + (hi - lo) * 2 ^ K) l
      rw [e]
      exact hl
  · rw [if_neg hlt, List.nil_append]
    exact Laid.mono (Nat.mul_le_mul_right _ hlo) hl

/-- The padding of a part whose runs pass the test is laid inside the part. -/
theorem laid_padL (K i row lp : ℕ) : ∀ (rs : List WfRun) (u : ℕ),
    Wf.runsOk lp u rs = true → u ≤ 2 ^ lp →
      Laid i row (2 ^ lp * 2 ^ K) (u * 2 ^ K) (padL K i row lp u rs)
  | [], u, _, hu => by
    have h := laid_stretch K i row (2 ^ lp) u (2 ^ lp) (Nat.le_refl _) hu (l := []) trivial
    rw [List.append_nil] at h
    rw [padL_nil]
    exact h
  | r :: rs, u, h, _ => by
    obtain ⟨_, h2, h3, h5⟩ := runsOk_cons h
    rw [padL_cons]
    refine laid_stretch K i row (2 ^ lp) u r.firstPlace (by omega) h2 ?_
    exact Laid.mono (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
      (laid_padL K i row lp rs _ h5 h3)

/-- All padding of a part names that part, whatever the runs are. -/
theorem padL_part (K i row lp : ℕ) : ∀ (rs : List WfRun) (u : ℕ),
    ∀ x ∈ padL K i row lp u rs, x.part = i
  | [], u, x, hx => Wf.Proved.pendOkKeys_stretch_part _ _ _ _ _ x hx
  | r :: rs, u, x, hx => by
    rw [padL_cons] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact Wf.Proved.pendOkKeys_stretch_part _ _ _ _ _ x hx
    · exact padL_part K i row lp rs _ x hx

/-- A stretch of padding holds the row that it names. -/
theorem stretch_row {K i row lo hi : ℕ} {x : Lkp.Padding} (hx : x ∈ Wf.stretch K i row lo hi) :
    x.row = row := by
  unfold Wf.stretch at hx
  split at hx
  · rw [List.mem_singleton] at hx
    rw [hx]
  · exact absurd hx List.not_mem_nil

/-- All padding of a part holds the one row, whatever the runs are. -/
theorem padL_row (K i row lp : ℕ) : ∀ (rs : List WfRun) (u : ℕ),
    ∀ x ∈ padL K i row lp u rs, x.row = row
  | [], _, _, hx => stretch_row hx
  | r :: rs, u, x, hx => by
    rw [padL_cons] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact stretch_row hx
    · exact padL_row K i row lp rs _ x hx

/-! ## 2. The order of two runs; no two have a place in common -/

/-- a stands before b: in an earlier part; or in the same part, a of step 1, and a ends at or before
b's first place. -/
def Before (a b : Lkp.Padding) : Prop :=
  a.part < b.part ∨ (a.part = b.part ∧ a.logStep = 0 ∧ a.first + a.length ≤ b.first)

theorem Laid.pairwise {i row top : ℕ} : ∀ {l : List Lkp.Padding} {u : ℕ},
    Laid i row top u l → l.Pairwise Before
  | [], _, _ => List.Pairwise.nil
  | _ :: _, _, ⟨h1, h2, _, _, _, _, h7⟩ =>
    List.pairwise_cons.2 ⟨fun b hb =>
      Or.inr ⟨h1.trans (Laid.mem h7 b hb).1.symm, h2, (Laid.mem h7 b hb).2.2.2.2.1⟩,
      Laid.pairwise h7⟩

/-- Two runs of which one stands before the other have no place in common. -/
theorem no_common {a b : Lkp.Padding} (h : Before a b) (i k : ℕ) :
    ¬ ((runOf a).holds i k = true ∧ (runOf b).holds i k = true) := by
  rintro ⟨ha, hb⟩
  obtain ⟨ha1, x, hx, hkx⟩ := ((runOf a).holds_iff i k).1 ha
  obtain ⟨hb1, y, _, hky⟩ := ((runOf b).holds_iff i k).1 hb
  have ea : a.part = i := ha1
  have eb : b.part = i := hb1
  have hx' : x < a.length := hx
  have hkx' : k = a.first + x * 2 ^ a.logStep := hkx
  have hky' : k = b.first + y * 2 ^ b.logStep := hky
  rcases h with h | ⟨_, h2, h5⟩
  · omega
  · rw [h2, Nat.pow_zero, Nat.mul_one] at hkx'
    have hle : b.first ≤ k := by
      rw [hky']
      exact Nat.le_add_right _ _
    omega

/-- All parts' padding, one part after the other: every run stands before every later one; and no
run names a part below the first. -/
theorem pairwise_parts (K row : ℕ) : ∀ (ps : List WfPart) (k : ℕ),
    (∀ p ∈ ps, Wf.runsOk p.logPlaces 0 p.runs = true) →
    ((ps.zipIdx k).flatMap fun p => padL K p.2 row p.1.logPlaces 0 p.1.runs).Pairwise Before ∧
      ∀ q ∈ (ps.zipIdx k).flatMap fun p => padL K p.2 row p.1.logPlaces 0 p.1.runs, k ≤ q.part
  | [], _, _ => ⟨List.Pairwise.nil, fun _ hq => by simp at hq⟩
  | p :: ps, k, h => by
    obtain ⟨ih1, ih2⟩ :=
      pairwise_parts K row ps (k + 1) fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hL := laid_padL K k row p.logPlaces p.runs 0 (h p (List.mem_cons_self ..))
      (Nat.zero_le _)
    rw [List.zipIdx_cons, List.flatMap_cons]
    refine ⟨List.pairwise_append.2 ⟨hL.pairwise, ih1, fun a ha b hb => Or.inl ?_⟩,
      fun q hq => ?_⟩
    · have e1 := (hL.mem a ha).1
      have e2 := ih2 b hb
      omega
    · rcases List.mem_append.1 hq with hq | hq
      · exact Nat.le_of_eq (hL.mem q hq).1.symm
      · exact Nat.le_trans (Nat.le_succ k) (ih2 q hq)

/-! ## 3. The clauses on one run -/

/-- What is used here of the test on a lookup by itself. -/
theorem lookupOk_padding {l : WfLookup} (h : Wf.lookupOk Wf.fBits l = true) :
    1 ≤ l.d ∧ l.paddingKey.toNat < 2 ^ l.d ∧
      ∀ p ∈ l.parts, Wf.runsOk p.logPlaces 0 p.runs = true ∧ p.runs ≠ [] := by
  simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, c6⟩, _⟩, _⟩, _⟩, _⟩, _⟩, c12⟩, _⟩, c14⟩ := h
  refine ⟨c6, c12, fun p hp => ?_⟩
  have h2 := (c14 p hp).1
  simp only [Wf.partOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h2
  exact ⟨h2.1.2, h2.2⟩

section
variable (id : ℕ) (m : Wf.Matrix) (l : WfLookup)

/-- The padding of the public inputs, part by part. -/
theorem padding_eq : (Wf.lookupOf id m l).padding =
    (l.parts.zipIdx 0).flatMap fun p =>
      padL m.kCol p.2 l.paddingKey.toNat p.1.logPlaces 0 p.1.runs := by
  show (l.parts.zipIdx.flatMap fun p =>
    (Wf.paddingFrom m.kCol p.2 l.paddingKey.toNat p.1.logPlaces 0 p.1.runs #[]).toList) = _
  simp only [paddingFrom_toList]
  rfl

/-- Every run of padding holds the lookup's one padding key. -/
theorem padding_row {q : Lkp.Padding} (hq : q ∈ (Wf.lookupOf id m l).padding) :
    q.row = l.paddingKey.toNat := by
  rw [padding_eq] at hq
  obtain ⟨w, _, hqw⟩ := List.mem_flatMap.1 hq
  exact padL_row _ _ _ _ _ _ q hqw

/-- The padding of part i. -/
theorem padding_filter (i : ℕ) (p : WfPart) (hp : l.parts[i]? = some p) :
    (Wf.lookupOf id m l).padding.filter (·.part == i) =
      padL m.kCol i l.paddingKey.toNat p.logPlaces 0 p.runs := by
  have a := Wf.Proved.pendOkKeys_filter
    (fun q => padL m.kCol q.2 l.paddingKey.toNat q.1.logPlaces 0 q.1.runs)
    (fun q x hx => padL_part _ _ _ _ _ _ x hx) l.parts 0 i p hp
  rw [Nat.zero_add] at a
  rw [padding_eq]
  exact a

/-- The bits of part i of the public inputs. -/
theorem getD_parts (i : ℕ) (p : WfPart) (hp : l.parts[i]? = some p) :
    (Wf.lookupOf id m l).parts.getD i 0 = p.logPlaces + m.kCol := by
  show (l.parts.map fun p => p.logPlaces + m.kCol).getD i 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
  rfl

/-- The clauses on one run of padding. -/
theorem run_ok (hl : Wf.lookupOk Wf.fBits l = true) {q : Lkp.Padding}
    (hq : q ∈ (Wf.lookupOf id m l).padding) :
    q.part < (Wf.lookupOf id m l).parts.length ∧ 1 ≤ q.length ∧
      q.first + (q.length - 1) * 2 ^ q.logStep < 2 ^ (Wf.lookupOf id m l).parts.getD q.part 0 ∧
      q.row < 2 ^ (Wf.lookupOf id m l).d := by
  obtain ⟨_, c12, hr⟩ := lookupOk_padding hl
  rw [padding_eq] at hq
  obtain ⟨w, hw, hqw⟩ := List.mem_flatMap.1 hq
  have hp : l.parts[w.2]? = some w.1 := List.mem_zipIdx_iff_getElem?.1 hw
  have hmem : w.1 ∈ l.parts := List.mem_of_getElem? hp
  obtain ⟨g1, g2, g3, g4, _, g6⟩ :=
    (laid_padL m.kCol w.2 l.paddingKey.toNat w.1.logPlaces w.1.runs 0 (hr _ hmem).1
      (Nat.zero_le _)).mem q hqw
  have hlen : (Wf.lookupOf id m l).parts.length = l.parts.length := List.length_map _
  have hlt : w.2 < l.parts.length := (List.getElem?_eq_some_iff.1 hp).1
  rw [← Nat.pow_add] at g6
  rw [g1, getD_parts id m l w.2 w.1 hp, hlen, g2, g3, Nat.pow_zero, Nat.mul_one]
  exact ⟨hlt, g4, by omega, c12⟩

end

/-! ## 4. The count -/

/-- The places of a list of runs of padding. -/
def padLen (l : List Lkp.Padding) : ℕ := (l.map (·.length)).sum

theorem padLen_append (a b : List Lkp.Padding) : padLen (a ++ b) = padLen a + padLen b := by
  unfold padLen
  rw [List.map_append, List.sum_append]

theorem padLen_stretch (K i row lo hi : ℕ) (h : lo ≤ hi) :
    padLen (Wf.stretch K i row lo hi) + lo * 2 ^ K = hi * 2 ^ K := by
  unfold Wf.stretch
  by_cases hlt : lo < hi
  · rw [if_pos hlt]
    show ((hi - lo) * 2 ^ K + 0) + lo * 2 ^ K = hi * 2 ^ K
    rw [Nat.add_zero, ← Nat.add_mul, Nat.sub_add_cancel h]
  · rw [if_neg hlt]
    have e : lo = hi := by omega
    rw [e]
    exact Nat.zero_add _

/-- Padding, covered places and the places before u fill the part. -/
theorem padLen_padL (K i row lp : ℕ) : ∀ (rs : List WfRun) (u : ℕ),
    Wf.runsOk lp u rs = true → u ≤ 2 ^ lp →
      padLen (padL K i row lp u rs) + (rs.map (·.places)).sum * 2 ^ K + u * 2 ^ K =
        2 ^ lp * 2 ^ K
  | [], u, _, hu => by
    have h := padLen_stretch K i row u (2 ^ lp) hu
    rw [padL_nil]
    show padLen (Wf.stretch K i row u (2 ^ lp)) + 0 * 2 ^ K + u * 2 ^ K = 2 ^ lp * 2 ^ K
    rw [Nat.zero_mul, Nat.add_zero]
    exact h
  | r :: rs, u, h, _ => by
    obtain ⟨_, h2, h3, h5⟩ := runsOk_cons h
    have ih := padLen_padL K i row lp rs _ h5 h3
    have hs := padLen_stretch K i row u r.firstPlace h2
    rw [padL_cons, padLen_append, List.map_cons, List.sum_cons, Nat.add_mul]
    rw [Nat.add_mul] at ih
    omega

/-- Runs that pass the test, if there is one, cover a place. -/
theorem places_pos {lp u : ℕ} : ∀ {rs : List WfRun}, Wf.runsOk lp u rs = true → rs ≠ [] →
    1 ≤ (rs.map (·.places)).sum
  | [], _, h => absurd rfl h
  | r :: rs, h, _ => by
    have h1 := (runsOk_cons h).1
    rw [List.map_cons, List.sum_cons]
    omega

/-- The padding of a part is less than the part. -/
theorem padded_lt (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (hl : Wf.lookupOk Wf.fBits l = true)
    (i : ℕ) (p : WfPart) (hp : l.parts[i]? = some p) :
    Lkp.paddedBy (Wf.lookupOf id m l) (fun q => q.part == i) < 2 ^ (p.logPlaces + m.kCol) := by
  obtain ⟨hr, hne⟩ := (lookupOk_padding hl).2.2 p (List.mem_of_getElem? hp)
  have e : Lkp.paddedBy (Wf.lookupOf id m l) (fun q => q.part == i) =
      padLen (padL m.kCol i l.paddingKey.toNat p.logPlaces 0 p.runs) := by
    unfold Lkp.paddedBy padLen
    rw [padding_filter id m l i p hp]
  have h4 := padLen_padL m.kCol i l.paddingKey.toNat p.logPlaces p.runs 0 hr (Nat.zero_le _)
  have h6 : 1 * 2 ^ m.kCol ≤ (p.runs.map (·.places)).sum * 2 ^ m.kCol :=
    Nat.mul_le_mul_right _ (places_pos hr hne)
  have h7 := Nat.two_pow_pos m.kCol
  rw [e, Nat.pow_add]
  omega

end Lk6.AtPlan

/-! ## 5. The record's conditions -/

namespace Lk6
open OnBytes
open OnBytes.Params (WfRun WfPart WfLookup WfPublic)

namespace AtPlan

theorem padIn_paddedBy (S : Lkp.Public) (i : ℕ) :
    (pubOf S).padIn i = Lkp.paddedBy S fun p => p.part == i := by
  unfold Pub.padIn Lkp.paddedBy
  show (((S.padding.map runOf).filter fun r => r.part == i).map (·.length)).sum = _
  rw [List.filter_map, List.map_map]
  rfl

theorem headD_getD (l : List ℕ) : l.headD 0 = l.getD 0 0 := by cases l <;> rfl

theorem allPairs_pairwise {α : Type} (p : α → α → Bool) :
    ∀ l : List α, Lkp.allPairs p l = true → l.Pairwise fun a b => p a b = true
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
    simp only [Lkp.allPairs, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons h.1 (allPairs_pairwise p l h.2)

/-- What the program's test on the sizes gives. -/
theorem sizes_of {S : Lkp.Public} (h : S.sizesOK = true) :
    S.parts ≠ [] ∧ S.live < 2 ^ S.mu ∧ 2 ≤ S.planes ∧ (∀ x ∈ S.parts, 1 ≤ x ∧ x < S.planes) ∧
      S.allKeys < 2 ^ S.planes ∧ S.d + S.planes < 64 := by
  simp only [Lkp.Public.sizesOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, c2⟩, _⟩, _⟩, c5⟩, c6⟩, _⟩, c8⟩, c9⟩, _⟩, c11⟩, _⟩, _⟩ := h
  refine ⟨fun he => ?_, c5, c6, fun x hx => ?_, c9, c11⟩
  · rw [he] at c2
    simp at c2
  · have := List.all_eq_true.1 c8 x hx
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this

end AtPlan

open AtPlan

/-- The record's conditions, for any public inputs of a lookup: from the program's tests on the
sizes and on the order of the last key level, a table of at least two rows, and three facts on the
runs of padding. -/
theorem adm_of_clauses {S : Lkp.Public} (hs : S.sizesOK = true) (ho : S.orderOK = true)
    (hd : 1 ≤ S.d)
    (p1 : ∀ p ∈ S.padding, p.part < S.parts.length ∧ 1 ≤ p.length ∧
      p.first + (p.length - 1) * 2 ^ p.logStep < 2 ^ S.parts.getD p.part 0 ∧ p.row < 2 ^ S.d)
    (p2 : S.padding.Pairwise fun a b =>
      ∀ i k, ¬ ((runOf a).holds i k = true ∧ (runOf b).holds i k = true))
    (p3 : ∀ i < S.parts.length, Lkp.paddedBy S (fun p => p.part == i) < 2 ^ S.parts.getD i 0) :
    (pubOf S).Adm Cb.Gl.p := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := sizes_of hs
  have hin : ∀ r ∈ (pubOf S).runs, r.part < (pubOf S).m ∧ 1 ≤ r.length ∧
      r.first + (r.length - 1) * 2 ^ r.logStep < 2 ^ (pubOf S).v r.part := by
    intro r hr
    obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hr
    exact ⟨(p1 p hp').1, (p1 p hp').2.1, (p1 p hp').2.2.1⟩
  have hnot : ∀ i < (pubOf S).m, (pubOf S).padIn i < 2 ^ (pubOf S).v i := by
    intro i hi
    rw [padIn_paddedBy]
    exact p3 i hi
  have hroom : (pubOf S).pl ≤ 2 ^ (pubOf S).mu := by
    show S.planes ≤ 2 ^ S.mu
    unfold Lkp.Public.planes
    split
    · exact le_rfl
    · exact le_of_lt s2
  have hbits : ∀ i < (pubOf S).m, 1 ≤ (pubOf S).v i ∧ (pubOf S).v i < (pubOf S).pl := by
    intro i hi
    have hi' : i < S.parts.length := hi
    have e : (pubOf S).v i = S.parts[i] := List.getD_eq_getElem _ _ hi'
    rw [e]
    exact s4 _ (List.getElem_mem hi')
  have hchar : 2 ^ (pubOf S).d * (2 ^ (pubOf S).pl - 1) < Cb.Gl.p := by
    show 2 ^ S.d * (2 ^ S.planes - 1) < Cb.Gl.p
    have e1 : 2 ^ S.d * (2 ^ S.planes - 1) ≤ 2 ^ S.d * 2 ^ S.planes :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have e2 : 2 ^ S.d * 2 ^ S.planes ≤ 2 ^ 63 := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact lt_of_le_of_lt (e1.trans e2) (by decide)
  have hrow : (pubOf S).padRow < 2 ^ (pubOf S).d := by
    show (S.padding.head?.map (·.row)).getD 0 < 2 ^ S.d
    cases hpad : S.padding with
    | nil => exact Nat.two_pow_pos _
    | cons q qs => exact (p1 q (by rw [hpad]; exact List.mem_cons_self)).2.2.2
  have hapart : (pubOf S).runs.Pairwise
      fun a b => ∀ i k, ¬ (a.holds i k = true ∧ b.holds i k = true) := by
    show (S.padding.map runOf).Pairwise _
    rw [List.pairwise_map]
    exact p2
  have hpads : (pubOf S).padCount ≤ (pubOf S).allKeys :=
    (pubOf S).padCount_le_of (fun r hr => (hin r hr).1) hnot
  have horder : (∀ j ∈ (pubOf S).order, j + 1 < (pubOf S).least) ∧ (pubOf S).order.Nodup := by
    simp only [Lkp.Public.orderOK, Bool.and_eq_true] at ho
    refine ⟨fun j hj => ?_, ?_⟩
    · have h3 := of_decide_eq_true (List.all_eq_true.1 ho.1 j hj)
      have e : (pubOf S).least = S.parts.foldl min S.firstBits := by
        unfold Pub.least Lkp.Public.firstBits
        rw [headD_getD]
        rfl
      rw [e]
      omega
    · exact (allPairs_pairwise _ _ ho.2).imp fun hab => bne_iff_ne.1 hab
  exact
    { some := List.length_pos_iff.2 s1
      planes := s3
      room := hroom
      bits := hbits
      keys := s5
      pads := hpads
      char := hchar
      tabs := hd
      row := hrow
      inPart := hin
      apart := hapart
      notAll := hnot
      order := horder }

/-- **The two tests of the block of the ranges on a lookup give the record's conditions** at what
that block hands the block of a lookup. -/
theorem adm_of_tests (id : ℕ) (m : Wf.Matrix) (l : WfLookup)
    (hl : Wf.lookupOk Wf.fBits l = true) (hf : Wf.fitsMatrix m l = true) :
    (pubOf (Wf.lookupOf id m l)).Adm Cb.Gl.p := by
  refine adm_of_clauses (KeyPlan.sizesOK_lookupOf id m l hl hf)
    (KeyPlan.orderOK_lookupOf id m l hl hf) (lookupOk_padding hl).1
    (fun p hp => run_ok id m l hl hp) ?_ fun i hi => ?_
  · rw [padding_eq]
    exact (pairwise_parts m.kCol _ l.parts 0
      fun x hx => ((lookupOk_padding hl).2.2 x hx).1).1.imp fun h => no_common h
  · have hlt : i < l.parts.length := by
      rwa [show (Wf.lookupOf id m l).parts.length = l.parts.length from List.length_map _] at hi
    have hp : l.parts[i]? = some l.parts[i] := List.getElem?_eq_getElem hlt
    rw [getD_parts id m l i _ hp]
    exact padded_lt id m l hl i _ hp

/-- **Every run of padding holds the record's one row.** The record keeps the first run's row alone
and forgets the others'; Adm cannot see them. At what the block of the ranges hands over all runs
hold one row, whatever the lookup is. -/
theorem padRow_lookupOf (id : ℕ) (m : Wf.Matrix) (l : WfLookup) :
    ∀ q ∈ (Wf.lookupOf id m l).padding, q.row = (pubOf (Wf.lookupOf id m l)).padRow := by
  intro q hq
  show q.row = (((Wf.lookupOf id m l).padding.head?).map (·.row)).getD 0
  have hr := fun a ha => padding_row id m l (q := a) ha
  cases hpad : (Wf.lookupOf id m l).padding with
  | nil =>
    rw [hpad] at hq
    cases hq
  | cons a as =>
    show q.row = a.row
    rw [hr q hq, hr a (by rw [hpad]; exact List.mem_cons_self)]

/-- Each lookup of an item "ranges" that is admitted passes the two tests. -/
theorem admitted_tests {codes : Codes} {x : WfPublic} {m : Wf.Matrix}
    (h : Wf.admitted codes x m = true) :
    ∀ l ∈ x.lookups, Wf.lookupOk Wf.fBits l = true ∧ Wf.fitsMatrix m l = true := by
  unfold Wf.admitted at h
  simp only [Bool.and_eq_true] at h
  have hp : Wf.publicOk x = true := h.1.1.1.1.1.1.1.1.1
  have hf : (x.lookups.all (Wf.fitsMatrix m)) = true := h.1.1.1.1.1.1.1.2
  unfold Wf.publicOk at hp
  simp only [Bool.and_eq_true] at hp
  exact fun l hl => ⟨List.all_eq_true.1 hp.2 l hl, List.all_eq_true.1 hf l hl⟩

/-- **At every lookup of an item "ranges" that is admitted.** -/
theorem adm_of_admitted {codes : Codes} {x : WfPublic} {m : Wf.Matrix}
    (h : Wf.admitted codes x m = true) : ∀ S ∈ Wf.lookupsOf x m, (pubOf S).Adm Cb.Gl.p := by
  intro S hS
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hS
  exact adm_of_tests _ m l (admitted_tests h l hl).1 (admitted_tests h l hl).2

/-- **At every lookup of a key's sizes that the planner returns**, at the sizing's own matrix. -/
theorem adm_at_keySized {l : Params.Lines} {shape : Plan.Shape} {z : Plan.KeySized}
    (h : Plan.keySized l shape = some z) :
    ∀ S ∈ Wf.lookupsOf z.ranges.x z.ranges.matrix, (pubOf S).Adm Cb.Gl.p := by
  obtain ⟨_, _, _, _, _, _, _, _, hR⟩ := Params.keySized_parts h
  obtain ⟨_, _, _, _, _, _, _, ha⟩ := Params.rangesSized_parts hR
  exact adm_of_admitted ha

/-- The same at the matrix that the blocks of a chain take, from the test on a key's values
together. -/
theorem adm_at_keyOk {z : Plan.KeySized} (h : Plan.keyOk z = true) :
    ∀ S ∈ Wf.lookupsOf z.ranges.x (Wf.matrixOf z.once.shape), (pubOf S).Adm Cb.Gl.p := by
  unfold Plan.keyOk Key.fixedOk at h
  simp only [Bool.and_eq_true] at h
  exact adm_of_admitted h.1.1.1.1.1.1.1.2

/-- The same at parameters of a key's one-time chain that pass the test of the check of a key file,
wherever they come from. -/
theorem adm_at_oneTime {q : Params.OneTime} (h : Key.admitted q = true) :
    ∀ S ∈ Wf.lookupsOf q.ranges (Wf.matrixOf q.lin), (pubOf S).Adm Cb.Gl.p := by
  unfold Key.admitted Key.fixedOk at h
  simp only [Bool.and_eq_true] at h
  exact adm_of_admitted h.1.1.1.1.1.1.1.2

/-- The planner's yes: the key's sizes pass the test on a key's values together. -/
theorem configure_keyOk {l : Params.Lines} {x : Params.Shapes} {cfg : ByteArray} {bits : ℕ}
    {made : Params.Configured} (h : Params.configure l x cfg bits = .ok made) :
    Plan.keyOk made.sized.key = true := by
  unfold Params.configure at h
  obtain ⟨z, _, h⟩ := Params.exc_bind h
  obtain ⟨proof, _, h⟩ := Params.exc_bind h
  obtain ⟨P1, _, h⟩ := Params.exc_bind h
  obtain ⟨P2, _, h⟩ := Params.exc_bind h
  obtain ⟨P3, _, h⟩ := Params.exc_bind h
  obtain ⟨entry, _, h⟩ := Params.exc_bind h
  split at h
  · obtain ⟨_, _, h⟩ := Params.exc_bind h
    replace h := Params.exc_guard h
    replace h := Params.exc_guard h
    replace h := Params.exc_guard h
    replace h := Params.exc_guard h
    have hk := Params.exc_guard_not h
    replace h := Params.exc_guard h
    replace h := Params.exc_guard h
    replace h := Params.exc_guard h
    cases h
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hk
    exact hk
  · cases h

/-- The same from the program's yes on three public files. -/
theorem planned_keyOk {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Model.Verify.Planned} (h : Model.Verify.planned pol KL layout = .ok p) :
    Plan.keyOk p.chains.made.sized.key = true := by
  obtain ⟨l, x, hc, _, _⟩ := Model.Verify.planned_made h
  exact configure_keyOk hc

/-- **At every lookup of the key's sizes in what the program computes from three public files, at
the matrix that the blocks of a chain take**: the size in the shape of the test on the table. -/
theorem adm_at_planned {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Model.Verify.Planned} (h : Model.Verify.planned pol KL layout = .ok p) :
    ∀ S ∈ Wf.lookupsOf p.chains.made.sized.key.ranges.x
        (Wf.matrixOf p.chains.made.sized.key.once.shape), (pubOf S).Adm Cb.Gl.p :=
  adm_at_keyOk (planned_keyOk h)

/-- The same at the matrix in the sizes of the proof of the ranges. -/
theorem adm_at_planned_sizing {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Model.Verify.Planned} (h : Model.Verify.planned pol KL layout = .ok p) :
    ∀ S ∈ Wf.lookupsOf p.chains.made.sized.key.ranges.x p.chains.made.sized.key.ranges.matrix,
      (pubOf S).Adm Cb.Gl.p := by
  obtain ⟨l, x, hc, _, _⟩ := Model.Verify.planned_made h
  exact adm_at_keySized (Params.sized_key (Params.configure_plans hc).1)

/-! ## 6. Controls: neither the condition nor the tests are empty words -/

/-- A record without parts is not admissible, at any characteristic. -/
theorem not_adm_noParts (p : ℕ) :
    ¬ (({ parts := [], d := 1, mu := 1, pl := 2, runs := [], padRow := 0, order := [] } :
      Pub).Adm p) := fun h => absurd h.some (by decide)

/-- An item "ranges" without a lookup is not admitted. -/
theorem not_admitted_noLookups (codes : Codes) (x : WfPublic) (m : Wf.Matrix)
    (hx : x.lookups = []) : Wf.admitted codes x m = false := by
  unfold Wf.admitted Wf.publicOk
  simp [hx]

/-- So an item that is admitted has a lookup: the statements "at every lookup" are not idle. -/
theorem lookupsOf_ne_nil {codes : Codes} {x : WfPublic} {m : Wf.Matrix}
    (h : Wf.admitted codes x m = true) : Wf.lookupsOf x m ≠ [] := by
  intro e
  rw [not_admitted_noLookups codes x m (List.map_eq_nil_iff.1 e)] at h
  cases h

/-- A small record: one part of two keys, a table of two rows, two planes, no padding. -/
def pubTiny : Pub :=
  { parts := [1], d := 1, mu := 1, pl := 2, runs := [], padRow := 0, order := [] }

/-- It is admissible at the characteristic 7. -/
theorem adm_pubTiny : pubTiny.Adm 7 where
  some := by decide
  planes := by decide
  room := by decide
  bits := by decide
  keys := by decide
  pads := by decide
  char := by decide
  tabs := by decide
  row := by decide
  inPart := by decide
  apart := List.Pairwise.nil
  notAll := by decide
  order := by decide

/-- At the characteristic 6 it is not: the clause on the characteristic alone fails. -/
theorem not_adm_char : ¬ pubTiny.Adm 6 := fun h => absurd h.char (by decide)

/-- A record in which one run of padding stands twice. -/
def pubTwice : Pub :=
  { parts := [2], d := 1, mu := 2, pl := 3, runs := [⟨0, 0, 0, 1⟩, ⟨0, 0, 0, 1⟩], padRow := 0,
    order := [] }

/-- It is not admissible, at any characteristic. -/
theorem not_adm_apart (p : ℕ) : ¬ pubTwice.Adm p := fun h =>
  (List.pairwise_cons.1 h.apart).1 _ (List.mem_singleton.2 rfl) 0 0 ⟨by decide, by decide⟩

/-- The default lookup fails the test on a lookup by itself. -/
theorem not_lookupOk_default : Wf.lookupOk Wf.fBits default = false := by decide

end Lk6

#print axioms Lk6.adm_of_clauses
#print axioms Lk6.adm_of_tests
#print axioms Lk6.adm_of_admitted
#print axioms Lk6.adm_at_keySized
#print axioms Lk6.adm_at_keyOk
#print axioms Lk6.adm_at_oneTime
#print axioms Lk6.planned_keyOk
#print axioms Lk6.adm_at_planned
#print axioms Lk6.adm_at_planned_sizing
#print axioms Lk6.padRow_lookupOf
#print axioms Lk6.lookupsOf_ne_nil
#print axioms Lk6.adm_pubTiny
#print axioms Lk6.not_adm_char
#print axioms Lk6.not_adm_apart
#print axioms Lk6.not_adm_noParts
#print axioms Lk6.not_admitted_noLookups
#print axioms Lk6.not_lookupOk_default
