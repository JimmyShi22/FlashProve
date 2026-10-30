-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieKeys.lean: THE TABLE'S
KEYS, READ, ARE THE LIBRARY'S KEYS; AND THE TABLE'S "IN RANGE" IS THE LINKS' KeysIn. The
table of the key file's joints speaks of a lookup's keys by machine elements (keyAt, InRange:
Johnson/Desc/Key/KeyWords.lean; keyVec: KeyK3W.lean); the kind's law speaks of them in the field
(Leaves.runKey, keyAt, key: OnBytes/Slice/KeyLeaves.lean; KeysIn:
Johnson/Desc/First/Look/KeyLaw/Closed.lean).

Main names:
  matR mat: a matrix of machine words, read.
  read_keyAt: the table's key of place firstPlace + t of a run, read, is the library's runKey.
  read_keyVec: key number i of a part, read, is the library's key, where the padding's value is the
    padding key, read.
  keyAt_cases, runsOk_from, keyAt_of_covers, runKey_cut: the library's key at a place is a covering
    run's or the padding's; among rising runs it is the covering run's; it reads the matrix inside
    its size.
  inRange_iff: InRange at "read alike" ⇔ KeysIn at the matrix read and cut at its size, at a lookup
    that passes lookupOk and fitsMatrix.

Object: definitions of the table's files, of K3's files and of the library; no block's text.
User: claim_front₀ (TieClaimFront.lean) calls inRange_iff; read_keyVec has none yet.
Letters: l, a lookup · mat, a matrix of machine words.

Limits. Nothing on soundness.

-/
import Johnson.Desc.Key.KeyK3Items
import Johnson.Desc.First.Look.KeyLaw.Closed
import OnBytes.Slice.KeyLeavesTop
import OnBytes.Slice.BlkLeavesTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieKeys
open OnBytes OnBytes.Slice
open OnBytes.Params (WfRun WfPart WfLookup)

/-- A matrix of machine words, read. -/
def matR (mat : ℕ → ℕ → F) (r c : ℕ) : GE := readE (OnBytes.ofF (mat r c))

theorem read_keyFold (mat : ℕ → ℕ → F) (r : WfRun) (t c : ℕ) : ∀ (L : List (F × ℕ)) (a : E),
    readE (L.foldl (fun s q => addE s (mulE (OnBytes.ofF q.1)
      (OnBytes.ofF (mat (r.firstRow + t + q.2 * r.stride) c)))) a) =
      readE a + (L.map fun q => readE (OnBytes.ofF q.1) *
        matR mat (r.firstRow + t + q.2 * r.stride) c).sum
  | [], a => by simp
  | q :: L, a => by
    rw [List.foldl_cons, read_keyFold mat r t c L, readE_add, readE_mul, List.map_cons,
      List.sum_cons]
    unfold matR
    ring

/-- **The table's key of a run's place, read, is the library's.** -/
theorem read_keyAt (l : WfLookup) (pad : GE) (mat : ℕ → ℕ → F) (r : WfRun) (t c : ℕ) :
    readE (VerifiableInference.Desc.Key.keyAt l mat r t c) =
      Leaves.runKey (Leaves.lkOf l pad) (matR mat) r (r.firstPlace + t) c := by
  unfold VerifiableInference.Desc.Key.keyAt Leaves.runKey Leaves.lkOf
  rw [read_keyFold, Leaves.map_zipIdx, List.map_map, Nat.add_sub_cancel_left]
  rfl

/-- **Key number i of a part, read, is the library's key.** -/
theorem read_keyVec (m : Wf.Matrix) (l : WfLookup) (mat : ℕ → ℕ → F) (part : ℕ) (p : WfPart)
    (hp : l.parts[part]? = some p) (i : ℕ) :
    readE (VerifiableInference.Desc.Key.keyVec m l mat part i) =
      Leaves.key (Leaves.lkOf l (readE (OnBytes.ofF l.paddingKey))) (matR mat) m.kCol p.runs i := by
  unfold VerifiableInference.Desc.Key.keyVec Leaves.key
  rw [hp]
  show readE (match p.runs.find? _ with
    | some r => _
    | none => _) = _
  generalize i / 2 ^ m.kCol = place
  generalize i % 2 ^ m.kCol = c
  induction p.runs with
  | nil => rfl
  | cons r rs ih =>
    rw [List.find?_cons]
    unfold Leaves.keyAt
    by_cases h : r.firstPlace ≤ place ∧ place < r.firstPlace + r.places
    · rw [if_pos h]
      have hb : (decide (r.firstPlace ≤ place) && decide (place < r.firstPlace + r.places)) =
          true := by simp [h.1, h.2]
      rw [hb]
      show readE (VerifiableInference.Desc.Key.keyAt l mat r (place - r.firstPlace) c) = _
      rw [read_keyAt l _ mat r, Nat.add_sub_cancel' h.1]
    · rw [if_neg h]
      have hb : (decide (r.firstPlace ≤ place) && decide (place < r.firstPlace + r.places)) =
          false := by
        rw [Bool.and_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
        exact not_and_or.1 h
      rw [hb]
      exact ih

/-! ## In range -/

/-- A number below 2 ^ 64 as a machine word, read. -/
theorem read_word (v : ℕ) (h : v < 2 ^ 64) : readE (OnBytes.ofF v.toUInt64) = (v : GE) := by
  rw [readE_ofF]
  unfold toF
  rw [show v.toUInt64.toNat = v from by
    show (UInt64.ofNat v).toNat = v
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt h], map_natCast]

/-- A run covers a place. -/
def Covers (r : WfRun) (place : ℕ) : Prop := r.firstPlace ≤ place ∧ place < r.firstPlace + r.places

/-- The library's key at a place is a covering run's key, or the padding's value. -/
theorem keyAt_cases (L : Leaves.LkF) (M : ℕ → ℕ → GE) (place col : ℕ) : ∀ runs : List WfRun,
    (∃ r ∈ runs, Covers r place ∧ Leaves.keyAt L M runs place col = Leaves.runKey L M r place col) ∨
      Leaves.keyAt L M runs place col = L.pad
  | [] => Or.inr rfl
  | r :: rs => by
    unfold Leaves.keyAt
    by_cases h : r.firstPlace ≤ place ∧ place < r.firstPlace + r.places
    · rw [if_pos h]
      exact Or.inl ⟨r, List.mem_cons_self, h, rfl⟩
    · rw [if_neg h]
      rcases keyAt_cases L M place col rs with ⟨r', hr', hc, e⟩ | e
      · exact Or.inl ⟨r', List.mem_cons_of_mem _ hr', hc, e⟩
      · exact Or.inr e

/-- Rising runs begin at or after the place from which they are counted. -/
theorem runsOk_from (lp : ℕ) : ∀ (rs : List WfRun) (u : ℕ), Wf.runsOk lp u rs = true →
    ∀ r ∈ rs, u ≤ r.firstPlace ∧ r.firstPlace + r.places ≤ 2 ^ lp
  | [], _, _, r, hr => absurd hr (List.not_mem_nil)
  | r0 :: rs, u, h, r, hr => by
    simp only [Wf.runsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rcases List.mem_cons.1 hr with rfl | hr'
    · exact ⟨h2, by omega⟩
    · have := runsOk_from lp rs _ h5 r hr'
      exact ⟨by omega, this.2⟩

/-- Among rising runs the library's key at a place that a run covers is that run's. -/
theorem keyAt_of_covers (L : Leaves.LkF) (M : ℕ → ℕ → GE) (lp place col : ℕ) :
    ∀ (rs : List WfRun) (u : ℕ), Wf.runsOk lp u rs = true → ∀ r ∈ rs, Covers r place →
      Leaves.keyAt L M rs place col = Leaves.runKey L M r place col
  | [], _, _, r, hr, _ => absurd hr (List.not_mem_nil)
  | r0 :: rs, u, h, r, hr, hc => by
    have h' := h
    simp only [Wf.runsOk, Bool.and_eq_true, decide_eq_true_eq] at h'
    unfold Leaves.keyAt
    rcases List.mem_cons.1 hr with rfl | hr'
    · exact if_pos hc
    · have hf := (runsOk_from lp rs _ h'.2 r hr').1
      have hn : ¬ (r0.firstPlace ≤ place ∧ place < r0.firstPlace + r0.places) := by
        intro hx
        have := hc.1
        omega
      rw [if_neg hn]
      exact keyAt_of_covers L M lp place col rs _ h'.2 r hr' hc

/-- A run's key reads the matrix inside its size. -/
theorem runKey_cut (m : Wf.Matrix) (L : Leaves.LkF) (M : ℕ → ℕ → GE) (runs : List WfRun)
    (hR : Leaves.RowsIn L m.rows runs) (r : WfRun) (hr : r ∈ runs) (place col : ℕ)
    (hc : Covers r place) (hcol : col < 2 ^ m.kCol) :
    Leaves.runKey L (VerifiableInference.Desc.K3.KeyLaw.cutM m M) r place col =
      Leaves.runKey L M r place col := by
  unfold Leaves.runKey
  congr 2
  refine List.map_congr_left fun w hw => ?_
  have h1 := hR r hr w hw
  have h2 : r.firstRow + (place - r.firstPlace) + w.2 * r.stride < m.rows := by
    have := hc.1
    have := hc.2
    omega
  unfold VerifiableInference.Desc.K3.KeyLaw.cutM
  rw [if_pos ⟨h2, hcol⟩]

/-- **THE TABLE'S "IN RANGE" IS THE LINKS' KeysIn**, at "two elements are the same where they read
alike", at a lookup that passes the public tests. -/
theorem inRange_iff (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (mat : ℕ → ℕ → F)
    (hlo : Wf.lookupOk Wf.fBits l = true) (hfm : Wf.fitsMatrix m l = true) :
    VerifiableInference.Desc.Key.InRange (fun a b => readE a = readE b) m l mat ↔
      VerifiableInference.Desc.K3.KeyLaw.KeysIn id m l
        (VerifiableInference.Desc.K3.KeyLaw.cutM m (matR mat)) := by
  have hpk : l.paddingKey.toNat < 2 ^ l.d := by
    have h := hlo
    simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.2
  have hd : l.d < 64 := by
    have h := hlo
    simp only [Wf.lookupOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have := h.1.1.1.1.1.1.1.2
    unfold Wf.fBits at this
    omega
  have h64 : ∀ v, v < 2 ^ l.d → v < 2 ^ 64 := fun v hv =>
    lt_trans hv (Nat.pow_lt_pow_right (by omega) hd)
  have hpad := Leaves.read_padOf id m l zeroE hpk
  have hRows : ∀ p ∈ l.parts, Leaves.RowsIn (Leaves.lkOf l (Leaves.padOf id m l zeroE)) m.rows
      p.runs := fun p hp => Leaves.rowsIn_of _ (List.length_map _) hfm hp
  constructor
  · intro h j p hp b hb
    have hmem : p ∈ l.parts := List.mem_of_getElem? hp
    have hcol : b % 2 ^ m.kCol < 2 ^ m.kCol := Nat.mod_lt _ (Nat.pow_pos (by omega))
    unfold Leaves.key
    rcases keyAt_cases (Leaves.lkOf l (Leaves.padOf id m l zeroE))
      (VerifiableInference.Desc.K3.KeyLaw.cutM m (matR mat)) (b / 2 ^ m.kCol) (b % 2 ^ m.kCol)
      p.runs with ⟨r, hr, hc, e⟩ | e
    · obtain ⟨v, hv, hs⟩ := h p hmem r hr (b / 2 ^ m.kCol - r.firstPlace) (by
        have := hc.1
        have := hc.2
        omega) (b % 2 ^ m.kCol) hcol
      refine ⟨v, hv, ?_⟩
      rw [e, runKey_cut m _ _ p.runs (hRows p hmem) r hr _ _ hc hcol, ← read_word v (h64 v hv),
        ← hs, read_keyAt l (Leaves.padOf id m l zeroE) mat r, Nat.add_sub_cancel' hc.1]
    · refine ⟨l.paddingKey.toNat, hpk, ?_⟩
      rw [e]
      show Leaves.padOf id m l zeroE = _
      rw [hpad, ← read_word _ (h64 _ hpk)]
      congr 2
      exact (UInt64.ofNat_toNat).symm
  · intro h p hp r hr t ht c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hp
    have hok := Leaves.runsOk_of hlo hp
    have hin := (runsOk_from p.logPlaces p.runs 0 hok r hr).2
    have hcov : Covers r (r.firstPlace + t) := ⟨Nat.le_add_right _ _, by omega⟩
    have hpos : 0 < 2 ^ m.kCol := Nat.pow_pos (by omega)
    have e1 : (c + 2 ^ m.kCol * (r.firstPlace + t)) / 2 ^ m.kCol = r.firstPlace + t := by
      rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hc, Nat.zero_add]
    have e2 : (c + 2 ^ m.kCol * (r.firstPlace + t)) % 2 ^ m.kCol = c := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
    have hb : c + 2 ^ m.kCol * (r.firstPlace + t) < 2 ^ (m.kCol + p.logPlaces) := by
      rw [Nat.pow_add]
      have h1 : r.firstPlace + t + 1 ≤ 2 ^ p.logPlaces := by omega
      calc c + 2 ^ m.kCol * (r.firstPlace + t) < 2 ^ m.kCol * (r.firstPlace + t + 1) := by
            rw [Nat.mul_succ]
            omega
        _ ≤ 2 ^ m.kCol * 2 ^ p.logPlaces := Nat.mul_le_mul_left _ h1
    obtain ⟨u, hu, e⟩ := h j p hj _ hb
    refine ⟨u, hu, ?_⟩
    unfold Leaves.key at e
    rw [e1, e2, keyAt_of_covers _ _ p.logPlaces _ _ p.runs 0 hok r hr hcov,
      runKey_cut m _ _ p.runs (hRows p hp) r hr _ _ hcov hc] at e
    show readE _ = readE _
    rw [read_word u (h64 u hu), ← e, read_keyAt l (Leaves.padOf id m l zeroE) mat r]

end Johnson.RunOne.Law.TieKeys

#print axioms Johnson.RunOne.Law.TieKeys.read_keyAt
#print axioms Johnson.RunOne.Law.TieKeys.read_keyVec
#print axioms Johnson.RunOne.Law.TieKeys.inRange_iff
