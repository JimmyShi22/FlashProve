-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttKfAt.lean.
The attention sub-proof: the key form of each call, by the call's kind.

States:
  setD_get: an entry of an array after one entry is set.
  setFold_size, setFold_get: a record of key forms after a loop over the calls that sets the form of
    each call of one kind.
  kfR16: the key form of a call of kind R16. kfA: the key form of call q: that of the call of kind
    WH at its number; else by the kind of call q: R16, KFD, KR; else the constant form 0.
  kf_size, kf_at: the record behind claim3, claim4, claim5, begun from the empty record for NC
    calls, has NC forms, and the form of call q is kfA h q, for every q below NC.
  claims345_gives: so every run of the three routines in turn that returns, returns that record.
Not claimed: anything on soundness, completeness or hiding. Nor is it claimed that every call's form
is set once (the byte-level verifier tests it: allJoined, OnBytes/Model/Attention.lean).

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoAttKf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

theorem setD_get {α : Type} (a : Array α) (i q : ℕ) (v d : α) :
    (a.setIfInBounds i v).getD q d = if i = q ∧ i < a.size then v else a.getD q d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases hiq : i = q
  · subst hiq
    by_cases hs : i < a.size
    · simp [hs]
    · simp [hs]
  · simp [hiq]

section
variable (P : ACall → Bool) (val : ACall × ℕ → Aff)

theorem setFold_size : ∀ (l : List ACall) (k : ℕ) (j : Joins),
    ((l.zipIdx k).foldl (fun j x => if P x.1 then j.set x.2 (val x) else j) j).kf.size = j.kf.size
  | [], _, _ => rfl
  | c :: l, k, j => by
    rw [List.zipIdx_cons, List.foldl_cons, setFold_size l (k + 1)]
    by_cases hp : P c = true
    · rw [if_pos hp]
      simp [Joins.set]
    · rw [if_neg hp]

theorem setFold_get (d : Aff) : ∀ (l : List ACall) (k : ℕ) (j : Joins) (q : ℕ),
    ((l.zipIdx k).foldl (fun j x => if P x.1 then j.set x.2 (val x) else j) j).kf.getD q d =
      if k ≤ q then
        match l[q - k]? with
        | some c => if P c = true ∧ q < j.kf.size then val (c, q) else j.kf.getD q d
        | none => j.kf.getD q d
      else j.kf.getD q d
  | [], k, j, q => by
    by_cases hk : k ≤ q
    · rw [if_pos hk]
      rfl
    · rw [if_neg hk]
      rfl
  | c :: l, k, j, q => by
    rw [List.zipIdx_cons, List.foldl_cons, setFold_get d l (k + 1)]
    have hsz : (if P c = true then j.set k (val (c, k)) else j).kf.size = j.kf.size := by
      by_cases hp : P c = true
      · rw [if_pos hp]
        simp [Joins.set]
      · rw [if_neg hp]
    have hget : (if P c = true then j.set k (val (c, k)) else j).kf.getD q d =
        if P c = true ∧ k = q ∧ k < j.kf.size then val (c, k) else j.kf.getD q d := by
      by_cases hp : P c = true
      · rw [if_pos hp]
        show (j.kf.setIfInBounds k (val (c, k))).getD q d = _
        rw [setD_get]
        simp [hp]
      · rw [if_neg hp]
        simp [hp]
    show (if k + 1 ≤ q then
        match l[q - (k + 1)]? with
        | some c' => if P c' = true ∧
            q < (if P c = true then j.set k (val (c, k)) else j).kf.size then val (c', q)
          else (if P c = true then j.set k (val (c, k)) else j).kf.getD q d
        | none => (if P c = true then j.set k (val (c, k)) else j).kf.getD q d
      else (if P c = true then j.set k (val (c, k)) else j).kf.getD q d) = _
    rw [hsz, hget]
    by_cases h1 : k + 1 ≤ q
    · have hk : k ≤ q := by omega
      have hne : ¬ (P c = true ∧ k = q ∧ k < j.kf.size) := fun hh => by omega
      have e : q - k = (q - (k + 1)) + 1 := by omega
      rw [if_pos h1, if_pos hk, if_neg hne, e, List.getElem?_cons_succ]
    · rw [if_neg h1]
      by_cases hk : k ≤ q
      · have e : q = k := by omega
        subst e
        rw [if_pos hk, Nat.sub_self, List.getElem?_cons_zero]
        simp
      · have hne : ¬ (P c = true ∧ k = q ∧ k < j.kf.size) := fun hh => by omega
        rw [if_neg hk, if_neg hne]

end

/-- The key form of a call of kind R16. -/
def kfR16 (h : Attention.Heard) (c : ACall) : Aff :=
  let v := Aff.ofConst zeroE
  let v := if c.holds .wl then v + keyWL h.d else v
  if c.holds .ix then v + keyIX h.S h.d else v

/-- The key form of call q. -/
def kfA (h : Attention.Heard) (q : ℕ) : Aff :=
  if h.d.qWH = q then keyWH h.d
  else match h.S.calls[q]? with
    | none => Aff.ofConst zeroE
    | some c =>
      if c.kind == .r16 then kfR16 h c
      else if c.kind == .kfd then kfKFD h q c
      else if c.kind == .kr then kfKR h q
      else Aff.ofConst zeroE

/-- The record of key forms behind the three routines. -/
def joinsA (h : Attention.Heard) (NC : ℕ) : Joins :=
  joins5 h (joins4 h (joins3 h (Joins.empty NC)))

theorem joinR16_eq (h : Attention.Heard) (j : Joins) :
    joinR16 h.S h.d j =
      h.S.calls.toList.zipIdx.foldl
        (fun j x => if x.1.kind == .r16 then j.set x.2 (kfR16 h x.1) else j) j := rfl

theorem kf_size (h : Attention.Heard) (NC : ℕ) : (joinsA h NC).kf.size = NC := by
  unfold joinsA joins5 joins4 joins3
  show (Array.setIfInBounds _ _ _).size = NC
  rw [Array.size_setIfInBounds, joinR16_eq,
    setFold_size (fun c => c.kind == .r16) (fun x => kfR16 h x.1),
    setFold_size (fun c => c.kind == .kfd) (fun x => kfKFD h x.2 x.1),
    setFold_size (fun c => c.kind == .kr) (fun x => kfKR h x.2)]
  simp [Joins.empty]

/-- The key form of each call. -/
theorem kf_at (h : Attention.Heard) (NC q : ℕ) (hq : q < NC) :
    (joinsA h NC).kf.getD q (Aff.ofConst zeroE) = kfA h q := by
  have s3 : (joins3 h (Joins.empty NC)).kf.size = NC := by
    unfold joins3
    rw [setFold_size (fun c => c.kind == .kr) (fun x => kfKR h x.2)]
    simp [Joins.empty]
  have s4 : (joins4 h (joins3 h (Joins.empty NC))).kf.size = NC := by
    unfold joins4
    rw [setFold_size (fun c => c.kind == .kfd) (fun x => kfKFD h x.2 x.1), s3]
  have s5 : (joinR16 h.S h.d (joins4 h (joins3 h (Joins.empty NC)))).kf.size = NC := by
    rw [joinR16_eq, setFold_size (fun c => c.kind == .r16) (fun x => kfR16 h x.1), s4]
  have g0 : (Joins.empty NC).kf.getD q (Aff.ofConst zeroE) = Aff.ofConst zeroE := by
    simp [Joins.empty, Array.getD_eq_getD_getElem?, hq]
  have g3 := setFold_get (fun c => c.kind == .kr) (fun x => kfKR h x.2) (Aff.ofConst zeroE)
    h.S.calls.toList 0 (Joins.empty NC) q
  have g4 := setFold_get (fun c => c.kind == .kfd) (fun x => kfKFD h x.2 x.1) (Aff.ofConst zeroE)
    h.S.calls.toList 0 (joins3 h (Joins.empty NC)) q
  have g5 := setFold_get (fun c => c.kind == .r16) (fun x => kfR16 h x.1) (Aff.ofConst zeroE)
    h.S.calls.toList 0 (joins4 h (joins3 h (Joins.empty NC))) q
  rw [if_pos (Nat.zero_le q), Nat.sub_zero, Array.getElem?_toList] at g3 g4 g5
  have e0 : (Joins.empty NC).kf.size = NC := by simp [Joins.empty]
  rw [e0, g0] at g3
  rw [s3] at g4
  rw [s4] at g5
  unfold joinsA joins5 kfA
  show (Array.setIfInBounds _ _ _).getD q _ = _
  rw [setD_get, s5]
  by_cases hw : h.d.qWH = q
  · rw [if_pos ⟨hw, hw ▸ hq⟩, if_pos hw]
  · rw [if_neg (fun hh => hw hh.1), if_neg hw, joinR16_eq]
    refine g5.trans ?_
    cases hc : h.S.calls[q]? with
    | none =>
      show (joins4 h (joins3 h (Joins.empty NC))).kf.getD q _ = _
      refine g4.trans ?_
      rw [hc]
      show (joins3 h (Joins.empty NC)).kf.getD q _ = _
      refine g3.trans ?_
      rw [hc]
    | some c =>
      show (if (c.kind == Table.r16) = true ∧ q < NC then kfR16 h c
        else (joins4 h (joins3 h (Joins.empty NC))).kf.getD q _) = _
      by_cases h1 : (c.kind == Table.r16) = true
      · rw [if_pos ⟨h1, hq⟩]
        show _ = if (c.kind == Table.r16) = true then _ else _
        rw [if_pos h1]
      · rw [if_neg (fun hh => h1 hh.1)]
        show _ = if (c.kind == Table.r16) = true then _ else _
        rw [if_neg h1]
        refine g4.trans ?_
        rw [hc]
        show (if (c.kind == Table.kfd) = true ∧ q < NC then kfKFD h q c
          else (joins3 h (Joins.empty NC)).kf.getD q _) = _
        by_cases h2 : (c.kind == Table.kfd) = true
        · rw [if_pos ⟨h2, hq⟩, if_pos h2]
        · rw [if_neg (fun hh => h2 hh.1), if_neg h2]
          refine g3.trans ?_
          rw [hc]
          show (if (c.kind == Table.kr) = true ∧ q < NC then kfKR h q else _) = _
          by_cases h3 : (c.kind == Table.kr) = true
          · rw [if_pos ⟨h3, hq⟩, if_pos h3]
          · rw [if_neg (fun hh => h3 hh.1), if_neg h3]

/-- The three routines in turn. -/
theorem claims345_gives (h : Attention.Heard) (NC : ℕ) :
    Returns (claim3 h (Joins.empty NC) >>= fun j => claim4 h j >>= fun j => claim5 h j)
      (joinsA h NC) :=
  gives_bind (claim3_gives h _) (gives_bind (claim4_gives h _) (claim5_gives h _))

end Fo
