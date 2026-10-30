-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/TreesSites.lean: four prover's messages of the test on the table and of the key's
proof of the ranges have at most two trees each.

Where the planner sends oracle messages by planSend at a number from treesOf
(OnBytes/Params/DeriveLin.lean), it writes the number of the message's trees into the entry of the
round that takes the message in, as the entry's number of roots. Each of the four
messages holds at most one oracle message with main rows, and its oracle messages lie in at most
two classes of leaves. So treesOf_two (TreesFew.lean) gives the bound.

Main names.
  treesOf_two_mem: treesOf_two with its premises on the members, for main rows of one length.
  trees_ranges: the message of the key's proof of the ranges (Wf.messageOf, OnBytes/Iop/Wf.lean).
  trees_linU: the message with the folded row (linMessageU).
  trees_linOmega, trees_linW: the messages with Omega and with W (OnBytes/Iop/Lin.lean), for a shape
    that passes its own test (LinShape.ok): a split's message has no main rows.
  linSizeOf_roots: so the three numbers of roots that linSizeOf returns are at most 2.

What this file does not claim. That treesOf has a value. Nothing on the messages of a request's
links.

The program does not import this file.


-/
import OnBytes.Params.Fit.TreesFew
import OnBytes.Iop.Wf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params
open OnBytes

/-- A member of an array by its number. -/
theorem getD_mem {α : Type} {A : Array α} {i : Nat} (d : α) (h : i < A.size) :
    A.getD i d ∈ A.toList := by
  have e : A.getD i d = A[i] := by simp [Array.getD, h]
  rw [e]
  exact Array.getElem_mem_toList h

/-- treesOf_two with its premises on the members, for main rows of one length. -/
theorem treesOf_two_mem {codes : Codes} {sent : Array OracleNotice} {a b L r : Nat}
    (h : treesOf codes sent = some r)
    (hc : ∀ n ∈ sent.toList, n.leafClass = a ∨ n.leafClass = b)
    (hL : ∀ n ∈ sent.toList, n.shape.mainRows ≠ 0 →
      (codes.base.getD n.shape.code default).logN = L) : r ≤ 2 :=
  treesOf_two (Lof := fun _ => L) h (fun _ hi => hc _ (getD_mem _ hi))
    fun _ hi => hL _ (getD_mem _ hi)

/-- The message of the key's proof of the ranges. -/
theorem trees_ranges (codes : Codes) (x : WfPublic) {r : Nat}
    (h : treesOf codes (Wf.messageOf x) = some r) : r ≤ 2 := by
  have key : ∀ n ∈ (Wf.messageOf x).toList,
      n.leafClass = x.message.leafClass ∧ (n.shape.mainRows ≠ 0 → n = x.message) := by
    intro n hn
    unfold Wf.messageOf at hn
    split at hn
    · split at hn
      · rcases List.mem_cons.1 (show n ∈ [_, _] from hn) with e | hn2
        · exact ⟨by rw [e], fun _ => e⟩
        · rw [List.mem_singleton.1 hn2]
          exact ⟨rfl, fun q => absurd rfl q⟩
      · have e := List.mem_singleton.1 (show n ∈ [_] from hn)
        exact ⟨by rw [e], fun _ => e⟩
    · have e := List.mem_singleton.1 (show n ∈ [_] from hn)
      exact ⟨by rw [e], fun _ => e⟩
  exact treesOf_two_mem (a := x.message.leafClass) (b := x.message.leafClass)
    (L := (codes.base.getD x.message.shape.code default).logN) h
    (fun n hn => Or.inl (key n hn).1) fun n hn hm => by rw [(key n hn).2 hm]

/-- The notice of a mask that is sent ahead has no main rows and the given class. -/
theorem linMaskNotice_spec {test : List IoppStage} {c : Nat} {m : OracleNotice}
    (h : linMaskNotice test c = some m) : m.shape.mainRows = 0 ∧ m.leafClass = c := by
  unfold linMaskNotice at h
  obtain ⟨s, _, e⟩ := Option.map_eq_some_iff.mp h
  rw [← e]
  exact ⟨rfl, rfl⟩

/-- The message with the folded row. -/
theorem trees_linU (codes : Codes) (S : LinShape) {sent : Array OracleNotice} {r : Nat}
    (hs : linMessageU S = some sent) (h : treesOf codes sent = some r) : r ≤ 2 := by
  have key : ∀ n ∈ sent.toList, n.leafClass = S.fold.leafClass ∧
      (n.shape.mainRows ≠ 0 → n = ⟨S.fold.u, S.fold.leafClass⟩) := by
    intro n hn
    unfold linMessageU at hs
    obtain ⟨w, hw, e⟩ := Option.map_eq_some_iff.mp hs
    rw [← e, Array.toList_append] at hn
    rcases List.mem_append.1 hn with hn1 | hn2
    · have e1 := List.mem_singleton.1 (show n ∈ [_] from hn1)
      exact ⟨by rw [e1], fun _ => e1⟩
    · unfold linWithU at hw
      split at hw
      · obtain ⟨m, hm, e2⟩ := Option.bind_eq_some_iff.mp hw
        rw [← Option.some.inj e2] at hn2
        rw [List.mem_singleton.1 (show n ∈ [_] from hn2)]
        exact ⟨(linMaskNotice_spec hm).2, fun q => absurd (linMaskNotice_spec hm).1 q⟩
      · rw [← Option.some.inj hw] at hn2
        exact absurd (show n ∈ [] from hn2) List.not_mem_nil
  exact treesOf_two_mem (a := S.fold.leafClass) (b := S.fold.leafClass)
    (L := (codes.base.getD S.fold.u.code default).logN) h
    (fun n hn => Or.inl (key n hn).1) fun n hn hm => by rw [(key n hn).2 hm]

/-- Two clauses of a shape's own test: a split's message has no main rows. -/
theorem LinShape.ok_splits {S : LinShape} (h : S.ok = true) :
    (S.sharedSplitNeeded = true → S.sharedSplit.mainRows = 0) ∧
      (S.ownSplitNeeded = true → S.ownSplit.mainRows = 0) := by
  unfold LinShape.ok at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, hOwn⟩ := h
  rw [Bool.and_eq_true] at h1
  obtain ⟨_, hShared⟩ := h1
  refine ⟨fun q => ?_, fun q => ?_⟩
  · have t := hShared
    rw [q] at t
    simp only [Bool.not_true, Bool.false_or, LinShape.splitMessageOk, Bool.and_eq_true,
      beq_iff_eq] at t
    exact t.1.1.1
  · have t := hOwn
    rw [q] at t
    simp only [Bool.not_true, Bool.false_or, LinShape.splitMessageOk, Bool.and_eq_true,
      beq_iff_eq] at t
    exact t.1.1.1

/-- The message with Omega. -/
theorem trees_linOmega (codes : Codes) {S : LinShape} (hok : S.ok = true) {r : Nat}
    (h : treesOf codes (linMessageOmega S) = some r) : r ≤ 2 := by
  have key : ∀ n ∈ (linMessageOmega S).toList,
      (n.leafClass = S.omegaLeafClass ∨ n.leafClass = S.sharedSplitLeafClass) ∧
        (n.shape.mainRows ≠ 0 → n = ⟨S.omega, S.omegaLeafClass⟩) := by
    intro n hn
    unfold linMessageOmega at hn
    dsimp only at hn
    split at hn
    · rename_i hq
      rcases List.mem_cons.1 (show n ∈ [_, _] from hn) with e | hn2
      · exact ⟨Or.inl (by rw [e]), fun _ => e⟩
      · rw [List.mem_singleton.1 hn2]
        exact ⟨Or.inr rfl, fun q => absurd ((LinShape.ok_splits hok).1 hq) q⟩
    · have e := List.mem_singleton.1 (show n ∈ [_] from hn)
      exact ⟨Or.inl (by rw [e]), fun _ => e⟩
  exact treesOf_two_mem (L := (codes.base.getD S.omega.code default).logN) h
    (fun n hn => (key n hn).1) fun n hn hm => by rw [(key n hn).2 hm]

/-- The message with W. -/
theorem trees_linW (codes : Codes) {S : LinShape} (hok : S.ok = true)
    {sent : Array OracleNotice} {r : Nat} (hs : linMessageW S = some sent)
    (h : treesOf codes sent = some r) : r ≤ 2 := by
  have hb : ∀ n ∈ (if S.ownSplitNeeded = true then
      (#[⟨S.w, S.wLeafClass⟩] : Array OracleNotice).push ⟨S.ownSplit, S.ownSplitLeafClass⟩
      else #[⟨S.w, S.wLeafClass⟩]).toList,
      (n.leafClass = S.wLeafClass ∨ n.leafClass = S.ownSplitLeafClass) ∧
        (n.shape.mainRows ≠ 0 → n = ⟨S.w, S.wLeafClass⟩) := by
    intro n hn
    split at hn
    · rename_i hq
      rcases List.mem_cons.1 (show n ∈ [_, _] from hn) with e | hn2
      · exact ⟨Or.inl (by rw [e]), fun _ => e⟩
      · rw [List.mem_singleton.1 hn2]
        exact ⟨Or.inr rfl, fun q => absurd ((LinShape.ok_splits hok).2 hq) q⟩
    · have e := List.mem_singleton.1 (show n ∈ [_] from hn)
      exact ⟨Or.inl (by rw [e]), fun _ => e⟩
  have key : ∀ n ∈ sent.toList,
      (n.leafClass = S.wLeafClass ∨ n.leafClass = S.ownSplitLeafClass) ∧
        (n.shape.mainRows ≠ 0 → n = ⟨S.w, S.wLeafClass⟩) := by
    intro n hn
    unfold linMessageW at hs
    dsimp only at hs
    split at hs
    · obtain ⟨m, hm, e2⟩ := Option.bind_eq_some_iff.mp hs
      rw [← Option.some.inj e2, Array.toList_push] at hn
      rcases List.mem_append.1 hn with hn1 | hn2
      · exact hb n hn1
      · rw [List.mem_singleton.1 hn2]
        exact ⟨Or.inl (linMaskNotice_spec hm).2,
          fun q => absurd (linMaskNotice_spec hm).1 q⟩
    · rw [← Option.some.inj hs] at hn
      exact hb n hn
  exact treesOf_two_mem (L := (codes.base.getD S.w.code default).logN) h
    (fun n hn => (key n hn).1) fun n hn hm => by rw [(key n hn).2 hm]

/-- The three numbers of roots that linSizeOf returns are at most 2. -/
theorem linSizeOf_roots {codes : Codes} {x : LinSized} {y : LinSize} (hok : x.shape.ok = true)
    (h : linSizeOf codes x = some y) :
    y.rootsW ≤ 2 ∧ y.rootsU ≤ 2 ∧ y.rootsOmega ≤ 2 := by
  unfold linSizeOf at h
  dsimp only at h
  obtain ⟨sW, hsW, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rW, hW, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨sU, hsU, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rU, hU, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rO, hO, h⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj h]
  exact ⟨trees_linW codes hok hsW hW, trees_linU codes x.shape hsU hU,
    trees_linOmega codes hok hO⟩

end OnBytes.Params
