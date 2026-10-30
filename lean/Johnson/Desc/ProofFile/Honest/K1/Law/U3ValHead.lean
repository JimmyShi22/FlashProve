-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/U3ValHead.lean: WHAT THE VALUES OF "U3" (u3Vals,
Johnson/HonestTrace/U3Rows.lean) ARE WHERE THEIR MAKERS ACCEPT: AT ANY SEGMENT THE VECTOR THAT THE
SEGMENT's MAKER RETURNS; AT THE OUTPUT HEAD's SEGMENT THE VECTOR OF READS readAt AT THE TABLES THAT
THE DESCRIPTION's OWN "tables" RETURNS. Five statements and their proofs. No definition. Public
data, the challenges heard and a reader of cells as letters: no thread, no run, no witness.

  lookup_graph   a list of pairs (a, f a), looked up at a member x, answers f x
  u3_size_at     where valsAt accepts a segment: "U3" has there one row and SV.n columns
  u3_val_at      and where SV.vec accepts the challenges heard: the value at (i, c) is entry c of
                 the vector that it returns at the reader's cells, read by Reading.gl
  valsAt_head    at a segment of the head's sort valsAt is headVals
  head_vec       where headVals accepts, and its vec accepts the challenges heard: SV.n is the
                 plan's number of reads; what was heard is made whole (x, WITH ITS EQUATION: a tie
                 of x to a verifier's state will want it); "tables" returns t at x;
                 and the vector's entry j, at cells C, is readAt at the plan's sizes, t's tables and
                 the cells read through matsOwn

Unfoldings of definitions, with headAt_eq and headParts_ok
(Johnson/HonestTrace/U3RowsLaws.lean, Johnson/HonestTrace/ReadsHead.lean). Kin of lookup_graph, not
called: lookup_range (Johnson/HonestTrace/U3Bound.lean): no other file can call it.

Limits. That a maker accepts is a premise everywhere: proved here of no public data and no list of
challenges. Where one rejects, u3Vals has no array or a written 0: nothing is said there. Nothing
ties x, t or cov to a verifier's state. matsOwn is not matsOf here. Nothing on the layers' or
attention's vectors beyond u3_val_at.
Nothing on
soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.HonestTrace.U3RowsLaws
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model VerifiableInference.Desc
open OnBytes.HonestTrace (parOfMats headParts_ok u3Head)
open OnBytes.HonestTrace.U3 (SegVals valsAt headVals u3Vals headAt headAt_eq placeIn)
open ProofFile.Honest.K8 (cellsAtOf)
open ProofFile.Honest.K3 (matsOwn)
open ProofFile.Honest.K4 (k4LookOf)
open ProofFile.Honest.K6 (headHeardWholeAt headParAt)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)

/-- A list of pairs (a, f a), looked up at a member. -/
theorem lookup_graph {β : Type} (f : ℕ → β) (l : List ℕ) (x : ℕ) (hx : x ∈ l) :
    (l.map fun a => (a, f a)).lookup x = some (f x) := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rw [List.map_cons, List.lookup_cons]
    by_cases e : x = a
    · subst e
      simp
    · have e' : (x == a) = false := by simpa using e
      rw [e']
      exact ih (by simpa [e] using hx)

/-- Where valsAt accepts a segment, "U3" has there one row and SV.n columns. -/
theorem u3_size_at (Z : Pub) (G : Ground) (cov : Head.Covered) {l : ℕ}
    (hl : l < G.first.shape.link.length) {SV : SegVals} (hv : valsAt Z G cov l = .ok SV) :
    (u3Vals Z G cov).size l "U3" = some (1, SV.n) := by
  have e : ((List.range G.first.shape.link.length).map fun l => (l, valsAt Z G cov l)).lookup l =
      some (valsAt Z G cov l) := lookup_graph _ _ _ (List.mem_range.2 hl)
  simp only [u3Vals]
  rw [e]
  simp [hv, Except.toOption]

/-- **The value of "U3" where its makers accept.** The text has Slice.toE (…).triple: that is
Reading.gl.val, by that definition's own text. -/
theorem u3_val_at (Z : Pub) (G : Ground) (cov : Head.Covered) {l : ℕ}
    (hl : l < G.first.shape.link.length) {SV : SegVals} (hv : valsAt Z G cov l = .ok SV)
    {hd : List Fmt.Drawn} {vec : Cells → ℕ → OnBytes.E} (hvec : SV.vec hd = .ok vec) (R : Readers)
    (nm : String) (i c : ℕ) :
    (u3Vals Z G cov).val R hd l nm i c = .inr (Reading.gl.val (vec R.cells c)) := by
  have e : ((List.range G.first.shape.link.length).map fun l => (l, valsAt Z G cov l)).lookup l =
      some (valsAt Z G cov l) := lookup_graph _ _ _ (List.mem_range.2 hl)
  simp only [u3Vals]
  rw [e]
  simp [hv, hvec, Except.toOption, Reading.gl]

/-- At a segment of the head's sort valsAt is headVals. -/
theorem valsAt_head (Z : Pub) (G : Ground) (cov : Head.Covered) {seg : ℕ} {SV : SegVals}
    (hv : valsAt Z G cov seg = .ok SV) {Y : OnBytes.Model.Stages.LinkH}
    (hY : G.built[seg]? = some Y) (hk : Y.kind = 2) :
    ∃ sps, spotsOf Z.cuts = some sps ∧ headVals Z G cov sps seg = .ok SV := by
  unfold valsAt at hv
  obtain ⟨sps, h1, hv⟩ := bind_eq_ok hv
  obtain ⟨Y', h2, hv⟩ := bind_eq_ok hv
  obtain ⟨_, -, hv⟩ := bind_eq_ok hv
  obtain ⟨_, -, hv⟩ := bind_eq_ok hv
  rw [hY] at h2
  obtain rfl : Y = Y' := Except.ok.inj h2
  refine ⟨sps, ?_, by simpa [hk] using hv⟩
  cases hs : spotsOf Z.cuts with
  | none => rw [hs] at h1; cases h1
  | some s => rw [hs] at h1; exact congrArg some (Except.ok.inj h1)

/-- **The head's vector is the vector of reads at the tables that "tables" returns.** -/
theorem head_vec (Z : Pub) (G : Ground) (cov : Head.Covered) (sps : List Spot) (seg : ℕ)
    {SV : SegVals} (h : headVals Z G cov sps seg = .ok SV) {hd : List Fmt.Drawn}
    {vec : Cells → ℕ → OnBytes.E} (hvec : SV.vec hd = .ok vec) :
    SV.n = G.W.H.nU.getD 2 0 ∧ ∃ (k6 k3 : Spot × ℕ) (x : Head.Heard) (t : Head.Tables),
      placeIn Z sps seg .K6 = .ok k6 ∧ placeIn Z sps seg .K3 = .ok k3 ∧
      headHeardWholeAt (headParAt G) (Kinds.Head.requestOf Z.s₀) 0
        (k4LookOf G.W.HLy.fs k3.2 hd) k6.2 hd = .ok x ∧
      ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok t ∧
      ∀ (C : Cells) (j : ℕ), vec C j =
        First.K8.Honest.readAt (parOfMats G.W.H.tl.mats) t.funs.toList
          (cellsAtOf C (matsOwn G.W seg)) j := by
  unfold headVals at h
  obtain ⟨k6, hk6, h⟩ := bind_eq_ok h
  obtain ⟨k3, hk3, h⟩ := bind_eq_ok h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain ⟨_, -, h⟩ := bind_eq_ok h
  obtain rfl := Except.ok.inj h
  refine ⟨rfl, ?_⟩
  dsimp only at hvec
  obtain ⟨x, hx, hvec⟩ := bind_eq_ok hvec
  obtain ⟨v, hv, hvec⟩ := bind_eq_ok hvec
  obtain rfl := Except.ok.inj hvec
  cases ht : ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x with
  | error e =>
    unfold headAt at hv
    rw [ht] at hv
    cases hv
  | ok t =>
    refine ⟨k6, k3, x, t, hk6, hk3, hx, ht, fun C j => ?_⟩
    show v (cellsAtOf C (matsOwn G.W seg)) j = _
    rw [headAt_eq hv]
    unfold u3Head
    rw [headParts_ok ht]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lookup_graph
#print axioms ProofFile.Honest.K1.u3_size_at
#print axioms ProofFile.Honest.K1.u3_val_at
#print axioms ProofFile.Honest.K1.valsAt_head
#print axioms ProofFile.Honest.K1.head_vec
