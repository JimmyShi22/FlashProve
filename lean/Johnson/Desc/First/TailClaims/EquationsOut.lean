-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsOut.lean: from the single equations of the list
"K8.equations" to the proved block's relation behind the draw of the matrix (relOut,
Cb/Pv/Tail/Block.lean): the joint between K08Claims (EquationsForms.lean) and the road
OnBytes/Tie/Pv/Tail/EndsAt.lean, EndsLedger.lean, EndsCut.lean.

Statements and proofs. K08Claims speaks of the list rowsForm at the tables funs that are handed to the
run; that road speaks of it at the record's own closed list tl.funs. The text tests that the two
are one list. No routine of `verify-on-bytes` is named. USED OF THE FILES UNDER OnBytes/, EACH ON
RECORDS AND PLAIN DATA ALONE: funsHeld, sameFun, getD_lt, sizeOf, AtT, eqs_cut, TiesReads, rowsLedger,
Fits, readsList, posOf.
Main names:
  sameFun_eq, funs_of_held, eq_held, eq_funs: a yes of "K8.equations" says: funs = tl.funs.
  eq_fields, eq_layout: fields that the returned record has in common with the record that was
    handed in.
  **K08Out** (a closed Prop), **k08_out**: where the list is made, its single equations hold on the
    entries m, the letters are read off the cells of m (AtT) and the digits are in their tables:
    relOut.
Limits: one direction. That the single equations hold is a premise: from the batch's gap (K08Claims) to
each single gap is the batching's step. AtT, Fits, "every table lies in U3" and "the digits are in
their tables" are premises.

-/
import Johnson.Desc.First.TailClaims.EquationsCover
import OnBytes.Tie.Pv.Tail.EndsCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows
open Cb.Pv.Tail Iop
open OnBytes.Tie.Pv.Tail (getD_lt)

theorem sameFun_eq {a b : HFun} (h : HTailF2.sameFun a b = true) : a = b := by
  unfold HTailF2.sameFun at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  cases a
  cases b
  simp_all

theorem funs_of_held {tl : HTailF2} {funs : Array HFun} (h : tl.funsHeld funs = true) :
    funs = tl.funs := by
  unfold HTailF2.funsHeld at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨_, hs⟩, ha⟩ := h
  apply Array.ext hs
  intro i h1 h2
  have e := sameFun_eq (ha i h1)
  rw [getD_lt _ _ _ h1, getD_lt _ _ _ h2] at e
  exact e

theorem eq_held {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    tl.funsHeld funs = true := by
  unfold equations at h
  cases e : eqAll tl funs front (F, #[]) with
  | error x => rw [e] at h; cases h
  | ok x =>
    rw [eqAll_split] at e
    obtain ⟨u1, t1, h1, k1⟩ := (eq_bind_ok _ _ _ _ _).1 e
    rw [(eq_must_ok h1).2] at k1
    obtain ⟨u2, t2, h2, k2⟩ := (eq_bind_ok _ _ _ _ _).1 k1
    exact (eq_must_ok h2).1

/-- A yes of "K8.equations" says: the tables that were handed in are the record's closed list. -/
theorem eq_funs {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) : funs = tl.funs :=
  funs_of_held (eq_held h)

/-- The fields that the returned record has in common with the record that was handed in. -/
theorem eq_fields {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    tl'.NM = tl.NM ∧ tl'.mats = tl.mats ∧ tl'.tabFirst = tl.tabFirst ∧ tl'.tabLen = tl.tabLen ∧
      tl'.nUF = tl.nUF ∧ tl'.ix = tl.ix ∧ tl'.funs = tl.funs ∧
      readsList tl' funs = readsList tl funs ∧
      ∀ Fn sg d, posOf tl' Fn sg d = posOf tl Fn sg d :=
  ⟨eq_same (fun t => t.NM) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.mats) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.tabFirst) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.tabLen) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.nUF) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.ix) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.funs) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => readsList t funs) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    fun Fn sg d => eq_same (fun t => posOf t Fn sg d) h (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ => rfl)⟩

/-- The five fields of the record that the layout of the lookup on the digits reads (the lookup's
files' list): the returned record has them as they were handed in. eqKeys is called at the record that
was handed in (eq_parts). -/
theorem eq_layout {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    tl'.f9 = tl.f9 ∧ tl'.ix = tl.ix ∧ tl'.mz = tl.mz ∧ tl'.z1 = tl.z1 ∧ tl'.z2 = tl.z2 :=
  ⟨eq_same (fun t => t.f9) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.ix) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.mz) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.z1) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl),
    eq_same (fun t => t.z2) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)⟩

/-- **From the single equations to the proved block's relation behind the draw.** The list
"K8.equations" is made at the record tl with the tables funs. The letters of the typed smallness test,
at the record's sizes t, are read off the cells of m (AtT); the shapes fit the matrices; every table
lies in U3; the digits are in their tables; and every single equation of the list rowsForm, at the
tables funs and the plan's number of claims, holds on m. Then relOut. -/
def K08Out : Prop :=
  ∀ (K : Type) [Field K] (J : Type) [Fintype J] (Y : Lay J) (ρ : Reading K) (m : J → K)
    (front : Nat) (tl tl' : HTailF2) (funs : Array HFun) (F F1 : Fork) (cls : List Claim)
    (t : TSize) (Θ : TLetters K t) (x : Θ.X) (msg : Θ.M) (Z : Dig K t.size) (β : Dr t.size),
    equations front tl funs F = .ok (tl', F1, cls) → OnBytes.Tie.Pv.Tail.sizeOf tl = t →
    AtT ρ tl t Θ x msg Z β (fun a r c => Y.cellAt m a r c) → Fits tl →
    (∀ Fn ∈ funs.toList, Fn.tree = 2) →
    (∀ μ u i, Cb.Rng.InTab t.size.lo (Z.zl μ u i) ∧ Cb.Rng.InTab t.size.hi (Z.zh μ u i)) →
    TWhole.Ledger.Holds (rowsLedger ρ Y tl funs F.planClaimsF) m →
    relOut Θ.letters x β msg Z

theorem k08_out : K08Out := by
  intro K _ J _ Y ρ m front tl tl' funs F F1 cls t Θ x msg Z β h ht at' hfit htree hdig hold
  have ef := eq_funs h
  rw [ef] at htree hold
  obtain ⟨a, b⟩ := eqs_cut ρ Y tl ht F.planClaimsF m at' hfit htree hold
  exact ⟨hdig, a, b⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_funs
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_fields
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_layout
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_out
