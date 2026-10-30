-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndsCut.lean: the statements of OnBytes/Tie/Pv/Tail/EndsLedger.lean for a record
of the smallness test that hangs on the statement: the drawn matrix, and whatever else of the record
comes from earlier draws, are not those of one fixed record.

Definitions, statements and proofs. The list `rowsTail` reads the drawn matrix and the tables'
weights off the verifier's record. In a typed reduction the drawn matrix is a part of the statement
behind the round, and the tables' weights are a part of the statement in front of it. So a ledger
for all statements must take a record for each statement. The sizes t are fixed; each record must
have these sizes (`sizeOf tl = t`).
Main names:
  `AtT`: `AtA` (OnBytes/Tie/Pv/Tail/EndsAt.lean) with the sizes as a letter t.
  `eqs_cut`: for a record with `sizeOf tl = t`: under `AtT` at the cells of m, the forms of
    `rowsLedger` at that record give every tie and every read at letters over t.
  `withDraw tl β`: the record with the entries of the typed challenge β as its drawn entries.
  `sizeOf_withDraw`, `fits_withDraw`: the sizes and `Fits` do not see the drawn entries.
  `sizeOf_funs`: the sizes see of the tables their matrices, lengths and first entries alone.
  `th_draw`: at `withDraw tl β` the clause of `AtT` on the drawn matrix holds, for every β, if the
    record's first columns are the running sums of the matrices' columns.
  `atT_draw`: so `AtT` at `withDraw tl β` follows from its five other clauses at tl.
  `withDraw_self`: a record whose drawn entries are the entries of β is `withDraw tl β`.
Limits: which record belongs to a statement is a letter of whoever uses this file.
-/
import OnBytes.Tie.Pv.Tail.EndsLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model OnBytes.Road.Rows

open Finset Cb.Pv.Tail Iop

variable {K : Type} [Field K] (ρ : Reading K)

/-- `AtA`, with the sizes as a letter. -/
structure AtT (tl : HTailF2) (t : TSize) (Θ : TLetters K t) (x : Θ.X) (msg : Θ.M)
    (Z : Dig K t.size) (β : Dr t.size) (A : Nat → Nat → Nat → K) : Prop where
  phi : ∀ n Fn, tl.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
    Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE)
  sym : ∀ μ i' c, μ < tl.NM → i' < Alg.symRows (tl.mats.getD μ {}).m → c < (tl.mats.getD μ {}).k →
    Θ.sym msg μ i' c = A (tl.gtTree.getD μ 0) i' c
  u3 : ∀ y ∈ readsList tl tl.funs, ∀ d, d < (tl.mats.getD y.1.mat {}).k →
    Θ.u3 msg (posOf tl y.1 y.2 d) = A (u3Of tl) 0 (posOf tl y.1 y.2 d)
  zl : ∀ μ u i, Z.zl μ u i = A tl.ix.ZZ u ((tl.zzCol μ 0 0).getD 0 + i)
  zh : ∀ μ u i, Z.zh μ u i = A tl.ix.ZZ u ((tl.zzCol μ 1 0).getD 0 + i)
  th : ∀ μ u c, (((β μ u c).val : ℤ) : K) =
    signOf (K := K) (tl.cfF.getD ((tl.cfFirst.getD μ 0 + c) * tl.tau + u) 0)

variable {J : Type} [Fintype J] (Y : Lay J)

/-- For a record with the sizes t: the forms of the list at that record give every tie and every
read at letters over t. -/
theorem eqs_cut (tl : HTailF2) {t : TSize} (ht : sizeOf tl = t) {Θ : TLetters K t} {x : Θ.X}
    {msg : Θ.M} {Z : Dig K t.size} {β : Dr t.size} (pc : Nat) (m : J → K)
    (at' : AtT ρ tl t Θ x msg Z β fun a r c => Y.cellAt m a r c) (hfit : Fits tl)
    (htree : ∀ Fn ∈ tl.funs.toList, Fn.tree = 2)
    (h : TWhole.Ledger.Holds (rowsLedger ρ Y tl tl.funs pc) m) :
    TiesReads Θ.letters x β msg Z := by
  subst ht
  exact eqs_of_ledger ρ Y tl pc m ⟨at'.phi, at'.sym, at'.u3, at'.zl, at'.zh, at'.th⟩ hfit htree h

/-- The record with the entries of β as its drawn entries. -/
def withDraw (tl : HTailF2) {t : TSize} (β : Dr t.size) : HTailF2 := { tl with cfF := listOf β }

theorem withDraw_self (tl : HTailF2) {t : TSize} (β : Dr t.size) (h : tl.cfF = listOf β) :
    withDraw tl β = tl := by
  unfold withDraw
  rw [← h]

theorem sizeOf_withDraw (tl : HTailF2) {t : TSize} (β : Dr t.size) :
    sizeOf (withDraw tl β) = sizeOf tl := rfl

/-- The sizes see of the tables their matrices, lengths and first entries alone. -/
theorem sizeOf_funs (tl : HTailF2) (funs : Array HFun)
    (h : (funs.toList.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) =
      tl.funs.toList.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) :
    sizeOf { tl with funs := funs } = sizeOf tl := by
  unfold sizeOf
  simp only [h]

theorem fits_withDraw {tl : HTailF2} (h : Fits tl) {t : TSize} (β : Dr t.size) :
    Fits (withDraw tl β) := h.of_same rfl rfl rfl

omit [Fintype J] in
/-- The clause on the drawn matrix, at every β. -/
theorem th_draw (tl : HTailF2) {t : TSize} (ht : sizeOf tl = t) (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    (β : Dr t.size) (μ : Fin t.size.NM) (u : Fin t.size.tau) (c : Fin (t.size.k μ)) :
    (((β μ u c).val : ℤ) : K) =
      signOf (K := K) ((listOf β).getD ((tl.cfFirst.getD μ 0 + c) * tl.tau + u) 0) := by
  subst ht
  rw [hfirst, cfFirst_eq tl hnm μ, show tl.tau = (sizeOf tl).size.tau from rfl, listOf_get,
    signOf_coef]

/-- `AtT` at the record with β's entries, from the five other clauses. -/
theorem atT_draw (tl : HTailF2) {t : TSize} (ht : sizeOf tl = t) (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    {Θ : TLetters K t} {x : Θ.X} {msg : Θ.M} {Z : Dig K t.size} {β₀ : Dr t.size}
    {A : Nat → Nat → Nat → K} (at' : AtT ρ tl t Θ x msg Z β₀ A) (β : Dr t.size) :
    AtT ρ (withDraw tl β) t Θ x msg Z β A :=
  ⟨at'.phi, at'.sym, at'.u3, at'.zl, at'.zh, fun μ u c => th_draw tl ht hnm hfirst β μ u c⟩

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.eqs_cut
#print axioms OnBytes.Tie.Pv.Tail.Port.th_draw
#print axioms OnBytes.Tie.Pv.Tail.Port.atT_draw
