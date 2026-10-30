-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsSheet.lean: the premises of K08Tested, K08CoverU3 and K08Out that
can be decided on data, as Boolean tests with code, each but partB with a theorem that its yes gives the
premise; and one theorem that joins them: where the sheet says yes, K08Tested's conclusion holds at a
world made of any cells (its proof pays all nine premises there).

Definitions with code, statements and proofs. FOR A RIDE AT REAL PLACES: so that the laws are shown not
to be empty there. No routine of `verify-on-bytes` is named. USED OF THE FILES UNDER OnBytes/, ON
RECORDS AND PLAIN DATA ALONE: Fits, UnitRow, ReadsRaw, rawWorld, rawWorld_reads, excBind_ok, readsList,
posOf, uOf, colsU, rowsForm, batchAt, oneE, zeroE, Lay, Lay.cellAt, Reading, World.
Main names:
  sizedB, fitsB, rowsB, unitB: the four tests for K08Tested; partB: K08CoverU3's two equations, and that
    the part and the list of reads are not empty; u3B: every table lies in U3.
  sheet: the run as K08Tested has it: the list made, added behind a list look, lsTail laid, the weights
    laid, the test by a second computation; with the tests between, each under its own name.
  sheet_ok: a yes of the sheet, taken apart: all eleven steps. sheet_world: then, at the rawWorld
    of the ledger with the weights laid: the list's yes, ReadsRaw, and the third clause of K08Tested's
    conclusion. (That all nine premises hold there is what its proof hands to k08_tested: from sheet_ok,
    sizedB_ok, fitsB_ok, rowsB_ok, unitB_ok and rawWorld_reads.)
Limits: the world of sheet_world is MADE of any cells whatever: nothing says that they are what was
committed. That the sheet says yes at a place is a run's word, no theorem.

-/
import Johnson.Desc.First.TailClaims.EquationsTested

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows Finset
open OnBytes.Tie.Pv.Tail (ReadsRaw UnitRow rawWorld rawWorld_reads)

def sizedB (F : Fork) : Bool := F.LS.size == F.ns

def fitsB (tl : HTailF2) : Bool :=
  (List.range tl.NM).all fun mu =>
    (tl.shp.getD mu {}).m == (tl.mats.getD mu {}).m && (tl.shp.getD mu {}).k == (tl.mats.getD mu {}).k

def rowsB (tl : HTailF2) (Fc : Fork) : Bool :=
  (Fc.trees.getD tl.ix.ZZ {}).rows.size == 2 * tl.zzBlocks + 2

def unitB (tl : HTailF2) (funs : Array HFun) (Fc F1 : Fork) : Bool :=
  (readsList tl funs).all fun x =>
    (Fc.trees.getD (uOf tl x.1) {}).R == 1 &&
    ((Fc.trees.getD (uOf tl x.1) {}).rows.getD 0 {}).coef.getD 0 zeroE == oneE &&
    (List.range (tl.mats.getD x.1.mat {}).k).all fun d =>
      decide (posOf tl x.1 x.2 d < colsU F1 (uOf tl x.1))

def partB (tl' : HTailF2) (funs : Array HFun) : Bool :=
  tl'.tabFirst.getD 1 0 == 0 && tl'.tabLen.getD 1 0 == tl'.nUF.getD 2 0 &&
    decide (0 < tl'.tabLen.getD 1 0) && !(readsList tl' funs).isEmpty

def u3B (funs : Array HFun) : Bool := funs.toList.all fun Fn => Fn.tree == 2

theorem sizedB_ok {F : Fork} (h : sizedB F = true) : F.LS.size = F.ns := by
  simpa [sizedB] using h

theorem fitsB_ok {tl : HTailF2} (h : fitsB tl = true) : Fits tl := by
  intro mu hmu
  simp only [fitsB, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact h mu hmu

theorem rowsB_ok {tl : HTailF2} {Fc : Fork} (h : rowsB tl Fc = true) :
    (Fc.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2 := by
  simpa [rowsB] using h

theorem unitB_ok {tl : HTailF2} {funs : Array HFun} {Fc F1 : Fork} (h : unitB tl funs Fc F1 = true) :
    ∀ x ∈ readsList tl funs, UnitRow Fc (uOf tl x.1) ∧
      ∀ d, d < (tl.mats.getD x.1.mat {}).k → posOf tl x.1 x.2 d < colsU F1 (uOf tl x.1) := by
  intro x hx
  simp only [unitB, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨a, b⟩, c⟩ := h x hx
  exact ⟨⟨a, b⟩, c⟩

theorem u3B_ok {funs : Array HFun} (h : u3B funs = true) : ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  intro Fn hFn
  simp only [u3B, List.all_eq_true, beq_iff_eq] at h
  exact h Fn hFn

theorem pure_bind_ok {β : Type} (k : PUnit → Except String β) (b : β)
    (h : ((pure PUnit.unit : Except String PUnit) >>= k) = .ok b) : k PUnit.unit = .ok b := h

/-- The run as K08Tested has it, with the tests between, each under its own name. It returns what the
adding and the laying of lsTail leave, and beside them the ledger with the weights laid. -/
def sheet (front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (look : List Claim) :
    Except String (HTailF2 × Fork × Fork) := do
  unless sizedB F do throw "SHEET one-coefficient-a-slot"
  unless fitsB tl do throw "SHEET Fits"
  unless u3B funs do throw "SHEET every-table-in-U3"
  let (tl', F1, cls) ← equations front tl funs F
  unless partB tl' funs do throw "SHEET the-part-of-U3"
  match addAll F1 (look ++ cls) with
  | none => throw "SHEET addAll"
  | some G =>
    let ts : HTailF2 := { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB }
    let Fc ← coefficientsP ts G
    rkSelfTestP ts Fc
    unless rowsB tl Fc do throw "SHEET the-digits'-virtual-rows"
    unless unitB tl funs Fc F1 do throw "SHEET unit-rows-and-places"
    pure (ts, G, Fc)

/-- A yes of the sheet, taken apart. -/
theorem sheet_ok {front : Nat} {tl ts : HTailF2} {funs : Array HFun} {F G Fc : Fork}
    {look : List Claim} (h : sheet front tl funs F look = .ok (ts, G, Fc)) :
    ∃ (tl' : HTailF2) (F1 : Fork) (cls : List Claim),
      sizedB F = true ∧ fitsB tl = true ∧ u3B funs = true ∧
      equations front tl funs F = .ok (tl', F1, cls) ∧ partB tl' funs = true ∧
      addAll F1 (look ++ cls) = some G ∧
      ts = { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB } ∧
      coefficientsP ts G = .ok Fc ∧ rkSelfTestP ts Fc = .ok () ∧
      rowsB tl Fc = true ∧ unitB tl funs Fc F1 = true := by
  unfold sheet at h
  dsimp only at h
  obtain ⟨b1, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨b2, h⟩ := guard_ok _ _ _ _ _ h
  obtain ⟨b3, h⟩ := guard_ok _ _ _ _ _ h
  replace h := pure_bind_ok _ _ h
  obtain ⟨⟨tl', F1, cls⟩, he, h⟩ := (excBind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨b4, h⟩ := guard_ok _ _ _ _ _ h
  replace h := pure_bind_ok _ _ h
  split at h
  · cases h
  · rename_i G' hadd
    obtain ⟨Fc', hco, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨u, hrk, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨b5, h⟩ := guard_ok _ _ _ _ _ h
    obtain ⟨b6, h⟩ := guard_ok _ _ _ _ _ h
    replace h := pure_bind_ok _ _ h
    have e := Except.ok.inj h
    obtain rfl : _ = ts := congrArg Prod.fst e
    obtain rfl : G' = G := congrArg (fun y => y.2.1) e
    obtain rfl : Fc' = Fc := congrArg (fun y => y.2.2) e
    exact ⟨tl', F1, cls, b1, b2, b3, he, b4, hadd, rfl, hco, hrk, b5, b6⟩

/-- **Where the sheet says yes, K08Tested is not empty**: at the rawWorld of the ledger with the
weights laid, over any lay Y, any entries m and any values under the slots: the list's yes, ReadsRaw,
and the third clause of K08Tested's conclusion. The proof pays all nine premises of K08Tested there. -/
theorem sheet_world {K : Type} [Field K] {J : Type} [Fintype J] (Y : Lay J) (ρ : Reading K)
    (m : J → K) (slot : Nat → K) {front : Nat} {tl ts : HTailF2} {funs : Array HFun}
    {F G Fc : Fork} {look : List Claim} (h : sheet front tl funs F look = .ok (ts, G, Fc)) :
    ∃ (tl' : HTailF2) (F1 : Fork) (cls : List Claim),
      equations front tl funs F = .ok (tl', F1, cls) ∧
      ReadsRaw ρ ts funs Fc (rawWorld ρ Fc slot fun t r c => Y.cellAt m t r c)
        (fun t r c => Y.cellAt m t r c) ∧
      ∃ (four rest : List Claim) (X X4 : Fork), cls = four ++ rest ∧ four.length = 4 ∧
        rest.length = tl.NM + (readsList tl funs).length ∧ addAll F1 look = some X ∧
        addAll X four = some X4 ∧ addAll X4 rest = some G ∧
        G.total ρ (rawWorld ρ Fc slot fun t r c => Y.cellAt m t r c) =
          X4.total ρ (rawWorld ρ Fc slot fun t r c => Y.cellAt m t r c) +
            (batchAt (ρ.val F.theta) (rowsForm Y ρ tl funs F.planClaimsF)).gap m := by
  obtain ⟨tl', F1, cls, b1, b2, -, he, -, hadd, rfl, hco, hrk, b5, b6⟩ := sheet_ok h
  have hW := rawWorld_reads ρ { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB } funs Fc slot
    (fun t r c => Y.cellAt m t r c)
  exact ⟨tl', F1, cls, he, hW,
    (k08_tested K J Y ρ _ m front tl tl' funs F F1 G Fc look cls _ (sizedB_ok b1) he hadd
      (fitsB_ok b2) hco hrk hW (rowsB_ok b5) (unitB_ok b6)).2.2⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.sheet_ok
#print axioms VerifiableInference.Desc.First.TailClaims.Law.sheet_world
