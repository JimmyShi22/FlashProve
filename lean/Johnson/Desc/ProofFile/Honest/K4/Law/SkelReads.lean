-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelReads.lean: CONDITIONAL: on `LookSkel`, `PtSkel` or
`HasSame`.

What is here. CONGRUENCES: WHETHER AN ENTRY OF THE HONEST READS HAS ITS WEIGHTS, AND WHETHER A FORM
CAN BE VALUED ON THEM (`wtsFit`, `readsAt`, `affFits`, `valAff?`:
Johnson/Desc/K4/Honest/Cells.lean), at two values of what the lookup has sampled (`Forest.Heard`),
two lists of named points AND ANY TWO INPUTS. Two definitions, and statements with their proofs.

  `PtSkel`   two lists of named points: the same names in the same order, the same lengths.
  `find_pt`, `any_rel`   a point by its name; a test on a value that may be missing.
  `length_flatMap_every`, `size_flatMap_const`, `longPhi_size_congr`   lengths, sizes that are one.
  `phiB_rel`, `phiOf_rel`   a family's weights at two lists of points.
  `wtsFit_skel`   does a family have its weights.
  `HasSame`, `has_congr`, **`readsAt_has`**   two reads whose entries have their weights together.
  `affFits_keys`, `affFits_rel`, **`valAff_rel`**   a form's entries; can it be valued.

Debts and ends. `PtSkel` AND `HasSame` ARE ENDS: NO DEBTS: WHEREVER A LAW THAT TAKES ONE OF THEM IS
CALLED BY A LAW THAT DOES NOT TAKE IT ITSELF, IT IS PAID ON THE SPOT. `PtSkel` is concluded in
Law/SkelEnv.lean (`namedPts_skel`, from `PtsSkel`: lengths of sampled values; and its three small
laws) and spent there and here; `readsAt_has` is called besides in Law/SkelStack.lean, with
`namedPts_skel`; in Law/SkelTerms.lean, at the two points of a token, from two lengths, by `All2`'s
constructors; and in Law/SkelJobs.lean, at one list of points, by the library's `All2.refl`.
`HasSame` is concluded by `readsAt_has`, here, from `LookSkel` and `PtSkel`, AT ANY TWO INPUTS w AND
w₀, and by `readsTok_has` (Law/SkelTerms.lean); it is spent here, in Law/SkelTerms.lean, inside one
proof of Law/SkelJobs.lean, and in Law/SkelStack.lean, where it is the field R of `DataSkel`: had
there from `readsAt_has`, or, at one data, by rfl in `dataSkel_refl` (Law/AtEnds.lean). One of the
laws of Law/SkelTerms.lean that take it (`trips_rel`) is called in Law/FitTerms.lean,
Law/TermsAll.lean and Law/AtEnds.lean too, each time with `readsTok_has`. IT COMPARES, ENTRY BY
ENTRY, A BOOL: does the entry have its weights: a test on names, lengths and public numbers
(`wtsFit`); no cell and no weight's digit is read. `LookSkel` (Law/LookSkel.lean) IS A DEBT: see
there.

Not shown here. NOTHING IS SHOWN TO RETURN OR TO BE TRUE ANYWHERE: each statement compares two
calls. Nothing on what an entry or a form is worth.

Kin. `length_flatMap_every` IS A TWIN: it is, up to the bound letters, the library's
`Bind.Twin.length_flatMap_const` (Johnson/Bind/TwinDom.lean), typed again so that that file's
imports stay out: they would nearly double what lies beneath this one. The library's
`length_flatMap_two` and `size_flatMap_two` (Johnson/Desc/First/K4/Returns/Pub/Kit.lean) are the
case n = 2, the second over the numbers below n. `find_pt` follows from `find_all2`
(Law/SkelLists.lean), which stands above this file, by weakening the end. `OptRel`
(OnBytes/Flat/LinksFreeLayer.lean), `All2` (OnBytes/Flat/DryRel.lean) and `FormKeys`, `keysOf`,
`optRel_ite`, `eqTab_size_eq` (Johnson/Desc/First/K4/Returns/Pub/) are the library's.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.Cells
import Johnson.Desc.First.K4.Returns.Pub.PanelsKeys
import Johnson.Desc.ProofFile.Honest.K4.Law.LookSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Aff Forest.Heard eqTab longPhi blockRows)
open OnBytes.Model.Layer (Lay Env TableAsk phiOf)
open OnBytes.Flat (All2 OptRel)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub

/-- Two lists of named points: the same names in the same order, the same lengths. -/
def PtSkel (pt pt₀ : List (String × Array E)) : Prop :=
  All2 (fun x x₀ => x.1 = x₀.1 ∧ x.2.size = x₀.2.size) pt pt₀

/-- A point by its name, in two lists of one skeleton: found in both or in neither, of one length.
-/
theorem find_pt {pt pt₀ : List (String × Array E)} (h : PtSkel pt pt₀) (n : String) :
    OptRel (fun x x₀ : String × Array E => x.2.size = x₀.2.size) (pt.find? fun p => p.1 == n)
      (pt₀.find? fun p => p.1 == n) := by
  induction h with
  | nil => trivial
  | @cons a b l l' h0 _ ih =>
    have e : (a.1 == n) = (b.1 == n) := by rw [h0.1]
    cases hb : (b.1 == n) with
    | true =>
      rw [List.find?_cons_of_pos (p := fun p : String × Array E => p.1 == n) (e.trans hb),
        List.find?_cons_of_pos (p := fun p : String × Array E => p.1 == n) hb]
      exact h0.2
    | false =>
      rw [List.find?_cons_of_neg (p := fun p : String × Array E => p.1 == n) (by
          show ¬ (a.1 == n) = true
          rw [e, hb]
          exact Bool.false_ne_true),
        List.find?_cons_of_neg (p := fun p : String × Array E => p.1 == n) (by
          show ¬ (b.1 == n) = true
          rw [hb]
          exact Bool.false_ne_true)]
      exact ih

/-- A test on a value that may be missing, at two values in R and two tests of one answer on R. -/
theorem any_rel {α : Type} {R : α → α → Prop} {f f₀ : α → Bool} {x y : Option α}
    (h : OptRel R x y) (hf : ∀ a b, R a b → f a = f₀ b) : x.any f = y.any f₀ := by
  cases x <;> cases y
  · rfl
  · exact False.elim h
  · exact False.elim h
  · exact hf _ _ h

/-- Lists of one length n, laid end to end: as many entries as lists times n. -/
theorem length_flatMap_every {α β : Type} (f : α → List β) (n : Nat) (h : ∀ a, (f a).length = n) :
    ∀ l : List α, (l.flatMap f).length = l.length * n
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, h, length_flatMap_every f n h l, List.length_cons,
      Nat.succ_mul, Nat.add_comm]

/-- The same over arrays. -/
theorem size_flatMap_const {α β : Type} (f : α → Array β) (n : Nat) (h : ∀ a, (f a).size = n)
    (xs : Array α) : (xs.flatMap f).size = xs.size * n := by
  rw [← Array.length_toList, Array.toList_flatMap,
    length_flatMap_every _ n (fun a => by rw [Array.length_toList]; exact h a),
    Array.length_toList]

/-- The long tables' weights at two points of one length are as many. -/
theorem longPhi_size_congr {p p₀ : Array E} (h : p.size = p₀.size) (ls lt : Nat) :
    (longPhi p ls lt).size = (longPhi p₀ ls lt).size := by
  unfold longPhi blockRows
  rw [size_flatMap_const _ _ (fun _ => Array.size_map ..),
    size_flatMap_const _ _ (fun _ => Array.size_map ..),
    eqTab_size_eq (z := p.extract 0 ls) (z' := p₀.extract 0 ls)
      (by rw [Array.size_extract, Array.size_extract, h]),
    eqTab_size_eq (z := p.extract ls (ls + lt)) (z' := p₀.extract ls (ls + lt))
      (by rw [Array.size_extract, Array.size_extract, h])]

variable {fo fo₀ : Forest.Heard} {pt pt₀ : List (String × Array E)}

/-- The planes' weights: there at both or at neither, as many. -/
theorem phiB_rel (S : LookSkel fo fo₀) (lm e : Nat) :
    OptRel (fun a b : Array E => a.size = b.size) (OnBytes.Model.Forest.phiB fo lm e)
      (OnBytes.Model.Forest.phiB fo₀ lm e) := by
  have hz : (fo.zb e).size = (fo₀.zb e).size := by
    unfold OnBytes.Model.Forest.Heard.zb
    by_cases he : e = 0
    · rw [if_pos he, if_pos he]
      exact S.zb0
    · rw [if_neg he, if_neg he]
      exact S.zb1
  unfold OnBytes.Model.Forest.phiB
  dsimp only
  rw [S.shape]
  refine optRel_ite (OptRel.some (eqTab_size_eq ?_)) trivial
  rw [Array.size_append, Array.size_append, Array.size_extract, Array.size_extract,
    Array.size_extract, Array.size_extract, hz]

/-- A family's weights: there at both or at neither, as many. -/
theorem phiOf_rel (y : Lay) (S : LookSkel fo fo₀) (h : PtSkel pt pt₀) (a : TableAsk) :
    OptRel (fun a b : Array E => a.size = b.size) (phiOf y fo pt a) (phiOf y fo₀ pt₀ a) := by
  unfold phiOf
  refine optRel_ite (phiB_rel S _ 0) (optRel_ite (phiB_rel S _ 1) (optRel_ite (OptRel.some rfl) ?_))
  have r := find_pt h a.point
  generalize pt.find? (fun p => p.1 == a.point) = o at r ⊢
  generalize pt₀.find? (fun p => p.1 == a.point) = o₀ at r ⊢
  cases o with
  | none =>
    cases o₀ with
    | none => trivial
    | some x₀ => exact False.elim r
  | some x =>
    cases o₀ with
    | none => exact False.elim r
    | some x₀ =>
      have r' : x.2.size = x₀.2.size := r
      dsimp only
      rw [r']
      refine optRel_ite trivial (OptRel.some ?_)
      by_cases hl : a.lng = true
      · rw [if_pos hl, if_pos hl]
        exact longPhi_size_congr r' _ _
      · rw [if_neg hl, if_neg hl]
        exact eqTab_size_eq r'

/-- **Does a family have its weights**: one answer at two lists of one skeleton. -/
theorem wtsFit_skel (y : Lay) (S : LookSkel fo fo₀) (h : PtSkel pt pt₀) (a : TableAsk) :
    wtsFit y fo pt a = wtsFit y fo₀ pt₀ a := by
  unfold wtsFit
  by_cases hp : a.point.isEmpty = true
  · rw [if_pos hp, if_pos hp]
    exact any_rel (phiOf_rel y S h a) fun x x₀ r => by simp only [r]
  · rw [if_neg hp, if_neg hp]
    exact any_rel (find_pt h a.point) fun x x₀ r => by simp only [r]

/-- Two reads whose entries have their weights together. -/
def HasSame (R R₀ : Reads) : Prop := ∀ e, R.has e = R₀.has e

/-- The first family that passes a test, in two lists made of one: its Bool is one. -/
theorem has_congr {α : Type} (l : List α) (g g₀ : α → Fam) (pred : Fam → Bool)
    (h1 : ∀ x, pred (g x) = pred (g₀ x)) (h2 : ∀ x, (g x).fit.get = (g₀ x).fit.get) :
    (match (l.map g).toArray.find? pred with
      | some f => f.fit.get
      | none => false) =
      (match (l.map g₀).toArray.find? pred with
      | some f => f.fit.get
      | none => false) := by
  rw [List.find?_toArray, List.find?_toArray]
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.find?_cons, List.find?_cons, h1 x]
    cases pred (g₀ x)
    · exact ih
    · exact h2 x

/-- **The honest reads at two lists of one skeleton**: both are there or neither is, and their
entries have their weights together. -/
theorem readsAt_has (Q : K4Pub) (w w₀ : K4In) (S : LookSkel fo fo₀) (h : PtSkel pt pt₀) :
    OptRel HasSame (readsAt Q w fo pt) (readsAt Q w₀ fo₀ pt₀) := by
  unfold readsAt famsAt
  cases laidOf Q with
  | none => trivial
  | some laid =>
    intro e
    exact has_congr laid _ _ _ (fun _ => rfl) fun x => wtsFit_skel Q.P.y S h x.1

/-- The test on a form's entries reads, of the form, the entries' places alone. -/
theorem affFits_keys (v : Env) (R : Reads) (a : Aff) :
    affFits v R a = (keysOf a).all fun k => k.1 == v.iU3 && R.has (k.2.1 * v.K3 + k.2.2) := by
  unfold affFits keysOf
  rw [← Array.all_toList, List.all_map]
  rfl

/-- So it gives one answer at two forms that name the same entries, on two reads in `HasSame`. -/
theorem affFits_rel {v v₀ : Env} {R R₀ : Reads} {a a₀ : Aff} (hi : v.iU3 = v₀.iU3)
    (hK : v.K3 = v₀.K3) (hR : HasSame R R₀) (hk : FormKeys a a₀) :
    affFits v R a = affFits v₀ R₀ a₀ := by
  have e : R.has = R₀.has := funext hR
  have hk' : keysOf a = keysOf a₀ := hk
  rw [affFits_keys, affFits_keys, hk', hi, hK, e]

/-- **Can a form be valued.** -/
theorem valAff_rel {v v₀ : Env} {R R₀ : Reads} {a a₀ : Aff} (hi : v.iU3 = v₀.iU3)
    (hK : v.K3 = v₀.K3) (hR : HasSame R R₀) (hk : FormKeys a a₀) (s s₀ : Nat → E) :
    OptRel (fun _ _ => True) (valAff? v R s a) (valAff? v₀ R₀ s₀ a₀) := by
  unfold valAff?
  rw [affFits_rel hi hK hR hk]
  exact optRel_ite trivial trivial

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.PtSkel
#print axioms ProofFile.Honest.K4.find_pt
#print axioms ProofFile.Honest.K4.any_rel
#print axioms ProofFile.Honest.K4.length_flatMap_every
#print axioms ProofFile.Honest.K4.size_flatMap_const
#print axioms ProofFile.Honest.K4.longPhi_size_congr
#print axioms ProofFile.Honest.K4.phiB_rel
#print axioms ProofFile.Honest.K4.phiOf_rel
#print axioms ProofFile.Honest.K4.wtsFit_skel
#print axioms ProofFile.Honest.K4.HasSame
#print axioms ProofFile.Honest.K4.has_congr
#print axioms ProofFile.Honest.K4.readsAt_has
#print axioms ProofFile.Honest.K4.affFits_keys
#print axioms ProofFile.Honest.K4.affFits_rel
#print axioms ProofFile.Honest.K4.valAff_rel
