-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelEnv.lean: CONDITIONAL: on `LookSkel`, on `PtsSkel`, or on
the library's `EnvKeys`.

What is here. CONGRUENCES AND EQUATIONS: the environment that the verifier's forms read (`envOf`,
Johnson/Desc/K4/Honest/Front.lean), made at two lists of what the lookup has sampled, of one
skeleton (`LookSkel`, Law/LookSkel.lean); readers of the environment that do not read the calls'
points; and the named points (`namedPts`, in that file). Five definitions, and statements with their
proofs.

  `mapM_all2_rel`, `amapM_all2_rel`, `amapM_rel`   maps that may yield nothing, over two lists or
      arrays.
  `EnvLook`, **`envOf_rel`**   two environments that differ in the calls' points alone, of one
      length each.
  `rowCells_eq`, `rowAt_eq`, `row5At_eq`, `rowR_eq`, `digitsAt_eq`, `termsForms_eq`   EQUATIONS.
  `PtsSkel`, `ztOf_skel`, **`namedPts_skel`**   two lists of sampled values of one skeleton: the
      same points are named, with the same lengths.
  `lastOf_rel`, `lastL`, `fullL`, `endL`, `namedPts_eq`, `lastL_skel`, `fullL_skel`, `endL_skel`
      the three small functions of which `namedPts` is made, and their laws.

Debts and ends. `EnvLook` IS AN END: NO DEBT. It is named in one statement of its writers' files, as
the end of `envOf_rel`, from `LookSkel` alone. As the field v of `SidesSkel` (Law/SkelSides.lean) it
rides in a hypothesis of inner laws of Law/SkelTerms.lean and Law/SkelStack.lean, each spent with
`sidesOf_rel`, which has it from `envOf_rel`, or, at one shared data, with `sidesSkel_refl`
(Law/AtEnds.lean). ITS CLAUSES sc AND g COMPARE A FIELD OF THE PUBLIC DATA WITH ITSELF: by `envOf`'s
text sc is Q.P.sc, the quantization scales in the verifier's public data of the layers, and g is
Q.g, the group's number; both close by rfl. `envOf` TAKES THE PUBLIC DATA AND THE SAMPLED VALUES,
NOT THE INPUT; of the sampled values it reads the lookup's points of the calls. THE SIX EQUATIONS
TAKE THE LIBRARY's `EnvKeys` AND NOTHING ELSE: the layout, the tables' places and two numbers,
equal. In this family it is had from `envOf_rel` (the field keys of `EnvLook`); outside it `rowR_eq`
is called in Law/W/RightTermsOf.lean, by a law that takes `EnvKeys` as a hypothesis of its own.
`PtsSkel` IS A FIELD OF A DEBT: it is the first field of `PtsFull` (Law/MakersAt.lean: see there for
its payers), and a hypothesis of `namedPts_skel` here and of three laws of Law/SkelStack.lean; no
law ends in it by itself; inside one proof it is PAID by hand, with no `PtsFull`: `k4MakersFit_skel`
(Law/MakersSkel.lean): from `LookSkel` and seven rfl, at the zero challenges. LENGTHS ALONE, beside
`LookSkel`. `LookSkel` IS A DEBT: see Law/LookSkel.lean.

Not shown here. NOTHING IS SHOWN TO RETURN ANYWHERE: each statement compares two calls, but for
`namedPts_eq`, which tells one call again. Nothing on what a form is worth.

Kin. No twin is known to its writers. The library's `EnvKeys`
(Johnson/Desc/First/K4/Returns/Pub/PanelsKeys.lean), the first field of `EnvLook`, holds four fields
of the environment; its `EnvSkel` (Johnson/Road/K4/Total/Returns.lean) three of these. On each of
the six readers the library has the weaker law from less: `rowCells_skel`, `row5At_skel`,
`rowAt_skel`, `rowR_skel`, `digitsAt_skel` (Johnson/Road/K4/Total/SkelReaders.lean) and
`termsForms_skel` (Johnson/Road/K4/Total/TermsGatedSkel.lean): from `EnvSkel` (the sixth takes one
hypothesis more), that both values are there or neither; the six here carry on the row of equations
from `EnvKeys` that begins with `U3at_eq` in Johnson/Desc/First/K4/Returns/Pub/PanelsKeys.lean.
`mapM_all2_rel` is the library's `mapM_opt_rel` (OnBytes/Flat/LinksFreeLayer.lean) over two lists in
S, where that law has one list; `amapM_rel` is its form for one array; the like for folds:
`foldlM_all2_rel`, `afoldlM_all2_rel` (Johnson/Desc/First/K4/Returns/Pub/Kit.lean). `lastOf_rel`
stands beside the library's `lastOf_some` and `lastOf_size`
(Johnson/Desc/First/K4/Returns/Points.lean). Laws of the short names rowAt_eq and rowR_eq, on other
matters, stand in Honest/K12/RunBySpec.lean, Johnson/Top/H0/K2Hands/CallerMade.lean and
Cb/Thin/Pass/RideSegs.lean.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelReads
import OnBytes.Desc.First.K4.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Aff Forest.Heard lastOf cutLast longPoint)
open OnBytes.Model.Layer (Lay Env Heard)
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)
open OnBytes.Desc.First.K4 (digitsAt termsForms)
open OnBytes.Desc.First.K4.Total (tabAt_skel)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub

/-! ## Maps that may yield nothing -/

/-- Two maps that may yield nothing, over two lists in S member by member: both return or neither,
and the returns are in R member by member. -/
theorem mapM_all2_rel {α α' β : Type} {S : α → α' → Prop} {R : β → β → Prop} {f : α → Option β}
    {f' : α' → Option β} (h : ∀ a a', S a a' → OptRel R (f a) (f' a')) {l : List α} {l' : List α'}
    (hl : All2 S l l') : OptRel (All2 R) (l.mapM f) (l'.mapM f') := by
  induction hl with
  | nil =>
    rw [List.mapM_nil, List.mapM_nil]
    exact .nil
  | @cons a b l l' h0 _ ih =>
    rw [List.mapM_cons, List.mapM_cons]
    have h1 := h a b h0
    revert h1 ih
    cases f a <;> cases f' b <;> cases l.mapM f <;> cases l'.mapM f' <;> intro ih h1 <;>
      first
        | trivial
        | exact False.elim h1
        | exact False.elim ih
        | exact All2.cons h1 ih

/-- The same over two arrays. -/
theorem amapM_all2_rel {α α' β : Type} {S : α → α' → Prop} {R : β → β → Prop} {f : α → Option β}
    {f' : α' → Option β} (h : ∀ a a', S a a' → OptRel R (f a) (f' a')) {l : Array α}
    {l' : Array α'} (hl : All2 S l.toList l'.toList) :
    OptRel (fun a a' => All2 R a.toList a'.toList) (l.mapM f) (l'.mapM f') := by
  rw [Array.mapM_eq_mapM_toList, Array.mapM_eq_mapM_toList]
  have r := mapM_all2_rel h hl
  revert r
  cases l.toList.mapM f <;> cases l'.toList.mapM f' <;> intro r
  · trivial
  · exact False.elim r
  · exact False.elim r
  · exact r

/-- The same over one array. -/
theorem amapM_rel {α β : Type} {R : β → β → Prop} {f f' : α → Option β}
    (h : ∀ a, OptRel R (f a) (f' a)) (l : Array α) :
    OptRel (fun a a' => All2 R a.toList a'.toList) (l.mapM f) (l.mapM f') :=
  amapM_all2_rel (S := Eq) (fun a _ e => e ▸ h a) (All2.refl (fun _ => rfl) _)

/-! ## The environment -/

/-- Two environments that differ in the calls' points alone, each point of one length. The NUMBER of
the calls' points is not held: a list that is longer by empty points is in the relation
(`LookSkel` holds the number). -/
structure EnvLook (v v₀ : Env) : Prop where
  keys : EnvKeys v v₀
  sc : v.sc = v₀.sc
  g : v.g = v₀.g
  zk : ∀ q, (v.zk.getD q #[]).size = (v₀.zk.getD q #[]).size

/-- **The environment at two lists of one skeleton**: both calls return or neither, and the two
environments are in `EnvLook`; the second's layout and group are the public data's. -/
theorem envOf_rel (Q : K4Pub) {p p₀ : Pts} (S : LookSkel p.fo p₀.fo) :
    OptRel (fun v v₀ => EnvLook v v₀ ∧ v₀.y = Q.P.y ∧ v₀.g = Q.g) (envOf Q p) (envOf Q p₀) := by
  unfold envOf
  refine optRel_bind_same fun iU3 => optRel_bind_same fun x => ?_
  obtain ⟨tab, a, b⟩ := x
  exact optRel_pure ⟨⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, S.zk⟩, rfl, rfl⟩

variable {v v₀ : Env}

/-- A row's cells read the four fields of `EnvKeys` alone. -/
theorem rowCells_eq (S : EnvKeys v v₀) (P : String) (i cells : Nat) :
    v.rowCells P i cells = v₀.rowCells P i cells := by
  unfold Env.rowCells
  rw [tabAt_skel S.skel, S.y]
  simp only [U3at_eq S]

/-- So does a row with four limbs. -/
theorem rowAt_eq (S : EnvKeys v v₀) (P : String) (i : Nat) : v.rowAt P i = v₀.rowAt P i := by
  unfold Env.rowAt
  rw [rowCells_eq S]

/-- So does a row with five limbs. -/
theorem row5At_eq (S : EnvKeys v v₀) (P : String) (i : Nat) : v.row5At P i = v₀.row5At P i := by
  unfold Env.row5At
  rw [rowCells_eq S]

/-- So does a row's reciprocal, in either form of the row. -/
theorem rowR_eq (S : EnvKeys v v₀) (P : String) (i : Nat) : v.rowR P i = v₀.rowR P i := by
  unfold Env.rowR
  rw [S.y, row5At_eq S, rowAt_eq S]

/-- So do a row's digits. -/
theorem digitsAt_eq (S : EnvKeys v v₀) (P : String) (i : Nat) :
    digitsAt v P i = digitsAt v₀ P i := by
  unfold digitsAt
  rw [rowCells_eq S]

/-- So do the verifier's claims on the values that the second token sumcheck shows. -/
theorem termsForms_eq (S : EnvKeys v v₀) (H : Heard) : termsForms v H = termsForms v₀ H := by
  unfold termsForms
  rw [S.y]
  simp only [rowR_eq S, shA_eq S]

/-! ## The named points -/

/-- Two lists of sampled values of one skeleton: the lookup's in LookSkel; of the sub-protocol's
own, the lengths of those from which a point is named. -/
structure PtsSkel (p p₀ : Pts) : Prop where
  fo : LookSkel p.fo p₀.fo
  PV : p.PV.size = p₀.PV.size
  ZE : p.ZE.size = p₀.ZE.size
  r6 : p.r6.size = p₀.r6.size
  rtV : p.rtV.size = p₀.rtV.size
  rt : p.rt.size = p₀.rt.size
  r12 : p.r12.size = p₀.r12.size
  r14 : p.r14.size = p₀.r14.size

/-- The last k coordinates of two points of one length: there at both or at neither, as many. -/
theorem lastOf_rel {z z₀ : Array E} (h : z.size = z₀.size) (k : Nat) :
    OptRel (fun a b : Array E => a.size = b.size) (lastOf z k).toOption (lastOf z₀ k).toOption := by
  have r := cutLast_rel h k
  unfold lastOf
  revert r
  cases cutLast z k <;> cases cutLast z₀ k <;> intro r
  · trivial
  · exact False.elim r
  · exact False.elim r
  · exact r.2

/-- The lookup's token point has one length at two lists of one skeleton. -/
theorem ztOf_skel (Q : K4Pub) {p p₀ : Pts} (S : LookSkel p.fo p₀.fo) :
    (ztOf Q p).size = (ztOf Q p₀).size := by
  unfold ztOf
  have r := lastOf_rel S.zx Q.P.y.h.lt
  revert r
  cases (lastOf p.fo.zx Q.P.y.h.lt).toOption <;> cases (lastOf p₀.fo.zx Q.P.y.h.lt).toOption <;>
    intro r
  · rfl
  · exact False.elim r
  · exact False.elim r
  · exact r

/-- The last la coordinates of a point under a name; nothing of an empty point or a shorter one. -/
def lastL (la : Nat) (n : String) (z : Array E) : List (String × Array E) :=
  match (lastOf z la).toOption with
  | some x => if z.isEmpty then [] else [(n, x)]
  | none => []

/-- A point under a name, if it has k coordinates and k is not 0. -/
def fullL (n : String) (k : Nat) (z : Array E) : List (String × Array E) :=
  if z.size == k && k != 0 then [(n, z)] else []

/-- The two points of the second token sumcheck's end: nothing unless Z is one point and rt has lt
coordinates. -/
def endL (ls lt : Nat) (Z : List (String × Array E)) (rt : Array E) : List (String × Array E) :=
  match Z, rt.size == lt with
  | [(_, z)], true => [("Y", longPoint (z.extract 0 ls) rt), ("rt", rt)]
  | _, _ => []

/-- What `namedPts` is, in these words. -/
theorem namedPts_eq (Q : K4Pub) (p : Pts) :
    namedPts Q p =
      lastL Q.P.y.h.la "Z" p.fo.zx ++ fullL "zt" Q.P.y.h.lt (ztOf Q p) ++
        lastL Q.P.y.h.la "Z_V" p.r6 ++ fullL "P_V" Q.P.y.h.lt p.PV ++
        fullL "Z_E" Q.P.y.h.la p.ZE ++ fullL "r_tV" Q.P.y.h.lt p.rtV ++
        lastL Q.P.y.h.la "Z_a" p.r12 ++
        endL Q.P.y.ls Q.P.y.h.lt (lastL Q.P.y.h.la "Z" p.fo.zx) p.rt ++
        lastL Q.P.y.h.la "Z_b" p.r14 := rfl

/-- `lastL` at two points of one length. -/
theorem lastL_skel (la : Nat) (n : String) {z z₀ : Array E} (h : z.size = z₀.size) :
    PtSkel (lastL la n z) (lastL la n z₀) := by
  have r := lastOf_rel h la
  unfold lastL Array.isEmpty
  rw [h]
  revert r
  cases (lastOf z la).toOption <;> cases (lastOf z₀ la).toOption <;> intro r
  · exact .nil
  · exact False.elim r
  · exact False.elim r
  · exact ite_rel (R := PtSkel) .nil (.cons ⟨rfl, r⟩ .nil)

/-- `fullL` at two points of one length. -/
theorem fullL_skel (n : String) (k : Nat) {z z₀ : Array E} (h : z.size = z₀.size) :
    PtSkel (fullL n k z) (fullL n k z₀) := by
  unfold fullL
  rw [h]
  exact ite_rel (R := PtSkel) (.cons ⟨rfl, h⟩ .nil) .nil

/-- `endL` at two lists of one skeleton and two points of one length. -/
theorem endL_skel (ls lt : Nat) {Z Z₀ : List (String × Array E)} (hZ : PtSkel Z Z₀)
    {rt rt₀ : Array E} (hr : rt.size = rt₀.size) :
    PtSkel (endL ls lt Z rt) (endL ls lt Z₀ rt₀) := by
  unfold endL
  rw [hr]
  cases hZ with
  | nil => exact .nil
  | @cons a b l l' h0 h1 =>
    obtain ⟨na, za⟩ := a
    obtain ⟨nb, zb⟩ := b
    cases h1 with
    | nil =>
      cases rt₀.size == lt
      · exact .nil
      · refine .cons ⟨rfl, ?_⟩ (.cons ⟨rfl, hr⟩ .nil)
        have e : za.size = zb.size := h0.2
        show (longPoint (za.extract 0 ls) rt).size = (longPoint (zb.extract 0 ls) rt₀).size
        unfold longPoint
        rw [Array.size_append, Array.size_append, Array.size_extract, Array.size_extract, e, hr]
    | cons _ _ => exact .nil

/-- **The same points are named, with the same lengths.** -/
theorem namedPts_skel (Q : K4Pub) {p p₀ : Pts} (S : PtsSkel p p₀) :
    PtSkel (namedPts Q p) (namedPts Q p₀) := by
  rw [namedPts_eq, namedPts_eq]
  have hZ := lastL_skel Q.P.y.h.la "Z" S.fo.zx
  exact ((((((((hZ.append (fullL_skel "zt" _ (ztOf_skel Q S.fo))).append
    (lastL_skel _ "Z_V" S.r6)).append (fullL_skel "P_V" _ S.PV)).append
    (fullL_skel "Z_E" _ S.ZE)).append (fullL_skel "r_tV" _ S.rtV)).append
    (lastL_skel _ "Z_a" S.r12)).append (endL_skel _ _ hZ S.rt)).append (lastL_skel _ "Z_b" S.r14))

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.mapM_all2_rel
#print axioms ProofFile.Honest.K4.amapM_all2_rel
#print axioms ProofFile.Honest.K4.amapM_rel
#print axioms ProofFile.Honest.K4.EnvLook
#print axioms ProofFile.Honest.K4.envOf_rel
#print axioms ProofFile.Honest.K4.rowCells_eq
#print axioms ProofFile.Honest.K4.rowAt_eq
#print axioms ProofFile.Honest.K4.row5At_eq
#print axioms ProofFile.Honest.K4.rowR_eq
#print axioms ProofFile.Honest.K4.digitsAt_eq
#print axioms ProofFile.Honest.K4.termsForms_eq
#print axioms ProofFile.Honest.K4.PtsSkel
#print axioms ProofFile.Honest.K4.lastOf_rel
#print axioms ProofFile.Honest.K4.ztOf_skel
#print axioms ProofFile.Honest.K4.lastL
#print axioms ProofFile.Honest.K4.fullL
#print axioms ProofFile.Honest.K4.endL
#print axioms ProofFile.Honest.K4.namedPts_eq
#print axioms ProofFile.Honest.K4.lastL_skel
#print axioms ProofFile.Honest.K4.fullL_skel
#print axioms ProofFile.Honest.K4.endL_skel
#print axioms ProofFile.Honest.K4.namedPts_skel
