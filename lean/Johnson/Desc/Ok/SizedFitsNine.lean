-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/SizedFitsNine.lean: three ties that the planner makes and, but for one of nine,
no test asks: laws of the making, for all lines and shapes.

docs/format/FORMAT.md, section 18, asks that the stages for which the errors of a proximity test's
rounds were computed are the shape's own stages under the codes that are hashed; that the stored
table has one pair of distances in the key file's plans, the link's and the proof's; and that each
file's errors were computed for the right test on the table (the one-time test in a key file, a
later test in a proof). "sizedFits" (OnBytes/Plan/Ranges.lean) is the first as a test; the planner
asks it of the key's proof of the ranges alone. At the other eight tests "ioppStages"
(OnBytes/Params/Derive.lean) makes the shape's stages from the priced ones. This file shows that
what is so made passes the test, at the file's finished lists of codes.

Main names.
 - ListKeeps, CodesKeep: every code of the one list stands under the same number in the other.
   placeCode_keeps, placeCode_at, ioppStages_keeps.
 - sizedFits_nil, sizedFits_cons.
 - **ioppStages_fits**: the stages that ioppStages returns pass sizedFits against the stages that
   went in, at every list of codes that keeps the list that ioppStages returns.
 - linSized_fits, proofSized_last, solveTest_head, linkSized_first, linkSized_fits.
 - ioppStages_first, **proofSized_linkCodes**: the two codes that a request's shape names for the
   group of its links are the codes of the group that was priced for them.
 - nineFits Z: the nine tests of the three files: the file's codes, the stages as its shape names
   them, the priced stages. Their order: a proof's last test, folded row, Omega, own; a key's
   ranges, folded row, Omega, own; the link's.
 - **sized_fits**, **configure_fits**: sizedFits at all nine.
 - **sized_oneTable**, configure_oneTable: the key's table, the link's and the proof's are one
   record: code, rows, record, answers and distances.
 - sized_rightTest, configure_rightTest: the key's test on the table is a one-time test, the
   proof's is none. They hand keySized_oneTime (OnBytes/Plan/PlanListsKey.lean) and proofSized_set
   (OnBytes/Plan/PlanListsProof.lean) on.
 - sized_oneSetting: the three records of sizes hold one setting, the lines'.

Limits. Laws of "sized" and "configure": they say nothing of sizes or plans that come from
elsewhere, for example written values: there the like is a fact to be shown at these values, or
these laws are spent with "configure l x cfg bits = .ok M" beside them. Implications: that "sized"
returns at any lines is shown by no term here. sizedFits compares numbers of row variables and the
codes' three numbers; it reads no radius, no number of positions and no price. "The priced stages"
is this file's name for fields of the records of sizes: that a plan's entries are priced from these
fields, tables and flags is said by configure_plans (OnBytes/Plan/PlanListsConfigure.lean) and
configure_proofPlans (OnBytes/Plan/PlanListsProof.lean), not here. That a run reads these stages and
these codes is not said here. Where Omega has no test of its own both lists are empty, and the test
says yes. The group of a proof file's links is none of the nine: of it proofSized_linkCodes has the
two codes, and nothing on its numbers of rows. The fourth list of stages in the shape of a test on
the table, testOwnOmega, is empty (linSized_tests) and is none of the nine. For the link the entry's
price is for a link by the routine that is called (linkPlan); no flag says so, and no statement
here. Of the seven plans' own settings nothing. Nothing on soundness.
For proofs only; no module that runs imports this file.

-/
import OnBytes.Params.Fit.StagesFew
import OnBytes.Params.Fit.SizedParts
import OnBytes.Params.EntrySizedLaws
import OnBytes.Params.ConfigureLaws
import OnBytes.Plan.PlanListsConfigure
import OnBytes.Plan.PlanListsProof

set_option autoImplicit false

namespace Johnson.Desc.Ok
open OnBytes OnBytes.Params OnBytes.Plan

/-! ## Lists of codes that keep their numbers -/

/-- Every code of a stands under the same number in b. -/
def ListKeeps (a b : Array Code) : Prop := ∀ (i : Nat) (c : Code), a[i]? = some c → b[i]? = some c

/-- Both lists. -/
structure CodesKeep (a b : Codes) : Prop where
  base : ListKeeps a.base b.base
  mask : ListKeeps a.mask b.mask

theorem CodesKeep.refl (a : Codes) : CodesKeep a a := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem CodesKeep.trans {a b c : Codes} (h : CodesKeep a b) (k : CodesKeep b c) : CodesKeep a c :=
  ⟨fun i x e => k.base i x (h.base i x e), fun i x e => k.mask i x (h.mask i x e)⟩

/-- placeCode moves no number. -/
theorem placeCode_keeps (list : Array Code) (c : CodeSize) :
    ListKeeps list (placeCode list c).1 := by
  unfold placeCode
  dsimp only
  split
  · exact fun _ _ h => h
  · intro i x h
    rw [← Array.getElem?_toList] at h ⊢
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.1 h
    rw [Array.toList_push, List.getElem?_append_left hi]
    exact h

/-- Under the number that placeCode returns stands the code. -/
theorem placeCode_at (list : Array Code) (c : CodeSize) :
    (placeCode list c).1[(placeCode list c).2]? = some ⟨c.logN, c.ell, c.r⟩ := by
  unfold placeCode
  dsimp only
  split
  · rename_i i hi
    obtain ⟨h, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
    show list[i]? = _
    rw [← Array.getElem?_toList, List.getElem?_eq_getElem h]
    exact congrArg some (beq_iff_eq.1 hp)
  · simp

/-- ioppStages moves no number. -/
theorem ioppStages_keeps : ∀ (st : List StageSize) (codes : Codes),
    CodesKeep codes (ioppStages st codes).2
  | [], codes => CodesKeep.refl codes
  | y :: rest, codes => by
    unfold ioppStages
    dsimp only
    exact CodesKeep.trans ⟨placeCode_keeps _ _, placeCode_keeps _ _⟩ (ioppStages_keeps rest _)

/-! ## The test -/

theorem sizedFits_nil (C : Codes) : sizedFits C [] [] = true := by
  simp [sizedFits, zipT_eq]

theorem sizedFits_cons {C : Codes} {t : IoppStage} {ts : List IoppStage} {y : StageSize}
    {ys : List StageSize} (hk : t.k = y.g.k) (hh : t.h = y.g.h)
    (hb : C.base[t.code]? = some ⟨y.g.main.logN, y.g.main.ell, y.g.main.r⟩)
    (hm : C.mask[t.maskCode]? = some ⟨y.g.mask.logN, y.g.mask.ell, y.g.mask.r⟩)
    (hr : sizedFits C ts ys = true) : sizedFits C (t :: ts) (y :: ys) = true := by
  simp only [sizedFits, zipT_eq, List.length_cons, List.zip_cons_cons, List.all_cons,
    Bool.and_eq_true, beq_iff_eq] at hr ⊢
  exact ⟨by omega, ⟨⟨⟨hk, hh⟩, hb⟩, hm⟩, hr.2⟩

/-- **What ioppStages makes passes sizedFits**, at every list that keeps the list it returns. -/
theorem ioppStages_fits : ∀ (st : List StageSize) (codes C : Codes),
    CodesKeep (ioppStages st codes).2 C → sizedFits C (ioppStages st codes).1 st = true
  | [], _, C, _ => sizedFits_nil C
  | y :: rest, codes, C, h => by
    unfold ioppStages at h ⊢
    dsimp only at h ⊢
    have k := ioppStages_keeps rest
      ⟨(placeCode codes.base y.g.main).1, (placeCode codes.mask y.g.mask).1⟩
    exact sizedFits_cons rfl rfl (h.base _ _ (k.base _ _ (placeCode_at _ _)))
      (h.mask _ _ (k.mask _ _ (placeCode_at _ _))) (ioppStages_fits rest _ C h)

/-! ## The test on the table: three tests -/

theorem linSized_fits {s : Setting} {L : LinLines} {T : TableSize} {codes c C : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) (hC : CodesKeep c C) :
    sizedFits C x.shape.testU x.folded.stages = true ∧
      sizedFits C x.shape.testOmega x.omega.stages = true ∧
      sizedFits C x.shape.testOwn x.own.stages = true := by
  obtain ⟨t1, t2, t3, _⟩ := linSized_tests h
  obtain ⟨G, X, Y, Z, a, b, stU, stO, stW, _, _, _, _, _, _, _, eF, eO, eW, _, _, _, _, _, _,
    _, _, ec⟩ := linSized_parts h
  have e1 : x.folded.stages = stU := by rw [eF]
  have e2 : x.omega.stages = stO := by rw [eO]
  have e3 : x.own.stages = stW := by rw [eW]
  rw [t1, t2, t3, e1, e2, e3]
  rw [ec] at hC
  have k3 := ioppStages_keeps stW (ioppStages stO (ioppStages stU codes).2).2
  have k2 := ioppStages_keeps stO (ioppStages stU codes).2
  exact ⟨ioppStages_fits _ _ _ ((k2.trans k3).trans hC), ioppStages_fits _ _ _ (k3.trans hC),
    ioppStages_fits _ _ _ hC⟩

/-- linSized's list keeps the list that went in. -/
theorem linSized_keeps {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) : CodesKeep codes c := by
  obtain ⟨G, X, Y, Z, a, b, stU, stO, stW, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, ec⟩ := linSized_parts h
  rw [ec]
  exact ((ioppStages_keeps stU codes).trans (ioppStages_keeps stO _)).trans
    (ioppStages_keeps stW _)

/-! ## A proof's last test -/

/-- The stages of a proof's last test, and the list of codes with which its test on the table
starts. -/
theorem proofSized_last {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    z.request.last = (ioppStages z.last.stages {}).1 ∧ z.request.code = 0 ∧
      z.request.maskCode = 0 ∧ ∃ (L : LinLines) (T : TableSize),
        linSized (settingOf l) L T (ioppStages z.last.stages {}).2 = some (z.batch, z.codes) := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, hl, h⟩ := opt_bind h
  obtain ⟨stages, hs, h⟩ := opt_bind h
  obtain ⟨T, hT, h⟩ := opt_bind h
  split at h
  rename_i last codes1 he
  replace h := opt_guard h
  obtain ⟨⟨batch, codes2⟩, hb, h⟩ := opt_bind h
  cases h
  rw [← show (ioppStages stages {}).2 = codes1 from congrArg Prod.snd he] at hb
  exact ⟨(congrArg Prod.fst he).symm, rfl, rfl, _, T, hb⟩

/-- The first stage's two codes stand under the number 0 where the lists were empty. -/
theorem ioppStages_first (y : StageSize) (r : List StageSize) {C : Codes}
    (hC : CodesKeep (ioppStages (y :: r) {}).2 C) :
    C.base[0]? = some ⟨y.g.main.logN, y.g.main.ell, y.g.main.r⟩ ∧
      C.mask[0]? = some ⟨y.g.mask.logN, y.g.mask.ell, y.g.mask.r⟩ := by
  unfold ioppStages at hC
  dsimp only at hC
  have k := ioppStages_keeps r
    ⟨(placeCode ({} : Codes).base y.g.main).1, (placeCode ({} : Codes).mask y.g.mask).1⟩
  exact ⟨hC.base _ _ (k.base _ _ (placeCode_at ({} : Codes).base y.g.main)),
    hC.mask _ _ (k.mask _ _ (placeCode_at ({} : Codes).mask y.g.mask))⟩

/-- **The two codes that a request's shape names for the group of its links are those of the group
that was priced for them.** -/
theorem proofSized_linkCodes {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) :
    z.codes.base[z.request.code]? =
        some ⟨z.link.group.main.logN, z.link.group.main.ell, z.link.group.main.r⟩ ∧
      z.codes.mask[z.request.maskCode]? =
        some ⟨z.link.group.mask.logN, z.link.group.mask.ell, z.link.group.mask.r⟩ := by
  obtain ⟨_, c0, m0, L, T, hb⟩ := proofSized_last h
  obtain ⟨_, _, K, _, _, _, _, _, hg, hs, _⟩ := proofSized_parts h
  unfold solveStages at hs
  split at hs
  · cases hs
  · obtain ⟨r, _, e⟩ := Option.map_eq_some_iff.1 hs
    have f := ioppStages_first ⟨z.last.group, z.link.t, 0⟩ r (C := z.codes)
      (by rw [e]; exact linSized_keeps hb)
    rw [hg] at f
    rw [c0, m0]
    exact f

/-! ## The link's test -/

/-- The first of the stages that solveTest returns has the shape's numbers of row variables. -/
theorem solveTest_head {s : Setting} {scope : Scope} {l : GroupLine} {load : GroupLoad}
    {draws : Nat → Nat} {shape : GroupSize} {t : TestSizes}
    (h : solveTest s scope l load draws shape = some t) :
    ∃ y r, t.stages = y :: r ∧ y.g.k = shape.k ∧ y.g.h = shape.h := by
  unfold solveTest at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨st, hs, h⟩ := opt_bind h
  cases h
  have S := solveGroup_solves hx
  unfold solveStages at hs
  split at hs
  · cases hs
  · obtain ⟨r, _, e⟩ := Option.map_eq_some_iff.1 hs
    exact ⟨⟨x.group, x.t, 0⟩, r, e.symm, S.k, S.h⟩

/-- The group for which a link's test was solved has the row variables of the shape's rows. -/
theorem linkSized_first {s : Setting} {l : Lines} {T : TableSize} {codes codes' : Codes}
    {x : LinkSized} (h : linkSized s l T codes = some (x, codes')) :
    ∃ load, solveTest s .once l.onceFolded load id
      (shapeOf l.onceFolded (1 + clog2 x.shape.rows) true) = some x.linked := by
  unfold linkSized at h
  dsimp only at h
  generalize scopePositions s Scope.once
    (tableAnalysis s T).later.agree = first at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_some] at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · rename_i g later c' hio
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hx, hc⟩ := h
    subst hx
    subst hc
    exact ⟨_, ht⟩
  · cases h

theorem linkSized_fits {s : Setting} {l : Lines} {T : TableSize} {codes codes' C : Codes}
    {x : LinkSized} (h : linkSized s l T codes = some (x, codes')) (hC : CodesKeep codes' C) :
    sizedFits C x.shape.test x.linked.stages = true := by
  obtain ⟨⟨a, b, k, h'⟩, later, hio, hc, hm, hl⟩ := linkSized_stages h
  obtain ⟨load, ht⟩ := linkSized_first h
  obtain ⟨y, r, hy, hk, hh⟩ := solveTest_head ht
  have fit := ioppStages_fits x.linked.stages codes C (by rw [hio]; exact hC)
  have kh := kh_of_stages x.linked.stages codes
  rw [hio] at fit kh
  rw [hy] at kh
  simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at kh
  have e : x.shape.test = ⟨a, b, k, h'⟩ :: later := by
    unfold LinkShape.test LinkShape.firstStage
    rw [hl, hc, hm, kh.1.1, kh.1.2, hk, hh]
    rfl
  rw [e]
  exact fit

/-! ## All nine -/

/-- The nine proximity tests of the three files: the file's codes, the stages as its shape names
them, the priced stages. -/
def nineFits (Z : Sized) : List (Codes × List IoppStage × List StageSize) :=
  [(Z.proof.codes, Z.proof.request.last, Z.proof.last.stages),
    (Z.proof.codes, Z.proof.batch.shape.testU, Z.proof.batch.folded.stages),
    (Z.proof.codes, Z.proof.batch.shape.testOmega, Z.proof.batch.omega.stages),
    (Z.proof.codes, Z.proof.batch.shape.testOwn, Z.proof.batch.own.stages),
    (Z.key.codes, Z.key.ranges.x.stages, Z.key.ranges.test.stages),
    (Z.key.codes, Z.key.once.shape.testU, Z.key.once.folded.stages),
    (Z.key.codes, Z.key.once.shape.testOmega, Z.key.once.omega.stages),
    (Z.key.codes, Z.key.once.shape.testOwn, Z.key.once.own.stages),
    (Z.entryCodes, Z.link.shape.test, Z.link.linked.stages)]

/-- **sizedFits at all nine.** -/
theorem sized_fits {l : Lines} {x : Shapes} {Z : Sized} (h : sized l x = .ok Z) :
    ∀ p ∈ nineFits Z, sizedFits p.1 p.2.1 p.2.2 = true := by
  obtain ⟨p0, _, _, L, T, hb⟩ := proofSized_last (sized_proof h)
  obtain ⟨p1, p2, p3⟩ := linSized_fits hb (CodesKeep.refl _)
  obtain ⟨T', L', rows, codes1, _, _, _, ho, hr⟩ := keySized_parts (sized_key h)
  obtain ⟨_, _, _, r1, r2, _⟩ := rangesSized_parts hr
  have kr : CodesKeep codes1 Z.key.codes := by
    rw [r2]
    exact ioppStages_keeps _ _
  obtain ⟨k1, k2, k3⟩ := linSized_fits ho kr
  obtain ⟨_, T'', _, hl⟩ := sized_link h
  have q0 : sizedFits Z.proof.codes Z.proof.request.last Z.proof.last.stages = true := by
    rw [p0]
    exact ioppStages_fits _ _ _ (linSized_keeps hb)
  have q4 : sizedFits Z.key.codes Z.key.ranges.x.stages Z.key.ranges.test.stages = true := by
    rw [r1]
    exact ioppStages_fits _ _ _ (by rw [← r2]; exact CodesKeep.refl _)
  have q8 := linkSized_fits hl (CodesKeep.refl _)
  intro p hp
  simp only [nineFits, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q0
  · exact p1
  · exact p2
  · exact p3
  · exact q4
  · exact k1
  · exact k2
  · exact k3
  · exact q8

theorem configure_fits {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {M : Configured}
    (h : configure l x cfg bits = .ok M) :
    ∀ p ∈ nineFits M.sized, sizedFits p.1 p.2.1 p.2.2 = true :=
  sized_fits (configure_plans h).1

/-! ## One table, the right test, one setting -/

/-- **The key's table, the link's and the proof's are one record.** -/
theorem sized_oneTable {l : Lines} {x : Shapes} {Z : Sized} (h : sized l x = .ok Z) :
    Z.key.once.table = Z.proof.batch.table ∧ Z.link.table = Z.proof.batch.table := by
  have hp := proofSized_table (sized_proof h)
  obtain ⟨T', _, _, _, hT', _, _, ho, _⟩ := keySized_parts (sized_key h)
  obtain ⟨_, T'', hT'', hl⟩ := sized_link h
  refine ⟨?_, ?_⟩
  · rw [linSized_table ho]
    exact Option.some.inj (hT'.symm.trans hp)
  · rw [linkSized_table hl]
    exact Option.some.inj (hT''.symm.trans hp)

theorem configure_oneTable {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {M : Configured} (h : configure l x cfg bits = .ok M) :
    M.sized.key.once.table = M.sized.proof.batch.table ∧
      M.sized.link.table = M.sized.proof.batch.table :=
  sized_oneTable (configure_plans h).1

/-- The key's test on the table is a one-time test, the proof's is none. -/
theorem sized_rightTest {l : Lines} {x : Shapes} {Z : Sized} (h : sized l x = .ok Z) :
    Z.key.once.lines.oneTime = true ∧ Z.proof.batch.lines.oneTime = false :=
  ⟨(keySized_oneTime (sized_key h)).1, (proofSized_set (sized_proof h)).2⟩

theorem configure_rightTest {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {M : Configured} (h : configure l x cfg bits = .ok M) :
    M.sized.key.once.lines.oneTime = true ∧ M.sized.proof.batch.lines.oneTime = false :=
  sized_rightTest (configure_plans h).1

/-- The three records of sizes hold one setting, the lines'. -/
theorem sized_oneSetting {l : Lines} {x : Shapes} {Z : Sized} (h : sized l x = .ok Z) :
    Z.set = settingOf l ∧ Z.proof.set = settingOf l ∧ Z.key.set = settingOf l :=
  ⟨(sized_link h).1, (proofSized_set (sized_proof h)).1, (keySized_oneTime (sized_key h)).2⟩

end Johnson.Desc.Ok

#print axioms Johnson.Desc.Ok.ioppStages_fits
#print axioms Johnson.Desc.Ok.proofSized_linkCodes
#print axioms Johnson.Desc.Ok.configure_fits
#print axioms Johnson.Desc.Ok.configure_oneTable
#print axioms Johnson.Desc.Ok.configure_rightTest
#print axioms Johnson.Desc.Ok.sized_oneSetting
