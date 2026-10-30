-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Rows.lean: THE CLOSING OF A SEGMENT (K10): THE MAKE OF THE SINGLE ROWS
THAT A YES LAYS INTO THE FRAME, ALL BUT ITS FORMS' MAKE: FROM THE YES ALONE. Lemmas on the
verifier's own text; no honest side's frame in them; none of the library's goals.

  `keptRowsS`, `keptRowsS_eq`   the count of kept rows, off the statement's shape
  `RowsMake`       what is said of the record in front (s), the place's parameters and the single
                   rows R: at the data D that the record names: the two codes' numbers are the
                   request's; the layout is the fold's shape's (the group's, with the request's
                   group's k and h laid in); there are k challenges, k the place's AND the
                   layout's; two masks; the fresh mask's number is the frame's; BOTH VECTORS ON
                   THE MASK TABLES HAVE THE MASK CODE's MESSAGE LENGTH; the count of kept rows is
                   `keptRowsS` of the statement's shape; the layout's h (the request's group's:
                   the place's own h is read by no clause) is at most k; the layout's three lists
                   are as long as its list of members; the fresh mask's message has 2^h mask rows
  `rows_make`      each yes of the decision: `RowsMake` of the single rows behind
  `yes_carried`    THE LIBRARY's OWN FOUR FACTS ON THESE ROWS, at a yes of the block's decision:
                   what the next code switching keeps is the group's kept members, in order; the
                   count of kept rows is the sum of their main rows; every tensor of the form on the
                   main table has the main code's number of place bits; both vectors' lengths. ITS
                   SUMS, BITS AND LENGTHS ARE AT THE STATEMENT BEHIND, its group is the one in
                   front; `RowsMake` speaks at the statement in front

THE LENGTHS ARE THE LIBRARY's (`foldMaskForm_size`, `foldMaskWeights_size`,
Johnson/Desc/First/Close/Law/CarriedRows.lean: another file of this kind's laws): they are called
here. WHAT STANDS IN OTHER FILES. The library's `CarriedOk` names the two lengths and the
count of kept rows: clause 7 here is its d0 and d1, with "just two vectors" and the codes in front
for those behind; clause 8 is a second wording of its keptRows: there a sum over what the next
switching keeps, at the statement behind; here the library's own fold, on the shape of the
statement in front. The two codes' numbers, the layout, two masks and the fresh mask's number are
Returns.lean's `rows_shape`; the k challenges its `CloseLeft`. OFF THE SAME YES THE LIBRARY ALSO
STATES, in files not called here: the k challenges (`closing_inv2`, First/Close/Law/Whole.lean, at
the plan's k, and `closeFrame_k`, KOfYes.lean, that this is the place's: the two together); that the
statement's own layout of the group has the request's group's k and h, so that laying these in turns
nothing (`closeFrame_kh`, KOfYes.lean); that the layout's members and flags are the group's
(`closeFrame_groups`, GroupsStay.lean); h ≤ k, the layout's three sizes and the fresh mask's 2^h
rows (`layFits_of_close`, Johnson/Desc/K2/Honest/Returns/ClosedReached.lean; and as what the two
tests on the fold's shape and mask check: Johnson/Desc/Own/FoldMean.lean). The files named here do
not state the whole as one sentence, in the order of a shape's fields.

Limits. OF THE FORM ON THE MAIN TABLE `RowsMake` SAYS NOTHING, and `yes_carried` one thing (each
tensor's number of variables); OF THE KEPT FORMS (how many, on which oracle messages, each one's
make) NOTHING IS SAID HERE: they hang on the batched row (`forms_behind`, AtMakes.lean). The
layout's clause stands at the record, not on the shape (that: `layoutS_eq`,
Johnson/Desc/Ground/Shape/Ground.lean). Of the block's decision at the kind's own record. It
stands over two files of another author's (Johnson/Desc/Ground/Shape/Core.lean, Ground.lean),
and over files of this
folder. AtMakes.lean STANDS OVER THIS FILE AND OVER OTHER AUTHORS' FILES: a tree may hold this
file without it: what this head says of it is then said of no file of that tree. Shown of no
honest run. Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Fits
import Johnson.Desc.K10.Honest.OnShape
import Johnson.Desc.First.Close.Law.CarriedRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Means VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.Ground.Sh

/-- The count of kept rows, off the statement's shape. -/
def keptRowsS (a : StSh) (L : GroupLayout) : Nat :=
  (List.range L.members.size).foldl (fun n i =>
    if L.kept.getD i false then
      n + ((a.oracles[L.members.getD i noId]?).map (·.shape.mainRows)).getD 0
    else n) 0

theorem keptRowsS_eq (S : Statement) (F : FoldShape) (row : GroupRow) (m : Nat) (eps : E)
    (gamma : List E) (claim : E) :
    (foldOutput S F row m eps gamma claim).keptRows = keptRowsS (stSh S) F.layout := by
  unfold keptRowsS
  show (List.range F.layout.members.size).foldl _ 0 = _
  congr 1
  funext n i
  rw [orc_get]
  cases S.oracles[F.layout.members.getD i noId]? <;> rfl

/-- **What is said of the single rows behind**, at the record in front and the data that it names:
fourteen clauses, the first eight in the order of a shape's fields. -/
def RowsMake (P : Par) (s : Rec) (D : BaseData) (R : SingleRows) : Prop :=
  R.code = s.frame.shape.code ∧ R.maskCode = s.frame.shape.maskCode ∧ R.layout = (D.F s).layout ∧
    R.gamma.length = P.k ∧ R.masks = 2 ∧ R.fresh = D.m ∧
    R.d.toList.map (·.size) =
      [(s.st.codes.mask.getD s.frame.shape.maskCode default).ell,
        (s.st.codes.mask.getD s.frame.shape.maskCode default).ell] ∧
    R.keptRows = keptRowsS (stSh s.st) (D.F s).layout ∧
    R.layout.k = P.k ∧ R.layout.h ≤ R.layout.k ∧
    R.layout.kept.size = R.layout.members.size ∧
    R.layout.mainFirst.size = R.layout.members.size ∧
    R.layout.maskFirst.size = R.layout.members.size ∧
    (s.st.oracles[D.m]?).map (·.shape.maskRows) = some (2 ^ R.layout.h)

/-- The count of kept rows reads the messages' shapes alone: so it is the same at the statement
behind the closing as in front. -/
theorem keptRowsS_behind (S : Statement) (g : Nat) (G : Group) (m : Nat) (L : GroupLayout) :
    keptRowsS (stSh (spent (Slice.begun S g G) m)) L = keptRowsS (stSh S) L := by
  unfold keptRowsS
  congr 1
  funext n i
  have e := congrArg (Option.map fun x : OracleShape => x.mainRows)
    (behind_shape S g G m (L.members.getD i noId))
  rw [Option.map_map, Option.map_map] at e
  rw [orc_get, orc_get, Option.map_map, Option.map_map]
  have e' : (((spent (Slice.begun S g G) m).oracles[L.members.getD i noId]?).map
      ((fun x : OrcSh => x.shape.mainRows) ∘ orcSh)) =
      ((S.oracles[L.members.getD i noId]?).map ((fun x : OrcSh => x.shape.mainRows) ∘ orcSh)) := e
  rw [e']

/-- What the verifier's test on a fold's shape gives, as far as it is spent here: off the library's
own opening of that test (`Own.foldShapeFits_iff`, Johnson/Desc/Own/FoldMean.lean). -/
theorem shapeFits_gives {S : Statement} {F : FoldShape} (h : Own.foldShapeFits S F = true) :
    F.layout.h ≤ F.layout.k ∧
      2 * F.layout.k + 1 - F.layout.h ≤ (S.codes.mask.getD F.maskCode default).ell ∧
      F.layout.kept.size = F.layout.members.size ∧
      F.layout.mainFirst.size = F.layout.members.size ∧
      F.layout.maskFirst.size = F.layout.members.size := by
  obtain ⟨c, zk, _, hz, _, a4, _, a6, a7, a8, a9, _⟩ := (Own.foldShapeFits_iff S F).1 h
  have ez : S.codes.mask.getD F.maskCode default = zk := by
    rw [Array.getD_eq_getD_getElem?, hz]
    rfl
  rw [ez]
  exact ⟨a4, a6, a7, a8, a9⟩

/-- **EACH YES OF THE DECISION: THE MAKE OF THE SINGLE ROWS BEHIND, ALL BUT THE FORMS'.** -/
theorem rows_make {Cl : Type} {P : Par} {s s' : Rec} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : ((kind (Cl := Cl)) P).decide s rs gs = .ok s') :
    ∃ D, baseData s = some D ∧ RowsMake P s D s'.frame.rows := by
  obtain ⟨_, _, hA, hB⟩ := (close_yes_split (Cl := Cl) P s rs gs).1 ⟨s', h⟩
  obtain ⟨D, hD, rB, rE, rR, t, row, sum, eps, gamma, claim, rfl, ht, hrow, _, _, hlen, rfl⟩ :=
    yes_left h
  refine ⟨D, hD, ?_⟩
  unfold closeShapeB at hA
  rw [hD] at hA
  have hA' : shapeAtB P s D = true := hA
  unfold shapeAtB at hA'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Option.isNone_iff_eq_none,
    and_assoc] at hA'
  obtain ⟨_, _, _, _, _, _, _, a8, a9, a10, _⟩ := hA'
  have hbd : batDraw (rB :: rE :: rR) = [t] := by simp [batDraw, ht]
  unfold closeValsB at hB
  rw [hD, hbd] at hB
  have hB' : (match Own.batch (D.S1 s) s.frame.group
      ⟨Own.layoutOf s.st D.G, Slice.runRows s.st D.G⟩ (E.ofTriple t) with
    | some row => Own.foldRowFits (spent (D.S1 s) D.m) (D.F s) row
    | none => false) = true := hB
  rw [hrow] at hB'
  obtain ⟨c4, c6, c7, c8, c9⟩ := shapeFits_gives a9
  have hcod : (D.S1 s).codes = s.st.codes := (extends_begun s.st s.frame.group D.G).codes
  have hcod2 : (spent (D.S1 s) D.m).codes = s.st.codes := behind_codes _ _ _ _
  have hk : (D.F s).layout.k = P.k := a8.symm
  have hd : row.d.size =
      (s.st.codes.mask.getD s.frame.shape.maskCode default).ell * 2 ^ (D.F s).layout.h := by
    unfold Own.foldRowFits at hB'
    simp only [Bool.and_eq_true, beq_iff_eq] at hB'
    have := hB'.1.2
    rw [hcod2] at this
    exact this
  rw [hcod] at c6
  have hm : (s.st.oracles[D.m]?).map (·.shape.maskRows) = some (2 ^ (D.F s).layout.h) := by
    unfold Own.foldMaskFits at a10
    have e := Slice.closeLedgers_shape D.G.members.toList s.st D.m
    have e2 : ((D.S1 s).oracles[D.m]?).map (·.shape) = (s.st.oracles[D.m]?).map (·.shape) := e
    cases ho : (D.S1 s).oracles[D.m]? with
    | none => rw [ho] at a10; cases a10
    | some o =>
      rw [ho] at a10 e2
      simp only [Bool.and_eq_true, beq_iff_eq] at a10
      have hr : o.shape.maskRows = 2 ^ (D.F s).layout.h := a10.1.1.1.1.2
      cases hs : s.st.oracles[D.m]? with
      | none =>
        rw [hs] at e2
        cases e2
      | some x =>
        rw [hs] at e2
        have e3 : o.shape = x.shape := Option.some.inj e2
        show some x.shape.maskRows = _
        rw [← e3, hr]
  refine ⟨rfl, rfl, rfl, hlen, rfl, rfl, ?_, ?_, hk, c4, c7, c8, c9, hm⟩
  · show [(foldMaskForm (D.F s).layout.h row.d eps gamma).size,
      (foldMaskWeights (D.F s).layout.k (D.F s).layout.h
        ((spent (D.S1 s) D.m).codes.mask.getD (D.F s).maskCode default).ell gamma.toArray).size] = _
    rw [hcod2, foldMaskWeights_size _ _ _ _ c4 c6, foldMaskForm_size, hd, hlen, ← hk,
      Nat.min_eq_left c4, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    rfl
  · show (foldOutput (spent (D.S1 s) D.m) (D.F s) row D.m eps gamma claim).keptRows = _
    rw [keptRowsS_eq]
    exact keptRowsS_behind _ _ _ _ _

/-- **THE LIBRARY's OWN FOUR FACTS ON THESE ROWS** (`CarriedOk`, `closeFrame_carried`,
Johnson/Desc/First/Close/Law/CarriedRows.lean), at a yes of the block's decision. -/
theorem yes_carried {Cl : Type} {P : Par} {s s' : Rec} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : ((kind (Cl := Cl)) P).decide s rs gs = .ok s') :
    ∃ (Gf : ReqGroup) (G : Group), s.frame.groups[s.frame.link]? = some Gf ∧
      s.st.groups[s.frame.group]? = some G ∧
      CarriedOk { code := s.frame.shape.code, maskCode := s.frame.shape.maskCode, k := Gf.k,
                  h := Gf.h, entries := entries P } G s'.st s'.frame.rows := by
  obtain ⟨x, hx, rfl⟩ := (kind_decide_iff P s s' rs gs).1 h
  exact closeFrame_carried hx

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.rows_make
#print axioms ProofFile.Honest.K10.YesFree.yes_carried
#print axioms ProofFile.Honest.K10.YesFree.keptRowsS_eq
