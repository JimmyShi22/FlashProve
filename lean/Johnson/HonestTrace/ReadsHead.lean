-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/ReadsHead.lean

The vector of reads of an honest prover in the sub-proof of the output head, at the description's
own list of tables; where the text that makes that list answers, the vector meets the law of the
reads at all fifteen tables, and the lookup's law at the three tables of the planes.

The description of the protocol makes the head's tables in a step without a round, behind the
sending of the reads: "K8.ReadsQuiet.tables h L hp cov x" (Johnson/Desc/K8/ReadsQuiet.lean), a plain
function; it has no effect but to return an error. h, L, hp: the head's public numbers, layout and
plan. cov: the covered positions, which that step reads off the request's words and the heard reply.
x: what the head's own rounds heard ("Head.Heard", OnBytes/Model/HeadHeard.lean). The fifteen
tables, in the order of docs/format/11-4-output-head.md ("The parts of U3"): two on hf, two on the
borrowed stream, two on hd, six on hr, three on the planes' matrix bH. A table on hf has one member
of the list for each of hf's NHf matrices, so the list has 2 NHf + 13 members. Here no list is
written anew: "headParts" is the list in that function's answer, and an entry of the vector is
"readAt" (Johnson/Desc/K8/Honest/Arrays.lean) at that list.

Main definitions:
* "headParts h L hp cov x": the list of tables in the answer of "tables"; empty where it returns an
  error: there the vector is 0 at every number, and no theorem of this file speaks.
* "u3Head h L hp cov x cell i": entry i of the vector, at the sizes of the plan's list of matrices
  and the integers cell (by the matrix's number in that list, the row of cells, the column).
Main theorems (e: "tables h L hp cov x = .ok t"):
* "headParts_congr": the list reads nine fields of x and no other.
* "tablesLie_head": under e the tables end at or below the plan's number of reads, and no entry lies
  in two of them.
* "u3Head_beyond": under e the vector is 0 from the plan's number of reads on.
* "readsAll_head": under e, where ρ reads integers as integers, a table of entries whose first
  entries of array iU3, up to the plan's number of reads, are "u3Head" read by ρ meets "Fo.ReadsAll"
  at the integers' images.
* "readsAll_head_answers": the same from a test on public numbers and five facts on sizes, in the
  place of e; there the plan's number of reads is not 0.
* "readsLaw_head": under e and the two premises of "readsAll_head", and three premises on the
  planes' matrix, "Fo.ReadsLaw" holds at the three tables on bH, at the lookup's two heard points on
  the planes, read by ρ.
* "holds_head", "tieThird_head": at the reading "Reading.gl": every table holds what it says
  ("Holds", Johnson/Road/FormsKeysMat.lean); the third clause of the smallness test's tie
  ("TieThird", Johnson/Desc/Kinds/Law/TieReads.lean).

Where e is met. "tables_answers" (Johnson/Desc/Kinds/Law/TablesAnswer.lean): under one test on
public numbers and five facts on sizes, four of them on what was heard. By a theorem of the library:
where the library's own test on the three public files accepts, its reader of these files returns,
and "publicOf" at the parameter file and the scale file returns X, the test accepts at X's head
shape, layout and plan (Johnson/Desc/Kinds/Law/TablesPlanInScope.lean). For the fact on a public
number, 5 ≤ lmbH, no theorem is named here. That the heard values of an honest run have these sizes
is shown nowhere here. Under e the plan's number of reads is not 0 ("tables_pos",
Johnson/Desc/Kinds/Law/HeadTabsBelow.lean).

Limits. cov and x are letters: how they come from a request and from an honest run's challenges is
not said here. e is a premise of every theorem but "headParts_congr" and "readsAll_head_answers".
The premise on the table of entries is as in Johnson/HonestTrace/Reads.lean: nothing here sends a
vector. "readsLaw_head" has three premises on the planes' matrix: its rows are one stretch of
2 ^ lmbH, it has at least the planes' columns, and ν reads its cells.

Ground. This file imports Johnson/Desc/K8/Honest/Arrays.lean, through
Johnson/HonestTrace/Reads.lean: it can be built only where the files under Johnson/Desc/K8/Honest/
lie.

Not claimed: that a verifier accepts a proof made of these entries (completeness of the protocol);
anything on soundness or on what a proof shows of the cells.
-/
import Johnson.HonestTrace.ReadsTie
import Johnson.Road.HeadMet
import Johnson.Desc.Reads.HeadAtRecord
import Johnson.Desc.Kinds.Law.FourRunsTie
import Johnson.Desc.Kinds.Law.TablesAnswer
import Johnson.Desc.Kinds.Law.HeadTabsBelow
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (CellsAt)
open OnBytes.Model.Head (Shape HL HPlanH2 Covered Heard Tables)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables ReadsQuiet.tables_ok)

local notation "readAtP" => VerifiableInference.Desc.First.K8.Honest.readAt

/-- **The list of tables of the output head**: the list in the answer of the description's own
"tables" at the head's public numbers, layout and plan, the covered positions and what was heard;
empty where "tables" returns an error. -/
def headParts (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x : Heard) : List HFun :=
  match ReadsQuiet.tables h L hp cov x with
  | .ok t => t.funs.toList
  | .error _ => []

/-- **Entry i of the output head's vector of reads**, at the sizes of the plan's list of matrices
and the integers cell. -/
def u3Head (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) (x : Heard) (cell : CellsAt)
    (i : ℕ) : E :=
  readAtP (parOfMats hp.tl.mats) (headParts h L hp cov x) cell i

variable {h : Shape} {L : HL} {hp : HPlanH2} {cov : Covered} {x : Heard} {t : Tables}

/-- Where "tables" answers t, the list is t's. -/
theorem headParts_ok (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    headParts h L hp cov x = t.funs.toList := by
  unfold headParts
  rw [e]

/-- **What the list reads of the heard values**: two values that agree in what the lookup left,
the merged point, the norm's point, the challenges of the squares' layer and of the three token
sumchecks, and the numbers of two calls give one list. -/
theorem headParts_congr (h : Shape) (L : HL) (hp : HPlanH2) (cov : Covered) {x x' : Heard}
    (e1 : x.g1 = x'.g1) (e2 : x.Zl = x'.Zl) (e3 : x.PV = x'.PV) (e4 : x.wpl.r = x'.wpl.r)
    (e5 : x.tV.r = x'.tV.r) (e6 : x.tN.r = x'.tN.r) (e7 : x.tH.r = x'.tH.r) (e8 : x.qN = x'.qN)
    (e9 : x.qH = x'.qH) : headParts h L hp cov x = headParts h L hp cov x' := by
  have e : ReadsQuiet.tables h L hp cov x = ReadsQuiet.tables h L hp cov x' := by
    unfold ReadsQuiet.tables
    simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9]
  unfold headParts
  rw [e]

/-- **Where "tables" answers, its tables end at or below the plan's number of reads, and no entry
lies in two of them.** -/
theorem tablesLie_head (e : ReadsQuiet.tables h L hp cov x = .ok t) :
    TablesLie hp.tl.mats t.funs (hp.nU.getD 2 0) := by
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, -, hf⟩ := VerifiableInference.Reads.AtSeat.tables_fold e
  have T0 : Road.Hd.TiledF hp.tl.mats ({} : Tables).funs ({} : Tables).p :=
    ⟨fun Fn h => absurd h (Array.not_mem_empty Fn), fun Fn h => absurd h (Array.not_mem_empty Fn)⟩
  have T := Road.Hd.tiled_fold hp.tl.mats _ {} t T0 hf
  have hn : t.p = hp.nU.getD 2 0 := beq_iff_eq.1 (ReadsQuiet.tables_ok e).2
  refine ⟨fun f hf' => ?_, fun f h1 f' h2 col hc col' hc' he => ?_⟩
  · rw [← hn]
    exact T.ends f (Array.mem_toList_iff.1 hf')
  · exact T.apart f (Array.mem_toList_iff.1 h1) f' (Array.mem_toList_iff.1 h2) (f.start + col)
      (Nat.le_add_right _ _) (Nat.add_lt_add_left hc _) (by omega)
      (by rw [he]; exact Nat.add_lt_add_left hc' _)

/-- Where "tables" answers, the vector is 0 from the plan's number of reads on. -/
theorem u3Head_beyond (e : ReadsQuiet.tables h L hp cov x = .ok t) (cell : CellsAt) {i : ℕ}
    (hi : hp.nU.getD 2 0 ≤ i) : u3Head h L hp cov x cell i = zeroE := by
  unfold u3Head
  rw [headParts_ok e]
  exact readAt_beyond (parFits_parOfMats _) (tablesLie_head e) cell hi

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The premise on the entries, in the words of Johnson/HonestTrace/Reads.lean. -/
theorem sentReads_head (e : ReadsQuiet.tables h L hp cov x = .ok t) {cell : CellsAt}
    {entry : ℕ → ℕ → ℕ → K} {iU3 K3 n : ℕ}
    (S : ∀ i < n, _root_.Fo.u3Val entry iU3 K3 i = ρ.val (u3Head h L hp cov x cell i)) :
    SentReads ρ (parOfMats hp.tl.mats) t.funs.toList cell entry iU3 K3 n := by
  intro i hi
  rw [S i hi]
  unfold u3Head
  rw [headParts_ok e]

/-- **The law of the reads at the output head, at all its tables.** Where "tables" answers t, ρ
reads integers as integers, and the entries of array iU3 below the plan's number of reads are
"u3Head" read by ρ, "Fo.ReadsAll" holds of these entries at t's tables and the integers' images. -/
theorem readsAll_head (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K))
    (e : ReadsQuiet.tables h L hp cov x = .ok t) {cell : CellsAt} {entry : ℕ → ℕ → ℕ → K}
    {iU3 K3 : ℕ}
    (S : ∀ i < hp.nU.getD 2 0,
      _root_.Fo.u3Val entry iU3 K3 i = ρ.val (u3Head h L hp cov x cell i)) :
    _root_.Fo.ReadsAll ρ hp.tl.mats t.funs entry iU3 K3 (castM cell) :=
  readsAll_sent ρ hZ (parFits_parOfMats _) (tablesLie_head e) (sentReads_head ρ e S)

/-- **The same with no premise that "tables" answers**: under the test "tabsPlanB" on public numbers
and five facts on sizes (the squares' point has at least la coordinates; the norm's columns' point
at least ls; the norm's positions' point just lt; lmbH is from 5 to the heard shape's kT + 5),
"tables" answers some t, the plan's number of reads is not 0, and "Fo.ReadsAll" holds at t's
tables. -/
theorem readsAll_head_answers (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K))
    (hB : VerifiableInference.Desc.Kinds.Head.Law.tabsPlanB h L hp = true)
    (s1 : h.la ≤ x.wpl.r.size) (s2 : h.ls ≤ (Head.zjOf L x.g1 x.qN).size)
    (s3 : x.tN.r.size = h.lt) (s4 : 5 ≤ h.lmbH) (s5 : h.lmbH ≤ x.g1.shape.kT + 5)
    {cell : CellsAt} {entry : ℕ → ℕ → ℕ → K} {iU3 K3 : ℕ}
    (S : ∀ i < hp.nU.getD 2 0,
      _root_.Fo.u3Val entry iU3 K3 i = ρ.val (u3Head h L hp cov x cell i)) :
    ∃ t, ReadsQuiet.tables h L hp cov x = .ok t ∧ 0 < hp.nU.getD 2 0 ∧
      _root_.Fo.ReadsAll ρ hp.tl.mats t.funs entry iU3 K3 (castM cell) := by
  obtain ⟨_, _, t, e, _⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.tables_answers h L hp cov x hB s1 s2 s3 s4 s5
  exact ⟨t, e, VerifiableInference.Desc.Kinds.Head.Law.tables_pos e, readsAll_head ρ hZ e S⟩

/-- **The lookup's law of the reads at the three tables on the planes' matrix bH**, under the
premises of "readsAll_head", at the lookup's two heard points on the planes, read by ρ. The three
first entries are those that t's table of tables has under the three names. h1: the matrix's rows
are one stretch of 2 ^ lmbH; h2: it has at least the planes' columns; h4: ν reads its cells'
images. -/
theorem readsLaw_head (hZ : ∀ z : ℤ, ρ.val (ofInt z) = (z : K))
    (e : ReadsQuiet.tables h L hp cov x = .ok t) {cell : CellsAt} {entry : ℕ → ℕ → ℕ → K}
    {iU3 K3 : ℕ}
    (S : ∀ i < hp.nU.getD 2 0,
      _root_.Fo.u3Val entry iU3 K3 i = ρ.val (u3Head h L hp cov x cell i))
    (ν : _root_.Fo.Pl → K)
    (h1 : (hp.tl.mats.getD (h.NHf + 1 + 1) {}).m / 2 ^ h.lmbH = 1)
    (h2 : _root_.Fo.planeCols x.g1.shape h.lmbH ≤ (hp.tl.mats.getD (h.NHf + 1 + 1) {}).k)
    (h4 : ∀ r < 2 ^ h.lmbH, ∀ c < _root_.Fo.planeCols x.g1.shape h.lmbH,
      ((cell (h.NHf + 1 + 1) r c : ℤ) : K) = ν (.cell r c)) :
    ∃ tB0 tB1 tP,
      (t.tab.find? fun a => a.1 == "bH-bits-0").map (·.2.1) = some tB0 ∧
      (t.tab.find? fun a => a.1 == "bH-bits-1").map (·.2.1) = some tB1 ∧
      (t.tab.find? fun a => a.1 == "bH-pin").map (·.2.1) = some tP ∧
      _root_.Fo.ReadsLaw x.g1.shape h.lmbH (_root_.Fo.rdL ρ x.g1.zb0) (_root_.Fo.rdL ρ x.g1.zb1) ν
        entry iU3 K3 tB0 tB1 tP := by
  have hh := VerifiableInference.Desc.Kinds.Head.Law.ok_of_tables e {}
    { ch := { dry := true, entries := [] } }
  obtain ⟨_, _, _, _, _, ZV, lowN, qFC, qROW, b0, b1, _, _, _, _, _, z3, z4, e'⟩ :=
    _root_.Fo.tablesOf_tied h L hp cov x _ _ _ _ t hh
  have w0 : ∀ j < 2 ^ h.lmbH, ρ.val (b0.getD j zeroE) =
      (_root_.Fo.phiBK x.g1.shape h.lmbH (_root_.Fo.rdL ρ x.g1.zb0)).getD j 0 := fun j _ => by
    rw [_root_.Fo.rdL_getD, _root_.Fo.phiB_val ρ x.g1 h.lmbH 0 b0 z3]
    rfl
  have w1 : ∀ j < 2 ^ h.lmbH, ρ.val (b1.getD j zeroE) =
      (_root_.Fo.phiBK x.g1.shape h.lmbH (_root_.Fo.rdL ρ x.g1.zb1)).getD j 0 := fun j _ => by
    rw [_root_.Fo.rdL_getD, _root_.Fo.phiB_val ρ x.g1 h.lmbH 1 b1 z4]
    rfl
  obtain ⟨tB0, f0, a0, T0⟩ := _root_.Fo.planeTab_of_tabIs ρ (_root_.Fo.tab_bits0 e') (castM cell) _
    x.g1.shape ν h1 h2 w0 h4
  obtain ⟨tB1, f1, a1, T1⟩ := _root_.Fo.planeTab_of_tabIs ρ (_root_.Fo.tab_bits1 e') (castM cell) _
    x.g1.shape ν h1 h2 w1 h4
  obtain ⟨tP, fP, a2, TP⟩ := _root_.Fo.planeTab_of_tabIs ρ (_root_.Fo.tab_pin e') (castM cell) _
    x.g1.shape ν h1 h2 (fun j hj => _root_.Fo.phiP_val ρ h.lmbH j hj) h4
  exact ⟨tB0, tB1, tP, a0, a1, a2,
    _root_.Fo.readsLaw_of_readsAll ρ (readsAll_head ρ hZ e S) T0 T1 TP⟩

end

/-- **Every table of the head holds what it says of the cells' images**, at the reading
"Reading.gl": where "tables" answers t, tl holds numbers of the smallness test with the plan's list
of matrices, and the entries of array iU3 of the world W below the plan's number of reads are
"u3Head", read. -/
theorem holds_head (e : ReadsQuiet.tables h L hp cov x = .ok t) {tl : HTailF2}
    (hm : tl.mats = hp.tl.mats) {cell : CellsAt} {W : World Cb.Gl.E} {iU3 K3 : ℕ}
    (S : ∀ i < hp.nU.getD 2 0,
      _root_.Fo.u3Val W.entry iU3 K3 i = Reading.gl.val (u3Head h L hp cov x cell i)) :
    ∀ Fn ∈ t.funs, Road.Holds Reading.gl W tl iU3 K3 (castM cell) Fn :=
  holds_sent Reading.gl gl_ofInt (p := parOfMats hp.tl.mats) (by rw [hm]; exact parFits_parOfMats _)
    (by rw [hm]; exact tablesLie_head e) (sentReads_head Reading.gl e S)

/-- **The third clause of the smallness test's tie**, at a table of cells A whose row 0 of the array
u3 holds "u3Head", read, below the plan's number of reads; tl: numbers of the smallness test with
the plan's list of matrices and the tables of t. -/
theorem tieThird_head (e : ReadsQuiet.tables h L hp cov x = .ok t) {tl : HTailF2}
    (hm : tl.mats = hp.tl.mats) (hfuns : tl.funs = t.funs) {cell : CellsAt} {u3 : ℕ}
    {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (S : ∀ i < hp.nU.getD 2 0, A u3 0 i = Reading.gl.val (u3Head h L hp cov x cell i)) :
    VerifiableInference.Desc.Kinds.Head.Law.TieThird tl u3 A cell := by
  refine tieThird_sent (p := parOfMats hp.tl.mats) (n := hp.nU.getD 2 0)
    (by rw [hm]; exact parFits_parOfMats _) (by rw [hm, hfuns]; exact tablesLie_head e)
    fun i hi => ?_
  rw [S i hi, hfuns]
  unfold u3Head
  rw [headParts_ok e]

#print axioms headParts_ok
#print axioms headParts_congr
#print axioms tablesLie_head
#print axioms u3Head_beyond
#print axioms sentReads_head
#print axioms readsAll_head
#print axioms readsAll_head_answers
#print axioms readsLaw_head
#print axioms holds_head
#print axioms tieThird_head

end OnBytes.HonestTrace
