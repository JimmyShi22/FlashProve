-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadFsWritten.lean: AT THE FULL SIZE's PUBLIC NUMBERS THE SHAPE OF THE LOOKUP
ON THE OUTPUT HEAD's CALLS IS WRITTEN NUMBERS. Statements and proofs.

The head's layout (OnBytes/Model/HeadLayout.lean: Head.layout) makes six calls, the lookup's record
of each, and the numbers of the lookup of all six together (Forest.shape). These numbers read of a
call its number of key bits and of table bits alone, and these read sizes alone: none of the eight
free numbers of the parameter file.

  layout_fs        ONE OPENING of Head.layout that keeps what the library's other openings drop: the
                   numbers' record, the calls, the accept of Forest.shape, the planes' columns.
  numbers_JV       the two sizes of the vocabulary that the calls read.
  lookOne_n, lookOne_k   the lookup's record of a call: its key bits, its table bits.
  SizesH h         the premise: eight equations on the head's public numbers, and its call lines.
  FsWritten L      the conclusion: ten numbers.
  fs_written       MAIN.
  sizesH_scan      the premise holds at the closed form of the parameter file's scan, whatever the
                   eight free numbers are.
  fs_of_steps, fs_in_scope   so the ten numbers stand: off the steps of the public part's text that
                   take no hash (Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean); at all public
                   files in the goals' scope.

WHAT IT IS NOT. Facts on public parameters alone. Nothing on soundness. The
arrays of columns that "place" builds (262,144 entries a call) are never evaluated: a call's column
bits come by Johnson/Goal/Meaning/HeadColsScope.lean's place_lJ.
LETTERS. Under "there is" in layout_fs: L0, calls, fs0, pub: each pinned by an equation.

-/
import Johnson.Goal.Meaning.HeadColsScope
import Johnson.Road.FormsKeysForest
import Johnson.Road.FormsKeysCap
import OnBytes.Tie.Pv.Lookup.Port.FoShape
import OnBytes.Tie.Pv.Lookup.Ends.FoZRec
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model (Call CallD place Forest.Shape)
open OnBytes.Model.Head (Shape HL)
open OnBytes.Road (ok_of_bind)
open OnBytes.Road.Hd (ok_of_needed)

/-- **One opening of the head's layout.** -/
theorem layout_fs {h : Shape} {tauFC : Array UInt64} {L : HL}
    (hy : OnBytes.Model.Head.layout h tauFC = .ok L) :
    ∃ (L0 : HL) (calls : List CallD) (fs0 : Forest.Shape) (pub : Array Nat),
      OnBytes.Model.Head.numbers h = .ok L0 ∧ OnBytes.Model.Head.callsOf h L0 = .ok calls ∧
      L.calls = calls.toArray ∧
      OnBytes.Model.Forest.shape (OnBytes.Model.Head.lookups h tauFC
        (OnBytes.Model.Head.tauFEOf h.famF h.digSh h.tabS) calls) h.LIDB = .ok fs0 ∧
      OnBytes.Model.Forest.planeCols fs0 h.lmbH = .ok L.kb ∧
      L.cl = (OnBytes.Model.Head.lookups h tauFC
        (OnBytes.Model.Head.tauFEOf h.famF h.digSh h.tabS) calls).mapIdx
          (fun q c => { c with iota := fs0.iota.getD q 0 }) ∧
      L.fs = { fs0 with calls := L.cl, pub := pub } := by
  unfold OnBytes.Model.Head.layout at hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨L0, h3, hy⟩ := ok_of_bind hy
  obtain ⟨calls, h4, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨fs, h7, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨kb, h9, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  cases hy
  exact ⟨L0, calls, fs, pub, h3, h4, rfl, h7, h9, rfl, rfl⟩

/-- The two sizes of the vocabulary in the record of numbers. -/
theorem numbers_JV {h : Shape} {L0 : HL} (hn : OnBytes.Model.Head.numbers h = .ok L0) :
    L0.JV = OnBytes.Model.roundUp h.V h.S2 ∧
      L0.JVa = 2 ^ (OnBytes.ceilLog2 (OnBytes.Model.roundUp h.V h.S2) - 1) := by
  unfold OnBytes.Model.Head.numbers at hn
  obtain ⟨-, -, hn⟩ := ok_of_bind hn
  obtain ⟨-, -, hn⟩ := ok_of_bind hn
  cases hn
  exact ⟨rfl, rfl⟩

/-- The lookup's record of one call. -/
def lookOne (h : Shape) (tauFC tauFE : Array UInt64) (c : CallD) : Call :=
  let base : Call :=
    { name := c.name, n := OnBytes.Model.Head.callBits h c, kappa := 5,
      k := if c.kind == "R8" then 8 else 16 }
  if c.kind == "FC" then { base with fn := 1, t0 := 32768, tau := some tauFC }
  else if c.kind == "FE" then { base with fn := 1, t0 := 0, tau := some tauFE }
  else base

theorem lookups_is (h : Shape) (a b : Array UInt64) (calls : List CallD) :
    OnBytes.Model.Head.lookups h a b calls = (calls.map (lookOne h a b)).toArray := rfl

theorem lookOne_n (h : Shape) (a b : Array UInt64) (c : CallD) :
    (lookOne h a b c).n = c.lJ + h.lt := by
  unfold lookOne
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem lookOne_k (h : Shape) (a b : Array UInt64) (c : CallD) :
    (lookOne h a b c).k = if c.kind == "R8" then 8 else 16 := by
  unfold lookOne
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- **The head's public numbers that the lookup's shape reads, at the full size.** -/
structure SizesH (h : Shape) : Prop where
  lt : h.lt = 10
  d : h.d = 5120
  V : h.V = 202048
  S2 : h.S2 = 64
  XL : h.XL = 5
  floor : OnBytes.Model.Head.keyFloor h = 27
  LIDB : h.LIDB = 28
  lmbH : h.lmbH = 15
  lines : OnBytes.Model.Head.callLines h = VerifierAndGoals.Lines.callsHRef

/-- **The numbers of the lookup on the head's calls.** -/
structure FsWritten (L : HL) : Prop where
  NC : L.fs.NC = 6
  calls : L.fs.calls.size = 6
  dT : L.fs.dT = 27
  kT : L.fs.kT = 16
  cK : L.fs.cK = 3
  NT : L.fs.NT = 9
  rK : L.fs.rK = 4
  kb : L.kb = 384
  elems : OnBytes.Model.Forest.elems L.fs = 1995
  n0 : ((L.fs.calls[0]?).map (·.n)).getD 0 = 28

/-- A fold over six. -/
theorem foldl_six {α β : Type} (f : β → α → β) (b : β) (a0 a1 a2 a3 a4 a5 : α) :
    (#[a0, a1, a2, a3, a4, a5] : Array α).foldl f b =
      f (f (f (f (f (f b a0) a1) a2) a3) a4) a5 := by
  simp

/-- **AT THE FULL SIZE's PUBLIC NUMBERS THE SHAPE OF THE LOOKUP ON THE HEAD's CALLS IS WRITTEN
NUMBERS.** -/
theorem fs_written {h : Shape} {tauFC : Array UInt64} {L : HL} (Z : SizesH h)
    (hy : OnBytes.Model.Head.layout h tauFC = .ok L) : FsWritten L := by
  obtain ⟨L0, calls, fs0, pub, h3, h4, _, h7, h9, hcl, hfs⟩ := layout_fs hy
  obtain ⟨j1, j2⟩ := numbers_JV h3
  have hJV : L0.JV = 202048 := by
    rw [j1, Z.V, Z.S2]
    decide
  have hJVa : L0.JVa = 131072 := by
    rw [j2, Z.V, Z.S2]
    decide
  have hc := calls_six h4 Z.lines
  rw [Z.d, hJV, hJVa, Z.XL, Z.floor, Z.lt] at hc
  generalize OnBytes.Model.Head.tauFEOf h.famF h.digSh h.tabS = tauFE at h7 hcl
  rw [lookups_is, hc] at h7 hcl
  simp only [List.map_cons, List.map_nil] at h7 hcl
  -- the key bits and the table bits of the six
  have n0 : (lookOne h tauFC tauFE (place "R16a" "R16"
      [("NF", 5120, false), ("NFH", 5120, false), ("HD0", 202048, false)] (27 - 10))).n = 28 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n1 : (lookOne h tauFC tauFE (place "R16b" "R16" [("HD1", 202048, false)] (27 - 10))).n =
      28 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n2 : (lookOne h tauFC tauFE (place "R8" "R8"
      [("ROW", OnBytes.Model.ledNRH 5, false), ("HD2", 202048, false)] (27 - 10))).n = 28 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n3 : (lookOne h tauFC tauFE (place "FEa" "FE" [("HE0", 131072, false)] (27 - 10))).n =
      27 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n4 : (lookOne h tauFC tauFE (place "FEb" "FE" [("HE1", 202048 - 131072, false)]
      (27 - 10))).n = 27 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  have n5 : (lookOne h tauFC tauFE (place "FC" "FC" [("CNF", 5120, false)] (27 - 10))).n = 27 := by
    rw [lookOne_n, place_lJ _ _ _ _ (by decide), Z.lt]
    decide
  obtain ⟨_, m2, _, m4, _⟩ := Cb.Fo.shape_more h7
  have d1 := OnBytes.Road.shape_dT h7
  have k1 := Fo.ZPlan.shape_cK h7
  obtain ⟨i1, i2, i3, _⟩ := OnBytes.Road.shape_numbers h7
  have eNC : fs0.NC = 6 := m2
  have edT : fs0.dT = 27 := by
    rw [d1, foldl_six, n0, n1, n2, n3, n4, n5, Z.LIDB]
    decide
  have ekT : fs0.kT = 16 := by
    rw [m4, foldl_six]
    simp only [lookOne_k]
    decide
  have ecK : fs0.cK = 3 := by
    rw [k1]
    show OnBytes.Model.clog2 6 = 3
    decide
  have eio : fs0.iota = #[1, 1, 1, 0, 0, 0] := by
    rw [i1, edT]
    simp only [List.map_toArray, List.map_cons, List.map_nil, n0, n1, n2, n3, n4, n5]
  have eNT : fs0.NT = 9 := by
    rw [i2, eio]
    show ∑ c ∈ Finset.range 6, 2 ^ (#[1, 1, 1, 0, 0, 0] : Array Nat).getD c 0 = 9
    decide
  have erK : fs0.rK = 4 := by
    rw [i3, eNT]
    decide
  have ekb : L.kb = 384 := by
    unfold OnBytes.Model.Forest.planeCols at h9
    rw [Z.lmbH, ekT, eNC] at h9
    exact (Except.ok.inj h9).symm
  refine ⟨by rw [hfs]; exact eNC, ?_, by rw [hfs]; exact edT, by rw [hfs]; exact ekT,
    by rw [hfs]; exact ecK, by rw [hfs]; exact eNT, by rw [hfs]; exact erK, ekb, ?_, ?_⟩
  · rw [hfs]
    show L.cl.size = 6
    rw [hcl, Array.size_mapIdx]
    rfl
  · unfold OnBytes.Model.Forest.elems OnBytes.Model.Forest.Shape.v OnBytes.Model.Forest.Shape.d
    rw [hfs]
    show _ = 1995
    simp only [edT, erK, ekT, ecK]
    decide
  · rw [hfs]
    show ((L.cl[0]?).map (·.n)).getD 0 = 28
    rw [hcl]
    simp [n0]

/-- **The premise, at the scan's closed form**: whatever the eight free numbers are. -/
theorem sizesH_scan (v : VerifierAndGoals.FreeLines) (y : OnBytes.Model.Layer.Lay) :
    SizesH (OnBytes.Model.Verify.headShape (VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef v) y) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Off the steps of the public part's text that take no hash**, where the scan is the closed
form: so at the library's publicOf and at publicOfO o alike. -/
theorem fs_of_steps {pol KL : ByteArray} {X : OnBytes.Model.Verify.Public}
    (St : VerifiableInference.PlanWritten.PublicSteps pol KL X) {v : VerifierAndGoals.FreeLines}
    (hP : X.P = VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef v) : FsWritten X.HLy :=
  fs_written (by rw [St.hS, hP]; exact sizesH_scan v _) St.head

/-- **AT ALL PUBLIC FILES IN THE GOALS' SCOPE.** -/
theorem fs_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : OnBytes.Model.Verify.publicOf Z.pol Z.KL lay = .ok X) : FsWritten X.HLy :=
  fs_of_steps (VerifiableInference.PlanWritten.publicSteps_of h)
    (OnBytes.Road.Hd.scan_of_scope hZ hR h)

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.sizesH_scan
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.fs_of_steps
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.fs_in_scope
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.layout_fs
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.fs_written
