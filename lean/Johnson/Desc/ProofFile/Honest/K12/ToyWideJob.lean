-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ToyWideJob.lean: a small made-up example of a proximity test whose
group has three members in three trees: the parameters, the written tables, a state on entry to the
test, computed by the description's own functions at these tables, the job (`TestJob`) and its
random values. Definitions only.

The group: member 0 has three main rows over the base field, in a tree of depth 5. Member 1 has two
main rows over the extension field and one mask row, in a second tree of depth 5. Member 2 has one
mask row alone, in a tree of depth 4. The first fold sends its own fresh table of two rows, in a
tree of depth 4. The stage's main table has eight rows: member 0's from row 0 on, member 1's from
row 4 on; rows 3, 6 and 7 are no member's. Its mask table has two rows: member 1's and member 2's.
Three stages, with (k, h) = (3, 1), (1, 1), (0, 0).

Limits. Made-up numbers. Nothing is evaluated or proved here; RunManyToy.lean has tests at this
example. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Test
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K1.Own

set_option autoImplicit false

namespace ProofFile.Honest.K12.ToyWide
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link (PS wordsOf wr mainSym maskSym)
open H2K.Pub (sgOf)

/-! ## 1 The place -/

def codes : Codes :=
  ⟨#[⟨5, 4, 2⟩, ⟨6, 2, 2⟩, ⟨8, 2, 2⟩], #[⟨4, 8, 2⟩, ⟨5, 16, 2⟩, ⟨7, 64, 2⟩]⟩
def s0 : Fmt.M1.Stage := ⟨⟨5, 4, 2⟩, ⟨4, 8, 2⟩, 3, 1, 2⟩
def s1 : Fmt.M1.Stage := ⟨⟨6, 2, 2⟩, ⟨5, 16, 2⟩, 1, 1, 2⟩
def s2 : Fmt.M1.Stage := ⟨⟨8, 2, 2⟩, ⟨7, 64, 2⟩, 0, 0, 2⟩
def ft : ℕ := 7
def n0 : OracleNotice := ⟨{ code := 0, mainRows := 3, mainDeg := 1, answers := 1 }, 0⟩
def n1 : OracleNotice :=
  ⟨{ code := 0, mainRows := 2, mainDeg := 3, maskRows := 1, maskCode := 0, answers := 1 }, 1⟩
def n2 : OracleNotice := ⟨{ maskRows := 1, maskCode := 0, answers := 1 }, 2⟩
def send : K1.Par :=
  { place := ⟨2, none, 1, .K1⟩, codes := codes, gp := ⟨1, ft⟩, work := 0
    parts := [("base", #[n0]), ("main", #[n1]), ("mask", #[n2])] }
def d0 : _root_.Desc.Plain.DState Unit := ⟨{ codes := codes }, {}, 0, [], ()⟩
def nums : H2U.TestNums :=
  { rows := 4, work := 0, stages := [s0, s1, s2], ownMask := true
    first := [(⟨5, 3, false, ft⟩, .own 0), (⟨5, 9, false, ft + 1⟩, .own 1),
      (⟨4, 3, false, ft + 2⟩, .own 2)], free := 3
    firstTree := ft }
def p : P12 := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ ⟨2, 0, nums, [(0, 0), (1, 1), (2, 2)], 1, 1, true⟩
def declared : List Fmt.DeclaredRound := (H2U.roundsOfNums nums).getD []

/-- Challenges off a list of declared rounds. -/
def genOf (ds : List Fmt.DeclaredRound) (n : ℕ) : List Fmt.Drawn :=
  ds.zipIdx.map fun d =>
    ⟨(List.range d.1.entry.drawE).map fun i =>
        ((3 + 5 * d.2 + i + n).toUInt64, (1 + d.2 + 2 * i).toUInt64, (2 + i + 3 * n).toUInt64),
      (List.range d.1.entry.poss).map fun i => (7 * i + 3 * d.2 + 1 + 5 * n) % 2 ^ d.1.entry.logN,
      [], none⟩

/-- What the sending's first round sampled. -/
def r1 : Fmt.RoundView := ⟨[], (genOf (K1.sendOwn (Cl := Unit) send).rounds 2).headD ⟨[], [], [], none⟩⟩

/-! ## 2 The tables, and the state on entry at true values -/

def tri (x y z : ℕ) : E := E.ofTriple (x.toUInt64, y.toUInt64, z.toUInt64)

/-- Member 0, over the base field: row i, place e; its tails. w: the input, added to entry (0, 0).
-/
def m0E (w i e : ℕ) : E := tri (11 + 7 * i + e + (if i = 0 ∧ e = 0 then w else 0)) 0 0
def m0Tl (i q : ℕ) : E := tri (101 + 3 * i + q) 0 0
/-- Member 1: two main rows; one mask row; their tails. -/
def m1E (i e : ℕ) : E := tri (31 + 5 * i + e) (3 + i) (5 + 2 * e)
def m1Tl (i q : ℕ) : E := tri (131 + 3 * i + q) 7 (1 + q)
def m1Z (e : ℕ) : E := tri (201 + e) (2 + e) 9
def m1ZTl (q : ℕ) : E := tri (301 + q) 4 4
/-- Member 2: one mask row; its tail. -/
def m2Z (e : ℕ) : E := tri (221 + e) (6 + e) 3
def m2ZTl (q : ℕ) : E := tri (321 + q) 5 8

def sumOf (n : ℕ) (f : ℕ → E) : E := ((List.range n).map f).foldl addE zeroE

/-- What a row's left side gives at the tables (input 0). A member's own table has its rows' number
rounded up to a power of two. -/
def valOf (r : Row) : E :=
  addE (addE
    (sumOf 16 fun i =>
      mulE (r.coefficient 0 .main i) (if i % 4 < 3 then m0E 0 (i % 4) (i / 4) else zeroE))
    (sumOf 8 fun i => mulE (r.coefficient 1 .main i) (m1E (i % 2) (i / 2))))
    (addE (sumOf 8 fun i => mulE (r.coefficient 1 .mask i) (m1Z i))
      (sumOf 8 fun i => mulE (r.coefficient 2 .mask i) (m2Z i)))

/-- The open row: single entries of the three members' tables. kappa: the next free entry of member
2's mask table. -/
def openRow (kappa : ℕ) (tau : E) : Row :=
  { (((({ } : Row).addUnit 0 .main 1 (tri 2 1 1)).addUnit 1 .main 2 (tri 3 5 1)).addUnit 2 .mask
      kappa oneE) with target := tau }

def madeAt (a : ℕ → E) (tau : Row → E) : Except String (_root_.Desc.Plain.DState Unit) := do
  let g ← (Ground.newGroupP d0 0 0).elim (.error "the group") .ok
  let x ← K1.decideSend send none g.2
    [r1, ⟨[.answer (a 0).triple, .answer (a 1).triple, .answer (a 2).triple], ⟨[], [], [], none⟩⟩]
  let j0 ← (Ground.joinP x.2 0 0 false).elim (.error "the first joining") .ok
  let j1 ← (Ground.joinP j0 0 1 false).elim (.error "the second joining") .ok
  let j2 ← (Ground.joinP j1 0 2 false).elim (.error "the third joining") .ok
  let k ← (Ground.takeMaskP j2 2).elim (.error "the mask's entry") .ok
  (Ground.addRowP k.2 0 (openRow k.1 (tau (openRow k.1 zeroE)))).elim (.error "the open row") .ok

def word {α : Type} : Except String α → String
  | .ok _ => "ok"
  | .error e => e

def sampleOf (o : ℕ) : Row :=
  match madeAt (fun _ => zeroE) fun _ => zeroE with
  | .ok d => ((d.st.oracles.getD o default).sampleRows.getD 0 {})
  | .error _ => {}

/-- The state on entry. da: added to the first answer. Where `madeAt` returns an error, the state is
built from `d0`. -/
def stateAt (da : E) : T12 :=
  let d := (madeAt (fun o => addE (valOf (sampleOf o)) (if o = 0 then da else zeroE))
    valOf).toOption.getD d0
  ⟨d.st, d.book, d.roots, 0, .nothing, none⟩

/-! ## 3 The job -/

/-- The stage's tables: main rows 0 to 2: member 0; 4, 5: member 1. Mask rows 0: member 1; 1: member
2. -/
def rowsAt (w : ℕ) : PS where
  tabM := fun n =>
    let b := n % 8
    let e := n / 8
    if e < 4 then
      (if b < 3 then readE (m0E w b e) else if 4 ≤ b ∧ b < 6 then readE (m1E (b - 4) e) else 0)
    else 0
  tabZ := fun n =>
    if n / 2 < 8 then (if n % 2 = 0 then readE (m1Z (n / 2)) else readE (m2Z (n / 2))) else 0
  tM := fun b q =>
    if b < 3 then readE (m0Tl b q) else if 4 ≤ b ∧ b < 6 then readE (m1Tl (b - 4) q) else 0
  tZ := fun b q => if b = 0 then readE (m1ZTl q) else if b = 1 then readE (m2ZTl q) else 0
  fM := fun _ _ => 0
  fT := fun _ _ => 0
  sM := fun _ => 0
  sT := fun _ => 0

def sender : Addr := ⟨⟨2, none, 1, .K1⟩, 0⟩

/-- One word of an element of the base field. -/
def word1 (x : GE) : UInt64 := (ofE x).1

def J (da : E) : TestJob ℕ Unit where
  p := p
  members := [(sender, 0, ⟨0, 7⟩), (sender, 1, ⟨0, 7⟩), (sender, 2, ⟨0, 3⟩)]
  fresh := none
  rec₀ := fun _ _ => stateAt da
  rows₀ := fun w _ _ => rowsAt w
  trees₀ := fun _ _ _ P =>
    [(5, fun x => (List.range 3).map fun b => word1 (mainSym (sgOf s0) P.tabM P.tM x b)),
     (5, fun x => wordsOf ([4, 5].map (fun b => ofE (mainSym (sgOf s0) P.tabM P.tM x b)) ++
        [ofE (maskSym (sgOf s0) P.tabZ P.tZ x 0)])),
     (4, fun x => wordsOf [ofE (maskSym (sgOf s0) P.tabZ P.tZ x 1)]),
     (4, freshCol (sgOf s0) P)]

def coins : TestCoins :=
  ⟨fun i => readE (tri (401 + i) 1 2), fun b q => readE (tri (501 + 2 * b + q) 3 1),
    fun _ => ⟨fun _ => 0, fun _ => 0⟩, fun i => readE (tri (601 + i) (1 + i) 7)⟩

end ProofFile.Honest.K12.ToyWide

#print axioms ProofFile.Honest.K12.ToyWide.codes
#print axioms ProofFile.Honest.K12.ToyWide.s0
#print axioms ProofFile.Honest.K12.ToyWide.s1
#print axioms ProofFile.Honest.K12.ToyWide.s2
#print axioms ProofFile.Honest.K12.ToyWide.ft
#print axioms ProofFile.Honest.K12.ToyWide.n0
#print axioms ProofFile.Honest.K12.ToyWide.n1
#print axioms ProofFile.Honest.K12.ToyWide.n2
#print axioms ProofFile.Honest.K12.ToyWide.send
#print axioms ProofFile.Honest.K12.ToyWide.d0
#print axioms ProofFile.Honest.K12.ToyWide.nums
#print axioms ProofFile.Honest.K12.ToyWide.p
#print axioms ProofFile.Honest.K12.ToyWide.declared
#print axioms ProofFile.Honest.K12.ToyWide.genOf
#print axioms ProofFile.Honest.K12.ToyWide.r1
#print axioms ProofFile.Honest.K12.ToyWide.tri
#print axioms ProofFile.Honest.K12.ToyWide.m0E
#print axioms ProofFile.Honest.K12.ToyWide.m0Tl
#print axioms ProofFile.Honest.K12.ToyWide.m1E
#print axioms ProofFile.Honest.K12.ToyWide.m1Tl
#print axioms ProofFile.Honest.K12.ToyWide.m1Z
#print axioms ProofFile.Honest.K12.ToyWide.m1ZTl
#print axioms ProofFile.Honest.K12.ToyWide.m2Z
#print axioms ProofFile.Honest.K12.ToyWide.m2ZTl
#print axioms ProofFile.Honest.K12.ToyWide.sumOf
#print axioms ProofFile.Honest.K12.ToyWide.valOf
#print axioms ProofFile.Honest.K12.ToyWide.openRow
#print axioms ProofFile.Honest.K12.ToyWide.madeAt
#print axioms ProofFile.Honest.K12.ToyWide.word
#print axioms ProofFile.Honest.K12.ToyWide.sampleOf
#print axioms ProofFile.Honest.K12.ToyWide.stateAt
#print axioms ProofFile.Honest.K12.ToyWide.rowsAt
#print axioms ProofFile.Honest.K12.ToyWide.sender
#print axioms ProofFile.Honest.K12.ToyWide.word1
#print axioms ProofFile.Honest.K12.ToyWide.J
#print axioms ProofFile.Honest.K12.ToyWide.coins
