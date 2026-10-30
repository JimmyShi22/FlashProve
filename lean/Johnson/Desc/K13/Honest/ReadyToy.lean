--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/ReadyToy.lean: A SYNTHETIC STATE AT WHICH THE PREMISES OF KIND K13's
STATEMENTS ON ITS HONEST PROVER ARE MET TOGETHER. Definitions with code, `#guard` lines, and
statements with their proofs.

Why. `atM3_accepts_ready` (Johnson/Desc/K13/Honest/Ready.lean), `family_accepts` and `family_law`
(Johnson/Desc/K13/Honest/TieAtM3.lean) stand under two tests on the verifier's state and under "all
rows on the pile are true". Statements under premises that nothing meets say nothing.

What is synthetic. The shape of the test on the committed table and the codes are the library's own
small lawful ones (OnBytes/Iop/TestLin.lean: `oneCode`, `codes`: a matrix of 5 rows and 4 columns).
The state: the chain's finish has run; one oracle message of 5 mask rows under a mask code of 2
places, with one OOD answer: 9 free entries by the library's count, whose numbers in the mask table
are 0 to 4 and 8 to 11; its ledger has handed out 3 and has 6 left, and the library's own tests on
ledgers and rows accept the state (`pileWithinC`, Johnson/Desc/K13/PubK13.lean); a reply; 3 rows on
the pile.
Main names:
  `P`, `stateAt pile`: the place's numbers; the state with a pile.
  `pileT`: rows that are true of a synthetic matrix `mat` and synthetic mask entries `maskV`, by
    evaluation. `pile0`: the same rows with the target 0, which are true of the matrix 0 and the
    mask entries 0, by proof (`holds_zero`).
  `#guard` lines: at `stateAt pileT` no clause of `readyL` fails and `pileBelowC` accepts; the
    decision accepts `honestRounds`; the row that it leaves has left side minus target 0, by a
    formula of this file's own. NEGATIVE TESTS: for each of the nine clauses a copy of the state or
    of the place's numbers with one value altered: just that clause fails, and the decision rejects
    under that name; two more for `pileBelowC`.
  `premises_met`: **the two tests accept at `stateAt pile0`, and all its rows are true of the zero
    witness**: so the three statements are not empty.

Limits. One size. `premises_met`'s witness is the idle one; the other witness is held by `#guard`
against this file's own formula, not against `Holds`. The synthetic message is marked as sampled and
has no sample row: the state holds no OOD answer. Nothing on the state of a real proof.
Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.TieAtM3
import Johnson.Desc.K13.PubK13
import OnBytes.Iop.TestLin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest.ReadyToy
open OnBytes OnBytes.Model
open OnBytes.Slice (GE toE ofE)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (Where atM3 pileWithinC)
open VerifiableInference.Desc.K13.Law

/-! ## Letters -/

def up (a : GE) : E := E.ofTriple (ofE a)
def dn (a : E) : GE := toE a.triple
def el (a b c : Nat) : GE := ⟨(a : Cb.Gl.F), (b : Cb.Gl.F), (c : Cb.Gl.F)⟩
def sumOver (n : Nat) (f : Nat → GE) : GE := (List.range n).foldl (fun r i => r + f i) 0

def Sh : Params.LinShape := TestLin.oneCode
def J : Nat := 3
def P : Where := { chain := 1, piece := 3, pieceRows := 4, rows := J, lin := Sh, sent := 1 }
abbrev kC : Nat := P.lin.kCol
abbrev nR : Nat := P.lin.matrixRows

#guard kC == 2 && nR == 5 && Sh.kRow == 3 && Sh.ownMaskCode == 0

/-! ## The synthetic witness, and what a row is worth on it -/

def mat (i c : Nat) : GE := el (3 + 5 * i + 7 * c) (1 + i + 2 * c) (11 * i + c)
def maskV (s : Slot) : GE := el (100 + 13 * s.index) (1 + s.index) (7 * s.index + s.oracle)
def weightsAt (g : List Tensor) (i : Nat) : GE := (g.map fun t => dn (t.entry i)).foldl (· + ·) 0
def colAt (g : List Tensor) (c : Nat) : GE := sumOver nR fun i => weightsAt g i * mat i c
def eqAt : List GE → Nat → GE
  | [], _ => 1
  | z :: zs, e => (if e % 2 == 1 then z else 1 - z) * eqAt zs (e / 2)
def formAt (m : MaskForm) : GE := (m.map fun t => dn t.2 * maskV t.1).foldl (· + ·) 0
def lhsAt (r : TensorRow) : GE :=
  sumOver (2 ^ kC) (fun c => eqAt (r.psi.map dn) c * colAt r.g c) + formAt r.masks
def gapAt (r : TensorRow) : GE := lhsAt r - dn r.target

/-- The witness in the form of the kind's laws: bit t of a column's number is coordinate t. -/
def wit : Law.Wit GE nR kC := ⟨fun i c => mat i.val (Nat.ofBits c), maskV⟩

/-! ## The pile and the state -/

def pile0 : List TensorRow :=
  (List.range J).map fun j =>
    { g := if j % 2 == 0 then [Tensor.eq [up (el (2 + j) 1 j), up (el 1 1 j), up (el 0 3 2)]]
           else [Tensor.eq [up (el (5 + j) 0 2), up (el 2 2 2), up (el 7 0 1)],
                 Tensor.eq [up (el 1 j 1), up (el 4 0 0), up (el 0 0 5)] (up (el 3 1 0))]
      psi := (List.range 2).map fun t => up (el (10 * j + t + 1) (t + 2) (j + 3))
      masks := [(⟨0, j⟩, up (el (j + 4) 0 1))]
      target := zeroE }

def pileT : List TensorRow := pile0.map fun r => { r with target := up (lhsAt r) }

def stM (next left : Nat) : Statement :=
  { codes := TestLin.codes
    oracles := #[{ shape := { mainRows := 0, maskRows := 5, maskCode := 0, answers := 1 }
                   sampled := true
                   ledger := some { next := next, left := left, rows := 5, logRows := 3 } }] }

def stateAt (l : List TensorRow) : S :=
  { (S.start TestLin.codes
      { frame := { shape := default, groups := #[] }, rows := ⟨default⟩ }).enterFin with
    st := stM J 6
    out := { indexMasks := 0, pending := l, reply := some (up (el 1 2 3)) } }

/-! ## The evaluation -/

def s0 : S := stateAt pileT
def xD : E := up (el 9 2 5)
def epsD : E := up (el 4 7 1)
def gsD : List E := [up (el 6 1 2), up (el 7 4 3)]

def word {α : Type} : Except String α → String
  | .ok _ => "accepts"
  | .error e => e

def decideAt (p : Where) (s : S) : Except String S :=
  (atM3 (Cl := Unit) p).decide s (honestRounds P s0 wit xD epsD gsD) []

#guard pileT.all fun r => gapAt r == 0
#guard pile0.any fun r => gapAt r != 0
#guard readyFails P s0 == [] && readyC P s0
#guard pileBelowC s0.st s0.out.indexMasks s0.out.pending
#guard pileWithinC s0
#guard (freshAt P s0).map (·.index) == [3, 4, 8, 9, 10]
#guard word (decideAt P s0) == "accepts"
#guard ((decideAt P s0).toOption.map fun s => s.rows.map fun r => gapAt r == 0) == some [true]
#guard ((decideAt P s0).toOption.map pileWithinC) == some true

/-! ## Negative tests: one value altered -/

def withPile (f : TensorRow → TensorRow) : S :=
  stateAt (pileT.zipIdx.map fun p => if p.2 == 1 then f p.1 else p.1)

def altered : List (String × Where × S) :=
  [("K13.comes-to-the-end-once", P, { s0 with here := .between }),
   ("K13.reply-heard", P, { s0 with out := { s0.out with reply := none } }),
   ("K13.pile-count", { P with rows := J + 1 }, s0),
   ("K13.pile-on-the-table", P, withPile fun r => { r with masks := [(⟨1, 1⟩, oneE)] }),
   ("K13.nothing-owed", P, { s0 with rowsOwed := some 3 }),
   ("K13.pile-form", P, withPile fun r => { r with g := [] }),
   ("K13.mask-entries", P, { s0 with st := stM J 4 }),
   ("K13.shape-lawful", { P with lin := { Sh with sharedMaskCode := 2 } }, s0),
   ("K13.message-W", { P with lin := { Sh with masksAhead := true } }, s0)]

#guard altered.map (·.1) == (readyL P s0).map (·.1)
#guard (altered.map fun b => (readyFails b.2.1 b.2.2, word (decideAt b.2.1 b.2.2))) ==
  altered.map fun b => ([b.1], b.1)
-- a row on the pile names an entry that the ledger has not handed out yet
#guard !pileBelowC s0.st 0 (withPile fun r => { r with masks := [(⟨0, 3⟩, oneE)] }).out.pending
#guard !pileBelowC (stM 2 7) 0 pileT
-- a ledger that claims more entries than the shape has free is told by the library's test
#guard !pileWithinC { s0 with st := stM J 10 }

/-! ## The premises are met together -/

/-- A row with the target 0 is true of the matrix 0 and the mask entries 0. -/
theorem holds_zero {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) {n k : ℕ} (r : TensorRow)
    (h : r.target = zeroE) : Law.Holds ρ (⟨fun _ _ => 0, fun _ => 0⟩ : Law.Wit K n k) r := by
  unfold Law.Holds Law.lhs Law.colOf Law.formVal Alg.mle
  simp [h, ρ.zero]

theorem pile0_target : ∀ r ∈ pile0, r.target = zeroE := by
  intro r hr
  obtain ⟨j, _, rfl⟩ := List.mem_map.1 hr
  rfl

theorem ready_member : readyC P (stateAt pile0) = true := by decide +kernel

theorem below_member : pileBelowC (stateAt pile0).st (stateAt pile0).out.indexMasks
    (stateAt pile0).out.pending = true := by decide +kernel

/-- **The two tests accept, and all rows on the pile are true of the zero witness.** -/
theorem premises_met :
    readyC P (stateAt pile0) = true ∧
    pileBelowC (stateAt pile0).st (stateAt pile0).out.indexMasks (stateAt pile0).out.pending =
      true ∧
    ∀ r ∈ (stateAt pile0).out.pending,
      Law.Holds ρg (⟨fun _ _ => 0, fun _ => 0⟩ : Law.Wit GE nR P.lin.kCol) r :=
  ⟨ready_member, below_member, fun r hr => holds_zero ρg r (pile0_target r hr)⟩

end VerifiableInference.Desc.K13.Honest.ReadyToy

#print axioms VerifiableInference.Desc.K13.Honest.ReadyToy.holds_zero
#print axioms VerifiableInference.Desc.K13.Honest.ReadyToy.ready_member
#print axioms VerifiableInference.Desc.K13.Honest.ReadyToy.below_member
#print axioms VerifiableInference.Desc.K13.Honest.ReadyToy.premises_met
