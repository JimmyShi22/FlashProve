-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHFill.lean: the key file's first chain's thread at the honest prover: one value of the
letters of `laid₁` (E2E/KeyRest.lean), with the three sendings' own tables.


  `HTab`, `HCells`: a message as two tables of field elements; the stored table as row and place.
  `readH`, `cellsOf`, `matAt_cells`: how a witness is read; the table of a matrix, and that the
    library's `matAt` reads the matrix off it.
  `baseH`: the reading. `meets` is true and a sample is (): THE PINS AND pinT ARE IDLE AT THIS THREAD:
    they follow from the clause on the state, and nothing is counted as paid by them. What a sample
    is worth is in the items srow and grows, which keep the library's sentences. pinT's content
    (the key's record is the cells' own) has its home on the shared chain.
  `msgRun`: a sending's message, of a run's coins: the words that the part lays.
  `OlderStay`, `StaysK`, `StaysW`: what a kind's step leaves of the state.
  `LaterFill`: the letters that stay: those of the two later chains (msg and fixedMsg from 3 on, ends,
    kind₂, kind₃, table₂, table₃, enc, rad), what the lookups' and the ranges' steps keep (kind₁),
    the first chain's tables but the three sendings' (table₁), and Rel, OF WHICH INPUTS SOMETHING IS
    SAID: a clause of the thread: at Rel := False every statement on the thread is empty.
  `fillH`: the value of `KeyFill`.
  `rngTbl`, `tbH`, `T₁`: the trees' tables: at own trees 0 to 5 the sender's own term; the thread.

Limits. Definitions, and one small equation. Nothing here says that the thread stands at any run.
No letter of what is said of a run stands here: no debt at the four members reads one.
`LaterFill`'s fields are letters. K is a letter: nothing here reads what its senders hold.
-/
import E2E.KeyRest
import E2E.KeyProver
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K12.ScriptLots
import E2E.KeyRangesJob
import E2E.KeyFirstSends

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob rowsLaid lentCut dueR treeTbl)
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Key (Xi FirstState KRead Source LaterPlaces matAt)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.KeyRows23 (BaseSt St₂ St₃)
open AtPublicFiles.KeyThread (KeyFill laid₁ D one₀)
open AtPublicFiles.KeyFile (KeyParts keyProver In1)

/-- A message: its main and mask tables, as field elements. -/
abbrev HTab : Type := OnBytes.Part → Nat → OnBytes.Slice.GE

/-- The stored table's message: row, then place. -/
abbrev HCells : Type := Nat → Nat → OnBytes.F

/-- **How a witness is read.** -/
def readH : KRead HCells HTab where
  tab := id
  val := fun m part i => OnBytes.E.ofTriple (OnBytes.Slice.ofE (m part i))
  of := fun w k => w.msg k
  same := fun a b => OnBytes.Slice.readE a = OnBytes.Slice.readE b

/-- The table of a matrix, at the library's layout (`matAt`). -/
def cellsOf (S : OnBytes.Params.LinShape) (f : Weights) : HCells :=
  fun r i => OnBytes.Slice.ofF (f.entry (i / 2 ^ S.kLo) (i % 2 ^ S.kLo + 2 ^ S.kLo * r))

/-- The library's `matAt` reads the matrix off that table. -/
theorem matAt_cells (S : OnBytes.Params.LinShape) (f : Weights) (y c : Nat) :
    matAt S (cellsOf S f) y c = OnBytes.Slice.ofF (f.entry y c) := by
  have hp : 0 < 2 ^ S.kLo := Nat.pow_pos (by decide)
  have hm : c % 2 ^ S.kLo < 2 ^ S.kLo := Nat.mod_lt _ hp
  have e1 : (c % 2 ^ S.kLo + 2 ^ S.kLo * y) / 2 ^ S.kLo = y := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hm, Nat.zero_add]
  have e2 : (c % 2 ^ S.kLo + 2 ^ S.kLo * y) % 2 ^ S.kLo = c % 2 ^ S.kLo := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_mod]
  unfold matAt cellsOf
  rw [e1, e2, Nat.mod_add_div]

/-- Which message a tree's first tenant holds: the six seats (`atSix`), read backwards. -/
def arrH : Nat → Nat → Nat := fun j _ =>
  match j with
  | 0 => 0
  | 1 => 1
  | 5 => 2
  | 6 => 3
  | 7 => 4
  | _ => 5

/-- **The reading.** -/
def baseH (one : OnBytes.Params.OneTime) : BaseSt HCells HTab Unit Unit where
  arr := arrH
  lay := fun _ _ a _ => a
  enc := fun _ _ _ _ _ => True
  rad := fun _ _ _ => 0
  meets := fun _ _ _ _ _ => True
  decT := fun _ _ => none
  recOf := fun _ => some ()
  sm := fun _ _ x => if x.sampled = true then some () else none
  orc₁ := (plan₁ one).orc

/-- **A sending's message, of a run's coins**: the words that the part lays at its own cut. -/
def msgRun {Bk : ProverCoinCounts} {W X : Type} (J : SendJob W X) (own₀ : X) (k : Coins Bk) (w : W)
    (h : List Fmt.Drawn) : HTab :=
  match lentCut k 0 ⟨J.P.place, 0⟩ (dueR J.P J.ride) with
  | some c => fun part i =>
      Johnson.Prover.Send.held (fun _ _ _ => 0) J.first J.P (rowsLaid J own₀ c w h) J.first part i
  | none => fun _ _ => 0

/-- The older messages stay, as far as a row or a sample reads them. -/
def OlderStay (T T' : OnBytes.Statement) : Prop :=
  T'.codes = T.codes ∧ ∀ (o : Nat) (x : OnBytes.Oracle), T.oracles[o]? = some x →
    ∃ x' : OnBytes.Oracle, T'.oracles[o]? = some x' ∧ x'.shape = x.shape ∧
      x'.sampled = x.sampled ∧ x'.sampleRows = x.sampleRows

/-- What a sending's step and the batching's leave. -/
def StaysK (s s' : FirstState) : Prop := OlderStay s.d.st s'.d.st

/-- What W's step leaves: that, and the claim. -/
def StaysW (s s' : FirstState) : Prop :=
  StaysK s s' ∧ s'.lin.map (·.claim) = s.lin.map (·.claim)

/-- **The letters that stay.** -/
structure LaterFill (Bk : ProverCoinCounts) (W₀ Rc : Type) where
  /-- the shared chain's messages -/
  msg : Nat → Coins Bk → W₀ → Rc → List Fmt.Drawn → HTab
  fixedMsg : Nat → Nat
  ends : Coins Bk → W₀ → Rc → Xi → List Fmt.Drawn → FirstState × St₂
  /-- what the step of a lookup, and of the ranges' test, keeps -/
  kind₁ : Nat → FirstState → FirstState → Prop
  kind₂ : Nat → St₂ → St₂ → Prop
  kind₃ : Nat → St₃ → St₃ → Prop
  /-- of which inputs something is said -/
  Rel : W₀ → Rc → Xi → Prop
  /-- the shared chain's code and radius: read by the shared chain's items alone -/
  enc : (Nat → OnBytes.E) → Nat → OnBytes.E
  rad : Nat
  /-- the first chain's trees but the three sendings' -/
  table₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table
  table₂ : Fmt.TreeSource → Coins Bk → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Place × Table
  table₃ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc)

/-- **The value of the letters**, at one instance. -/
def fillH (x : Xi) : KeyFill Bk W₀ Rc HCells HTab Unit Unit where
  R := readH
  base := baseH (one₀ Xs)
  meetsT := fun _ _ => True
  enc := Q.enc
  rad := Q.rad
  cells := fun w₀ _ => cellsOf (one₀ Xs).lin (f w₀)
  msg := fun n k w₀ rc h =>
    match n with
    | 0 => msgRun K.idx K.own₀ k (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) h
    | 1 => msgRun K.msg K.own₀ k (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) h
    | 2 => msgRun K.w K.own₀ k (⟨w₀, rc, x, ()⟩ : In1 W₀ Rc) h
    | n + 3 => Q.msg (n + 3) k w₀ rc h
  fixedMsg := fun n =>
    match n with
    | 0 => roundsTo (D Xs N Pl).first.blocksInOrder 0
    | 1 => roundsTo (D Xs N Pl).first.blocksInOrder 1
    | 2 => roundsTo (D Xs N Pl).first.blocksInOrder 17
    | n + 3 => Q.fixedMsg (n + 3)
  pad := fun _ _ _ _ _ _ _ => 0
  ends := Q.ends
  kind₁ := fun b =>
    match b with
    | 0 | 1 | 16 => StaysK
    | 17 => StaysW
    | b => Q.kind₁ b
  kind₂ := Q.kind₂
  kind₃ := Q.kind₃
  Rel := Q.Rel
  stored := (keyProver K).storedWords
  item := 0
  table₁ := Q.table₁
  table₂ := Q.table₂
  table₃ := Q.table₃

/-- Tree number τ of the ranges' test: the table that the switch out of stage τ sends. -/
def rngTbl (τ : Nat) : Coins Bk → In1 W₀ Rc → List Fmt.Drawn → Place × Table :=
  ProofFile.Honest.K12.testTbl 0 (AtPublicFiles.KeyThread.rangesTestJob (X' := X') Xs N Pl (AtPublicFiles.KeyValues.matrixEntryOf f)
          (AtPublicFiles.KeyValues.multiplicitiesGroups Xs) 0) K.own₀ (roundsTo (D Xs N Pl).first.blocksInOrder 15) (fun _ _ _ => true) τ

/-- **The trees' tables.** Own tree 0 is the index masks', 1 the multiplicities', 2, 3 and 4 the ranges'
test's, 5 W's: each is the sender's own term, at the part's own cut of the run's coins. -/
def tbH : Fmt.TreeSource → Coins Bk → In1 W₀ Rc → List Fmt.Drawn → Place × Table
  | .own 0 => treeTbl 0 id K.idx K.own₀ 0
  | .own 1 => treeTbl 0 id K.msg K.own₀ 0
  | .own 2 => rngTbl Xs N Pl K f 0
  | .own 3 => rngTbl Xs N Pl K f 1
  | .own 4 => rngTbl Xs N Pl K f 2
  | .own 5 => treeTbl 0 id K.w K.own₀ 0
  | σ => Q.table₁ σ

variable (w₀ : W₀) (rc : Rc) (x : Xi)

/-- **The first chain's thread at the honest prover.** -/
def T₁ : Thread Bk (D Xs N Pl).S₁ (D Xs N Pl).Cl (In1 W₀ Rc) (In1 W₀ Rc) X' Xi :=
  laid₁ Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x (keyProver K).first (tbH Xs N Pl K f Q)

end

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.matAt_cells
