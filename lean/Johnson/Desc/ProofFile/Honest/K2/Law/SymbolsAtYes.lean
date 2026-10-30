-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SymbolsAtYes.lean: the kind "the code switch" (K2): THE FIELD
`symbols` OF THE RECORD `MadeAsks`, A FOURTH EXCHANGE: `SymbolsAre` AT A YES OF THE KIND's OWN
DECISION (`AtYes`, Johnson/Top/H0/K2Hears/Whole.lean), AT THE GROUPS THAT THE STEP MAKES OF THE
COLUMNS THAT THE FRAME FILLS: FROM TABLES AT HAND WHOSE COLUMNS ARE SENDERS' WRITTEN COLUMNS. One
lemma; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding.

  **`symbols_at_yes`**  ⊢ `SymbolsAre Z x.f.rows (frozenLeft … (foldEndAt x.f.rows.layout … (fun w
      => Vw w (kw w)) …)) (Positions.ofDraws q.logN r₂.drawn.poss) Y`
WHAT SPEAKS OF WHAT WAS OPENED. A: the yes. hfill: the columns are those that the frame
fills at the tables at hand. hT: at each read message's tree a table is at hand, and below the
tree's length its column is the sender's written column.
How. `AtYes.read` and the sealed `readOld_inv` (Johnson/Top/H0/Tw/K2C/Closed.lean) give `ReadIs`;
`symbolsAre_of_orc` (SymbolsOfOracles.lean) at the reading of the tables that `colsOf_filled` writes
out; `colsOf_flat` (ColsOfFilled.lean).
Limits. «NOT IN FRONT OF A LAW OVER COINS». THE GROUND, of the first kind: cols stands under hfill;
the states, the rounds and Y under A; the tables at hand under hT, which ties them to Vw, rows that
hold a run's coins. Made term and lemma that lift the bar: none: the bar is flat. AN IMPLICATION: IT
PAYS NOTHING: none of its premises is shown here of anything; whether they can be met together is
not shown. The other premises are those of `symbolsAre_of_orc`, at the statement and the book behind
the sending: they read the verifier's state at a yes. Vw HOLDS A RUN's COINS: letters under "for
all".
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SymbolsOfOracles
import Johnson.Desc.ProofFile.Honest.K2.Law.ColsOfFilled
import Johnson.Top.H0.K2Hears.Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE readL codeOf)
open Johnson.Prover.Send (Rows shapeAt col)
open ProofFile.Honest (Table Read readsOf fillCols)
open ProofFile.Honest.K2 (frozenLeft colsOf_filled colsOf_flat)
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 rounds flat AtYes readOld_inv)

set_option quotPrecheck false in
/-- The kept rows, by member and row, as `rowOfComplex` lists them. -/
local notation "keptList" Z =>
  ((Sizes.kept Z).zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b))

/-- **`SymbolsAre` AT A YES, FROM THE TABLES AT HAND.** NOT IN FRONT OF A LAW OVER COINS: the
ground stands in this file's head. -/
theorem symbols_at_yes {St Cl : Type} (b : Block St Cl) (q : P2) (hr : b.rounds = rounds q)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : b.Fits q.firstTree rs cols) (chain : Nat)
    (stored : Nat → Nat → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table))
    (R1 R2 : Fmt.Drawn)
    (hfill : fillCols (readsOf chain q.firstTree stored tree (rounds q) [R1, R2]) [] = .ok cols)
    {s₁ t : S} {r₁ r₂ : Fmt.RoundView} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent} {S3 : Statement}
    {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes q s₁ t r₁ r₂ (b.shown q.firstTree rs cols) x z S3 Y rows G cd)
    (Z : Sizes) (ms : List GroupMember) (γ : List GE)
    (Pw : Nat → K1.Par) (Vw : Nat → Nat → Rows) (kw : Nat → Nat) (Xw : Nat → OnBytes.Oracle)
    (pw : Nat → Nat × Nat) (tw : Nat → Tree)
    (hm : x.f.rows.masks = 2) (hk : x.f.rows.keptRows = (keptList Z).length)
    (hγ : ∀ t, t < x.f.rows.layout.k → γ.getD t zeroG = readL x.f.rows.gamma t)
    (hZk : Z.kept = (Own.keptNos x.f.rows.layout).map (shapeOf ms))
    (hnos : ((List.range ms.length).filter fun w => keptOf ms w) = Own.keptNos x.f.rows.layout)
    (hkept : ∀ w, w < x.f.rows.layout.members.size → x.f.rows.layout.kept.getD w false = true →
      x.f.rows.layout.mainFirst.getD w none = none)
    (hapM : ∀ w w', w < x.f.rows.layout.members.size → w' < x.f.rows.layout.members.size →
      w ≠ w' → ∀ f f', x.f.rows.layout.mainFirst.getD w none = some f →
      x.f.rows.layout.mainFirst.getD w' none = some f' →
      f + (shapeOf ms w).mainRows ≤ f' ∨ f' + (shapeOf ms w').mainRows ≤ f)
    (hapZ : ∀ w w', w < x.f.rows.layout.members.size → w' < x.f.rows.layout.members.size →
      w ≠ w' → ∀ f f', x.f.rows.layout.maskFirst.getD w none = some f →
      x.f.rows.layout.maskFirst.getD w' none = some f' →
      f + (shapeOf ms w).maskRows ≤ f' ∨ f' + (shapeOf ms w').maskRows ≤ f)
    (hP : ∀ w, w ≤ x.f.rows.layout.members.size → K1.planOkOwn (Pw w) = true)
    (hkw : ∀ w, w ≤ x.f.rows.layout.members.size → kw w < (Pw w).sent.size)
    (hX : ∀ w, w ≤ x.f.rows.layout.members.size → (Xw w).shape = shapeAt (Pw w) (kw w))
    (hs : ∀ w, w < x.f.rows.layout.members.size → shapeOf ms w = shapeAt (Pw w) (kw w))
    (hsF : 2 ^ x.f.rows.layout.h ≤
      (shapeAt (Pw x.f.rows.layout.members.size) (kw x.f.rows.layout.members.size)).maskRows)
    (hcd : ∀ w, w < x.f.rows.layout.members.size → (shapeAt (Pw w) (kw w)).mainRows ≠ 0 →
      (Pw w).codes.base.getD (shapeAt (Pw w) (kw w)).code default =
        Z.codes.base.getD Z.code default)
    (hz : ∀ w, w ≤ x.f.rows.layout.members.size → (shapeAt (Pw w) (kw w)).maskRows ≠ 0 →
      (Pw w).codes.mask.getD (shapeAt (Pw w) (kw w)).maskCode default =
        Z.codes.mask.getD Z.maskCode default)
    (hpl : ∀ w (hw : w < (singleRowsOracles x.f.rows).size),
      z.book.place[(singleRowsOracles x.f.rows)[w]]? = some (pw w))
    (hor : ∀ w (hw : w < (singleRowsOracles x.f.rows).size),
      z.st.oracles[(singleRowsOracles x.f.rows)[w]]? = some (Xw w))
    (htr : ∀ w, w ≤ x.f.rows.layout.members.size → z.book.trees[(pw w).1]? = some (tw w))
    (hsh : ∀ w, w ≤ x.f.rows.layout.members.size → (tw w).shape =
      ((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).shapes.getD
        (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).tree.getD (kw w) 0) {})
    (hpt : ∀ w, w ≤ x.f.rows.layout.members.size → (pw w).2 =
      ((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).part.getD (kw w) 0)
    (hlogM : ∀ w, w < x.f.rows.layout.members.size → (shapeOf ms w).mainRows ≠ 0 →
      (tw w).shape.logN = q.logN)
    (hlogZ : ∀ w, w ≤ x.f.rows.layout.members.size → (shapeAt (Pw w) (kw w)).maskRows ≠ 0 →
      (codeOf (Z.codes.mask.getD Z.maskCode default)).a ≤ (tw w).shape.logN)
    (hpos : ∀ j, j < (Positions.ofDraws q.logN r₂.drawn.poss).all.size →
      (Positions.ofDraws q.logN r₂.drawn.poss).all.getD j 0 < 2 ^ q.logN)
    (hT : ∀ w, w ≤ x.f.rows.layout.members.size →
      ∃ u, tree (.own ((tw w).number - q.firstTree)) = some u ∧
        ∀ p, p < 2 ^ (tw w).shape.logN → u.2.col p =
        col (Pw w) (Vw w)
          (((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).tree.getD (kw w) 0) p) :
    SymbolsAre Z x.f.rows
      (frozenLeft (Z.codes.base.getD Z.code default) (Z.codes.mask.getD Z.maskCode default) Z.kept
        (foldEndAt x.f.rows.layout Z.codes Z.code Z.maskCode ms (fun w => Vw w (kw w))
          (Vw x.f.rows.layout.members.size (kw x.f.rows.layout.members.size)) γ))
      (Positions.ofDraws q.logN r₂.drawn.poss) Y := by
  obtain ⟨B, left, h⟩ := A.read
  obtain ⟨places, cs, opened, k⟩ := readOld_inv h
  exact symbolsAre_of_orc k (fun key p => ((tree (.own key)).map (·.2.col p)).getD [])
    (colsOf_flat b q hr rs cols hF _ (colsOf_filled chain stored tree q R1 R2 cols hfill))
    Z ms γ Pw Vw kw Xw pw tw hm hk hγ hZk hnos hkept hapM hapZ hP hkw hX hs hsF hcd hz hpl hor htr
    hsh hpt hlogM hlogZ hpos fun w hw p hp => by
      obtain ⟨u, hu, hc⟩ := hT w hw
      show ((tree (.own ((tw w).number - q.firstTree))).map (·.2.col p)).getD [] = _
      rw [hu]
      exact hc p hp

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.symbols_at_yes
