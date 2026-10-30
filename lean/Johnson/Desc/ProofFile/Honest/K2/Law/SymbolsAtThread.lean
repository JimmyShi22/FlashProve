-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SymbolsAtThread.lean: the kind "the code switch" (K2): THE
FIELD `symbols` OF THE RECORD `MadeAsks`, A FIFTH EXCHANGE: `symbols_at_yes` (SymbolsAtYes.lean)
UNDER A THREAD's INVARIANT: ITS PREMISE ON THE TABLES AT HAND PAID BY CLAUSE (H) (`table_at_hand`,
TableAtHand.lean) AND THE SEALED `col_treeTable` (Honest/K12/TreesSentBeforeTestFromSentTable.lean: a sending's table shows
the written column), FOR ONE NAMED PREMISE A SENDER. Two lemmas; NONE OF THE LIBRARY's GOALS.
Nothing on completeness, soundness or hiding.

  `treeTables_logLength`  a sending's table is as long as its tree in the sending's own layout: by
      `treeTables_at`, `treeTables_length` (Honest/K1/TableShape.lean); kin at tree 0:
      `depth_treeTable` (Honest/K12/TreesSentBeforeTestFromSameColumns.lean)
  **`symbols_at_thread`**  ⊢ `SymbolsAre` as in `symbols_at_yes`
THE ONE PREMISE A SENDER. hSend: the thread's own table (`Thread.tableAt`) of the tree that
holds read message w is table number τ of the tables that the sending Pw makes of the rows Vw
(`treeTables`, Johnson/Desc/ProofFile/Honest/K1/Part.lean). WHO COULD PAY IT: `OwnTrees`
(Honest/Thread/ScriptLots.lean) at the earlier sender, and that sender's own text of its table.
WHAT ELSE SPEAKS OF THE RUN. hA: the invariant in front of the member. hfill: the frame's
filling behind the rounds played. A: the yes.
THE OTHERS, beyond those of `symbols_at_yes`. hft: the thread's first tree's number is the
plan's. hn: each read tree was sent in front of the border.
Limits. «NOT IN FRONT OF A LAW OVER COINS». THE GROUND, of the first kind: s, m and En stand under
hA beside the run's coins k; cols under hfill; the states, the rounds and Y under A; Vw under hSend,
which ties it to the thread's table at k. Of the second kind: hA's clause on the input (`valid`).
Made term and lemma that lift the bar: none: the bar is flat. AN IMPLICATION: IT PAYS NOTHING: none
of its premises is shown here of anything; whether they can be met together is not shown. hSend
speaks of senders that make their tables by `treeTables`: whether every read message's sender does
is not said. That the senders' rows are those that a closing makes anew is not said. Vw HOLDS A
RUN's COINS, and k is that run's: letters under "for all".
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SymbolsAtYes
import Johnson.Desc.ProofFile.Honest.K2.Law.TableAtHand
import Johnson.Desc.ProofFile.Honest.K12.TreesSentBeforeTestFromSentTable
import Johnson.Desc.ProofFile.Honest.K1.TableShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE readL codeOf)
open Johnson.Prover.Send (Rows shapeAt col)
open ProofFile.Honest (Table Read readsOf fillCols Thread Thr Coins Mid Env Played ProverCoinCounts treesTo)
open ProofFile.Honest.K1 (treeTables treeTables_length treeTables_at)
open ProofFile.Honest.K12 (col_treeTable)
open ProofFile.Honest.K2 (frozenLeft table_at_hand)
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 rounds flat AtYes)

set_option quotPrecheck false in
/-- The kept rows, by member and row, as `rowOfComplex` lists them. -/
local notation "keptList" Z =>
  ((Sizes.kept Z).zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b))

/-- A sending's table is as long as its tree in the sending's own layout. -/
theorem treeTables_logLength (P : K1.Par) (V : Nat → Rows) (τ : Nat) (T : Table)
    (hT : (treeTables P V)[τ]? = some T) :
    T.logLength = (((Own.treesMade P.codes P.sent).getD {}).shapes.getD τ {}).logN := by
  have hlt : τ < P.trees.length := by
    rw [← treeTables_length P V]
    exact (List.getElem?_eq_some_iff.1 hT).1
  obtain ⟨t, ht⟩ : ∃ t, P.trees[τ]? = some t := ⟨_, List.getElem?_eq_getElem hlt⟩
  obtain ⟨T', h1, h2, -⟩ := treeTables_at P V τ t ht
  rw [hT] at h1
  obtain rfl := Option.some.inj h1
  rw [h2]
  unfold K1.Par.trees at ht
  cases e : Own.treesMade P.codes P.sent with
  | none =>
    rw [e] at ht
    simp at ht
  | some Ly =>
    rw [e] at ht
    simp only [Option.map_some, Option.getD_some, Array.getElem?_toList] at ht
    simp only [Option.getD_some, Array.getD_eq_getD_getElem?, ht]

/-- **`SymbolsAre` AT A YES, UNDER THE THREAD's INVARIANT.** NOT IN FRONT OF A LAW OVER COINS:
the ground stands in this file's head. -/
theorem symbols_at_thread {St Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk St Cl V W X Pb)
    {n₀ : Nat} {k : Coins Bk} {s : St} {m : Mid W X} {En : Env} (hA : Thr T n₀ k s m En)
    (b : Block St Cl) (q : P2) (hr : b.rounds = rounds q) (hft : T.ft = q.firstTree)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : b.Fits q.firstTree rs cols) (ps : List Played)
    (R1 R2 : Fmt.Drawn)
    (hfill : fillCols (readsOf T.chain T.ft (En.add ps).stored (En.add ps).tree b.rounds [R1, R2])
      [] = .ok cols)
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
    (hn : ∀ w, w ≤ x.f.rows.layout.members.size →
      (tw w).number - q.firstTree < treesTo T.bs n₀)
    (hSend : ∀ w, w ≤ x.f.rows.layout.members.size →
      (treeTables (Pw w) (Vw w))[((Own.treesMade (Pw w).codes (Pw w).sent).getD {}).tree.getD
        (kw w) 0]? = some (T.tableAt (.own ((tw w).number - q.firstTree)) k m).2) :
    SymbolsAre Z x.f.rows
      (frozenLeft (Z.codes.base.getD Z.code default) (Z.codes.mask.getD Z.maskCode default) Z.kept
        (foldEndAt x.f.rows.layout Z.codes Z.code Z.maskCode ms (fun w => Vw w (kw w))
          (Vw x.f.rows.layout.members.size (kw x.f.rows.layout.members.size)) γ))
      (Positions.ofDraws q.logN r₂.drawn.poss) Y := by
  rw [hr, hft] at hfill
  refine symbols_at_yes b q hr rs cols hF T.chain _ _ R1 R2 hfill A Z ms γ Pw Vw kw Xw pw tw hm hk
    hγ hZk hnos hkept hapM hapZ hP hkw hX hs hsF hcd hz hpl hor htr hsh hpt hlogM hlogZ hpos
    fun w hw => ?_
  obtain ⟨u, hu, hc⟩ := table_at_hand T hA ps _ (hn w hw)
  refine ⟨u, hu, fun p hp => ?_⟩
  rw [hc p (by rw [treeTables_logLength _ _ _ _ (hSend w hw), ← hsh w hw]; exact hp)]
  exact col_treeTable (Pw w) (Vw w) (hP w hw) _ p _ (hSend w hw)

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.treeTables_logLength
#print axioms VerifiableInference.Desc.K2.Honest.symbols_at_thread
