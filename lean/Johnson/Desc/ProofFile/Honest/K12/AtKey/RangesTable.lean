-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesTable.lean: the first chain's table of trees as the
test on the ranges reads it, written out: tree 1 is the table that the sending of the
multiplicities makes, at its own coins; trees 2, 3, 4 are the test's own; every other tree is a
letter. At this table the two premises of RangesPlays.lean on the letter tb are theorems, and what
is left of PlaysS at the key file's prover is that the parts bear their places, and of AcceptedS
besides that the rows are true.

  msgTable      the sending's first table, at the purse that the book lends it, cut at its start
  tbRng         the table of trees
  treeTable_some   a sending with a tree has a first table
  tbRng_test    behind the trees 2, 3, 4 stand the test's tables
  tbRng_sent    TbIsSent at this table, at every stand, in scope
  playsS_at_table, acceptedS_at_table   PlaysS and AcceptedS at member 15, at keyProver with the
                four tests laid, at this table

Limits.
- NOT IN FRONT OF A LAW OVER COINS: as RangesPlays.lean and RangesAccepted.lean.
- The table says what tree 1 and trees 2 to 4 are, by definition. So tbRng_sent and tbRng_test say
  nothing of a run: that the parts' play sends these tables is the clause Trees of the members that
  send them. For tree 1 that is member 1, the sending at the parts' msg: it is this table only
  under MsgIsJob (RangesAtProver.lean).
- rest is a letter: tree 0 and every tree behind the test.
- A purse that cannot be cut gives the table of no word; at the key file's book in scope it can be
  cut at all coins (purse_cut, E2E/KeyRangesWholeS.lean).
- In scope; at the written sizes.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesAtProver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open OnBytes.Slice (GF)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyTest (sMsg)
open AtPublicFiles.KeyThread (KeyFill laid₁ D rangesTestJob sentRanges TbIsSent trees_len one_msg sent_codes
  sent_msgs)
open AtFullSide.K12 (withTests)
open VerifierAndGoals (InScope)

/-- A sending with a tree has a first table. -/
theorem treeTable_some (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Johnson.Prover.Send.Rows)
    (d : Table) (h : 0 < P.trees.length) :
    (K1.treeTables P Vr)[0]? = some ((K1.treeTables P Vr).getD 0 d) := by
  have hl : 0 < (K1.treeTables P Vr).length := by
    unfold K1.treeTables
    simpa using h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rfl

section
variable {W₀ Rc Cells M Smp Rec X₀ X Wk : Type} {Z : VerifierAndGoals.PublicFiles} {K₀ : KeyPub}
  (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **The sending's first table**, at the purse that the book lends it, cut at its start. -/
def msgTable (k : Coins (keyBook K₀)) (w : Local W₀ Rc Xi Unit) : Place × Table :=
  ((sentRanges Xs entry groups first).P.place,
    match ((k.look 0) sMsg).2.cut ⟨0, 0⟩
        (K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride) with
    | some c₁ =>
      (K1.treeTables (sentRanges Xs entry groups first).P
        (K1.rowsR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride
          ((sentRanges Xs entry groups first).data w) c₁)).getD 0 K1.wordlessTable
    | none => K1.wordlessTable)

/-- **The table of trees.** own₀: the state that the test's tables are read at. rest: every other
tree. -/
def tbRng (own₀ : X)
    (rest : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table) :
    Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table :=
  fun σ => match σ with
    | .own n =>
      if n = 1 then fun k w _ => msgTable Xs entry groups first k w
      else if 2 ≤ n ∧ n < 5 then
        testTbl 0 (rangesTestJob (X' := X) Xs N Pl entry groups first) own₀
          (roundsTo (D Xs N Pl).first.blocksInOrder 15) (fun _ _ _ => true) (n - 2)
      else rest (.own n)
    | σ => rest σ

variable (own₀ : X)
  (rest : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **Behind the trees 2, 3, 4 stand the test's tables.** -/
theorem tbRng_test {τ : Nat} (hτ : τ < 3) :
    tbRng Xs N Pl entry groups first own₀ rest (.own (2 + τ)) =
      testTbl 0 (rangesTestJob (X' := X) Xs N Pl entry groups first) own₀
        (roundsTo (D Xs N Pl).first.blocksInOrder 15) (fun _ _ _ => true) τ := by
  show (if 2 + τ = 1 then _ else if 2 ≤ 2 + τ ∧ 2 + τ < 5 then
    testTbl 0 (rangesTestJob (X' := X) Xs N Pl entry groups first) own₀
      (roundsTo (D Xs N Pl).first.blocksInOrder 15) (fun _ _ _ => true) (2 + τ - 2)
    else rest (.own (2 + τ))) = _
  rw [if_neg (by omega : ¬ 2 + τ = 1), if_pos (⟨by omega, by omega⟩ : 2 ≤ 2 + τ ∧ 2 + τ < 5),
    Nat.add_sub_cancel_left]

variable (L : KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))

/-- **TbIsSent at this table, at every stand**, in scope. -/
theorem tbRng_sent (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (k : Coins (keyBook K₀)) (m : Mid (Local W₀ Rc Xi Unit) X) :
    TbIsSent Xs N Pl entry groups first L w₀ rc x hs
      (tbRng Xs N Pl entry groups first own₀ rest) k m := by
  intro c₁ hown
  have ht : 0 < (sentRanges Xs entry groups first).P.trees.length := by
    rw [trees_len _ _ _ (sent_codes Xs N Pl entry groups first hsrc scope)
      (sent_msgs Xs N Pl entry groups first hsrc scope), one_msg]
    decide
  have e : (msgTable Xs entry groups first k m.st.input).2 =
      (K1.treeTables (sentRanges Xs entry groups first).P
        (K1.rowsR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride
          ((sentRanges Xs entry groups first).data m.st.input) c₁)).getD 0 K1.wordlessTable := by
    unfold msgTable
    simp only [hown]
  refine (treeTable_some _ _ K1.wordlessTable ht).trans ?_
  rw [← e]
  all_goals rfl

variable (Kp : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12)

/-- **Member 15 plays at the key file's prover, at this table.** What is left: the parts bear their
places. NOT IN FRONT OF A LAW OVER COINS. -/
theorem playsS_at_table (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hP : Kp.AtPlaces)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop) :
    PlaysS (laid₁ Xs N Pl L w₀ rc x
      (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first
      (tbRng Xs N Pl entry groups first own₀ rest)) Said 15 :=
  playsS_at_tests Kp Xs N Pl pU pO entry groups first L w₀ rc x _ hK hsrc scope hP Said
    (fun k _ m _ _ => tbRng_sent Xs N Pl entry groups first own₀ rest L w₀ rc x _ hsrc scope k m)
    own₀ fun _ hτ => tbRng_test Xs N Pl entry groups first own₀ rest hτ

/-- **Member 15 is accepted at the key file's prover, at this table.** What is left: the parts bear
their places, and the rows are true. NOT IN FRONT OF A LAW OVER COINS. -/
theorem acceptedS_at_table (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hP : Kp.AtPlaces)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hRows : ∀ k s m E (c : RowCoins [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)]),
      ThrS (laid₁ Xs N Pl L w₀ rc x
        (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first
        (tbRng Xs N Pl entry groups first own₀ rest)) Said 15 k s m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)] 0 = .ok c →
      RowsTrue (X' := X) Xs N Pl entry groups first s m
        (restCoins (rangesTestJob (X' := X) Xs N Pl entry groups first) c.2.1))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    AcceptedS (laid₁ Xs N Pl L w₀ rc x
      (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first
      (tbRng Xs N Pl entry groups first own₀ rest)) Said fall 15 :=
  acceptedS_at_tests Kp Xs N Pl pU pO entry groups first L w₀ rc x _ hK hsrc scope hP Said
    (fun k _ m _ _ => tbRng_sent Xs N Pl entry groups first own₀ rest L w₀ rc x _ hsrc scope k m)
    hRows fall

end

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.treeTable_some
#print axioms ProofFile.Honest.K12.AtKey.msgTable
#print axioms ProofFile.Honest.K12.AtKey.tbRng
#print axioms ProofFile.Honest.K12.AtKey.tbRng_test
#print axioms ProofFile.Honest.K12.AtKey.tbRng_sent
#print axioms ProofFile.Honest.K12.AtKey.playsS_at_table
#print axioms ProofFile.Honest.K12.AtKey.acceptedS_at_table
