-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/KeyBorders23.lean: THE KEY FILE's ROWS OF THE TABLE OF JOINTS: THE SHARED AND THE LAST CHAIN (12 + 4 blocks; 13 + 5 borders), beside Johnson/Desc/Key/KeyBorders.lean (the items, a row's
form, the first chain's rows). Definitions with code, and tests on the table by evaluation. NO MEANING IS TYPED HERE. NO ROW IS CONFIRMED.
THE CUT IS THE LIBRARY's OWN: Cb/Ld/LdLin.lean («the test for linear constraints on the encoded index, beyond unique decoding, as a chain of interactive oracle reductions»), whose
relaxed relations j0 … j6 (:270-350) say, border by border, what is open, and whose own blocks' laws are THEOREMS OF THE LIBRARY (stated: Spec.ldLin_pt | ldLin_loc | ldLin_zeta, :542-563; proved: Cb/Ld/LdLinProofs.lean:103 | :225 | :282; the chain:
LdLinProofsChain.lean:41 ldLin_core; errors errPt | errLoc | errZeta, LdLin.lean:405-408): so a kind's law can be CARRIED, not proved anew.
THE LIBRARY's CUT, IN ITS WORDS AND THIS FILE's:
  j0 | j1 (in front of the shared point; W sent or not): the index decodes with its record AND the claimed row holds of what it decodes to (Cl): pinT · pile: THE PILE STAYS OPEN ACROSS V's SENDING.
  j2 (behind the shared point): Ev (the row Eval on w) · NearW e' (the stored words' fold at gamma) u · RecRow u · DotU u w: WITH u A COMPONENT OF THE WITNESS BEFORE IT IS SENT.
  j3: and u's message is pinned · j4 (behind the locations): NearW is gone, ColT u stands (the codeword of u has the folded columns' values at the drawn locations): the stored table is read nowhere else.
  j5: and Omega's message is pinned · j6 (behind zeta): DotU is gone: FoldR zeta psi_lo u omega · Dot g omega psi* w.
THE NAMED CLAIMS (KItem.claim chain name):
  1 "Eval"     LdLin's Ev: V(psi_c) + (the masks' term) = target · reads V, I · as a row it lies on the own group since V's sending · owed to the own test
  2 "NearU"    LdFoldEq's NearW: u's codeword is within e' positions of the stored words' fold at gamma · reads U and the stored strings · owed to LOC
  2 "RecRow"   LdFoldEq's RecRow: the sample of u's message part at the record's seed is the record's answers folded at gamma · reads U · owed to (rec_gamma), which lays it as rows
  2 "DotU"     LdLin's DotU: ⟨g, what is read off u at psi_lo⟩ = V at psi_sh · reads U, V · owed to LIN zeta
  2 "record"   the rows (rec_gamma) as they lie on G_u hold · reads U · owed to the test on G_u
  2 "columns"  LdLin's ColT, as the rows (loc_x) lie on G_u · reads U (the stored columns' folds stand in the rows' targets) · owed to the test on G_u
  2 "Fold"     LdLin's FoldR: Omega(zeta) = what u gives at (psi_lo, zeta) · reads Omega, U · owed to SPLIT
  2 "DotOm"    LdLin's Dot: ⟨g, Omega⟩ = V(psi_sh) · reads Omega, V · owed to K14's second part, which lays it as the row (Dot)
  2 "FoldO" | "FoldU"   the two rows as they lie: (Fold)'s part on G_omega + Sp[kappa] = mu | its part on G_u − Sp[kappa] = −mu · read Omega, Sp | U, Sp · owed to the two tests
  3 "Dot"      the row (Dot) as it lies on the own group holds · reads Omega, V · owed to the own test
THE SEAM. In front of the shared chain: «seam»: unmarked · pinT · pin 0 · srow 0 · pile · pin 2 · srow 2: so V's sending closes nothing and opens pin 2 · srow 2 alone: Johnson/Desc/Key/KeyBorders.lean has it so: «seam» is its end₁ (tested). A MASK SENT AHEAD HAS NO ITEM: by report it is raised inside K12's row (the library's joint behind a sending asks nothing of it).
THE CELLS. The library's relaxed relation reads no table of messages off the witness («no extractor produces it»): it says «there is U, dec = some U». In the table's form (PINW: the witness's cells ARE what the table decodes to) LIN point lays them.
Limits. By reading. That F_K's blocks ARE the library's (the typed key file's lists) is other files' to show. (Where
this and lean/THEOREM.md differ, the page holds.) The library's chain is for ONE instance and has all three parts in one row: here they lie on three hash chains. Nothing on soundness.

-/
import Johnson.Desc.Key.KeyBorders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-- The shared chain's blocks, by their names in F_K. -/
def names₂ : List String :=
  ["the shared chain's front", "LIN point", "send o_u", "(rec_gamma)", "LOC", "send o_omega", "joins", "LIN zeta", "SPLIT",
   "the proximity test (chain 2, piece 9)", "the proximity test (chain 2, piece 10)", "the end of chain 2"]

/-- The last chain's. -/
def names₃ : List String := ["K14, second part", "the taken trees' sources", "the proximity test (chain 3, piece 2)", "the end of chain 3"]

/-- **The shared chain's rows.** Messages: 0 I · 2 V · 3 U · 4 Omega · 5 the shared split's masks. -/
def rows₂ : List KRow :=
  [ { whose := "«link for key file»'s (the front: tests on the plan alone)" },
    { ins := [.pinT, .pile], outs := [.claim 1 "Eval", .claim 2 "NearU", .claim 2 "RecRow", .claim 2 "DotU"], ctx := [.pin 2, .pin 0], laysCells := true,
      whose := "K14's house: the library's pt (j1 → j2; Spec.ldLin_pt; errPt): the fold's bad points at gamma («theorem on codes»' foldErr_lin) and Schwartz-Zippel in kCol variables" },
    { outs := [.pin 3, .srow 3], whose := "K1's house: the library's sU (j2 → j3)" },
    { ins := [.claim 2 "RecRow"], outs := [.claim 2 "record"], whose := "K14's house: no round: the rows are laid: what they mean (its recLaw)" },
    { ins := [.claim 2 "NearU"], outs := [.claim 2 "columns"], ctx := [.pin 3], whose := "K14's house: the library's loc (j3 → j4; Spec.ldLin_loc; errLoc)" },
    { outs := [.pin 4, .srow 4, .pin 5, .srow 5], whose := "K1's house: the library's sO (j4 → j5)" },
    { whose := "K14's house: no round: book-keeping alone" },
    { ins := [.claim 2 "DotU"], outs := [.claim 2 "Fold", .claim 2 "DotOm"], ctx := [.pin 2, .pin 3, .pin 4], whose := "K14's house: the library's zeta (j5 → j6; Spec.ldLin_zeta; errZeta)" },
    { ins := [.claim 2 "Fold"], outs := [.claim 2 "FoldO", .claim 2 "FoldU"], whose := "K14's house: the two rows add up to (Fold), whatever mu and the mask entry are" },
    { ins := [.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3], ctx := [.pin 5, .srow 5], lays := [3], whose := "K12's house (H2): of the library's closing T" },
    { ins := [.claim 2 "FoldO", .srow 5, .pin 5], ctx := [.pin 4, .srow 4], lays := [5], whose := "K12's house (H2): of the library's closing T" },
    { whose := "the chains' end's" } ]

/-- What is open in front of the shared chain: THE PILE RIDES ACROSS V's SENDING. -/
def seam : List KItem := [.unmarked, .pinT, .pin 0, .srow 0, .pile, .pin 2, .srow 2]

/-- What is open behind the shared chain. -/
def end₂ : List KItem := [.unmarked, .pin 0, .srow 0, .pin 2, .srow 2, .claim 1 "Eval", .pin 4, .srow 4, .claim 2 "DotOm"]

/-- **The last chain's rows.** -/
def rows₃ : List KRow :=
  [ { ins := [.claim 2 "DotOm"], outs := [.claim 3 "Dot"], whose := "part 2's (K14's second part): no round: the row is laid; what a row means is the hash build's" },
    { whose := "part 2's: no round: the record is handed on as it is" },
    { ins := [.claim 1 "Eval", .claim 3 "Dot", .srow 0, .srow 2, .srow 4, .pin 0, .pin 2, .pin 4], lays := [0, 2, 4], whose := "K12's house (H2)" },
    { whose := "the chains' end's" } ]

/-- Which of the witness's messages an item of these two chains reads (none: the stored strings, the state, or a «there is» of its own). cells: no item of these chains reads them but pinT. -/
def readsMsg : KItem → List Nat
  | .pin k => [k]
  | .srow k => [k]
  | .claim 1 "Eval" => [2, 0]
  | .pile => [0]
  | .claim 2 "NearU" => [3]
  | .claim 2 "RecRow" => [3]
  | .claim 2 "record" => [3]
  | .claim 2 "columns" => [3]
  | .claim 2 "DotU" => [2, 3]
  | .claim 2 "DotOm" => [4, 2]
  | .claim 2 "Fold" => [4, 3]
  | .claim 2 "FoldO" => [4, 5]
  | .claim 2 "FoldU" => [3, 5]
  | .claim 3 "Dot" => [4, 2]
  | _ => []

def readsCells : KItem → Bool
  | .pinT => true
  | .pile => true
  | _ => false

/-- A TEST ON THE TABLE (after the proof file's table's laysClear): behind a block that lays a component NO OPEN ITEM READS IT: what the witness behind holds there is thrown away. -/
def laysClear : List KRow → List KItem → Bool
  | [], _ => true
  | r :: rs, O =>
    let O' := stepOpen O r
    O'.all (fun i => (readsMsg i).all (fun k => !r.lays.contains k) && !(r.laysCells && readsCells i)) && laysClear rs O'

/-- A TEST ON THE TABLE: every message that an item reads is pinned while the item is open, or the item speaks of a message that is sent later (told by name). later: the items that may. -/
def readsPinned (later : List KItem) : List KRow → List KItem → Bool
  | [], O => O.all fun i => later.contains i || (readsMsg i).all fun k => O.contains (.pin k)
  | r :: rs, O => (O.all fun i => later.contains i || (readsMsg i).all fun k => O.contains (.pin k)) && readsPinned later rs (stepOpen O r)

/-! ## Tests on the table, by evaluation -/

#eval (names₂.length, rows₂.length, names₃.length, rows₃.length)
#eval readsOpen (rows₂ ++ rows₃) seam
#eval decide (lastOpen rows₂ seam = end₂)
#eval decide (lastOpen (rows₂ ++ rows₃) seam = [.unmarked])
#eval laysClear (rows₂ ++ rows₃) seam
-- three items speak of U before it is pinned, as the library's j2 does: told by name; without the leave the test is due «false»
#eval readsPinned [.claim 2 "NearU", .claim 2 "RecRow", .claim 2 "DotU"] (rows₂ ++ rows₃) seam
#eval readsPinned [] (rows₂ ++ rows₃) seam
#eval decide (end₁ = seam) && decide (lastOpen (rows₁ 2) (start₁ 2) = seam)
#eval readsOpen (rows₁ 2 ++ rows₂ ++ rows₃) (start₁ 2) && decide (lastOpen (rows₁ 2 ++ rows₂ ++ rows₃) (start₁ 2) = [.unmarked])
-- controls: each is due «false»
#eval readsOpen ((rows₂ ++ rows₃).eraseIdx 2) seam                                          -- U's sending struck
#eval readsOpen ((rows₂ ++ rows₃).eraseIdx 7) seam                                          -- LIN zeta struck
#eval decide (lastOpen ((rows₂ ++ rows₃).eraseIdx 4) seam = [.unmarked])                    -- LOC struck: «NearU» stays open
#eval decide (lastOpen ((rows₂ ++ rows₃).eraseIdx 9) seam = [.unmarked])                    -- the test on G_u struck
#eval decide (lastOpen ((rows₂ ++ rows₃).eraseIdx 14) seam = [.unmarked])                   -- the own test struck
#eval readsOpen (rows₂ ++ rows₃) (seam.erase .pile)                                          -- the seam without the pile
#eval readsOpen (rows₂ ++ rows₃) [.unmarked, .pinT, .pin 0, .srow 0, .pin 2, .srow 2, .claim 1 "Eval", .claim 1 "VIs"]   -- a seam with the pile closed at V's sending
#eval laysClear ((rows₂ ++ rows₃).modify 9 fun r => { r with lays := [3, 5] }) seam          -- the test on G_u lays the split's masks too, which FoldO still reads
#eval laysClear ((rows₂ ++ rows₃).modify 0 fun r => { r with laysCells := true }) seam       -- the cells laid in front of LIN point, where pinT and the pile are open
#eval (openSets (rows₂ ++ rows₃) seam).zipIdx.map fun x => (x.2, x.1.length)

end VerifiableInference.Desc.Key
