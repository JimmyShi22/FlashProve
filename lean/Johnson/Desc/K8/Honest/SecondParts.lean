-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SecondParts.lean: THE SMALLNESS TEST: THE VERIFIER's TWO TESTS ON WEIGHTS BY
A SECOND COMPUTATION THAT ALSO ASK "NOT 0" OR "ALL DIFFERENT" (pieceWeightsHeld, tieWeightsHeld:
OnBytes/Model/Tail.lean), EACH TAKEN APART: WHAT MUST NEVER FAIL (equalities, weights that must be
0, one test on public numbers) AND WHAT A CHALLENGE CAN FAIL. Definitions and lemmas; none of the
library's goals. No prover stands in them; nothing on completeness, soundness or hiding.

  `PieceEqs`, `PieceNz`, **`piece_split`**   the test on a piece's weights says yes just where both
      hold
  `TieEqs`, `TieNz`, `TieDiff`, **`tie_split`**   the test on a tie's weights says yes just where
      the three hold
  `tiesL`   the weights on the columns of the ties' row of the digits' array
  `SecondEqs tl F`, `SecondRest tl F`   the first halves, and the others, at every wanted piece and
      every matrix, behind the step that lays the rows' weights (coefBody,
      Johnson/Desc/First/TailClaims/Coefficients.lean), at whatever the data hold
By: TailClaims.pieceWeightsHeld_iff, tieWeightsHeld_iff
(Johnson/Desc/First/TailClaims/AgainMeans.lean), which read the two tests aloud as propositions: the
definitions here regroup their right sides, with their own "let"s · pieceWeightsHeld_eq,
tieWeightsHeld_eq (AgainAgrees.lean).
Limits. A REGROUPING: nothing is shown to hold. Where the test walks with EqRun.all the propositions
speak of eqAt, as the library's do, not of eqPlainF.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.TailClaims.AgainMeans
import Johnson.Desc.First.TailClaims.AgainAgrees
import Johnson.Desc.First.TailClaims.Coefficients

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc.First.TailClaims (eqAt coefBody)

/-- **The piece's test: what must never fail**: the equalities and the weights that must be 0. -/
def PieceEqs (tl : HTailF2) (F : Fork) (g : Forest.Heard) (kappa : E) (w : Want) : Prop :=
  let p := (tl.zOf w.call).pieces.getD w.i {}
  let row := (F.trees.getD tl.ix.ZZ {}).rows.getD w.row {}
  let cv := row.coef
  let L := row.L
  let zk := g.zk.getD w.call #[]
  let ka := mulE kappa (callWeightAgain g w.call)
  let mk := subE zeroE ka
  let cv0 := cv.getD w.r0 zeroE
  let L0 := L.getD w.c0 zeroE
  (∀ cc < w.Cp, mulE cv0 (L.getD (w.c0 + cc) zeroE) = mulE mk (eqAt zk p.off cc)) ∧
    (∀ r < w.Rp,
      mulE (cv.getD (w.r0 + r) zeroE) L0 = mulE mk (eqPlainF zk (p.off + r * p.CP))) ∧
    mulE (cv.getD (w.r0 + w.Rp - 1) zeroE) (L.getD (w.c0 + w.Cp - 1) zeroE) =
      mulE mk (eqPlainF zk (p.off + (w.Rp - 1) * p.CP + (w.Cp - 1))) ∧
    (∀ r < w.r0, cv.getD r zeroE = zeroE) ∧
    (∀ r, w.r0 + w.Rp ≤ r → r < cv.size → cv.getD r zeroE = zeroE) ∧
    (∀ cc < w.c0, L.getD cc zeroE = zeroE) ∧
    ∀ cc, w.c0 + w.Cp ≤ cc → cc < L.size → L.getD cc zeroE = zeroE

/-- **The piece's test: "not 0".** -/
def PieceNz (tl : HTailF2) (F : Fork) (g : Forest.Heard) (kappa : E) (w : Want) : Prop :=
  let p := (tl.zOf w.call).pieces.getD w.i {}
  let row := (F.trees.getD tl.ix.ZZ {}).rows.getD w.row {}
  let cv := row.coef
  let L := row.L
  let zk := g.zk.getD w.call #[]
  let ka := mulE kappa (callWeightAgain g w.call)
  let mk := subE zeroE ka
  let cv0 := cv.getD w.r0 zeroE
  let L0 := L.getD w.c0 zeroE
  ka ≠ zeroE ∧ cv0 ≠ zeroE ∧ L0 ≠ zeroE ∧
    (∀ cc < w.Cp, mulE mk (eqAt zk p.off cc) ≠ zeroE) ∧
    ∀ r < w.Rp, mulE mk (eqPlainF zk (p.off + r * p.CP)) ≠ zeroE

/-- **The verifier's test on a piece's weights, in two.** -/
theorem piece_split (tl : HTailF2) (F : Fork) (g : Forest.Heard) (kappa : E) (w : Want) :
    tl.pieceWeightsHeld F g kappa w = true ↔ PieceEqs tl F g kappa w ∧ PieceNz tl F g kappa w := by
  rw [← TailClaims.pieceWeightsHeld_eq, TailClaims.pieceWeightsHeld_iff]
  unfold PieceEqs PieceNz
  dsimp only
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩
    exact ⟨⟨fun cc h => (a4 cc h).2, fun r h => (a5 r h).2, a6, a7, a8, a9, a10⟩, a1, a2, a3,
      fun cc h => (a4 cc h).1, fun r h => (a5 r h).1⟩
  · rintro ⟨⟨b1, b2, b3, b4, b5, b6, b7⟩, c1, c2, c3, c4, c5⟩
    exact ⟨c1, c2, c3, fun cc h => ⟨c4 cc h, b1 cc h⟩, fun r h => ⟨c5 r h, b2 r h⟩, b3, b4, b5,
      b6, b7⟩

/-- **The tie's test: what must never fail**: the equalities and one test on public numbers. -/
def TieEqs (tl : HTailF2) (F : Fork) (L5 : Array E) (mu : Nat) : Prop :=
  let s := tl.shp.getD mu {}
  let row := (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}
  let np2 := pow2Again tl.tau
  let ka := powE F.theta (F.planClaimsF + tl.firstAgain mu)
  let hi := powersAgain F.theta np2 s.mS
  let c0 := tl.off.getD mu 0
  let c1 := tl.mz + c0
  let before := (List.range mu).foldl (fun n nu => n + (tl.mats.getD nu {}).k) 0
  let xi2 := (Array.range tl.tau).map fun u => powE F.theta u
  (tl.loX.getD mu #[]).getD 0 zeroE = oneE ∧
    (∀ R < s.R, row.coef.getD R zeroE = hi.getD R zeroE) ∧
    s.m ≤ 3 * s.mS ∧
    (∀ R < s.mS, ∀ i, 3 * R ≤ i → i < 3 * R + min 3 (s.m - 3 * R) →
      let x := mulE ka (hi.getD R zeroE)
      let xB := scaleE (fOfNat radb) x
      let xBB := scaleE (fOfNat radb) xB
      let v := if i % 3 = 0 then x else if i % 3 = 1 then xB else xBB
      L5.getD (c0 + i) zeroE = v ∧ L5.getD (c1 + i) zeroE = scaleNat v (2 ^ t2D0)) ∧
    ∀ c < s.k,
      let gam := sumAgain tl.cfF ((before + c) * tl.tau) xi2 tl.tau 0 zeroE
      (tl.gamX.getD mu #[]).getD c zeroE = gam ∧ (tl.gamV.getD mu #[]).getD c zeroE = gam ∧
        row.L.getD c zeroE = mulE (subE zeroE ka) gam

/-- **The tie's test: "not 0".** -/
def TieNz (tl : HTailF2) (F : Fork) (mu : Nat) : Prop :=
  let s := tl.shp.getD mu {}
  let row := (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}
  let np2 := pow2Again tl.tau
  let ka := powE F.theta (F.planClaimsF + tl.firstAgain mu)
  let hi := powersAgain F.theta np2 s.mS
  (∀ R < s.R, row.coef.getD R zeroE ≠ zeroE) ∧
    ∀ R < s.mS, ∀ i, 3 * R ≤ i → i < 3 * R + min 3 (s.m - 3 * R) →
      let x := mulE ka (hi.getD R zeroE)
      let xB := scaleE (fOfNat radb) x
      let xBB := scaleE (fOfNat radb) xB
      (if i % 3 = 0 then x else if i % 3 = 1 then xB else xBB) ≠ zeroE

/-- **The tie's test: "all different"**: of the sorted weights no two neighbours are equal. -/
def TieDiff (tl : HTailF2) (F : Fork) (mu : Nat) : Prop :=
  let row := (F.trees.getD (tl.gtTree.getD mu 0) {}).rows.getD 0 {}
  ∀ i a b, (row.coef.toList.mergeSort TailClaims.leE)[i]? = some a →
    (row.coef.toList.mergeSort TailClaims.leE)[i + 1]? = some b → a ≠ b

/-- **The verifier's test on a tie's weights, in three.** -/
theorem tie_split (tl : HTailF2) (F : Fork) (L5 : Array E) (mu : Nat) :
    tl.tieWeightsHeld F L5 mu = true ↔
      TieEqs tl F L5 mu ∧ TieNz tl F mu ∧ TieDiff tl F mu := by
  rw [← TailClaims.tieWeightsHeld_eq, TailClaims.tieWeightsHeld_iff]
  unfold TieEqs TieNz TieDiff
  dsimp only
  constructor
  · rintro ⟨a1, a2, a3, a4, a5, a6⟩
    exact ⟨⟨a1, fun R h => (a2 R h).1, a4, fun R h i h1 h2 => (a5 R h i h1 h2).2, a6⟩,
      ⟨fun R h => (a2 R h).2, fun R h i h1 h2 => (a5 R h i h1 h2).1⟩, a3⟩
  · rintro ⟨⟨b1, b2, b3, b4, b5⟩, ⟨c1, c2⟩, d⟩
    exact ⟨b1, fun R h => ⟨b2 R h, c1 R h⟩, d, b3,
      fun R h i h1 h2 => ⟨c2 R h i h1 h2, b4 R h i h1 h2⟩, b5⟩

/-- The ties' row's weights on the columns, at a ledger. -/
def tiesL (tl : HTailF2) (G : Fork) (nbW : Nat) : Array E :=
  ((G.trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L

/-- **WHAT OF THE TWO TESTS MUST NEVER FAIL**, behind the step that lays the rows' weights, at
whatever the data hold. -/
def SecondEqs (tl : HTailF2) (F : Fork) : Prop :=
  ∀ g jo nbW W, tl.heard = some g → tl.joinObj9 = some jo → tl.wants = some (nbW, W) →
    (∀ w ∈ W, PieceEqs tl (coefBody tl g F) g (t2fKappaByText (coefBody tl g F).theta jo) w) ∧
      ∀ mu < tl.NM, TieEqs tl (coefBody tl g F) (tiesL tl (coefBody tl g F) nbW) mu

/-- **What of the two tests a challenge can fail**: "not 0" and "all different". -/
def SecondRest (tl : HTailF2) (F : Fork) : Prop :=
  ∀ g jo nbW W, tl.heard = some g → tl.joinObj9 = some jo → tl.wants = some (nbW, W) →
    (∀ w ∈ W, PieceNz tl (coefBody tl g F) g (t2fKappaByText (coefBody tl g F).theta jo) w) ∧
      ∀ mu < tl.NM, TieNz tl (coefBody tl g F) mu ∧ TieDiff tl (coefBody tl g F) mu

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.piece_split
#print axioms VerifiableInference.Desc.First.K8.Honest.tie_split
