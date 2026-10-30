--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/IMR/Row101W.lean:
OUR 101 NUMBERS AT THE CONSTANT AT WHICH THE JOIN OF THE 358 IS
WRITTEN: EW (Johnson/LPFK9R/SharesAtE.lean). Two theorems, proved.



  eAt_eq_EW   EAt D base linksW placesW z (MadeOwed.lean) and EW D base z are one function: by
    rfl.
  row_101W   row_101 (Row101.lean) with EW in its conclusion. The debt MadeOwed keeps its own
    letters.

OBJECT: HandsR at c.blocksInOrder[14 l + i + 2]. USER: none in Lean yet. LETTERS: as at row_101.

What is not claimed. As at row_101. No soundness.
-/
import Johnson.IMR.Row101
import Johnson.LPFK9R.SharesAtE

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Place KindName)
open VerifiableInference.Desc.First (S Numbers Pub PubData bookAt)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.Tl (SameTl)
open ProofFile (Cl)

/-- Two names for one function. -/
theorem eAt_eq_EW {Q : Type} (D : PubData) (base : Pub → Q × S → Bool) (z : Q) :
    EAt D base linksW placesW z = LPFK9.HandsAt.EW D base z := rfl

/-- **OUR 101, AT THE JOIN's CONSTANT.** -/
theorem row_101W {Q : Type} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {c : Chain S Cl} {N : Numbers}
    {D : PubData} {base : Pub → Q × S → Bool} {z : Q} {p : ProofFile.InstPub} {Fk : ℕ → S → Prop}
    (hB : ∀ k s, Reach 0 c.blocksInOrder (ProofFile.startS Z) k (p, s) → bookAt N placesW[k]? s = true)
    {l i : ℕ} {k0 : KindName} {b b' : Block S Cl} {name : String} (hl : l < 25)
    (hk : (VerifiableInference.Desc.First.kindsBeforeBatching (subAt l) (l == 0))[i]? = some k0)
    (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀)
    (hp : b'.place = { chain := 1, link := some l, piece := i + 1, kind := k0 })
    (hq : quietMaker k0 = true)
    (hla : LaidAlone ProofFile.sameReply b b' name
      { chain := 1, link := some l, piece := i + 1, kind := k0 })
    (hb : c.blocksInOrder[14 * l + i + 2]? = some b)
    (hFk : ∀ s, Fk (14 * l + i + 2) s → RF 0 c.blocksInOrder (ProofFile.startS Z) p (14 * l + i + 2) s)
    (alike : ∀ q s s', base q (z, s') = base q (z, s))
    (M : MadeOwed Fk N linksW placesW D base z 0 (14 * l + i + 2) b
      { chain := 1, link := some l, piece := i + 1, kind := k0 }) :
    HandsR Fk N linksW placesW (LPFK9.HandsAt.EW D base z) 0 (14 * l + i + 2) b :=
  eAt_eq_EW D base z ▸ row_101 hB hl hk lot hp hq hla hb hFk alike M

end IM

#print axioms IM.eAt_eq_EW
#print axioms IM.row_101W
