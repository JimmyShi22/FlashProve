--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/Row101.lean: OUR 101 NUMBERS IN THE FORM THAT COUNTS, AT THE PROMISE's
PUBLIC TEST: HandsR, all six fields, at ANY FENCE Fk INSIDE "the fold from the typed start reaches
the state", at E := EAt D base linksW placesW z, for the seated sub-protocol at a
number 14 l + i + 2 whose kind is K3, K4, K5, K6, K8 or K11: FROM THE KIND's OWN DEBT MadeOwed AT
THAT SAME FENCE AND TWO NAMED PREMISES. One theorem, proved.



  row_101   five fields: quiet_row_R at the test that is switched off behind
    the number (offNext), narrowed to Fk (HandsR.weaker); the sixth, "more":
    more_of_owed at sameOn_yes; joined by handsR_on.
  WHY A LETTER FOR THE FENCE: whoever can show the debt only at states of which more is known than
    that raw steps reach them hands it in at that narrower fence, and gets HandsR there.
  PREMISES THAT STAY: hB (the book's test at every reached state) · hFk (Fk lies inside "reached") ·
    alike (base has one value at all states) · M : MadeOwed at Fk.

OBJECT: c.blocksInOrder[14 l + i + 2]. USER: none in Lean yet. LETTERS: N, D, base, z, p: free.

What is not claimed. MadeOwed at any sub-protocol. hB. No soundness.
-/
import Johnson.IMR.GrownReach
import Johnson.IMR.HandsMore
import Johnson.IMR.KeepsAt
import Johnson.IMR.SendsK1

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Place KindName)
open VerifiableInference.Desc.First (S Numbers Pub PubData bookAt)
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach)
open Meaning.Tl (SameTl)
open ProofFile (Cl)

/-- **OUR 101, FROM THE KINDS' OWN DEBTS.** -/
theorem row_101 {Q : Type} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {c : Chain S Cl} {N : Numbers}
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
    HandsR Fk N linksW placesW (EAt D base linksW placesW z) 0 (14 * l + i + 2) b := by
  obtain ⟨L, hL, hb'⟩ := lot
  refine handsR_on
    ((quiet_row_R (E := offNext (EAt D base linksW placesW z) (14 * l + i + 2)) hB hl hk
      ⟨L, hL, hb'⟩ hp hq hla hb fun _ s' _ _ _ _ => more_offNext s').weaker hFk)
    (more_of_owed (hear_placeW hl hk) (fun s s' hy => ?_) alike M)
  have h := sameOn_yes D hL hb' (by rw [hp]; exact hq) (alone_underR hla) hy
  rw [hp] at h
  exact h

end IM

#print axioms IM.row_101
