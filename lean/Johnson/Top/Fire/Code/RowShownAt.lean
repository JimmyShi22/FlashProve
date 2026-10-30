-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/RowShownAt.lean: «shownAll» AT THE MAKER's PIECE NUMBER n OF CHAIN 1, FOR EVERY n AND EVERY DESCRIPTION: so that a row need not unfold the maker's cut block by block (shown10_of | shown11_of, in Row10Eight.lean | Row11Eight.lean, do so at n = 0 | 1; at 17 that is no road).
NOTHING NEW IS PROVED OF WHAT IS SHOWN: cutShown (Johnson/Desc/Sound/ShownOfData.lean) says it OF EVERY PIECE OF A CUT ROW AT ONCE. WHAT WAS WANTING IS THAT THE ROW HAS A PIECE AT n AND WHICH: by cutRow_length (RowLengths.lean) · cutRow_at (RowCut.lean) · held_get (RowPieces.lean): CALLED.
  piece_mem₁    n ≤ k₁.length → (c₁ :: k₁)[n]? = some bn → the piece «pieceOf (held bn) (cutBase …) (cutDs …) (cutPut …) (rest₁ n (cutDs …))» IS A MEMBER OF THE MAKER's ROW
  shown_at₁     so, under the description's tests on the plan and its own data: that piece shows all (ShownAll F cs m fam), at every family that fits
  shown_inner₁  the same at an inner block (n < k₁.length), where nothing is put back: the form in which the rows' structures ask it, at any names base' | ds' for the base and the stretch
OBJECT: the maker's cut of chain 1 · USER: row 1.17's shownAll (and any row's of chain 1) · LETTERS: F file D; c₁ k₁ rest₁; n bn; cs m fam. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.RowLengths
import Johnson.Top.Fire.Code.RowCut
import Johnson.Desc.Sound.ShownOfData
import Johnson.Desc.Sound.ToldCount
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

section
variable {Xi W : Type} (C : CK) (F : FileDescription Xi) (D : WholeD)
    (c₁ : Block F.S₁ F.Cl) (k₁ : List (Block F.S₁ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)

theorem piece_mem₁ (putBack : List _root_.Fmt.RoundView) (n : ℕ) (hn : n ≤ k₁.length) (bn : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some bn) :
    pieceOf (held bn) (cutBase 0 D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n) (cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n)
        (cutPut putBack (k₁.map (held (P := F.XiPub))) n) (rest₁ n (cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n)) ∈
      (cutRow rest₁ putBack 0 0 D.ds₁ (held c₁) (k₁.map held)).1 :: (cutRow rest₁ putBack 0 0 D.ds₁ (held c₁) (k₁.map held)).2 := by
  have hlen : n < ((cutRow rest₁ putBack 0 0 D.ds₁ (held c₁) (k₁.map held)).1 :: (cutRow rest₁ putBack 0 0 D.ds₁ (held c₁) (k₁.map held)).2).length := by
    rw [List.length_cons, cutRow_length, List.length_map]
    omega
  have hg := List.getElem?_eq_getElem hlen
  obtain ⟨b', hb', hp⟩ := cutRow_at rest₁ putBack (k₁.map held) n 0 0 D.ds₁ (held c₁) _ hg
  obtain ⟨b, hb'', rfl⟩ := held_get c₁ k₁ n b' hb'
  obtain rfl : bn = b := Option.some.inj (hb.symm.trans hb'')
  rw [Nat.zero_add] at hp
  rw [← hp]
  exact List.getElem_mem hlen

theorem shown_at₁ (file : String) (hp : F.planOk = true) (hdata : F.data file = .ok D)
    (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ)) (fam : Fin m.length → ℕ × ℕ) (fits : SeatFits F cs m fam)
    (putBack : List _root_.Fmt.RoundView) (n : ℕ) (hn : n ≤ k₁.length) (bn : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some bn) :
    (pieceOf (held bn) (cutBase 0 D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n) (cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n)
        (cutPut putBack (k₁.map (held (P := F.XiPub))) n) (rest₁ n (cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n))).ShownAll F cs m fam :=
  cutShown C _ _ _ _ rest₁ putBack D (k₁.map held) (held c₁) 0 0 D.ds₁ rfl (shape_own₁ _) _ F cs m fam fits
    (oraclesAreOk _ F file D hdata (sentFit_of_planOk _ hp) (blocksOk_ok.2 (F.planOk_ok.1 hp).blocks₁) (blocksOk_ok.2 (F.planOk_ok.1 hp).blocks₂)) _
    (piece_mem₁ C F D c₁ k₁ rest₁ putBack n hn bn hb)

theorem shown_inner₁ (file : String) (hp : F.planOk = true) (hdata : F.data file = .ok D)
    (cs : OnBytes.Codes) (m : List (OnBytes.OracleShape × ℕ)) (fam : Fin m.length → ℕ × ℕ) (fits : SeatFits F cs m fam)
    (n : ℕ) (hn : n < k₁.length) (bn : Block F.S₁ F.Cl) (hb : (c₁ :: k₁)[n]? = some bn) (base' : ℕ) (ds' : List RDT)
    (eb : cutBase 0 D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n = base')
    (e : cutDs D.ds₁ (held c₁ : Block (F.XiPub × F.S₁) F.Cl) (k₁.map held) n = ds') :
    (pieceOf (held bn) base' ds' [] (rest₁ n ds')).ShownAll F cs m fam := by
  subst eb e
  have h := shown_at₁ C F D c₁ k₁ rest₁ file hp hdata cs m fam fits [] n (Nat.le_of_lt hn) bn hb
  rw [cutPut_inner [] _ n (by rw [List.length_map]; exact hn)] at h
  exact h

end

end LPFD

#print axioms LPFD.piece_mem₁
#print axioms LPFD.shown_at₁
#print axioms LPFD.shown_inner₁
