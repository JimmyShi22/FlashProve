-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedJointCountRowH.lean: THE ROW `shared_joint_count`, STATED, SEVENTH FORM: THE ROW
IN THE SENTENCE (Johnson/Desc/Sound/SharedJointCountRowG.lean) APPLIED AT THE TABLE's FILES' NAMED TERMS,
as they rest (Johnson/Desc/Sound/BordersSharedFill.lean and
TieEnd.lean). One definition of a term, ONE STATEMENT, and two small theorems.

What turns, against the sixth form (SharedJointCountRowF.lean: not in this library).
  THE SENTENCE: each kind's own errors stand in the row (own; within the cap; the laws at them; the
    point's split named): SharedJointCountRowG.lean's head.
  THE TERMS. Wt := `Wit Cells Tok MsgT` (with the pads by seat) · ext := `extOf … (e₀H …)`: the table's
    one extractor `extS … k` handed the acting part's value · same := `sameAt` (the number's table and
    the pad at the tenant's seat) · pin, pinT := `meaningSigS` · noColl, shown, held := `promSigS` · AND
    NEW: THE SLOT's OWN LETTERS ARE THE FIRST CHAIN's TABLE's: pin₁, claimM, ev, unmarked1 :=
    `tiedMeaning get Mg₁` · W's and the index masks' tenants := `tiedNumbers N₁` · Oc := `ocEnd get N₁ Mg₁
    links ps` (the first chain's whole promise at its last border): SO THE ROW's TERMS ARE, TO THE
    SIGN, THOSE AT WHICH THE JOINT OF THE TWO CHAINS IS SAID (`TieEnd`).
  G := F.
  `extNamedH`: the row's clause (4) holds at these terms, under ONE TEST WITH CODE on the plan's numbers:
    at every k and every component c that block k does not lay: `apartAt … k c = true`. By
    `extS_id`, `extSSame`. By report that test is not run at a real plan, and would
    say no at another version of the arr.
  `rowH_gives_E`: it gives the fifth form at these terms, with 1 ≤ N.

STILL A FORM WITH LETTERS: NOT A CLOSED ROW. F, T, D, all, C · N (the files' own number of slots) ·
Ns.lo, Ns.tenant, split · own, δK, δO · of Mg: nearU, recRow, omU, row, dot · of Pm: tablePromise,
shape, nothingLeft · the first table's: get, N₁, Mg₁, links, ps · beneath the terms: cs, arr, smp₂,
ms, decT₂, c₀, stOf, bookOf, Cells, Tok. UNTIL smp₂ HAS AN HONEST FILLING EVERY PIN HOLDS OF NOTHING.


Every "there is", walked: none of its own. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedJointCountRowG
import Johnson.Desc.Sound.BordersSharedFillProofs
import Johnson.Desc.Sound.TieEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Err)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (ModelPart Meaning Numbers)

section
variable (cs : OnBytes.Codes) {Xi S₂ Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp₂ : S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → S₂ → Option Cells) (c₀ : Cells)
  (Ns : NumbersS) (split : Bool)

/-- **The table's one extractor, handed the acting part's value.** -/
def e₀H (Fr : Frame) (k : ℕ) (v : ActV S₂ Fr) (w : Wit Cells Tok MsgT) : Wit Cells Tok MsgT :=
  extS cs G arr smp₂ ms decT₂ c₀ Ns split k v.1 (strsOfAct Fr v) w

/-- **The row's clause on the named extractor, at the named terms**, under one test with code. -/
theorem extNamedH {P₁ Cl : Type} {C : CK} {Fr : Frame}
    (p : Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT))
    (l : List (Piece C Fr (P₁ × S₂) Cl (Wit Cells Tok MsgT)))
    (h : ∀ k c, c ∉ laysAtS split k → apartAt Ns arr split k c = true) :
    ExtNamed split (extOf Ns p l (e₀H cs G arr smp₂ ms decT₂ c₀ Ns split Fr)) (sameAt Ns arr) :=
  ⟨fun k hk _ w => extS_id cs G arr smp₂ ms decT₂ c₀ Ns split k hk _ _ w,
    fun k _ w c hc =>
      extSSame cs Xi S₂ Cells Tok G arr smp₂ ms decT₂ c₀ Ns split k c hc (h k c hc) _ _ w⟩

end

/-- **THE ROW `shared_joint_count`, AS A FORM: SEVENTH FORM.** -/
def SharedJointCountRowH (C : CK) (D : WholeD) (all : List LeftT)
    (X Rec X₁ X₂ Cells Tok P₀ : Type) (F : FileDescription (X × Rec))
    (T : ThreeAt C D all F X₁ X₂ (Wit Cells Tok MsgT)) (Ns : NumbersS)
    (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) (Wit Cells Tok MsgT)) (Pm : PromMeaning F.S₂)
    (split : Bool) (N : ℕ) (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
    (smp₂ : F.S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → F.S₂ → Option Cells) (c₀ : Cells)
    (stOf : F.S₂ → OnBytes.Statement) (bookOf : F.S₂ → OnBytes.TreeBook)
    (get : F.XiPub × F.S₁ → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Place)
    (own : OwnErrs C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl
      (Wit Cells Tok MsgT))
    (δK δO : (p : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl
      (Wit Cells Tok MsgT)) → Err (uLT C p.ds)) : Prop :=
  SharedJointCountRowG C D all X Rec X₁ X₂ (Wit Cells Tok MsgT) F T (tiedNumbers N₁ Ns)
    (tiedMeaning get Mg₁ (meaningSigS cs F arr smp₂ ms decT₂ Mg))
    (promSigS cs F smp₂ ms stOf bookOf Pm) (ocEnd get N₁ Mg₁ links ps) split N
    (extOf (tiedNumbers N₁ Ns) (atDesc F T).p₂ (atDesc F T).l₂
      (e₀H cs F arr smp₂ ms decT₂ c₀ (tiedNumbers N₁ Ns) split _))
    (sameAt (tiedNumbers N₁ Ns) arr) own δK δO

/-- **It gives the fifth form at these terms, for at least one slot.** -/
theorem rowH_gives_E (C : CK) (D : WholeD) (all : List LeftT)
    (X Rec X₁ X₂ Cells Tok P₀ : Type) (F : FileDescription (X × Rec))
    (T : ThreeAt C D all F X₁ X₂ (Wit Cells Tok MsgT)) (Ns : NumbersS)
    (Mg : MeaningS F.S₂ (F.XiPub × F.S₁) (Wit Cells Tok MsgT)) (Pm : PromMeaning F.S₂)
    (split : Bool) (N : ℕ) (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
    (smp₂ : F.S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → F.S₂ → Option Cells) (c₀ : Cells)
    (stOf : F.S₂ → OnBytes.Statement) (bookOf : F.S₂ → OnBytes.TreeBook)
    (get : F.XiPub × F.S₁ → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ (Wit Cells Tok MsgT))
    (links : List ModelPart) (ps : List Place)
    (own : OwnErrs C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl
      (Wit Cells Tok MsgT))
    (δK δO : (p : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl
      (Wit Cells Tok MsgT)) → Err (uLT C p.ds))
    (h : SharedJointCountRowH C D all X Rec X₁ X₂ Cells Tok P₀ F T Ns Mg Pm split N cs arr smp₂ ms
      decT₂ c₀ stOf bookOf get N₁ Mg₁ links ps own δK δO) :
    1 ≤ N ∧ SharedJointCountRowE C D all X Rec X₁ X₂ (Wit Cells Tok MsgT) F T (tiedNumbers N₁ Ns)
      (tiedMeaning get Mg₁ (meaningSigS cs F arr smp₂ ms decT₂ Mg))
      (promSigS cs F smp₂ ms stOf bookOf Pm) (ocEnd get N₁ Mg₁ links ps) split N
      (extOf (tiedNumbers N₁ Ns) (atDesc F T).p₂ (atDesc F T).l₂
        (e₀H cs F arr smp₂ ms decT₂ c₀ (tiedNumbers N₁ Ns) split _))
      (sameAt (tiedNumbers N₁ Ns) arr) :=
  rowG_gives_E C D all X Rec X₁ X₂ (Wit Cells Tok MsgT) F T _ _ _ _ split N _ _ own δK δO h

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.extNamedH
#print axioms VerifiableInference.Desc.Sound.rowH_gives_E
