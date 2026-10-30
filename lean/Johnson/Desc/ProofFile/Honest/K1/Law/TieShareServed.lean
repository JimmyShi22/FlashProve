-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieShareServed.lean: THE ITEM "tie
m": exchangeAtS_tie_wide (Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShareWide.lean) WITH ITS TWO
PREMISES THAT NAME THE INPUT, hOwn AND hSmall, EXCHANGED FOR THE ONE SENTENCE hTr
(Johnson/Desc/ProofFile/Honest/K1/Law/TieDebtsAtServed.lean), AT ProofFile's OPENED BASE: the public part
spelled P5J.At.X Zp where the trace's laws stand, and Bs.G₀.W where the place's own list stands.
Two theorems; NO DEFINITION. COROLLARIES: a rewriting and calls.
NO PROPERTY IS CLAIMED.

  - hOwn_at_opened   "(h3)'s one rewrite": hOwn_of_served's end with the list at the ground's
                  spelling: K3.matsOwn Bs.G₀.W m: by the library's sealed IM.Open.W : Bs.G₀.W =
                  Z.p.X (Johnson/IMR/SeatOpen.lean); P5J.At.X Zp is Zp.p.X by definition
                  (Johnson/P5J/LettersAt.lean).
  - exchangeAtS_tie_served   ExchangeAtS L.thread Said b (.tie m), at Sz.ref and that list, from:
                  hM · hSt · hF1 · hF2 (unturned) · hTr · hMA · PartsFit · PlanMarks · O · m < 25.

THE TERMS THAT RIDE WITH IT. On
exchangeAtS_tie_wide: TiePlanShareWide.lean's head, and where it is called:
TiePlanShare.lean's head; on hTr and hMA: TieDebtsAtServed.lean's head: (h1)
(h2) (m1) (m2) (m3): BOTH ARE BINDERS, NEVER DEFINITIONS; hTr NAMES THE INPUT: OF COMPLETENESS's
KIND: never told as public; i and x are fixed only up to what cellOf reads of
theTrace; it may hold emptily where no w is valid; hMA feeds premises of completeness's kind:
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean's head).
THE SAME TERMS RIDE WITH exchangeAtS_tie_served, which is
exchangeAtS_tie_wide called once, at two letters fixed and two premises filled by theorems,
hOwn_at_opened and hSmall_of_served, WITH ONE TERM MORE: (s1) nothing in the statement ties L to
O: whoever spends the law shows that L's letters are those of the same three files: else hTr and
hF2 speak of one public part and the thread of another: not false: idle.

THE LETTERS L STAY A LETTER: no letters of ProofFile's are named, and no filling. NOTHING IN THE
STATEMENT TIES L TO O: Zp and Bs stand in O, in Mk, N, hMA and hTr, and in hF2's list alone: O is
spent for the one rewriting.

Limits. IT PAYS NOTHING: two premises on the input are exchanged for one, hTr, with Mk, N, hMA and
O beside. EVERY PREMISE IS ASKED AND NONE IS PROVED HERE: hTr is paid here at no letters; the tie to
another house's CellsOwnAt is not typed. AT Sz.ref ALONE; m < 25. A law under "Stepped", as
exchangeAtS_tie_wide is: it holds of nothing at a book that does not cover the part's count. Nothing
on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanShareWide
import Johnson.Desc.ProofFile.Honest.K1.Law.TieDebtsAtServed
import Johnson.IMR.SeatOpen
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT Mem cellsAt)
open OnBytes.HonestTrace (Sz cellOf PartsFit PlanMarks ServesAt MeetsAll theTrace)
open ProofFile.Honest.FirstThread (Letters)

/-- **"(h3)'s one rewrite"**: hOwn, with the list at the ground's spelling of the public part. hTr
and hMA: binders, on the terms of TieDebtsAtServed.lean's head. -/
theorem hOwn_at_opened {W : Type} {valid : W → Prop} {cells : W → ProofFile.Honest.Cells}
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Zp : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Zp Bs base c A B)
    (Mk : PlanMarks (P5J.At.X Zp)) (N : PartsFit (P5J.At.X Zp))
    (hMA : ∀ i x, ServesAt (P5J.At.X Zp) i x →
      MeetsAll (P5J.At.X Zp) i x (theTrace (P5J.At.X Zp) i x))
    (hTr : ∀ w, valid w → ∃ i x,
      (cells w).cell = cellOf (P5J.At.X Zp) (theTrace (P5J.At.X Zp) i x) ∧
        ServesAt (P5J.At.X Zp) i x)
    {m : ℕ} (hm : m < 25) :
    ∀ w, valid w → OwnersAgree Sz.ref (cells w) (K3.matsOwn Bs.G₀.W m) m := by
  rw [O.W]
  exact hOwn_of_served Mk N hMA hTr hm

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P CellsT Tok : Type}

/-- **THE SHARE AT THE ITEM tie m, FROM ONE SENTENCE ON THE INPUT.**
exchangeAtS_tie_wide with hTr for hOwn and hSmall. hTr NAMES THE INPUT: OF COMPLETENESS's KIND;
never told as public; a binder, never a definition; i and x are fixed only up to what cellOf reads
of theTrace; it may hold emptily where no w is valid. hMA: a binder: see TieDebtsAtServed.lean's
head. -/
theorem exchangeAtS_tie_served {L : Letters Bk Cl W₀ Rc Xi Tr' X' P CellsT Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {cs : OnBytes.Codes}
    {arr : ℕ → ℕ → ℕ} {ms : List Mem} {wit : Local W₀ Rc Xi Tr' → PlaceIn Xi} {b m nR : ℕ}
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Zp : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Zp Bs base c A B)
    (Mk : PlanMarks (P5J.At.X Zp)) (N : PartsFit (P5J.At.X Zp))
    (hMA : ∀ i x, ServesAt (P5J.At.X Zp) i x →
      MeetsAll (P5J.At.X Zp) i x (theTrace (P5J.At.X Zp) i x))
    (hTr : ∀ w, L.valid w → ∃ i x,
      (wit w).R.cells.cell = cellOf (P5J.At.X Zp) (theTrace (P5J.At.X Zp) i x) ∧
        ServesAt (P5J.At.X Zp) i x)
    (hm : m < 25)
    (hM : ∀ w, (L.Mg w).tie = First.K8.tieK8Rec (cellsAt cs arr ms L.N))
    (hSt : TieStateP L Said Sz.ref b m nR) (hF1 : TieMatS L Said cs arr ms Sz.ref wit b m)
    (hF2 : TieReadsS L Said cs arr ms wit (K3.matsOwn Bs.G₀.W m) b m nR) :
    ExchangeAtS L.thread Said b (.tie m) :=
  exchangeAtS_tie_wide hM
    (hOwn_at_opened (cells := fun w => (wit w).R.cells) O Mk N hMA hTr hm)
    (hSmall_of_served (cells := fun w => (wit w).R.cells) hMA hTr) hSt hF1 hF2

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.hOwn_at_opened
#print axioms ProofFile.Honest.K1.exchangeAtS_tie_served
