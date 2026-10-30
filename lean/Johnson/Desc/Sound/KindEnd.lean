-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KindEnd.lean: FROM THE END OF A KIND's FILES' TOP TO THE FORM IN WHICH THE
TOWER ASKS IT: another file's h.Kind 𝔇₀ 𝔏 K (Johnson/P5J/RowsAtMg.lean: AtMg.Kind), TO THE
LETTER, at the closed constant (𝔇₀ := h.𝔇, Johnson/P5J/MgAtAll.lean). Eight theorems.

Why. Three kinds' tops end in "for every i q p: the i-th piece of the three rows of pieces
with the cap as their errors is q, the i-th place is p, p's kind is K: q, with the table's
extractor laid, is tied at i" at their spellings of the list of segments, the places, the numbers,
the meaning, the extractor and the pieces. The tower's field reads the same sentence at its own
spellings. HERE EACH PAIR OF SPELLINGS IS SHOWN ONE, BY NAME; ALL SIX BY rfl.

  kind_links · kind_ps · kind_N · kind_mg · kind_row · kind_ex   the six equations of letters.
  kind_iff         **h.Kind h.𝔇 𝔏 K IS these tops' end**, at Rch := RchAt (F0T …) and at the data
                   D.at frS.P.T.a: an "if and only if" by rfl.
  kind_of_end      the direction that a kind's files call.
THE DATA. The tower's pieces and frames stand at D.at frS.P.T.a. A top that is general in the data
is CALLED at that value, with "the description's data are these" by LaidAt.atDepth
(Johnson/P5J/FourAtMg.lean: in scope D.at frS.P.T.a = D).
What is not claimed. That any kind's top's premises hold at RchAt, at 𝔏's letters or at the
closed constant. No member of h.Kind. Nothing on soundness.

-/
import Johnson.P5J.RowsAtMg
import Johnson.P5J.MgAtAll
import Johnson.Goal.Skeleton.TheThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (flatPlacesOf)
open Johnson.Desc.First.Walk.Tied (RchAt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

theorem kind_links : fullLinks = linksFull := rfl

theorem kind_ps : At.ps = flatPlacesOf linksFull true := rfl

theorem kind_N (h : AtMgA o Z D r Zp Np cF x) : At.N Zp cF = h.𝔇.N := rfl

theorem kind_mg (h : AtMgA o Z D r Zp Np cF x) : mgAt h.toAtMg h.𝔇 = mgAtAll h := rfl

/-- The tower's first chain's pieces are the three rows' first row, with the cap as its errors. -/
theorem kind_row (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) :
    h.toAtMg.row 𝔏 =
      (threeCap (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃
        𝔏.dW 𝔏.wEnd).p₁ ::
      (threeCap (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃
        𝔏.dW 𝔏.wEnd).l₁ := rfl

/-- The tower's extractor is the first table's own, at the constant's letters. -/
theorem kind_ex (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) :
    h.toAtMg.ex 𝔏 =
      (fun k => extQAt h.𝔇.cs h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT 𝔏.c₀ At.tokOf h.𝔇.N linksFull
        (flatPlacesOf linksFull true) (fun a => a) k) := rfl

/-- **The tower's field is these tops' end (see the head).** -/
theorem kind_iff (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (K : KindName) :
    h.toAtMg.Kind h.𝔇 𝔏 K ↔ ∀ i q p,
      ((threeCap (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃
        𝔏.dW 𝔏.wEnd).p₁ ::
      (threeCap (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃
        𝔏.dW 𝔏.wEnd).l₁)[i]? = some q →
      (flatPlacesOf linksFull true)[i]? = some p → p.kind = K →
      TiedAtR h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun a => a)
        (RchAt (F0T o Zp Np cF)) i
        (q.withMap ((fun k => extQAt h.𝔇.cs h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT 𝔏.c₀ At.tokOf
            h.𝔇.N
          linksFull (flatPlacesOf linksFull true) (fun a => a) k) i)) := Iff.rfl

/-- The direction that a kind's files call. -/
theorem kind_of_end (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (K : KindName)
    (hEnd : ∀ i q p,
      ((threeCap (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃
        𝔏.dW 𝔏.wEnd).p₁ ::
      (threeCap (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃
        𝔏.dW 𝔏.wEnd).l₁)[i]? = some q →
      (flatPlacesOf linksFull true)[i]? = some p → p.kind = K →
      TiedAtR h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun a => a)
        (RchAt (F0T o Zp Np cF)) i
        (q.withMap ((fun k => extQAt h.𝔇.cs h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT 𝔏.c₀ At.tokOf
            h.𝔇.N
          linksFull (flatPlacesOf linksFull true) (fun a => a) k) i))) :
    h.toAtMg.Kind h.𝔇 𝔏 K := (kind_iff h 𝔏 K).2 hEnd

end P5J
