-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KindEndA.lean: FROM THE END OF A KIND's FILES' TOP TO THE FORM IN WHICH A
KIND's LAW IS COUNTED: h.Kind 𝔏 K at h : AtMgA … (Johnson/P5J/RowsAtAll.lean:
AtMgA.Kind): at the closed constant mgAtAll h and at "reached AND the public part is a typed
instance's". Three theorems. It stands on Johnson/Desc/Sound/KindEnd.lean.


  kindA_iff      **h.Kind 𝔏 K IS the end of the tops (KindEnd.lean's head), at Rch := fun k a =>
                 RchAt (F0T …) k a ∧ ∃ z, a.1.1 = (instanceAsPlainRecord z).pub**: "if and only if" by rfl.
  kindA_of_kind  the share at bare "reached" gives the counted one (AtMg.Kind.toR).
  kindA_of_end   the direction that a kind's files call, from their top's end at bare "reached" (the
                 stronger sentence: less is in hand in each tie).
What is not claimed. That any kind's top's premises hold. No member of h.Kind. Nothing on
soundness.

-/
import Johnson.Desc.Sound.KindEnd
import Johnson.P5J.RowsAtAll

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

/-- **The counted form is those tops' end (KindEnd.lean's head), at "reached and typed".** -/
theorem kindA_iff (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
    (K : KindName) :
    h.Kind 𝔏 K ↔ ∀ i q p,
      ((threeCap (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃
        𝔏.dW 𝔏.wEnd).p₁ ::
      (threeCap (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃
        𝔏.dW 𝔏.wEnd).l₁)[i]? = some q →
      (flatPlacesOf linksFull true)[i]? = some p → p.kind = K →
      TiedAtR h.𝔇.N (mgAtAll h) linksFull (flatPlacesOf linksFull true) (fun a => a)
        (fun k a => RchAt (F0T o Zp Np cF) k a ∧ ∃ z, a.1.1 = (LPFD.Full.instanceAsPlainRecord z).pub) i
        (q.withMap ((fun k => extQAt h.𝔇.cs h.𝔇.G h.𝔇.arr h.𝔇.smp h.𝔇.ms h.𝔇.decT 𝔏.c₀ At.tokOf
            h.𝔇.N
          linksFull (flatPlacesOf linksFull true) (fun a => a) k) i)) := Iff.rfl

/-- The share at bare "reached" gives the counted one. -/
theorem kindA_of_kind (h : AtMgA o Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok) (K : KindName)
    (k : h.toAtMg.Kind h.𝔇 𝔏 K) : h.Kind 𝔏 K := by
  rw [AtMgA.kind_is]
  exact AtMg.Kind.toR k

/-- The direction that a kind's files call. -/
theorem kindA_of_end (h : AtMgA o Z D r Zp Np cF x) (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)
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
    h.Kind 𝔏 K := kindA_of_kind h 𝔏 K (kind_of_end h 𝔏 K hEnd)

end P5J
