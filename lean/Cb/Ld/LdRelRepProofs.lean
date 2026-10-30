-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelRepProofs.lean: the proofs of the statements of Cb/Ld/LdRelRep.lean (Cb.Spec.ldr_*).
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

The statements of Cb/Ld/LdRelRep.lean derive properties of a family of interleaved linear codes,
read at common positions as one `LdCode` (`T.ld E R`), from properties of the codes and of the
reading.
Main names (statements and hypotheses: Cb/Ld/LdRelRep.lean):
  `ldr_near`: within e long positions of an encoding.
  `ldr_onCode_of`, `ldr_onCode`: "on the code on S".
  `ldr_laws`: the laws.
  `ldr_dist`: the distance under T.
  `ldr_list`: the list.
  `ldr_mca`: agreement.
  `ldr_transparent`, `ldr_local`: transparent; one native position of each component for a long
    position.
  `ldr_zk`: see its statement in Cb/Ld/LdRelRep.lean.
-/
import Cb.Ld.LdRelRep
import Cb.Ld.LdRelProofsCode
import Cb.Gen.CodeRepProofs
import Cb.Gen.CodeRepHides
import Cb.Gen.CodeOnto

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks

section One
variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] {P : Type}

omit [Field F] [Algebra F E] in
theorem ldr_fm_add (C₀ : Code.Enc F) (m m' : Fin C₀.msg → E) (r r' : Fin C₀.r → E) :
    C₀.fm (m + m') (r + r') = C₀.fm m r + C₀.fm m' r' := by
  funext i
  simp only [Code.Enc.fm, Pi.add_apply]
  split_ifs <;> simp

omit [Field F] [Algebra F E] in
theorem ldr_fm_smul (C₀ : Code.Enc F) (c : E) (m : Fin C₀.msg → E) (r : Fin C₀.r → E) :
    C₀.fm (c • m) (c • r) = c • C₀.fm m r := by
  funext i
  simp only [Code.Enc.fm, Pi.smul_apply]
  split_ifs <;> simp

omit [Field F] [Algebra F E] in
theorem ldr_fm_inj (C₀ : Code.Enc F) (hp : C₀.msg + C₀.r ≤ C₀.k) {m m' : Fin C₀.msg → E}
    {r r' : Fin C₀.r → E} (h : C₀.fm m r = C₀.fm m' r') : m = m' ∧ r = r' :=
  ⟨by rw [← msgPart_fm hp m r, h, msgPart_fm hp],
    by rw [← rndPart_fm C₀ hp m r, h, rndPart_fm C₀ hp]⟩

omit [Field F] [Algebra F E] in
theorem ldr_fm_zero (C₀ : Code.Enc F) : C₀.fm (0 : Fin C₀.msg → E) (0 : Fin C₀.r → E) = 0 := by
  funext i
  simp only [Code.Enc.fm, Pi.zero_apply]
  split_ifs <;> rfl

/-- Under `hp`, `hd`, `h0`: one code, read at given positions (`LdCode.ofEnc C₀ pos`), has the laws
(`LdCode.Laws`, Cb/Ld/LdRel.lean). -/
theorem laws_ofEnc (C₀ : Code.Enc F) (pos : P → Fin C₀.n) (hp : C₀.msg + C₀.r ≤ C₀.k)
    (hd : HasDist C₀.G C₀.d) (h0 : 0 < C₀.d) :
    (LdCode.ofEnc (E := E) C₀ pos).Laws := by
  refine ⟨⟨fun a b => ?_, fun c a => ?_⟩, ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
    fun m r h => ?_, fun f g x hfg => ?_⟩
  · funext p _
    show (C₀.GE E).mulVec (C₀.fm (a.1 + b.1) (a.2 + b.2)) p =
      (C₀.GE E).mulVec (C₀.fm a.1 a.2) p + (C₀.GE E).mulVec (C₀.fm b.1 b.2) p
    rw [ldr_fm_add, Matrix.mulVec_add, Pi.add_apply]
  · funext p _
    show (C₀.GE E).mulVec (C₀.fm (c • a.1) (c • a.2)) p = c • (C₀.GE E).mulVec (C₀.fm a.1 a.2) p
    rw [ldr_fm_smul, Matrix.mulVec_smul, Pi.smul_apply]
  · have h1 : (C₀.GE E).mulVec (C₀.fm m r) =
        (C₀.GE E).mulVec (C₀.fm (0 : Fin C₀.msg → E) (0 : Fin C₀.r → E)) := by
      rw [ldr_fm_zero, Matrix.mulVec_zero]
      exact funext fun p => congrFun (congrFun h p) ()
    exact ldr_fm_inj C₀ hp ((HasDist.map (E := E) hd).injective h0 h1)
  · funext _
    exact congrFun (hfg (pos x) (Finset.mem_singleton_self _)) ()

end One

section
variable (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]

theorem ldr_near : Spec.ldr_near F E := by
  intro A _ _ C T R _ _ e f m r
  unfold LdCode.Near Reading.DecodesTo
  rw [cnt_congr (Q := T.Off E (T.tabs f) (T.fms m r)) fun x => ?_]
  constructor
  · intro h
    obtain ⟨α, hα⟩ := Function.ne_iff.1 h
    exact ⟨α.1, α.2.1, hα⟩
  · rintro ⟨a, i, h⟩ hh
    exact h (congrFun hh ⟨a, (i, ())⟩)

theorem ldr_onCode_of : Spec.ldr_onCode_of F E := by
  intro A _ _ C T R _ _ f S ⟨m, r, h⟩
  exact ⟨T.fms m r, fun x hx a i => congrFun (h x hx) ⟨a, (i, ())⟩⟩

theorem ldr_onCode : Spec.ldr_onCode F E := by
  intro A _ _ C T R _ _ hk f S
  refine ⟨ldr_onCode_of F E A C T R f S, ?_⟩
  rintro ⟨M, h⟩
  refine ⟨fun n => msgPart (C n.1) (M n.1 n.2.1) n.2.2,
    fun n => rndPart (C n.1) (M n.1 n.2.1) n.2.2,
    fun x hx => funext fun α => ?_⟩
  have h1 := h x hx α.1 α.2.1
  rw [← fm_parts (C α.1) (hk α.1) (M α.1 α.2.1)] at h1
  exact h1

theorem ldr_laws : Spec.ldr_laws F E := fun A _ _ C T R _ _ hp hd h0 =>
  ld_laws_fam E T.P A _ fun a =>
    ld_laws_il E T.P _ (R a) (laws_ofEnc (C a) (T.pos a) (hp a) (hd a) (h0 a))

theorem fms_ne_zero {A : Type} [Fintype A] [DecidableEq A] {C : A → Code.Enc F} (T : Reading C)
    {R : A → Type} [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)]
    (hp : ∀ a, (C a).msg + (C a).r ≤ (C a).k) {m m' : (T.ld E R).J → E}
    {r r' : (T.ld E R).Q → E} (h : T.fms m r = T.fms m' r') : m = m' ∧ r = r' := by
  have hh : ∀ a i,
      (fun j => m ⟨a, (i, j)⟩) = (fun j => m' ⟨a, (i, j)⟩) ∧
      (fun q => r ⟨a, (i, q)⟩) = fun q => r' ⟨a, (i, q)⟩ :=
    fun a i => ldr_fm_inj (C a) (hp a) (congrFun (congrFun h a) i)
  exact ⟨funext fun n => congrFun (hh n.1 n.2.1).1 n.2.2,
    funext fun n => congrFun (hh n.1 n.2.1).2 n.2.2⟩

theorem ldr_dist : Spec.ldr_dist F E := by
  intro A _ _ C T R _ _ D hT hp hd hD m r hne
  have h0 : T.fms m r ≠ T.fms (E := E) (R := R) 0 0 := fun h => hne (fms_ne_zero F E T hp h)
  refine le_trans (dist_under F E A C T hT hd D hD R _ _ h0) (cnt_mono fun x hx hh => ?_)
  obtain ⟨a, i, h⟩ := hx
  refine h ?_
  have h1 : ((C a).GE E).mulVec (T.fms m r a i) (T.pos a x) = 0 := congrFun hh ⟨a, (i, ())⟩
  have h2 : T.fms (E := E) (R := R) 0 0 a i = 0 := ldr_fm_zero (C a)
  rw [h1, h2, Matrix.mulVec_zero, Pi.zero_apply]

theorem ldr_transparent : Spec.ldr_transparent F E := by
  intro A _ _ C T R _ _
  refine ⟨fun _ g p s => g ⟨p.1, (s.1, ())⟩, fun m r x p hp => ?_⟩
  obtain ⟨a, j⟩ := p
  have hj : j = T.pos a x := Finset.mem_singleton.1 (Finset.mem_sigma.1 hp).2
  subst hj
  rfl

theorem ldr_local : Spec.ldr_local F E := by
  intro A _ _ C T R _ _ x
  show (Finset.univ.sigma fun a => ({T.pos a x} : Finset (Fin (C a).n))).card ≤ Fintype.card A
  rw [Finset.card_sigma]
  simp

theorem ldr_list [Finite E] : Spec.ldr_list F E := by
  intro A _ _ C T R _ _ e L hp h f
  refine le_trans ?_ (h (T.tabs f))
  exact Nat.card_le_card_of_injective
    (fun w : {w : ((T.ld E R).J → E) × ((T.ld E R).Q → E) //
        (T.ld E R).Near e f ((T.ld E R).enc w.1 w.2)} =>
          (⟨T.fms w.1.1 w.1.2, (ldr_near F E A C T R e f w.1.1 w.1.2).1 w.2⟩ :
            {M : ∀ a, R a → Fin (C a).k → E // T.DecodesTo E e (T.tabs f) M})) fun w w' hw =>
              Subtype.ext
                (Prod.ext (fms_ne_zero F E T hp (congrArg Subtype.val hw)).1
                  (fms_ne_zero F E T hp (congrArg Subtype.val hw)).2)

theorem ldr_mca [Finite E] : Spec.ldr_mca F E := by
  intro A _ _ C T R _ _ e bad hk h f₀ f₁
  refine le_trans (cnt_mono fun θ hθ => ?_) (h (T.tabs f₀) (T.tabs f₁))
  obtain ⟨S, hS, hl, hn⟩ := hθ
  refine ⟨S, hS,
    (ldr_onCode F E A C T R hk (f₀ + θ • f₁) S).1 hl,
    fun hc => hn ⟨(ldr_onCode F E A C T R hk f₀ S).2 hc.1, (ldr_onCode F E A C T R hk f₁ S).2 hc.2⟩⟩

end
section Zk
variable (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] [Fintype F] [Fintype E]

/-- The randomness of the record (`T.ld E R`, Cb/Ld/LdRelRep.lean) and that of the complex (`Cx`) of
Cb/Gen/Code.lean are the same, up to currying. -/
def rndCurry {A : Type} (R : A → Type) (n : A → ℕ) :
    ((Σ a, R a × Fin (n a)) → E) ≃ (∀ a, R a → Fin (n a) → E) where
  toFun r := fun a i q => r ⟨a, (i, q)⟩
  invFun r := fun n => r n.1 n.2.1 n.2.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem ldr_zk : Spec.ldr_zk F E := by
  intro A _ _ C T R _ _ t hc ht
  classical
  let K : Cx F := ⟨A, fun a => ⟨C a, R a, false⟩⟩
  have hK : (K.enc E).Hides (K.bud E) := cx_hides_core F E K hc
  refine (hides_iff_equiv _ (T.ld E R).Nn ((T.ld E R).budT t)).2 fun S hS m m' => ?_
  obtain ⟨X, hX, hSX⟩ := hS
  have hbud : K.bud E S := fun a => by
    refine le_trans
      (le_trans (Finset.card_le_card (t := X.image (T.pos a)) fun p hp => ?_) Finset.card_image_le)
      (le_trans hX (ht a))
    have hp' : (⟨a, p⟩ : (K.ext E).Pos) ∈ (S : Finset (K.ext E).Pos) :=
      (mem_fibre (E := fun a => (K.comp a).ext E) S a p).1 hp
    obtain ⟨x, hx, hpx⟩ := Finset.mem_biUnion.1 (hSX hp')
    exact Finset.mem_image.2 ⟨x, hx, (Finset.mem_singleton.1 (Finset.mem_sigma.1 hpx).2).symm⟩
  obtain ⟨e, he⟩ := (hides_iff_equiv (K.ext E) (K.enc E) (K.bud E)).1
    hK S hbud (fun a i j => m ⟨a, (i, j)⟩) (fun a i j => m' ⟨a, (i, j)⟩)
  refine ⟨((rndCurry E R fun a => (C a).r).trans e).trans (rndCurry E R fun a => (C a).r).symm,
    fun r p hp => ?_⟩
  have h1 := he (rndCurry E R (fun a => (C a).r) r) p hp
  have h2 := eq_of_heq (Sigma.mk.inj h1).2
  exact congrArg (Sigma.mk p) (funext fun s => congrFun h2 s.1)

end Zk

end Cb
