-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/LinkJKit.lean: rules by which links with keys for the statements of a batch
(`LinkJ`, OnBytes/TypedOracleCompiler/Joined/LinkJ.lean) are made and turned.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.


Main names:
  `LinkJ.conseq`: fewer statements, a larger input relation, a smaller output relation, a finer key
    in front, a coarser key behind.
  `stepAt f`, `LinkJ.step`: a step without a round.
  `LinkJ.pre`: a step in front of a link. The rounds, the annotation and the errors are the link's.
  `postAt K f`, `LinkJ.post`: a step behind a link, likewise.
  `adm_of_view`: under shared verifier messages one key goes to one key if the new key is a function
    of the old and of what all slots see alike of the transcript (`shView`,
    CompileK/Joined/Frame.lean).
  `LinkJ.ofSharedView`: a reduction with the clause `Know`, under shared verifier messages: the
    errors once for each slot; the new key by `adm_of_view`.
  `LinkJ.ofKeyed`: a reduction on keys, carried to statements (`onKey`, Frame.lean), in rounds in
    which only the shared part speaks: THE ERRORS ONCE.
  `adm_of_tr`: where only the shared part speaks the new key may read the whole transcript.
  `LinkJ.ofKeep`: an IOR with the clause `Know`, run once on what the slots share, beside what each
    slot carries (`IOR.keep`): THE ERRORS ONCE. By the library's `knowB_shared_beside` and
    `sameKey_shared` (Ior/KnowBRules.lean).
  `LinkJ.ofInto`: a reduction with the clause `KnowInto` (Ior/KnowColl.lean), in local rounds: every
    statement counts, and the relations are enlarged by the statements outside the conditions.

Limits: rules alone. Nothing here shows a clause of any protocol.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Joined.LinkJ
import CompileK.Joined.Frame
import Ior.KnowColl
import Ior.KnowBRules

set_option autoImplicit false

namespace TypedOracleCompiler.Joined
open _root_.Iop
open _root_.CompileK.Joined (KnowJ AllKind knowJ_sh knowJ_lost onKey extKey lostKey lost_onKey
  back_onKey ShV shView shView_slot)

section Kit
variable {A B C κ κ₂ κ₃ κs WA WB WC : Type} {N : ℕ}

/-! ## Consequence -/

/-- Fewer statements, a larger input relation, a smaller output relation; a finer key in front
(the old key is f of it), a coarser key behind (g of the old). -/
theorem LinkJ.conseq {K : Reduction A B} {An : RoundSplits K.shape} {key : A → κ} {key₂ : B → κ₂}
    {on on' : A → Prop} {RA RA' : A → WA → Prop} {RB RB' : B → WB → Prop}
    {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape}
    (h : LinkJ K An N key key₂ on RA RB ext ε) (keyS : A → κs) (f : κs → κ)
    (hf : ∀ a, key a = f (keyS a)) (g : κ₂ → κ₃) (hon : ∀ a, on' a → on a)
    (hA : ∀ a w, on' a → RA a w → RA' a w) (hB : ∀ b w, RB' b w → RB b w) :
    LinkJ K An N keyS (fun b => g (key₂ b)) on' RA' RB' ext ε := by
  have hk : ∀ a : Fin N → Option A, IOR.SameKey keyS a → IOR.SameKey key a :=
    fun a ha j j' x x' hx hx' => by rw [hf, hf, ha j j' x x' hx hx']
  obtain ⟨⟨bad, c, J⟩, adm⟩ := h
  exact ⟨⟨bad, fun a τ b w ha hτ hb hw => hA a _ ha (c a τ b w (hon a ha) hτ hb (hB b w hw)),
    fun a ha => J a (hk a ha)⟩,
    fun a ha τ j j' b b' hb hb' => congrArg g (adm a (hk a ha) τ j j' b b' hb hb')⟩

/-! ## Steps without a round -/

/-- a step without a round -/
@[reducible] def stepAt (f : A → Option B) : Reduction A B := ⟨[], fun a _ => f a⟩

/-- A step without a round, as a link: back turns a witness behind the step into one before it; the
new key is a function G of the old. -/
theorem LinkJ.step (f : A → Option B) (N : ℕ) (key : A → κ) (key₂ : B → κ₂) (on : A → Prop)
    (RA : A → WA → Prop) (RB : B → WB → Prop) (back : A → WB → WA)
    (h : ∀ a b w, on a → f a = some b → RB b w → RA a (back a w)) (G : κ → κ₂)
    (hG : ∀ a b, f a = some b → key₂ b = G (key a)) :
    LinkJ (stepAt f) PUnit.unit N key key₂ on RA RB (fun a _ w => back a w) () :=
  ⟨⟨fun _ => (), fun a _ b w ha _ hb hw => h a b w ha hb hw, fun _ _ => trivial⟩,
    fun _ ha _ => ldk_sameKey_bind (fun _ aj => f aj) G (fun _ aj b hb => hG aj b hb) ha⟩

/-- A step in front of a link: the rounds, the annotation and the errors are the link's. -/
theorem LinkJ.pre {K : Reduction B C} {An : RoundSplits K.shape} {key₂ : B → κ₂} {key₃ : C → κ₃}
    {on₂ : B → Prop} {RB : B → WB → Prop} {RC : C → WC → Prop} {ext : B → Tr K.shape → WC → WB}
    {ε : Err K.shape} (h : LinkJ K An N key₂ key₃ on₂ RB RC ext ε) (f : A → Option B)
    (key : A → κ) (on : A → Prop) (RA : A → WA → Prop) (back : A → WB → WA)
    (hs : ∀ a b w, on a → f a = some b → RB b w → RA a (back a w)) (G : κ → κ₂)
    (hG : ∀ a b, f a = some b → key₂ b = G (key a)) (hon : ∀ a b, on a → f a = some b → on₂ b)
    (d : WA) :
    LinkJ ((stepAt f).seq K) An N key key₃ on RA RC
      (Reduction.extSeq (stepAt f) K (fun a _ w => back a w) ext d) ε :=
  (LinkJ.step f N key key₂ on RA RB back hs G hG).seq h (fun a _ b ha hb => hon a b ha hb) d

/-- a reduction, then a step without a round, over the reduction's own rounds -/
@[reducible] def postAt (K : Reduction A B) (f : B → Option C) : Reduction A C :=
  ⟨K.shape, fun a τ => (K.out a τ).bind f⟩

/-- A step behind a link: the rounds, the annotation and the errors are the link's. d: a value of
the extractor where the link's verifier rejects. -/
theorem LinkJ.post {K : Reduction A B} {An : RoundSplits K.shape} {key : A → κ} {key₂ : B → κ₂}
    {on : A → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA}
    {ε : Err K.shape} (h : LinkJ K An N key key₂ on RA RB ext ε) (f : B → Option C)
    (key₃ : C → κ₃) (RC : C → WC → Prop) (back : B → WC → WB)
    (hs : ∀ b c w, f b = some c → RC c w → RB b (back b w)) (G : κ₂ → κ₃)
    (hG : ∀ b c, f b = some c → key₃ c = G (key₂ b)) (d : WA) :
    LinkJ (postAt K f) An N key key₃ on RA RC
      (fun a τ w => ((K.out a τ).map fun b => ext a τ (back b w)).getD d) ε := by
  obtain ⟨⟨bad, c, J⟩, adm⟩ := h
  refine ⟨⟨bad, fun a τ x w ha hτ hx hw => ?_, J⟩, fun a ha τ j j' x x' hx hx' => ?_⟩
  · obtain ⟨b, hb, hfb⟩ := Option.bind_eq_some_iff.1 hx
    show RA a (((K.out a τ).map fun b => ext a τ (back b w)).getD d)
    rw [hb]
    exact c a τ b _ ha hτ hb (hs b x w hfb hw)
  · obtain ⟨aj, haj, ho⟩ := Option.bind_eq_some_iff.1 hx
    obtain ⟨aj', haj', ho'⟩ := Option.bind_eq_some_iff.1 hx'
    obtain ⟨b, hb, hfb⟩ := Option.bind_eq_some_iff.1 ho
    obtain ⟨b', hb', hfb'⟩ := Option.bind_eq_some_iff.1 ho'
    rw [hG b x hfb, hG b' x' hfb']
    refine congrArg G (adm a ha τ j j' b b' ?_ ?_)
    · show (a j).bind (fun aj => K.out aj (τ.slot j)) = some b
      rw [haj]
      exact hb
    · show (a j').bind (fun aj => K.out aj (τ.slot j')) = some b'
      rw [haj']
      exact hb'

/-! ## Shared verifier messages -/

/-- Under shared verifier messages one key goes to one key, if the new key is a function of the old
and of what all slots see alike of the transcript. -/
theorem adm_of_view {K : Reduction A B} {An : RoundSplits K.shape} (hAn : AllKind .sh K.shape An)
    {key : A → κ} {key₂ : B → κ₂} (fJ : κ → ShV K.shape An → κ₂)
    (law : ∀ a τ b, K.out a τ = some b → key₂ b = fJ (key a) (shView K.shape An τ))
    (a : Fin N → Option A) (ha : IOR.SameKey key a) (τ : BTr N K.shape An) :
    IOR.SameKey key₂ fun j => (a j).bind fun aj => K.out aj (τ.slot j) := by
  intro j j' b b' hb hb'
  obtain ⟨aj, haj, ho⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨aj', haj', ho'⟩ := Option.bind_eq_some_iff.1 hb'
  rw [law aj _ b ho, law aj' _ b' ho', ha j j' aj aj' haj haj',
    shView_slot K.shape An hAn τ j j']

/-- A reduction with the clause `Know`, under shared verifier messages: the errors once for each
slot; the new key may read what all slots see alike of the transcript. -/
theorem LinkJ.ofSharedView {K : Reduction A B} {An : RoundSplits K.shape}
    (hAn : AllKind .sh K.shape An) (N : ℕ) {key : A → κ} {key₂ : B → κ₂} {on : A → Prop}
    {RA : A → WA → Prop} {RB : B → WB → Prop} {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape}
    (h : K.Know on RA RB ext ε) (fJ : κ → ShV K.shape An → κ₂)
    (law : ∀ a τ b, K.out a τ = some b → key₂ b = fJ (key a) (shView K.shape An τ)) :
    LinkJ K An N key key₂ on RA RB ext (Err.times N ε) :=
  ⟨(knowJ_sh hAn N h).adm fun _ _ => trivial, adm_of_view hAn fJ law⟩

end Kit

/-- **A reduction on keys, carried to statements, in rounds in which only the shared part speaks:
the errors once.** K': the reduction on keys, with the clause `Know`; key, glue: the key of a
statement, and how the output of K' is laid back; hon, split, join: as in
CompileK/Joined/Frame.lean; law: the new key is a function of the old and of what all slots see
alike of the transcript. -/
theorem LinkJ.ofKeyed {AJ A₂ κ κ' κ₂ WJ W₂ Wκ Wκ' : Type} (N : ℕ) {K' : Reduction κ κ'}
    {key : AJ → κ} {glue : AJ → κ' → A₂} {e' : κ → Tr K'.shape → Wκ' → Wκ} {p : W₂ → Wκ'}
    {mk : AJ → W₂ → Wκ → WJ} {on' : κ → Prop} {onJ : AJ → Prop} {Rκ : κ → Wκ → Prop}
    {Rκ' : κ' → Wκ' → Prop} {RJ : AJ → WJ → Prop} {R₂ : A₂ → W₂ → Prop} {ε₂ : Err K'.shape}
    {key₂ : A₂ → κ₂} (know : K'.Know on' Rκ Rκ' e' ε₂) (hon : ∀ a, onJ a → on' (key a))
    (split : ∀ a τ k' w, K'.out (key a) τ = some k' → R₂ (glue a k') w → Rκ' k' (p w))
    (join : ∀ a τ k' w wk, onJ a → K'.out (key a) τ = some k' → R₂ (glue a k') w →
      Rκ (key a) wk → RJ a (mk a w wk))
    (fJ : κ → ShV K'.shape (RoundSplits.const (RAnn.ofShared .sh) K'.shape) → κ₂)
    (law : ∀ a τ b, (onKey K' key glue).out a τ = some b →
      key₂ b = fJ (key a) (shView K'.shape (RoundSplits.const (RAnn.ofShared .sh) K'.shape) τ)) :
    LinkJ (onKey K' key glue) (RoundSplits.const (RAnn.ofShared .sh) K'.shape) N key key₂ onJ RJ R₂
      (extKey K' key e' p mk) ε₂ :=
  ⟨knowJ_lost (onKey K' key glue) N key (lostKey K' e' Rκ Rκ') (lost_onKey know hon)
      (back_onKey split join),
    adm_of_view (K := onKey K' key glue)
      (_root_.CompileK.Joined.allKind_const (fun _ => rfl) K'.shape) fJ law⟩

/-- Where only the shared part speaks, under shared verifier messages, all slots see one transcript
(the library's `slot_shared`): so one key goes to one key if the new key is a function of the old
and of the transcript. -/
theorem adm_of_tr {A B κ κ₂ : Type} {N : ℕ} {K : Reduction A B} {key : A → κ} {key₂ : B → κ₂}
    (g : κ → Tr K.shape → κ₂) (law : ∀ a τ b, K.out a τ = some b → key₂ b = g (key a) τ)
    (a : Fin N → Option A) (ha : IOR.SameKey key a)
    (τ : BTr N K.shape (RoundSplits.const (RAnn.ofShared .sh) K.shape)) :
    IOR.SameKey key₂ fun j => (a j).bind fun aj => K.out aj (τ.slot j) := by
  intro j j' b b' hb hb'
  obtain ⟨aj, haj, ho⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨aj', haj', ho'⟩ := Option.bind_eq_some_iff.1 hb'
  rw [law aj _ b ho, law aj' _ b' ho', ha j j' aj aj' haj haj',
    _root_.Iop.slot_shared N K.shape τ j j']

/-- **An IOR run once on what the slots share, beside what each slot carries: the errors once.** The
key in front is the acting part of a statement; the new key is a function of it and of the
transcript. -/
theorem LinkJ.ofKeep {Xi Xo Z κ₂ : Type} {Ei Eo F : ExtSpec} {Wi Wo Wz : Type}
    (R : IOR Xi Ei Xo Eo) (N : ℕ) {on : Xi × Ei.Str → Prop} {RA : Xi × Ei.Str → Wi → Prop}
    {RB : Xo × Eo.Str → Wo → Prop} {ext : Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (onS : Z × F.Str → Prop) (RS : Z × F.Str → Wz → Prop) (h : R.red.Know on RA RB ext ε)
    {key₂ : (Xo × Z) × (Eo.prod F).Str → κ₂} (g : Xi × Ei.Str → Tr R.shape → κ₂)
    (law : ∀ a τ b, (R.keep Z F).red.out a τ = some b → key₂ b = g (a.1.1, a.2.1) τ) :
    LinkJ (R.keep Z F).red (RoundSplits.const (RAnn.ofShared .sh) R.shape) N
      (fun a : (Xi × Z) × (Ei.prod F).Str => (a.1.1, a.2.1)) key₂
      (fun a => on (a.1.1, a.2.1) ∧ onS (a.1.2, a.2.2))
      (fun a (w : Wi × Wz) => RA (a.1.1, a.2.1) w.1 ∧ RS (a.1.2, a.2.2) w.2)
      (fun b (w : Wo × Wz) => RB (b.1.1, b.2.1) w.1 ∧ RS (b.1.2, b.2.2) w.2)
      (fun a τ w => (ext (a.1.1, a.2.1) τ w.1, w.2)) ε :=
  ⟨knowB_shared_beside Xi Xo Z Ei Eo F Wi Wo Wz R N on RA RB ext ε onS RS h,
    adm_of_tr (K := (R.keep Z F).red) g law⟩

/-- A reduction with the clause `KnowInto`, in local rounds: every statement counts; the relations
are enlarged by the statements outside the conditions. -/
theorem LinkJ.ofInto {A B κ κ₂ WA WB : Type} {K : Reduction A B} {An : RoundSplits K.shape}
    (hAn : AllKind .lo K.shape An) (N : ℕ) {key : A → κ} {key₂ : B → κ₂} {on : A → Prop}
    {on' : B → Prop} {RA : A → WA → Prop} {RB : B → WB → Prop}
    {ext : A → Tr K.shape → WB → WA} {ε : Err K.shape} (h : K.KnowInto on on' RA RB ext ε)
    (G : κ → κ₂) (hG : ∀ a τ b, K.out a τ = some b → key₂ b = G (key a)) :
    LinkJ K An N key key₂ (fun _ => True) (Reduction.orOff on RA) (Reduction.orOff on' RB) ext ε :=
  LinkJ.ofLocal hAn N ((knowInto_iff _ _ _ _ _ _ _ _ _ _ _).1 h) G hG

end TypedOracleCompiler.Joined
