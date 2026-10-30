-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfCloseProofs.lean: proofs of the statements of Cb/Ld/LdWfClose.lean (the end of a
preamble's chain). Nothing is assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.

Why: the last step has no rounds, so shape, positions, budget and what a run shows are the chain's
(Ior/FrameProofs.lean: `IsLocal.post`, `Honest.Exact.post`). Knowledge soundness: on every
transcript the goal of the list's item follows from the goal of the chain's (`Doomed.mono`,
Iop/Rbr.lean): a message m in the relaxed constraint relation, put beside fixed randomness and the
fixed further witness, is a witness of the chain's last joint; a statement with a collision is
outside the last joint's condition.

Limits: what the head of Cb/Ld/LdWfClose.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfClose
import Cb.Ld.LdSigProofs
import Ior.FrameProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

section
variable (E : Type) [Field E]

theorem ldClose_decAll : Spec.ldClose_decAll E := by
  intro S σ y m
  unfold Sig.decAll
  constructor
  · intro h a
    by_cases hs : ∀ a, (S.decs σ y a).isSome
    · rw [dif_pos hs] at h
      rw [← Option.some.inj h]
      exact (Option.some_get (hs a)).symm
    · rw [dif_neg hs] at h
      exact absurd h (by simp)
  · intro h
    have hs : ∀ a, (S.decs σ y a).isSome := fun a => by rw [h a]; rfl
    rw [dif_pos hs]
    exact congrArg some (funext fun a => Option.some.inj ((Option.some_get (hs a)).trans (h a)))

theorem ldClose_rlin : Spec.ldClose_rlin E := by
  intro C S Cl holds x y w
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2, h3, h1, h4⟩
  · rintro ⟨h2, h3, h1, h4⟩
    exact ⟨h1, h2, h3, h4⟩

theorem ldClose_rlinR : Spec.ldClose_rlinR E := by
  intro C S Cl holds x y w
  constructor
  · rintro ⟨U, h1, h2, _, h4⟩
    exact ⟨fun i => (ldClose_decAll E S x.2 y.2 (S.msgs w.1)).1 h2 i, U, h1, h4⟩
  · rintro ⟨h2, U, h1, h4⟩
    exact ⟨U, h1, (ldClose_decAll E S x.2 y.2 (S.msgs w.1)).2 h2,
      fun a => (sig_dec_cand E (S.om a) (y.2 a) (x.2 a) _ (h2 a)).2, h4⟩

theorem ldClose_cond : Spec.ldClose_cond E := by
  intro C S Cl holds x y
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

omit [Field E] in
/-- the last step changes no source -/
theorem closeF_srcE {C : ConfigurationWithOutOfDomainSample} {S : Sig E} {Cl Xi : Type}
    (F : IOR Xi C.E0 ((Cl × C.Rec) × S.Smp) (C.E0.prod S.ext))
    (ρ : Rho F.shape) (q : (C.E0.prod S.ext).Pos) :
    (closeF F).srcE ρ q = F.srcE ρ q := by
  refine Finset.ext fun u => ?_
  unfold closeF IOR.post
  simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton, exists_eq_left]

omit [Field E] in
theorem closeF_srcO {C : ConfigurationWithOutOfDomainSample} {S : Sig E} {Cl Xi : Type}
    (F : IOR Xi C.E0 ((Cl × C.Rec) × S.Smp) (C.E0.prod S.ext))
    (ρ : Rho F.shape) (q : (C.E0.prod S.ext).Pos) :
    (closeF F).srcO ρ q = F.srcO ρ q := by
  refine Finset.ext fun u => ?_
  unfold closeF IOR.post
  simp only [ExtMap.id, Finset.mem_biUnion, Finset.mem_singleton, exists_eq_left]

omit [Field E] in
/-- Where the closed chain outputs a statement, the chain does, and the two differ by the
re-bracketing. -/
theorem closeF_out {C : ConfigurationWithOutOfDomainSample} {S : Sig E} {Cl Xi : Type}
    (F : IOR Xi C.E0 ((Cl × C.Rec) × S.Smp) (C.E0.prod S.ext)) (a : Xi × C.E0.Str) (τ : Tr F.shape)
    (b : ((Cl × S.Smp) × C.Rec) × (C.E0.prod S.ext).Str) (hb : (closeF F).red.out a τ = some b) :
    ∃ x, F.red.out a τ = some (x, b.2) ∧ b.1 = closeX S x := by
  obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
  obtain ⟨x, hx, hx'⟩ := Option.bind_eq_some_iff.1
    (show (F.out a.1 a.2 τ).bind (fun x => some (closeX S x)) = some b.1 from h1)
  exact ⟨x, red_out_eq_some.2 ⟨hx, h2⟩, (Option.some.inj hx').symm⟩

theorem ldClose_know : Spec.ldClose_know E := by
  intro C S Kc Xi Wi Wr Cl Wp holds F on RA B ext ε RiR fr z0 r0 hK hR hon hA a ha
  refine Doomed.mono _ _ ?_ (hK a ha)
  intro τ hτ b m hb hm
  obtain ⟨x, hx, hbx⟩ := closeF_out E F a τ b hb
  refine hA a _ ha (hτ (x, b.2) (S.pair m r0, z0) hx ?_)
  obtain ⟨b1, b2⟩ := b
  subst hbx
  rcases hm with ⟨U, h1, h2, _, h4⟩ | hn
  · exact Or.inl ⟨fun i => (ldClose_decAll E S x.2 b2.2 m).1 h2 i, hR (x.1, b2.1) m U h1 h4⟩
  · exact Or.inr fun h => hn ⟨hon _ h.2, h.1⟩

theorem ldClose_list : Spec.ldClose_list E := by
  intro C S Kc Xi Wi Cl Wp holds F H A B ext P rc px pi g hD hrc hpx hB
  have hrun : ∀ w x c ρ, ((closeH pi H).strat w x c).run ρ =
      (((H.strat w x c).run ρ).1,
        (closeX S ((H.strat w x c).run ρ).2.1, closeW S pi ((H.strat w x c).run ρ).2.2)) :=
    fun w x c ρ => Strat.run_map _ _ _
  exact
    { point := g.point
      isLocal := g.isLocal.post _ _ (extMap_isLocal.1 _)
      acc := by
        intro x y w c ρ hR hρ
        obtain ⟨h1, h2, h3, h4⟩ := g.acc x y w c ρ hR hρ
        rw [hrun]
        refine ⟨?_, ?_⟩
        · show (F.out x y ((H.strat w x c).run ρ).1).bind (fun x => some (closeX S x)) = _
          rw [h1]
          rfl
        · exact ⟨(hB _ _ _ h4).1, h2, h3, (hB _ _ _ h4).2⟩
      prBad := g.prBad
      prHid := fun x _ w _ => le_trans (pr_mono _ (g.cover w x)) (g.prCov _)
      exact := g.exact.post _ _ _
      noReads := hD.noReads
      noTie := hD.noTie
      passes := by
        intro x y τ b hb
        obtain ⟨x', hx, hx'⟩ := Option.bind_eq_some_iff.1
          (show (F.out x y τ).bind (fun x => some (closeX S x)) = some b from hb)
        rw [← Option.some.inj hx']
        exact hrc x y τ x' hx
      hands := by
        intro x y w c ρ hR hρ
        rw [hrun]
        exact hpx x y w c ρ hR hρ
      copy := fun y τ => hD.copy y τ
      srcIdx := fun ρ p =>
        ⟨(closeF_srcE E F ρ _).trans (hD.srcIdx ρ p).1,
          (closeF_srcO E F ρ _).trans (hD.srcIdx ρ p).2⟩
      srcAux := fun ρ q => (closeF_srcE E F ρ _).trans (hD.srcAux ρ q) }

theorem ldClose : Spec.ldClose E := by
  intro C S Kc Xi Wi Wr Cl Wp holds F H A B ext P rc px pi RiR fr z0 r0 g hD hrc hpx hB hR hon hA
  exact ⟨ldClose_list E C S Kc Xi Wi Cl Wp holds F H A B ext P rc px pi g hD hrc hpx hB,
    ldClose_know E C S Kc Xi Wi Wr Cl Wp holds F A.on A.relR B ext P.err RiR
      fr z0 r0 g.know hR hon hA⟩

end
end Cb
