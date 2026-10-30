-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfIdxProofs.lean: proofs of the statements of Cb/Ld/LdWfIdx.lean (the index-lifting rule).
Nothing is assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs.

Why: the block copies the index and keeps the record (the hypotheses `himp`, `hrc`), so the decoding
of the index is the same at both ends. If it is none, no output statement has a witness in the
relaxed relation, and nothing is to be shown; if it is U, knowledge soundness at the tuple (U, m) is
what is asked. The rest is re-typing (Ior/KnowCollRulesFrame.lean: `mapW`; Ior/MaskedFrame.lean,
Ior/MaskedMap.lean for the item "masked messages"), and the lifting rule of Cb/Ld/LdSigLift.lean on
top.

Main names (statements and hypotheses: Cb/Ld/LdWfIdx.lean):
  `idxLift_goodAt`: the index-lifting rule: a block R whose oracles are the index alone, which
    copies the index and keeps the record: `GoodAt` for tuples (U, m) gives `GoodAt` for tuples m,
    between `idxAt C rc A` and `idxAt C rc' B`. Same numbers.
    (not all hypotheses are named here: see its statement)
  `idxLift_goodB`: over a signature.
  `idxLift_mm`: see its statement in Cb/Ld/LdWfIdx.lean.
  `idxLift_goodM`: see its statement in Cb/Ld/LdWfIdx.lean.
  `idxAt_pred`: the base joint of a predicate (Cb/Ld/LdWfClose.lean: `idxRels`) is a case, up to the
    empty further witness.

Limits: what the head of Cb/Ld/LdWfIdx.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfIdx
import Cb.Ld.LdSigLiftProofs
import Ior.FrameProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

theorem idxLift_goodAt : Spec.idxLift_goodAt := by
  intro C K X X' M Wp Wp' R H A B rc rc' ext P hrc himp g
  have hrun : ∀ w x c ρ, ((idxH C H).strat w x c).run ρ =
      (((H.strat (idxIn C w) x c).run ρ).1,
        (((H.strat (idxIn C w) x c).run ρ).2.1,
          (w.1, (w.2.1, ((H.strat (idxIn C w) x c).run ρ).2.2.2)))) :=
    fun w x c ρ => Strat.run_map _ _ _
  have hsame : ∀ (w : M × (C.PIdx × Wp)) x c ρ, ((H.strat (idxIn C w) x c).run ρ).2.2 =
      ((w.2.1.1.1, w.1), ((H.strat (idxIn C w) x c).run ρ).2.2.2) :=
    fun w x c ρ => Prod.ext (g.same _ x c ρ) rfl
  exact
    { point := g.point
      isLocal := g.isLocal
      acc := by
        intro x y w c ρ hR hρ
        obtain ⟨h1, h2⟩ := g.acc x y (idxIn C w) c ρ hR.2 hρ
        rw [hrun]
        refine ⟨h1, ?_, ?_⟩
        · show C.Enc (rc' _) (R.imp y _) w.2.1
          rw [hrc x y _ _ h1, himp]
          exact hR.1
        · show B.rel _ _ ((w.2.1.1.1, w.1), _)
          rw [← hsame]
          exact h2
      onOut := by
        intro a τ b ha hb
        obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
        refine ⟨?_, g.onOut a τ b ha.2 hb⟩
        rw [h2, himp, hrc _ _ _ _ h1]
        exact ha.1
      keeps := by
        intro w x c ρ
        rw [hrun]
        show B.core ((w.2.1.1.1, w.1), _) = A.core (idxIn C w)
        rw [← hsame]
        exact g.keeps _ x c ρ
      prBad := g.prBad
      cover := fun w x => g.cover (idxIn C w) x
      prCov := g.prCov
      same := fun w x c ρ => by rw [hrun]
      know := by
        intro m a ha
        cases hd : C.dcd a.2 (rc a.1) with
        | none =>
          refine Doomed.of_forall _ _ fun τ b w hb hw => ?_
          obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
          obtain ⟨U, hU, _⟩ := hw
          rw [h2, himp, hrc _ _ _ _ h1, hd] at hU
          exact absurd hU (by simp)
        | some U =>
          refine Doomed.mono _ _ ?_ (g.know (U, m) a ha.2)
          intro τ hτ b w hb hw
          obtain ⟨h1, h2⟩ := red_out_eq_some.1 hb
          obtain ⟨U', hU', hB⟩ := hw
          rw [h2, himp, hrc _ _ _ _ h1, hd] at hU'
          have e : U = U' := Option.some.inj hU'
          subst e
          exact ⟨U, hd, hτ b w.2 hb hB⟩ }

theorem idxLift_goodB : Spec.idxLift_goodB := by
  intro E _ C S K X X' Wp Wp' R H A B rc rc' ext P hrc himp g
  exact sigLift_goodB E S K X X' (C.PIdx × Wp) (C.PIdx × Wp') C.E0 C.E0 R (idxH C H) (idxAt C rc A)
    (idxAt C rc' B) (idxExt C ext) P
    (idxLift_goodAt C K X X' S.Msg Wp Wp' R H A B rc rc' ext P hrc himp g)

theorem idxLift_mm : Spec.idxLift_mm := by
  intro E C S X X' Wp Wp' R H D h
  exact mm_mapW _ _ _ _ _ _ _ _ _ ((idxH C H).keep S.Smp S.ext)
    ((D.mapW (idxIn C)).keep S.Smp S.ext) (fun w : S.Wit × (C.PIdx × Wp) => (S.msgs w.1, w.2))
    (fun (w : S.Wit × (C.PIdx × Wp)) (o : S.Msg × (C.PIdx × Wp')) => (w.1, o.2))
    (mm_keep _ _ _ _ _ _ _ (idxH C H) (D.mapW (idxIn C)) S.Smp S.ext
      (mm_mapW _ _ _ _ _ _ _ _ _ H D (idxIn C) _ h))

theorem idxLift_goodM : Spec.idxLift_goodM := by
  intro E _ C S K X X' Wp Wp' R H A B rc rc' ext P D hrc himp g hm hcl
  exact ⟨idxLift_goodB E C S K X X' Wp Wp' R H A B rc rc' ext P hrc himp g,
    idxLift_mm E C S X X' Wp Wp' R H D hm,
    fun x y w h => hcl _ _ _ h.2.2.2⟩

theorem idxAt_pred : Spec.idxAt_pred := by
  intro C St M P PR x y m p A
  exact ⟨Iff.rfl, Iff.rfl, ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩⟩

end Cb
