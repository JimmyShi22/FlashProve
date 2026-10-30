-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/CarriedSizes.lean: FIVE PLAIN
FACTS ON THE ROWS THAT A LINK's CLOSING (kind K10) LAYS INTO THE FRAME, OFF THE CLOSING's OWN YES
AND THE TEXT OF `foldOutput` (OnBytes/Iop/Fold.lean): two masks · as many challenges as the plan's k
· the layout's k and h are the plan's · the message that is named as the fresh mask has 2 ^ h mask
rows. They are five of the clauses that the premise on the carried claim asks of a front (masks,
gamma, expK, expH, freshRows). After Johnson/Desc/First/Close/Law/CarriedRows.lean,
which has four other facts by the same road. Theorems. A law file; no running text imports it.
  `closing_sizes`      closing P S g mask rs = .ok (out, S') ⊢ out.masks = 2 ∧ out.gamma.length =
                    P.k ∧ out.layout.k = P.k ∧ out.layout.h = P.h ∧ the message at out.fresh IN
                    THE STATEMENT BEHIND, S', has 2 ^ P.h mask rows.
  `closeFrame_sizes`   the like at a yes of the frame's closing of a link, of x.1.rows: the rows
                    that the frame behind carries; k and h are those of the frame's group of the
                    link.
  `stage_sum`, `stage_h`   the library's stage at a planner's group: h + g = k where h ≤ k; h = h.
  `sizes_at_stage`     so, in the letters of the premise: where the frame's group has the k and
                    the h of a planner's group gs with gs.h ≤ gs.k: masks = 2 · gamma.length = s.h +
                    s.g · layout.k = s.h + s.g · layout.h = s.h, s := stageOf gs t.

Limits. THE STATE RIGHT BEHIND THE CLOSING ALONE. That the frame's group's k and h are gs's is a
premise. The fresh mask's shape is said at the statement right behind the closing (S'; x.2): that it
is the same at a later state is not said (the statement only grows: other files' law). Nothing on
soundness or on hiding.
-/
import Johnson.Desc.First.Close.Law.CarriedRows
import Johnson.Top.H.StageJ
import Johnson.Goal.Meaning.GrowsSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params Johnson.Top.H
open VerifiableInference.Desc.First.Close (Plan closing closeFrame closing_iff closeFrame_iff
  fold_iff fold_inv2)

/-- The five, at a yes of the closing. -/
theorem closing_sizes {P : Plan} {S S' : Statement} {g : ℕ} {mask : Option ℕ} {rs : List Fmt.RoundView}
    {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    out.masks = 2 ∧ out.gamma.length = P.k ∧ out.layout.k = P.k ∧ out.layout.h = P.h ∧
      ∃ o : OnBytes.Oracle, S'.oracles[out.fresh]? = some o ∧ o.shape.maskRows = 2 ^ P.h := by
  obtain ⟨eB, es, rB, rs', -, -, m, -, row, L, S1, -, -, hF⟩ :=
    (closing_iff P S g mask rs out S').1 h
  have hfold := (fold_iff _ _ _ _ _ _ _ _).2 hF
  obtain ⟨-, -, -, -, -, -, -, -, -, hmask, -⟩ := hF
  obtain ⟨rE, rR, sum, eps, qs, gs, S2, -, -, -, -, b5, -, -, -, b9⟩ := fold_inv2 hfold
  subst b9
  obtain ⟨o, ho, -, hr, -⟩ := (Own.foldMaskFits_iff _ _ _).1 hmask
  obtain ⟨o', ho', hg, -⟩ := (Meaning.K2.fold_grows hfold).2.2 m o ho
  exact ⟨rfl, b5, rfl, rfl, o', ho', by rw [hg]; exact hr⟩

/-- **At a yes of the frame's closing of a link.** -/
theorem closeFrame_sizes {owed : Option ℕ} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f S es rs = .ok x) :
    ∃ Gf : ReqGroup, f.groups[f.link]? = some Gf ∧ x.1.rows.masks = 2 ∧
      x.1.rows.gamma.length = Gf.k ∧ x.1.rows.layout.k = Gf.k ∧ x.1.rows.layout.h = Gf.h ∧
      ∃ o : OnBytes.Oracle, x.2.oracles[x.1.rows.fresh]? = some o ∧
        o.shape.maskRows = 2 ^ Gf.h := by
  obtain ⟨-, Lk, -, Gf, hGf, -, rows, hc, e⟩ := (closeFrame_iff owed f S es rs x.1 x.2).1 h
  have hs := closing_sizes ((closing_iff _ _ _ _ _ _ _).2 hc)
  rw [e]
  exact ⟨Gf, hGf, hs⟩

theorem stage_sum (gs : GroupSize) (t : ℕ) (h : gs.h ≤ gs.k) :
    (stageOf gs t).h + (stageOf gs t).g = gs.k := by
  show gs.h + (gs.k - gs.h) = gs.k
  omega

theorem stage_h (gs : GroupSize) (t : ℕ) : (stageOf gs t).h = gs.h := rfl

/-- **In the letters of the premise on the carried claim.** -/
theorem sizes_at_stage {owed : Option ℕ} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f S es rs = .ok x)
    (gs : GroupSize) (t : ℕ) (hle : gs.h ≤ gs.k)
    (hg : ∀ Gf, f.groups[f.link]? = some Gf → Gf.k = gs.k ∧ Gf.h = gs.h) :
    x.1.rows.masks = 2 ∧ x.1.rows.gamma.length = (stageOf gs t).h + (stageOf gs t).g ∧
      x.1.rows.layout.k = (stageOf gs t).h + (stageOf gs t).g ∧
      x.1.rows.layout.h = (stageOf gs t).h ∧
      ∃ o : OnBytes.Oracle, x.2.oracles[x.1.rows.fresh]? = some o ∧
        o.shape.maskRows = 2 ^ (stageOf gs t).h := by
  obtain ⟨Gf, hGf, h1, h2, h3, h4, o, ho, h5⟩ := closeFrame_sizes h
  obtain ⟨ek, eh⟩ := hg Gf hGf
  rw [stage_sum gs t hle, stage_h]
  exact ⟨h1, h2.trans ek, h3.trans ek, h4.trans eh, o, ho, by rw [h5, eh]⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.closing_sizes
#print axioms VerifiableInference.Desc.LinkJoin.closeFrame_sizes
#print axioms VerifiableInference.Desc.LinkJoin.stage_sum
#print axioms VerifiableInference.Desc.LinkJoin.sizes_at_stage
