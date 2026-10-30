-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointGame.lean: THE SHARED POINT OF THE TEST ON THE STORED TABLE, IN THE GAME's
FORM, IN TWO PARTS: the library's typed reduction `LdLinP.pt` (Cb/Ld/LdLin.lean) has the plain law
for a batch (`Reduction.LeadsB`, `LeadsBN`, Johnson/Desc/Plain/Both.lean) WITH THE PROMISE KEPT. Two
theorems.

What is said. `pt_leadsB`: under `FoldErr`, at the key k1 (the encoded index and its record), on the
statements with the typed condition of j1: two games:
  the key's: "the point's γ is not bad for the fold of the table": lost at εf · q^klo: ONCE;
  a slot's own: "the point is not bad for this slot's (g, w)": lost at (v + klo) · q^(v + klo - 1):
    the Schwartz-Zippel count for ONE instance: N TIMES;
where both hold: the typed condition of j2 holds behind, and every witness of j2 behind gives one of
j1 in front (its second part). `pt_leadsBN`: so at the library's own number `errPtB εf N`, for every
N.

NOTHING IS PROVED ANEW: the games, their counts and the step back are
Johnson/Desc/Sound/FoldSlotsAtPoint.lean's (`lostPtK_doomed`, `lostPtO_doomed`, `pt_back_both`),
which call the library's `cnt_fst`, `ldLin_cnt_pt`, `pt_back`. The key's game is guarded already
("where the table has at most εf bad points"): so it is lost AT EVERY KEY, as `LeadsB` asks.

Every "there is", walked. `LeadsB`'s two games: named here. None else.
Limits. On typed rounds: no block of a description. `FoldErr` is a premise. It would stay proved if
the protocol were otherwise: it closes no row.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldSlotsAtPoint
import Johnson.Desc.Plain.Both

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob IOR

section
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)

omit [Nonempty ι] in
/-- **The shared point, in two parts, with the promise kept.** -/
theorem LdLinP.pt_leadsB (εf : ℕ) (hF : P.FoldErr on0 εf) :
    P.pt.red.LeadsB P.k1 (P.j1 on0).on
      (fun a b => (P.j2 on0).on b ∧ ∀ w', (P.j2 on0).relR b w' → (P.j1 on0).relR a w'.2)
      ((εf * Fintype.card E ^ P.D.klo, ()) : ℕ × Unit)
      (((P.D.X.v + P.D.klo) * Fintype.card E ^ (P.D.X.v + P.D.klo - 1), ()) : ℕ × Unit) := by
  refine ⟨P.lostPtK εf, P.lostPtO, P.lostPtK_doomed εf, fun a _ => P.lostPtO_doomed a,
    fun a τ b ha hk ho hb => ⟨?_, fun w' hw' => ?_⟩⟩
  · obtain rfl : _ = b := Option.some.inj ((ldk_peek_out P.vPt a τ).symm.trans hb)
    exact ha
  · exact (P.pt_back_both on0 εf hF a τ b w' hk ho hb (Or.inl hw')).elim id fun n => absurd ha n

omit [Nonempty ι] in
/-- **At the library's own number for N instances.** -/
theorem LdLinP.pt_leadsBN (εf N : ℕ) (hF : P.FoldErr on0 εf) :
    P.pt.red.LeadsBN P.k1 (P.j1 on0).on
      (fun a b => (P.j2 on0).on b ∧ ∀ w', (P.j2 on0).relR b w' → (P.j1 on0).relR a w'.2) N
      ((P.errPtB εf N, ()) : ℕ × Unit) :=
  ⟨_, _, ⟨Nat.le_refl _, trivial⟩, P.pt_leadsB on0 εf hF⟩

end
end Cb

#print axioms Cb.LdLinP.pt_leadsB
#print axioms Cb.LdLinP.pt_leadsBN
