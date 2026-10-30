-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegProofsLoc.lean: proofs for Cb/Req1/LdSeg.lean: under `D.Hyp`, the move "loc" has the
whole bundle (`ldSeg_loc_goodT`). By the block "locations" (Cb/Ld/LdSwitchLoc.lean) at predicates
that do not read the open word, two re-bracketings, and the lemma on kept messages. No new
definition that a reader must agree on (`E'` to `jO` are used in this file's proofs alone).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegProofsFold
import Cb.Ld.LdSwitchLocProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

section
variable {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc)

namespace LdLocD

/-- the carried oracles of the block -/
abbrev E' : ExtSpec := D.E₀.prod D.S.ext
/-- (message, randomness) of the open word, read off a witness -/
def old (w : D.src.W) : (D.C.J → E) × (D.C.Q → E) := D.cut (D.S.msgs w.1)

/-- the old samples' rows on the slots -/
def Rows (x : D.src.X) (w : D.src.W) : Prop :=
  ∀ k, (D.hd.o k).Z.val (x.1.1.2 k).1 (D.hd.msg (D.old w).1 k) = (x.1.1.2 k).2

def ΦiH (x : D.src.X) (y₀ : D.E'.Str) (w : D.src.W) : Prop :=
  D.S.Enc y₀.2 w.1 ∧ D.S.Ans x.2 (D.S.msgs w.1) ∧ D.Φ x.1.1.1 (D.old w).1 ∧
  D.Rows x w ∧ D.A₁.rel x.1.2 y₀.1 (D.S.msgs w.1, w.2)
def ΦiR (x : D.src.X) (y₀ : D.E'.Str) (w : D.src.W) : Prop :=
  (∀ i, D.S.decs x.2 y₀.2 i = some (w.1 i).1) ∧
  D.Φ x.1.1.1 (D.old w).1 ∧
  D.Rows x w ∧
  D.A₁.relR (x.1.2, y₀.1) (D.S.msgs w.1, w.2)
def onI (a : D.src.X × (D.C.ext.prod D.E').Str) : Prop :=
  (D.S.over D.A).on (a.1, ((a.2.1, a.2.2.1), a.2.2.2))

/-- the joints of the block -/
def jI : Rels Kc D.src.X (D.V.Cin.ext.prod D.E') D.src.W :=
  ldLocIn D.V D.old D.e D.ΦiH D.ΦiR D.onI fun w => D.A₁.core (D.S.msgs w.1, w.2)
def jO : Rels Kc D.tgt.X (extNone.prod D.E') D.src.W :=
  ldLocOut D.V (fun x y₀ w => (D.S.over D.tgt.A).rel x y₀ w)
    (fun x y₀ w => (D.S.over D.tgt.A).relR (x, y₀) w)
    (fun b => (D.S.over D.tgt.A).on (b.1, b.2.2)) fun w => D.A₁.core (D.S.msgs w.1, w.2)

theorem block_good (h : D.Hyp) :
    Good (ldLocOf D.V D.E') (ldLocHon D.V D.E' D.old) D.jI D.jO
      (fun _ _ w => w) (ldLocNums D.V Kc D.E' D.e) := by
  refine ldLoc_good E D.P D.src.X D.tgt.X D.V D.E' D.src.W Kc D.old _ D.e D.ΦiH
    D.ΦiR _ _ D.onI _ ?_ ?_ ?_ ?_
  · rintro x Qs v y₀ w ⟨hd, ⟨hΦ, hr, hv⟩, hA⟩
    exact ⟨⟨hd, hΦ, hr, hA⟩, hv⟩
  · intro a _ w w' hw hw'
    have : D.S.msgs w.1 = D.S.msgs w'.1 :=
      funext fun i => Option.some.inj ((hw.1 i).symm.trans (hw'.1 i))
    show D.cut _ = D.cut _
    rw [this]
  · rintro x y₀ w Qs ⟨hE, hA, hΦ, hr, hA₁⟩
    exact ⟨hE, hA, ⟨hΦ, hr, rfl⟩, hA₁⟩
  · intro a Qs ha
    exact ⟨ha.1, ((h.near.on _).1 ha.2).2⟩

theorem inE_isLocal : D.inE.IsLocal := by
  obtain ⟨-, hfs, -, hcomp, hpair⟩ := extMap_isLocal
  exact hpair _ _ _ _ _ (hcomp _ _ _ _ _ (hfs _ _).1 (hfs _ _).1)
    (hpair _ _ _ _ _ (hcomp _ _ _ _ _ (hfs _ _).2 (hfs _ _).1) (hfs _ _).2)

theorem stepIn (h : D.Hyp) :
    StepT (fun x : D.src.X => some x) D.inE (fun p : D.src.X × D.src.W => p) (fun _ w => w)
      (D.S.over D.A) D.jI where
  isLocal := D.inE_isLocal
  acc := by
    rintro x y w ⟨hE, hA, hr⟩
    obtain ⟨hc, hrow, hA₁⟩ := (h.near.rel _ _ _).1 hr
    exact ⟨rfl, hc.1, hE, hA, hc.2, hrow, hA₁⟩
  onOut := by
    intro x y x' ha hx
    cases hx
    exact ha
  keeps := fun _ w => (h.near.core _).symm
  know := by
    rintro x y x' w' ha hx ⟨hn, hd, hΦ, hrow, hA₁⟩
    cases hx
    refine ⟨hd, (h.near.relR _ _).2 ⟨⟨hn, hΦ⟩, fun k => ?_, hA₁⟩⟩
    exact ldSeg_kept E D.P D.C D.e D.hd h.laws y.1.1 (D.old w') k (x.1.1.2 k)
      (((h.near.on _).1 ha.2).1 k) hn (hrow k)

theorem stepOut :
    StepT (fun x : D.tgt.X => some x) D.outE (fun p : D.tgt.X × D.src.W => p) (fun _ w => w)
      D.jO (D.S.over D.tgt.A) where
  isLocal := (extMap_isLocal.2.1 _ _).2
  acc := fun _ _ _ hr => ⟨rfl, hr⟩
  onOut := by
    intro x y x' ha hx
    cases hx
    exact ha
  keeps := fun _ _ => rfl
  know := by
    intro x y x' w' _ hx hw
    cases hx
    exact hw

end LdLocD

/-- Under `h`: the move "loc" has the whole bundle. -/
theorem ldSeg_loc_goodT (h : D.Hyp) : D.link.GoodT := by
  have g := goodT_of_good _ _ _ _ _ _ _ _ _ _ _ _ _ (D.block_good h)
  have gB := ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).1 g).1
  have g₁ := goodB_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ w => w) _ _ _ _ _ (D.stepIn h)
    gB (fun _ _ _ _ _ => rfl)
  have g₂ := goodB_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ w => w)
    _ _ _ _ _ g₁ D.stepOut (fun _ _ _ _ _ => rfl)
  have e₁ := exact_pre _ _ _ _ _ _ _ _ _ _ _ _ (D.S.over D.A).rel _ _ _
    (fun p : D.src.X × D.src.W => p) D.inE_isLocal (D.stepIn h).acc g.exact
  have e₂ := exact_post _ _ _ _ _ _ _ _ _ _ _ _ _ (fun x : D.tgt.X => some x) D.outE
    (fun p : D.tgt.X × D.src.W => p) e₁
  exact goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _ ((goodT_iff _ _ _ _ _ _ _ _ _ _ _ _ _).2 ⟨g₂, e₂⟩)

end
end Cb
