-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/Arrows.lean: how a statement on a reduction reaches the property of a bare block
(`KObj.BK.Good`, Johnson/E/KObj/Blocks.lean).

Knowledge soundness is kept apart from the three facts on the verifier alone (point queries, local,
what it leaves meets the next condition). Definitions and proofs. No library file turns.
Main names:
  `BK.good_of`: the four apart give the property.
  `jOver`, `BK.ofSig`, `good_ofSig`: a block stated at the base, for each fixed tuple of committed
    messages, is lifted over a signature at the same errors (`sigLift_know`,
    Cb/Ld/LdSigLiftProofs.lean).
  `good_ofGoodAt`, `jOf`, `good_ofGoodB`: the library's bundles `GoodAt` and `IOR.GoodB` give a
    block; four of their fields are read.
  `LK.fam`, `LK.each_fam`: a family of blocks in a row; every block of it ⇔ each index.
Limits: nothing here says that a reduction has any of the four.

-/
import Johnson.E.KObj.Blocks
import Cb.Ld.LdSigLiftProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Cb IOR

/-- (A1) «know» alone is the hole; the other three stand beside it -/
theorem BK.good_of {A B : JK} (b : BK A B) (point : Nonempty b.R.shape.IsPoint)
    (isLocal : b.R.IsLocal) (onOut : ∀ a τ x, b.R.red.out a τ = some x → A.on a → B.on x)
    (know : b.R.red.Know A.on A.relR B.relR b.ext b.err) : b.Good :=
  ⟨point, isLocal, knowInto_of_carry _ _ _ _ _ _ _ _ _ _ _ onOut know⟩

/-! ### (A2) over a signature -/

section
variable {E : Type} [Field E] (S : Sig E) {Kc St St' Wp Wp' : Type} {E₀ E₀' : ExtSpec}

/-- the joint over the oracle messages of S, the verifier's side alone -/
@[reducible] def jOver (A : IOR.Rels Kc St E₀ (S.Msg × Wp)) : JK :=
  ⟨St × S.Smp, E₀.prod S.ext, S.Wit × Wp, (S.over A).on, (S.over A).relR⟩

/-- a block at the base, lifted over the signature -/
@[reducible] noncomputable def BK.ofSig (R : IOR St E₀ St' E₀') (A : IOR.Rels Kc St E₀ (S.Msg × Wp))
    (B : IOR.Rels Kc St' E₀' (S.Msg × Wp'))
    (ext : S.Msg → St × E₀.Str → Tr R.shape → Wp' → Wp) (ε : Err R.shape) :
    BK (jOver S A) (jOver S B) where
  R := R.keep S.Smp S.ext
  ext := fun a τ w => (w.1, ext (S.msgs w.1) (a.1.1, a.2.1) τ w.2)
  err := ε

end

section
variable {E : Type} [Field E] (S : Sig E) {Kc St St' Wp Wp' : Type} {E₀ E₀' : ExtSpec}

/-- (A2) -/
theorem good_ofSig (R : IOR St E₀ St' E₀') (A : IOR.Rels Kc St E₀ (S.Msg × Wp))
    (B : IOR.Rels Kc St' E₀' (S.Msg × Wp')) (ext : S.Msg → St × E₀.Str → Tr R.shape → Wp' → Wp)
    (ε : Err R.shape) (point : Nonempty R.shape.IsPoint) (isLocal : R.IsLocal)
    (onOut : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b)
    (know : ∀ m, R.red.Know A.on (fun a wp => A.relR a (m, wp)) (fun b wp => B.relR b (m, wp))
      (ext m) ε) : (BK.ofSig S R A B ext ε).Good :=
  BK.good_of _ point (IsLocal.keepE S.ext (isLocal_keepX isLocal S.Smp))
    (fun a τ b hb ha => by
      obtain ⟨h1, h2, h3⟩ := keep_red_out R S.Smp S.ext a τ b hb
      refine ⟨?_, onOut _ τ _ ha.2 h3⟩
      rw [h1, h2]
      exact ha.1)
    (sigLift_know E S Kc St St' Wp Wp' E₀ E₀' R A B ext ε know)

/-- the library's bundle at the base gives a block of the spine: four of its ten fields are read -/
theorem good_ofGoodAt (R : IOR St E₀ St' E₀') (H : R.Honest (S.Msg × Wp) (S.Msg × Wp'))
    (A : IOR.Rels Kc St E₀ (S.Msg × Wp)) (B : IOR.Rels Kc St' E₀' (S.Msg × Wp'))
    (ext : S.Msg → St × E₀.Str → Tr R.shape → Wp' → Wp) (P : IOR.Nums Kc R)
    (g : GoodAt R H A B ext P) : (BK.ofSig S R A B ext P.err).Good :=
  good_ofSig S R A B ext P.err g.point g.isLocal g.onOut g.know

end

/-- any link's four verifier-side facts between two joints give a block: from the library's GoodB -/
@[reducible] def jOf {K X : Type} {E : ExtSpec} {W : Type} (A : IOR.Rels K X E W) : JK :=
  ⟨X, E, W, A.on, A.relR⟩

theorem good_ofGoodB {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} (R : IOR Xi Ei Xo Eo)
    (H : R.Honest Wi Wo) (A : IOR.Rels K Xi Ei Wi) (B : IOR.Rels K Xo Eo Wo)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (P : IOR.Nums K R) (g : IOR.GoodB R H A B ext P) :
    (⟨R, ext, P.err⟩ : BK (jOf A) (jOf B)).Good :=
  BK.good_of _ g.point g.isLocal (fun a τ b hb ha => g.onOut a τ b ha hb) g.know

/-! ### (A3) a family in a row -/

/-- the blocks b 0, …, b n in a row -/
def LK.fam (J : ℕ → JK) (b : ∀ i, BK (J i) (J (i + 1))) : ∀ n, LK (J 0) (J (n + 1))
  | 0 => .one (b 0)
  | n + 1 => .snoc (LK.fam J b n) (b (n + 1))

theorem LK.each_fam (Q : ∀ A B : JK, BK A B → Prop) (J : ℕ → JK) (b : ∀ i, BK (J i) (J (i + 1))) :
    ∀ n, (LK.fam J b n).Each Q ↔ ∀ i ≤ n, Q _ _ (b i) := by
  intro n
  induction n with
  | zero =>
    rw [LK.fam, LK.each_one]
    exact ⟨fun h i hi => by rw [Nat.le_zero.1 hi]; exact h, fun h => h 0 le_rfl⟩
  | succ n ih =>
    rw [LK.fam, LK.each_snoc, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · exact h1 i (Nat.lt_succ_iff.1 h)
      · rw [Nat.le_antisymm hi h]
        exact h2
    · exact fun h => ⟨fun i hi => h i (Nat.le_succ_of_le hi), h (n + 1) le_rfl⟩

#print axioms KObj.BK.good_of
#print axioms KObj.good_ofSig
#print axioms KObj.good_ofGoodAt
#print axioms KObj.good_ofGoodB
#print axioms KObj.LK.each_fam

end KObj
