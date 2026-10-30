-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinProofs.lean: the proofs of the statements of Cb/Ld/LdLin.lean on its own blocks: step0,
the shared point, the locations, ζ; the rounds; the two regimes. The chain is in
Cb/Ld/LdLinProofsChain.lean. Cb/Ld/LdLin.lean has the test for linear constraints on the encoded
index, beyond unique decoding, as a chain of interactive oracle reductions.

Each round without a prover message is `IOR.peek` (Cb/Ld/LdLinKit.lean: `piece_peek`); what is
shown here is its six hypotheses: local, forward, conditions, cores, the count of bad values,
positions. The counts are those of Cb/Ld/LdLinWordsProofs.lean and Cb/Ld/LdFoldEqProofs.lean.

Main names (statements and hypotheses: Cb/Ld/LdLin.lean):
  `ldLin_shape`: the rounds: those of the blocks, in a row.
  `ldLin_step0`, `ldLin_pt`, `ldLin_loc`, `ldLin_zeta`: the four own blocks, each as a piece of a
    chain.
  `ldLin_foldErr`, `ldLin_foldErr_far`: `P.FoldErr` in the first and in the second regime.
  `ldLin_loc_far`: the error of the locations in the second regime, at the largest radius allowed.
-/
import Cb.Ld.LdLin
import Cb.Ld.LdLinWordsProofs
import Ior.FrameProofsBasic

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype κ] [Fintype J] [Fintype Y] in
theorem ldLin_shape : Spec.ldLin_shape E ι κ J Y := fun _ _ => rfl

open Classical in
/-- sources under the identity -/
theorem ldk_biUnion_id {Ex : ExtSpec} (U : Finset Ex.Pos) : U.biUnion (ExtMap.id Ex).src = U := by
  ext p
  simp [ExtMap.id]

/-- nothing is read and the oracles are copied: what is needed is what follows needs -/
theorem ldk_eq_of_mem_id {Ex : ExtSpec} {U S : Finset Ex.Pos}
    (h : ∀ p, p ∈ S ↔ p ∈ (∅ : Finset Ex.Pos) ∨ ∃ u ∈ U, p ∈ (ExtMap.id Ex).src u) : S = U := by
  ext p
  rw [h p]
  constructor
  · rintro (h | ⟨u, hu, hp⟩)
    · exact absurd h (Finset.notMem_empty _)
    · rw [Finset.mem_singleton.1 hp]
      exact hu
  · exact fun hp => Or.inr ⟨p, hp, Finset.mem_singleton_self p⟩

omit [Fintype E] [Nonempty ι] in
theorem ldLin_step0 : Spec.ldLin_step0 E ι κ J Y := by
  classical
  intro P on0 q
  refine pieceTr_pure Unit P.X0 P.X0 P.E0 P.E0 P.W0 P.WA (P.j0 on0) (P.jA on0) some (ExtMap.id _) _
    (fun _ w => w.2) q q ?_ ?_
  · exact
      { isLocal := extMap_isLocal.1 _
        acc := fun x y w h => ⟨rfl, h, rfl⟩
        onOut := fun x y x' h hx => by
          obtain rfl := Option.some.inj hx
          exact h
        keeps := fun _ _ => rfl
        know := fun x y x' w' _ hx h => by
          obtain rfl := Option.some.inj hx
          exact h }
  · intro U hU
    rw [ldk_biUnion_id]
    exact hU

/-- what a family decodes to is determined by samples and words -/
theorem Sig.DecTo.unique {E : Type} [Field E] {N : Sig E} {σ : N.Smp} {y : N.ext.Str} {m m' : N.Msg}
    (h : N.DecTo σ y m) (h' : N.DecTo σ y m') : m = m' :=
  funext fun i => Option.some.inj ((h i).symm.trans (h' i))

/-! ### The shared point -/

omit [Fintype E] [Nonempty ι] in
/-- the backward step over the shared point, on vectors -/
theorem LdLinP.pt_back (P : LdLinP E ι κ J Y) (x : P.X0) (f : P.D.X.Row → ι → E) (wa : P.Wa)
    (w : P.D.Col → E) (ψs : P.D.Pt) (u : κ → E)
    (hbad : ¬ P.D.BadSh (N := 1) f x.2 P.e' (fun _ => some (P.g x.1, w)) ψs)
    (hev : P.Ev x wa w) (hn : P.D.X.NearW P.e' (foldAll ψs.1 f) u)
    (hr : P.D.X.RecRow x.2 ψs.1 u) (hd : P.DotU x ψs u w) :
    ∃ U, P.D.X.dec f x.2 = some U ∧ P.Cl x wa U := by
  have hw : ¬ P.D.X.Wrong f x.2 ψs.1 u := fun h => hbad (Or.inl ⟨u, hn, hr, h⟩)
  unfold LdIx.Wrong at hw
  push Not at hw
  obtain ⟨U, hU, hmsg⟩ := hw
  refine ⟨U, hU, ?_⟩
  have hww : w = P.D.wOf U (P.g x.1) := by
    by_contra hne
    refine hbad (Or.inr ⟨U, hU, 0, _, rfl, hne, ?_⟩)
    rw [← P.D.dot_honest U (P.g x.1) ψs, ldLin_om_fold P.D U ψs, ← hmsg]
    exact hd.symm
  rw [hww] at hev
  exact (ldLin_eval_iff P.D U (P.g x.1) (P.ψ x.1) _ _).1 hev

omit [Nonempty ι] in
theorem ldLin_pt : Spec.ldLin_pt E ι κ J Y := by
  classical
  intro P on0 εf q hF
  refine piece_peek Unit P.X1 P.X2 P.E1 P.E1 P.W1 P.W2 P.vPt _ _ (fun _ _ w => w.2) (P.j1 on0)
    (P.j2 on0) (P.errPt εf) q q (extMap_isLocal.1 _) ?_ ?_ ?_ ?_ ?_
  · exact fun x y w c h => ⟨rfl, h, rfl⟩
  · exact fun x y c h => h
  · exact fun _ _ _ => rfl
  · intro x y hon
    have hf : cnt (P.D.X.Bad (P.tab y.1.1) x.1.2 P.e') ≤ εf := hF _ _ hon.2.1
    by_cases hdec : ∃ m, P.NW.DecTo x.2 y.2 m
    swap
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro c ⟨w', h, -⟩
        exact hdec ⟨_, h.1⟩
    · obtain ⟨m, hm⟩ := hdec
      have h1 :=
        ldk_cnt_badSh P.D (N := 1) (P.tab y.1.1) x.1.2 (fun _ => some (P.g x.1.1, P.wv m)) hf
      rw [Nat.one_mul] at h1
      refine le_trans (cnt_mono fun c hc => ?_) h1
      obtain ⟨w', ⟨hd, haa, hev, hn, hr, hdot⟩, hnot⟩ := hc
      obtain rfl : m = P.NW.msgs w'.2.1 := hm.unique hd
      by_contra hbad
      exact hnot ⟨hd, haa, P.pt_back x.1 (P.tab y.1.1) w'.2.2.2 _ c w'.1 hbad hev hn hr hdot⟩
  · intro c U S hU hS
    rw [ldk_eq_of_mem_id hS]
    exact hU


/-! ### The locations -/

omit [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem LdLinP.dropIx_local (P : LdLinP E ι κ J Y) : P.dropIx.IsLocal := by
  intro y y' q h
  rcases q with (p | p) | p
  · have h1 := h (.inl (.inl (.inr p))) (Finset.mem_singleton_self _)
    exact congrArg (fun s => Sum.inl (Sum.inl s)) (Sum.inr.inj (Sum.inl.inj (Sum.inl.inj h1)))
  · have h1 := h (.inl (.inr p)) (Finset.mem_singleton_self _)
    exact congrArg (fun s => Sum.inl (Sum.inr s)) (Sum.inr.inj (Sum.inl.inj h1))
  · have h1 := h (.inr p) (Finset.mem_singleton_self _)
    exact congrArg Sum.inr (Sum.inr.inj h1)

omit [Fintype E] [Fintype κ] [Fintype J] [Fintype Y] in
/-- what the verifier of the locations outputs: the folded word at the drawn locations -/
theorem LdLinP.loc_nx (P : LdLinP E ι κ J Y) (x : P.X3) (y : P.E3.Str) (Q : Fin P.t → ι) :
    P.vLoc.nx x y Q = (x, (Q, fun i => foldAll x.1.2.1 (P.tab y.1.1.1) (Q i))) := by
  classical
  refine Prod.ext rfl (Prod.ext rfl (funext fun i => ?_))
  show P.foldSym x.1.2.1 (P.E3.ans (P.vLoc.rd Q) y (.inl (.inl (.inl (Q i))))) = _
  have hmem : (Sum.inl (Sum.inl (Sum.inl (Q i))) : P.E3.Pos) ∈ P.vLoc.rd Q :=
    Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
  rw [P.E3.ans_of_mem y hmem]
  show ∑ r, Alg.eqk x.1.2.1 r * P.up (y.1.1.1 (Q i)) r = foldAll x.1.2.1 (P.tab y.1.1.1) (Q i)
  rw [foldAll_apply]
  rfl

omit [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- the positions that the locations need -/
theorem LdLinP.loc_pos (P : LdLinP E ι κ J Y) (S : P.Snd) (qa : Finset P.Ea.Pos → Prop)
    (Q : Fin P.t → ι) (U : Finset P.E4.Pos) (hU : P.q4 S qa U) (V : Finset P.E3.Pos)
    (hm : ∀ p, p ∈ V ↔ (∃ i, p = .inl (.inl (.inl (Q i)))) ∨ ∃ u ∈ U, p ∈ P.dropIx.src u) :
    P.q3 S qa V := by
  classical
  have e1 : V.toRight = U.toRight := by
    ext p
    rw [Finset.mem_toRight, Finset.mem_toRight, hm]
    constructor
    · rintro (⟨i, hi⟩ | ⟨u, hu, hp⟩)
      · exact absurd hi (by simp)
      · rcases u with (u | u) | u
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · obtain rfl : p = u := Sum.inr.inj (Finset.mem_singleton.1 hp)
          exact hu
    · exact fun h => Or.inr ⟨_, h, Finset.mem_singleton_self _⟩
  have e2 : V.toLeft.toRight = U.toLeft.toRight := by
    ext p
    rw [Finset.mem_toRight, Finset.mem_toLeft, Finset.mem_toRight, Finset.mem_toLeft, hm]
    constructor
    · rintro (⟨i, hi⟩ | ⟨u, hu, hp⟩)
      · exact absurd hi (by simp)
      · rcases u with (u | u) | u
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · obtain rfl : p = u := Sum.inr.inj (Sum.inl.inj (Finset.mem_singleton.1 hp))
          exact hu
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
    · exact fun h => Or.inr ⟨_, h, Finset.mem_singleton_self _⟩
  have e3 : V.toLeft.toLeft.toRight = U.toLeft.toLeft := by
    ext p
    rw [Finset.mem_toRight, Finset.mem_toLeft, Finset.mem_toLeft,
      Finset.mem_toLeft, Finset.mem_toLeft, hm]
    constructor
    · rintro (⟨i, hi⟩ | ⟨u, hu, hp⟩)
      · exact absurd hi (by simp)
      · rcases u with (u | u) | u
        · obtain rfl : p = u := Sum.inr.inj (Sum.inl.inj (Sum.inl.inj (Finset.mem_singleton.1 hp)))
          exact hu
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
    · exact fun h => Or.inr ⟨_, h, Finset.mem_singleton_self _⟩
  have e4 : V.toLeft.toLeft.toLeft ⊆ Finset.univ.image Q := by
    intro p hp
    rw [Finset.mem_toLeft, Finset.mem_toLeft, Finset.mem_toLeft, hm] at hp
    rcases hp with ⟨i, hi⟩ | ⟨u, hu, hp⟩
    · exact Finset.mem_image.2
        ⟨i, Finset.mem_univ _, (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj hi))).symm⟩
    · rcases u with (u | u) | u
      · exact absurd (Finset.mem_singleton.1 hp) (by simp)
      · exact absurd (Finset.mem_singleton.1 hp) (by simp)
      · exact absurd (Finset.mem_singleton.1 hp) (by simp)
  refine ⟨⟨⟨?_, ?_⟩, fun a => ?_⟩, fun a => ?_⟩
  · refine (Finset.card_le_card e4).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_univ, Fintype.card_fin]
  · rw [e3]
    exact hU.1.1
  · refine le_of_eq_of_le (cnt_congr fun x => ?_) (hU.1.2 a)
    rw [← Finset.mem_toRight, e2, Finset.mem_toRight]
  · refine le_of_eq_of_le (cnt_congr fun x => ?_) (hU.2 a)
    rw [← Finset.mem_toRight, e1, Finset.mem_toRight]

omit [Fintype E] in
theorem ldLin_loc : Spec.ldLin_loc E ι κ J Y := by
  classical
  intro P on0 S qa
  refine piece_peek Unit P.X3 P.X4 P.E3 P.E4 P.W3 P.W4 P.vLoc _ _ (fun _ _ w => w.2) (P.j3 on0)
    P.j4 P.errLoc (P.q3 S qa) (P.q4 S qa) P.dropIx_local ?_ ?_ ?_ ?_ ?_
  · intro x y w Q h
    obtain ⟨hUe, hUa, ⟨hWe, hWa, ⟨htab, hrec, haa, hcl⟩, hw⟩, hu⟩ := h
    have hu' : P.uv (P.NU.msgs w.1) = foldAll x.1.2.1 w.2.2.1 := hu
    have hfold : ∀ j, foldAll x.1.2.1 (P.tab y.1.1.1) j =
        P.D.X.G.mulVec (foldAll x.1.2.1 w.2.2.1) j := fun j => by
      rw [P.D.X.mulVec_foldAll, show P.tab y.1.1.1 = fun r => P.D.X.G.mulVec (w.2.2.1 r) from htab]
    rw [P.loc_nx]
    refine ⟨Prod.ext rfl (Prod.ext rfl (funext fun i => hfold _)), ⟨hUe, hUa⟩, ⟨hWe, hWa⟩,
      hrec, haa, hcl, hw, hu', fun i => ?_, rfl⟩
    show P.D.X.G.mulVec (P.uv (P.NU.msgs w.1)) (Q i) = foldAll x.1.2.1 (P.tab y.1.1.1) (Q i)
    rw [hu', hfold]
  · intro x y Q h
    rw [P.loc_nx]
    exact ⟨h.2.2.2, h.2.1, h.1⟩
  · exact fun _ _ _ => rfl
  · intro x y _
    by_cases hU : ∃ mU, P.NU.DecTo x.2 y.2 mU
    swap
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro Q ⟨w', h, -⟩
        rw [P.loc_nx] at h
        exact hU ⟨_, h.1⟩
    obtain ⟨mU, hU⟩ := hU
    by_cases hn : P.D.X.NearW P.e' (foldAll x.1.2.1 (P.tab y.1.1.1)) (P.uv mU)
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro Q ⟨w', h, hnot⟩
        rw [P.loc_nx] at h
        obtain ⟨hdU, hdW, haa, hev, hrec, hdot, -⟩ := h
        obtain rfl : mU = P.NU.msgs w'.2.1 := hU.unique hdU
        exact hnot ⟨hdU, hdW, haa, hev, hn, hrec, hdot⟩
    · refine le_trans (cnt_mono fun Q hQ => ?_) (P.D.X.cnt_far_lists P.t hn)
      obtain ⟨w', h, -⟩ := hQ
      rw [P.loc_nx] at h
      obtain ⟨hdU, -, -, -, -, -, hcol⟩ := h
      obtain rfl : mU = P.NU.msgs w'.2.1 := hU.unique hdU
      exact hcol
  · intro Q U V hU hV
    refine P.loc_pos S qa Q U hU V fun p => ?_
    rw [hV p]
    refine or_congr ?_ Iff.rfl
    constructor
    · intro h
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩

/-! ### ζ -/

omit [Fintype ι] [Nonempty ι] in
theorem ldLin_zeta [Fintype ι] : Spec.ldLin_zeta E ι κ J Y := by
  classical
  intro P q hpy
  refine piece_peek Unit P.X5 P.X6 P.E5 P.E5 P.W5 P.W5 P.vZeta _ _ (fun _ _ w => w)
    P.j5 P.j6 P.errZeta q q (extMap_isLocal.1 _) ?_ ?_ ?_ ?_ ?_
  · exact fun x y w c h => ⟨rfl, h⟩
  · exact fun x y c h => h
  · exact fun _ _ _ => rfl
  · intro x y _
    by_cases hO : ∃ mO, P.NO.DecTo x.2 y.2 mO
    swap
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro c ⟨w', h, -⟩
        exact hO ⟨_, h.1⟩
    by_cases hU : ∃ mU, P.NU.DecTo x.1.1.2 y.1.2 mU
    swap
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro c ⟨w', h, -⟩
        exact hU ⟨_, h.2.1⟩
    obtain ⟨mO, hO⟩ := hO
    obtain ⟨mU, hU⟩ := hU
    refine le_trans (cnt_mono fun c hc => ?_)
      (ldLin_cnt_zeta P.D (P.D.X.msg (P.uv mU)) x.1.1.1.2.2 (P.ov mO) hpy)
    obtain ⟨w', ⟨hdO, hdU, hdW, haa, hrec, hcol, hfold, hev, hdot⟩, hnot⟩ := hc
    obtain rfl : mO = P.NO.msgs w'.1 := hO.unique hdO
    obtain rfl : mU = P.NU.msgs w'.2.1 := hU.unique hdU
    refine ⟨fun hom => hnot ⟨hdO, hdU, hdW, haa, hev, hrec, ?_, hcol⟩, hfold⟩
    show P.D.Dot (P.g x.1.1.1.1.1.1) (P.D.omU (P.D.X.msg (P.uv (P.NU.msgs w'.2.1))) x.1.1.1.2.2)
      x.1.1.1.2 (P.wv (P.NW.msgs w'.2.2.1))
    rw [← hom]
    exact hdot
  · intro c U S hU hS
    rw [ldk_eq_of_mem_id hS]
    exact hU

/-! ### The two regimes -/

omit [Nonempty ι] [Fintype Y] in
theorem ldLin_foldErr : Spec.ldLin_foldErr E ι κ J Y := fun P d bad L hd he hee hm hL f rec hc =>
  ldFe_cnt P.D.X d P.e' bad L f rec hd he hee hm (hL f) hc

omit [Nonempty ι] [Fintype Y] in
theorem ldLin_foldErr_far : Spec.ldLin_foldErr_far E ι κ J Y := by
  intro P d hd he f rec hdec
  rw [cnt_false]
  exact ldFe_none P.D.X d P.e' f rec hd he hdec

omit [Field E] [Fintype E] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem ldLin_loc_far [Field E] : Spec.ldLin_loc_far E ι κ J Y := by
  intro P d h
  unfold LdLinP.errLoc
  congr 1
  omega

end
end Cb
