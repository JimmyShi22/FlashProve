-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinkProofs.lean: the proofs of the statements of Cb/Ld/LdLink.lean. No axiom beyond Lean's
three; no hypothesis beyond those in the statements' own text.

Each round without a prover message is `IOR.peek` (`piece_peek`, Cb/Ld/LdLinKit.lean); what is shown
is its hypotheses: locality, forward, conditions, cores, the count of bad values, positions. The
sending of the family of oracle messages is the block of Cb/Ld/LdSendFam.lean (`ldSendFam_chain`,
Cb/Ld/LdSendFamProofs.lean); here: what it needs of positions. The chain: the rules of
Cb/Ld/LdTowerKit.lean at the joints whose conditions may fail.
Main names (statements and hypotheses: Cb/Ld/LdLink.lean):
  `ldLk_gam`, `ldLk_send`, `ldLk_loc`, `ldLk_phi`: the four blocks, in the chain's order.
  `ldLk_core`: the chain up to the rows that are left.
  `ldLk_tail`: the link, with any closing, for ι not empty and under the four premises of its
    statement (the fourth: the closing is a tail by itself).
  `ldLk_know`: knowledge soundness on the statements with the conditions, with nothing extracted,
    for ι not empty and under the four premises of its statement.
  `ldLk_end`: see its statement in Cb/Ld/LdLink.lean.
  `ldLk_foldErr_rec`, `ldLk_foldErr`: `P.FoldErr` from the fold lemma, in two pairings, each under
    the hypotheses of its statement.
What the statements say, with their hypotheses, and what they do not say: Cb/Ld/LdLink.lean.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLink
import Cb.Ld.LdLinkWordsProofs
import Cb.Ld.LdSendFamProofs
import Cb.Ld.LdLinProofsChain

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldLk_mem_biUnion {α β : Type} {inst : DecidableEq β} {s : Finset α}
    {t : α → Finset β} {b : β} :
    b ∈ @Finset.biUnion α β inst s t ↔ ∃ a ∈ s, b ∈ t a :=
  Finset.mem_biUnion
theorem ldLk_mem_image {α β : Type} {inst : DecidableEq β} {f : α → β} {s : Finset α} {b : β} :
    b ∈ @Finset.image α β inst f s ↔ ∃ a ∈ s, f a = b := Finset.mem_image

theorem Sig.mem_fib {E : Type} (N : Sig E) (U : Finset N.ext.Pos) (a : N.O) (x : (N.om a).P) :
    x ∈ N.fib U a ↔ (⟨a, x⟩ : N.ext.Pos) ∈ U := by
  unfold Sig.fib
  rw [Finset.mem_preimage]

section Send
variable {E : Type} [Field E]

theorem ldLk_send : Spec.ldLk_send E := by
  classical
  intro N Sd X W W' E₀ A back D L t q hC hF hL hE hD hB hZ
  refine ⟨ldSendFam_chain E N Sd Unit X W W' E₀ A back D L t hC hF hL hE hD hB hZ,
    fun _ _ => rfl, fun _ _ => rfl,
    fun ρ U hU => ⟨fun a => ⟨N.fib U.toRight a, hU.2 a, fun p hp => ?_⟩, ?_⟩⟩
  · have h1 := Finset.mem_toLeft.1 hp
    obtain ⟨u, hu, hpu⟩ := ldLk_mem_biUnion.1 h1
    rcases u with u | u
    · exact absurd hpu (Finset.notMem_empty _)
    · obtain ⟨p', hp', he⟩ := ldLk_mem_image.1 hpu
      obtain ⟨a', x⟩ := u
      have he' := Sum.inl.inj he
      obtain rfl : a' = a := (Sigma.mk.inj he').1
      obtain rfl : p' = p := eq_of_heq (Sigma.mk.inj he').2
      exact Finset.mem_biUnion.2 ⟨x, (N.mem_fib _ _ _).2 (Finset.mem_toRight.2 hu), hp'⟩
  · have e : (ldSendFam N Sd X E₀).need ρ U = U.toLeft := by
      ext p
      rw [mem_need, mem_given, Finset.mem_toLeft]
      constructor
      · rintro ((h | ⟨r, _, h⟩) | ⟨u, hu, h⟩)
        · exact absurd h (Finset.notMem_empty _)
        · exact absurd h (Finset.notMem_empty _)
        · rcases u with u | u
          · rw [Finset.mem_singleton.1 h]
            exact hu
          · exact absurd h (Finset.notMem_empty _)
      · exact fun h => Or.inr ⟨_, h, Finset.mem_singleton_self p⟩
    rw [e]
    exact hU.1

end Send

section
variable {E ι κ J Λ : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Λ]

omit [Fintype κ] [Fintype J] [Fintype Λ] in
theorem ldLk_shape : Spec.ldLk_shape E ι κ J Λ := fun _ _ _ => rfl

/-! ### γ -/

omit [Nonempty ι] [Fintype Λ] in
theorem ldLk_gam : Spec.ldLk_gam E ι κ J Λ := by
  classical
  intro P on0 on1 ε₀ ε₁ q hF
  refine piece_peek Unit P.X0 P.X1 P.E0 P.E0 P.W0 P.W1 P.vGam _ _ (fun _ _ w => w.2) (P.j0 on0 on1)
    (P.j1 on0 on1) (P.errGam ε₀ ε₁) q q (extMap_isLocal.1 _) ?_ ?_ ?_ ?_ ?_
  · exact fun x y w c h => ⟨rfl, h, rfl, rfl⟩
  · exact fun x y c h => h
  · exact fun _ _ _ => rfl
  · intro x y hon
    refine le_trans (cnt_mono fun c hc => ?_)
      (ldLk_cnt_gam P.D (P.tab y.1) (P.tab y.2) x.1 x.2 P.e₀ P.e₁ ε₀ ε₁
        (hF.1 _ _ hon.1) (hF.2 _ _ hon.2))
    obtain ⟨w', ⟨⟨n0, r0⟩, ⟨n1, r1⟩, hl⟩, hnot⟩ := hc
    by_contra hbad
    exact hnot (ldLk_back_gam P.D _ _ _ _ _ _ c w'.1.1 w'.1.2 hbad n0 r0 n1 r1 hl)
  · intro c U S hU hS
    rw [ldk_eq_of_mem_id hS]
    exact hU

/-! ### The locations -/

omit [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Λ] in
theorem LdLkP.dropIx_local (P : LdLkP E ι κ J Λ) : P.dropIx.IsLocal := by
  intro y y' q h
  exact Sum.inr.inj (h (.inr q) (Finset.mem_singleton_self _))

omit [Fintype E] [Fintype κ] [Fintype J] [Fintype Λ] in
/-- What the verifier of the locations outputs: the two folded words at the drawn locations (ι is
not empty). -/
theorem LdLkP.loc_nx (P : LdLkP E ι κ J Λ) (x : P.X2)
    (y : P.E2.Str) (Q : (Fin P.t₀ → ι) × (Fin P.t₁ → ι)) :
    P.vLoc.nx x y Q =
      (x, ((Q.1, fun i => foldAll x.1.2 (P.tab y.1.1) (Q.1 i)),
          (Q.2, fun i => foldAll x.1.2 (P.tab y.1.2) (Q.2 i)))) := by
  classical
  refine Prod.ext rfl
    (Prod.ext (Prod.ext rfl (funext fun i => ?_)) (Prod.ext rfl (funext fun i => ?_)))
  · show P.foldSym₀ x.1.2 (P.E2.ans (P.vLoc.rd Q) y (.inl (.inl (Q.1 i)))) = _
    have hmem : (Sum.inl (Sum.inl (Q.1 i)) : P.E2.Pos) ∈ P.vLoc.rd Q :=
      Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    rw [P.E2.ans_of_mem y hmem]
    show ∑ r, Alg.eqk x.1.2 r * P.up (y.1.1 (Q.1 i)) r = foldAll x.1.2 (P.tab y.1.1) (Q.1 i)
    rw [foldAll_apply]
    rfl
  · show P.foldSym₁ x.1.2 (P.E2.ans (P.vLoc.rd Q) y (.inl (.inr (Q.2 i)))) = _
    have hmem : (Sum.inl (Sum.inr (Q.2 i)) : P.E2.Pos) ∈ P.vLoc.rd Q :=
      Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
    rw [P.E2.ans_of_mem y hmem]
    show ∑ r, Alg.eqk x.1.2 r * P.up (y.1.2 (Q.2 i)) r = foldAll x.1.2 (P.tab y.1.2) (Q.2 i)
    rw [foldAll_apply]
    rfl

omit [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Λ] in
/-- The positions that the locations need are within `P.q2 S`, under `hU`, `hm`. -/
theorem LdLkP.loc_pos (P : LdLkP E ι κ J Λ) (S : P.Snd) (Q : (Fin P.t₀ → ι) × (Fin P.t₁ → ι))
    (U : Finset P.E3.Pos) (hU : P.q3 S U) (V : Finset P.E2.Pos)
    (hm : ∀ p,
      p ∈ V ↔ ((∃ i, p = .inl (.inl (Q.1 i))) ∨ ∃ i, p = .inl (.inr (Q.2 i))) ∨
        ∃ u ∈ U, p ∈ P.dropIx.src u) : P.q2 S V := by
  classical
  have e1 : V.toRight = U := by
    ext p
    rw [Finset.mem_toRight, hm]
    constructor
    · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | ⟨u, hu, hp⟩)
      · exact absurd hi (by simp)
      · exact absurd hi (by simp)
      · obtain rfl : p = u := Sum.inr.inj (Finset.mem_singleton.1 hp)
        exact hu
    · exact fun h => Or.inr ⟨_, h, Finset.mem_singleton_self _⟩
  have e2 : V.toLeft.toLeft ⊆ Finset.univ.image Q.1 := by
    intro p hp
    rw [Finset.mem_toLeft, Finset.mem_toLeft, hm] at hp
    rcases hp with (⟨i, hi⟩ | ⟨i, hi⟩) | ⟨u, hu, hp⟩
    · exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, (Sum.inl.inj (Sum.inl.inj hi)).symm⟩
    · exact absurd hi (by simp)
    · exact absurd (Finset.mem_singleton.1 hp) (by simp)
  have e3 : V.toLeft.toRight ⊆ Finset.univ.image Q.2 := by
    intro p hp
    rw [Finset.mem_toRight, Finset.mem_toLeft, hm] at hp
    rcases hp with (⟨i, hi⟩ | ⟨i, hi⟩) | ⟨u, hu, hp⟩
    · exact absurd hi (by simp)
    · exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, (Sum.inr.inj (Sum.inl.inj hi)).symm⟩
    · exact absurd (Finset.mem_singleton.1 hp) (by simp)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine (Finset.card_le_card e2).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_univ, Fintype.card_fin]
  · refine (Finset.card_le_card e3).trans (Finset.card_image_le.trans ?_)
    rw [Finset.card_univ, Fintype.card_fin]
  · rw [e1]
    exact hU

omit [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Λ] in
/-- The messages of a witness of a relaxed relation are those that the statement decodes to (`hm`,
`hw`). -/
theorem LdLkP.msgs_eq (P : LdLkP E ι κ J Λ) {σ : P.N.Smp} {y : P.N.ext.Str} {m : P.N.Msg}
    (hm : ∀ i, P.N.decs σ y i = some (m i)) {w : P.N.Wit}
    (hw : ∀ i, P.N.decs σ y i = some (w i).1) : P.N.msgs w = m :=
  funext fun i => Option.some.inj ((hw i).symm.trans (hm i))

omit [Fintype Λ] in
theorem ldLk_loc : Spec.ldLk_loc E ι κ J Λ := by
  classical
  intro P on0 on1 S
  refine piece_peek Unit P.X2 P.X3 P.E2 P.E3 P.W2 P.W2 P.vLoc _ _ (fun _ _ w => w) (P.j2 on0 on1)
    P.j3 P.errLoc (P.q2 S) (P.q3 S) P.dropIx_local ?_ ?_ ?_ ?_ ?_
  · intro x y w Q h
    obtain ⟨hEnc, hAns, ⟨⟨ht0, hr0⟩, ⟨ht1, hr1⟩, hsame⟩, hu0, hu1⟩ := h
    have hu0' : P.uv₀ (P.N.msgs w.1) = foldAll x.1.2 w.2.1 := hu0
    have hu1' : P.uv₁ (P.N.msgs w.1) = foldAll x.1.2 w.2.2 := hu1
    have hf0 : ∀ j,
        foldAll x.1.2 (P.tab y.1.1) j = P.D.X.G.mulVec (foldAll x.1.2 w.2.1) j := fun j => by
      rw [P.D.X.mulVec_foldAll, show P.tab y.1.1 = fun r => P.D.X.G.mulVec (w.2.1 r) from ht0]
    have hf1 : ∀ j,
        foldAll x.1.2 (P.tab y.1.2) j = P.D.X.G.mulVec (foldAll x.1.2 w.2.2) j := fun j => by
      rw [P.D.X.mulVec_foldAll, show P.tab y.1.2 = fun r => P.D.X.G.mulVec (w.2.2 r) from ht1]
    rw [P.loc_nx]
    refine ⟨Prod.ext rfl
        (Prod.ext (Prod.ext rfl (funext fun i => hf0 _)) (Prod.ext rfl (funext fun i => hf1 _))),
      hEnc, hAns, hr0, hr1, hsame, hu0', hu1', fun i => ?_, fun i => ?_⟩
    · show P.D.X.G.mulVec (P.uv₀ (P.N.msgs w.1)) (Q.1 i) = foldAll x.1.2 (P.tab y.1.1) (Q.1 i)
      rw [hu0', hf0]
    · show P.D.X.G.mulVec (P.uv₁ (P.N.msgs w.1)) (Q.2 i) = foldAll x.1.2 (P.tab y.1.2) (Q.2 i)
      rw [hu1', hf1]
  · intro x y Q h
    rw [P.loc_nx]
    exact h.1
  · exact fun _ _ _ => rfl
  · intro x y _
    by_cases hex : ∃ m : P.N.Msg, ∀ i, P.N.decs x.2 y.2 i = some (m i)
    · obtain ⟨m, hm⟩ := hex
      refine le_trans (cnt_mono fun Q hQ => ?_)
        (ldLk_cnt_loc P.D P.t₀ P.t₁ P.e₀ P.e₁ (foldAll x.1.2 (P.tab y.1.1))
          (foldAll x.1.2 (P.tab y.1.2)) (P.uv₀ m) (P.uv₁ m))
      obtain ⟨w', h, hnot⟩ := hQ
      rw [P.loc_nx] at h
      obtain ⟨hd, ⟨r0, c0⟩, ⟨r1, c1⟩, hl⟩ := h
      have hmm := P.msgs_eq hm hd
      rw [hmm] at r0 c0 r1 c1 hl
      refine ⟨?_, c0, c1⟩
      by_contra hboth
      push Not at hboth
      refine hnot ⟨hd, ?_⟩
      show (P.j1 on0 on1).relR (x.1, y.1) (P.back (P.N.msgs w'.1) w'.2)
      rw [hmm]
      exact ⟨⟨hboth.1, r0⟩, ⟨hboth.2, r1⟩, hl⟩
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro Q ⟨w', h, -⟩
        rw [P.loc_nx] at h
        exact hex ⟨_, h.1⟩
  · intro Q U V hU hV
    refine P.loc_pos S Q U hU V fun p => ?_
    rw [hV p]
    refine or_congr ?_ Iff.rfl
    constructor
    · intro h
      rcases Finset.mem_union.1 h with h | h
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
        exact Or.inl ⟨i, hi.symm⟩
      · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
        exact Or.inr ⟨i, hi.symm⟩
    · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)

/-! ### φ -/

omit [Nonempty ι] [Fintype ι] in
theorem ldLk_phi : Spec.ldLk_phi E ι κ J Λ := by
  classical
  intro P q hpl
  refine piece_peek Unit P.X3 P.X4 P.E3 P.E3 P.W2 P.W2 P.vPhi _ _ (fun _ _ w => w)
    P.j3 P.j4 P.errPhi q q (extMap_isLocal.1 _) ?_ ?_ ?_ ?_ ?_
  · exact fun x y w c h => ⟨rfl, h⟩
  · exact fun x y c h => h
  · exact fun _ _ _ => rfl
  · intro x y _
    by_cases hex : ∃ m : P.N.Msg, ∀ i, P.N.decs x.1.2 y i = some (m i)
    · obtain ⟨m, hm⟩ := hex
      refine le_trans (cnt_mono fun c hc => ?_) (ldLk_cnt_phi P.D (P.uv₀ m) (P.uv₁ m) hpl)
      obtain ⟨w', ⟨hd, h0, h1, heq⟩, hnot⟩ := hc
      have hmm := P.msgs_eq hm hd
      rw [hmm] at h0 h1 heq
      refine ⟨fun hl => hnot ⟨hd, ?_⟩, heq⟩
      rw [hmm]
      exact ⟨h0, h1, hl⟩
    · rw [cnt_false]
      · exact Nat.zero_le _
      · rintro c ⟨w', h, -⟩
        exact hex ⟨_, h.1⟩
  · intro c U S hU hS
    rw [ldk_eq_of_mem_id hS]
    exact hU

/-! ### The chain -/

theorem ldLk_core : Spec.ldLk_core E ι κ J Λ := by
  intro P on0 on1 ε₀ ε₁ S d hF hpl hS
  have hG := ldk_pieceTr_cf (ldLk_gam P on0 on1 ε₀ ε₁ P.q0 hF)
  have hN := ldLk_send P.N S.Sd P.X1 P.W1 P.W0 P.E0 (P.j1 on0 on1) P.back S.dS S.L S.t P.q0 hS.laws
    hS.fair hS.list hS.ev hS.snd hS.bl hS.hid
  have hL := ldk_pieceTr_cf (ldLk_loc P on0 on1 S)
  have hP := ldk_pieceTr_cf (ldLk_phi P (P.q3 S) hpl)
  have c3 := pieceTr_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.2.2 _ _ _ _ _ hL hP
  have c2 := pieceTr_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.2.1 _ _ _ _ _ hN c3
  exact pieceTr_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.1 _ _ _ _ _ hG c2

theorem ldLk_tail : Spec.ldLk_tail E ι κ J Λ := by
  intro P on0 on1 ε₀ ε₁ S d Z hF hpl hS hZ
  have h := tailTr_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.1 _ _ _ _
    (ldLk_core P on0 on1 ε₀ ε₁ S d hF hpl hS) hZ
  exact ⟨goodT_cf_out _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ => trivial) h.good,
    h.noHid, h.tied, h.bears⟩

theorem ldLk_know : Spec.ldLk_know E ι κ J Λ := by
  intro P on0 on1 ε₀ ε₁ S Z hF hpl hS hZ
  have d : P.W0 × P.W1 × P.W2 :=
    ((fun _ _ => 0, fun _ _ => 0),
      ((fun _ => 0, fun _ => 0), (fun _ _ => 0, fun _ _ => 0)),
      (fun _ => (fun _ => 0, fun _ => 0), (fun _ _ => 0, fun _ _ => 0)))
  have h := (ldLk_tail P on0 on1 ε₀ ε₁ S d Z hF hpl hS hZ).good.know
  intro a ha
  exact Doomed.mono _ _ (fun τ hτ b w hb _ => hτ b w hb trivial) (h a ha)

theorem ldLk_end : Spec.ldLk_end E ι κ J Λ := by
  intro P on0 on1 ε₀ ε₁ S Z hF hpl hS hZ
  have d : P.W0 × P.W1 × P.W2 :=
    ((fun _ _ => 0, fun _ _ => 0),
      ((fun _ => 0, fun _ => 0), (fun _ _ => 0, fun _ _ => 0)),
      (fun _ => (fun _ => 0, fun _ => 0), (fun _ _ => 0, fun _ _ => 0)))
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8, h9⟩ :=
    tailTr_end _ _ _ _ _ _ _ _ _ _ _ _ _ (ldLk_tail P on0 on1 ε₀ ε₁ S d Z hF hpl hS hZ)
  exact ⟨h1, h2, h3, h4, h5, h7, h8,
    fun ρ =>
      ⟨(Finset.card_le_card (Finset.toLeft_subset_toLeft (h9 ρ).2)).trans (h9 ρ).1.1,
        (Finset.card_le_card (Finset.toRight_subset_toRight (h9 ρ).2)).trans (h9 ρ).1.2⟩⟩

omit [Nonempty ι] [Fintype Λ] in
theorem ldLk_foldErr : Spec.ldLk_foldErr E ι κ J Λ := by
  intro P d bad L hd he0 he1 hm hL
  refine ⟨fun f rec hdec => ?_,
    fun f rec hc => ldFe_cnt P.D.X d P.e₁ bad L f rec hd (by omega) he1 hm (hL f) hc⟩
  rw [cnt_false]
  exact ldFe_none P.D.X d P.e₀ f rec hd he0 hdec

omit [Nonempty ι] [Fintype Λ] in
theorem ldLk_foldErr_rec :
    Spec.ldLk_foldErr_rec E ι κ J Λ := fun P d bad₀ L₀ bad₁ L₁ hd he h0 h1 hm0 hL0 hm1 hL1 =>
  ⟨fun f rec hc => ldFe_cnt P.D.X d P.e₀ bad₀ L₀ f rec hd he h0 hm0 (hL0 f) hc,
    fun f rec hc => ldFe_cnt P.D.X d P.e₁ bad₁ L₁ f rec hd he h1 hm1 (hL1 f) hc⟩

end
end Cb
