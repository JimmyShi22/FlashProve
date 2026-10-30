-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinBHonProofs.lean: the proofs of the statements of Cb/Ld/LdLinBHon.lean.

Under the hypotheses of these statements each link is a piece by the rules of Ior/LinkVRules.lean
(a run in every slot; a run by the shared part alone) and Ior/LinkVBears.lean (budgets for
families), from the one-instance theorems of Cb/Ld/LdLinProofs.lean and Cb/Ld/LdSendPiece.lean.
What is shown here, link by link:
  the tie is carried along honest runs;
  the one-instance prover's transcript is the shared strategy's;
  what a simulator is given is determined by what the shared part holds;
  what is needed of the old oracles is within the demand.
Link, piece, tie, shared part and demand are told in the heads of Cb/Ld/LdLinBHon.lean and
Cb/Ld/LdLinChainV.lean.

Main names (each of the four `ldLinV_..` proves the statement of its name in `Cb.Spec`,
Cb/Ld/LdLinBHon.lean, under that statement's hypotheses):
  `ldLinV_her`: the demands are kept by subsets of the set of slots.
  `ldLinV_forget`: the chain's links with annotations are those of the batch's knowledge soundness
    (`P.chainA`).
  `LdLinP.pv0`, `pvW`, `pvPt`, `pvU`, `pvLoc`, `pvO`, `pvZeta`: each under its own hypotheses, the
    link of `step0`, `sW`, `pt`, `sU`, `loc`, `sO`, `zeta` is a piece (`LinkV.PV`); the first two by
    the rule for a run in every slot (`localV`), the other five by that for a run by the shared part
    alone (`sharedV`; in `pt`, `loc`, `zeta` nobody sends).
  `ldLinV_pv`: the seven together. `ldLinV_core`: under the hypotheses of `Spec.ldLinV_pv`: all
    links of `P.chainV` are pieces.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinBHon
import Cb.Ld.LdLinBData

set_option autoImplicit false

namespace Iop
open Prob IOR

/-- what is needed of the old oracles: a step without rounds that copies; a round without a prover
message -/
theorem ldk_need_pure {X : Type} {Ex : ExtSpec}
    (ρ : Rho (IOR.pure (Xi := X) some (ExtMap.id Ex)).shape) (U : Finset Ex.Pos) :
    (IOR.pure (Xi := X) some (ExtMap.id Ex)).need ρ U = U := by
  classical
  ext p
  rw [mem_need, mem_given]
  constructor
  · rintro ((h | ⟨r, _, h⟩) | ⟨u, hu, h⟩)
    · exact absurd h (Finset.notMem_empty _)
    · exact absurd h (Finset.notMem_empty _)
    · rw [Finset.mem_singleton.1 h]
      exact hu
  · exact fun h => Or.inr ⟨p, h, Finset.mem_singleton_self p⟩

theorem ldk_mem_need_peek {Xi Xo : Type} {Ei Eo : ExtSpec} (V : PeekV Xi Ei Xo Eo)
    (ρ : Rho [drawRound V.D]) (U : Finset Eo.Pos) (p : Ei.Pos) :
    p ∈ (IOR.peek V).need ρ U ↔ p ∈ V.rd (show V.D × Unit from ρ).1 ∨ ∃ u ∈ U, p ∈ V.g.src u := by
  classical
  rw [mem_need, mem_given]
  constructor
  · rintro ((h | ⟨r, _, h⟩) | ⟨u, hu, h⟩)
    · exact Or.inl h
    · exact absurd h (Finset.notMem_empty _)
    · exact Or.inr ⟨u, hu, h⟩
  · rintro (h | ⟨u, hu, h⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨u, hu, h⟩

/-- Of the implicit instance nothing is given to the simulator of a round without a prover message
but what the verifier reads
(`p ∈ (IOR.peek V).given ρ T ↔ p ∈ V.rd (show V.D × Unit from ρ).1`). -/
theorem ldk_mem_given_peek {Xi Xo : Type} {Ei Eo : ExtSpec} (V : PeekV Xi Ei Xo Eo)
    (ρ : Rho [drawRound V.D]) (T : Finset (OPos [drawRound V.D])) (p : Ei.Pos) :
    p ∈ (IOR.peek V).given ρ T ↔ p ∈ V.rd (show V.D × Unit from ρ).1 := by
  classical
  rw [mem_given]
  exact ⟨fun h => h.elim id fun ⟨_, _, h⟩ => absurd h (Finset.notMem_empty _), Or.inl⟩

/-- every budget: such a block bears whatever follows, as far as its own oracles go -/
theorem ldk_bears_true {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) :
    R.Bears (fun _ _ => True) (fun _ => True) (fun _ => True) :=
  fun _ _ _ => ⟨trivial, trivial⟩

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldk_need_send {E : Type} [Field E] (N : Sig E) (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec)
    (ρ : Rho (N.sh Sd)) (U : Finset (E₀.prod N.ext).Pos) :
    (ldSendFam N Sd X E₀).need ρ U = U.toLeft := by
  classical
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

theorem ldk_given_send {E : Type} [Field E] (N : Sig E) (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec)
    (ρ : Rho (N.sh Sd)) (T : Finset (OPos (N.sh Sd))) (p : E₀.Pos) :
    p ∉ (ldSendFam N Sd X E₀).given ρ T := by
  classical
  rw [mem_given]
  rintro (h | ⟨_, _, h⟩)
  · exact absurd h (Finset.notMem_empty _)
  · exact absurd h (Finset.notMem_empty _)

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem LdLinP.her0 (P : LdLinP E ι κ J Y) (qa : Finset P.Ea.Pos → Prop) (N : ℕ) :
    (P.qv0 qa N).Her := fun _ _ h _ H =>
  ⟨fun T hT => H.1 T fun i hi => (hT i hi).elim fun j hj => ⟨⟨j.1, h j.2⟩, hj⟩,
    fun j => H.2 ⟨j.1, h j.2⟩⟩

omit [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem ldLinV_her : Spec.ldLinV_her E ι κ J Y := by
  intro P S qa N
  have h0 := P.her0 qa N
  have h1 : (P.qv1 S qa N).Her := fun J J' h Us H =>
    ⟨h0 J J' h _ H.1, fun j a => H.2 ⟨j.1, h j.2⟩ a⟩
  have h3 : (P.qv3 S qa N).Her := fun J J' h Us H =>
    ⟨h1 J J' h _ H.1,
      fun a => (cnt_mono fun x hx => hx.elim fun j hj => ⟨⟨j.1, h j.2⟩, hj⟩).trans (H.2 a)⟩
  have h4 : (P.qv4 S qa N).Her := fun J J' h Us H =>
    ⟨⟨fun j => H.1.1 ⟨j.1, h j.2⟩, fun j a => H.1.2 ⟨j.1, h j.2⟩ a⟩,
      fun a => (cnt_mono fun x hx => hx.elim fun j hj => ⟨⟨j.1, h j.2⟩, hj⟩).trans (H.2 a)⟩
  have h5 : (P.qv5 S qa N).Her := fun J J' h Us H =>
    ⟨h4 J J' h _ H.1,
      fun a => (cnt_mono fun x hx => hx.elim fun j hj => ⟨⟨j.1, h j.2⟩, hj⟩).trans (H.2 a)⟩
  exact ⟨h0, h1, h3, h4, h5⟩

theorem ldLinV_forget : Spec.ldLinV_forget E ι κ J Y := by
  intro P on0 εf N S qa
  unfold LdLinP.chainV LdLinP.chainA
  simp only [ChainV.forget_snoc, ChainV.forget_one]
  rfl

variable (P : LdLinP E ι κ J Y)
  (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (N : ℕ) (S : P.Snd) (qa : Finset P.Ea.Pos → Prop)

omit [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
theorem LdLinP.restW (h : S.dW.Laws P.backW) (w : P.WA) : S.dW.rest w = w.2 :=
  congrArg Prod.snd (h.back w (Classical.arbitrary _))

omit [Fintype E] [Nonempty ι] in
theorem LdLinP.pv0 : (P.lv0 qa N on0).PV := by
  have h0 := ldk_pieceTr_cf (ldLin_step0 P on0 fun _ => True)
  refine ⟨⟨h0.good.isLocal, ?_, ?_, ?_⟩, P.her0 qa N⟩
  · exact accV_local P.X0 P.X0 P.E0 P.E0 P.step0 P.W0 P.WA P.Sh0 P.hStep0 (P.j0 on0).rel
      (P.jA on0).rel (P.V0 qa N on0).rel (P.VA qa N on0).rel h0.good.acc h0.noHid
      (fun _ _ _ h => h.1) (fun x y w c ρ hV _ hRo => ⟨hRo, hV.2⟩)
  · exact exactV_local P.X0 P.X0 P.E0 P.E0 P.step0 P.W0 P.WA P.Sh0 P.hStep0 (P.j0 on0).rel
      (P.V0 qa N on0).rel _ N h0.good.exact h0.noHid (fun _ _ _ h => h.1)
  · refine bearsV_local P.X0 P.X0 P.E0 P.E0 P.step0 (RoundSplits.allLocal _) N _ (fun _ => True)
      (fun _ => True) (P.qv0 qa N) (P.qv0 qa N) (ldk_bears_true _)
      (fun _ _ _ _ => trivial) fun J ρ Us h => ?_
    have e : (fun j : J => P.step0.need (ρ.slot j.1) (Us j)) = Us :=
      funext fun j => ldk_need_pure _ _
    rw [e]
    exact h

omit [Fintype E] [Nonempty ι] in
theorem LdLinP.pvW (hS : S.OK) : (P.lvW S qa N on0).PV := by
  have hW := ldSendFam_piece E P.NW P.SdW Unit P.X0 P.WA P.W0 P.E0 (P.jA on0) P.backW S.dW S.LW S.tW
    (fun _ => True) hS.lawsW hS.fairW hS.listW hS.evW hS.sndW hS.blW hS.hidW
  refine ⟨⟨hW.good.isLocal, ?_, ?_, ?_⟩, (ldLinV_her P S qa N).2.1⟩
  · refine accV_local P.X0 P.X1 P.E0 P.E1 P.sW P.WA P.W1 P.Sh0 (ldSendFamHon P.SdW P.X0 P.E0 S.dW)
      (P.jA on0).rel (P.j1 on0).rel (P.VA qa N on0).rel (P.V1 S qa N on0).rel hW.good.acc hW.noHid
      (fun _ _ _ h => h.1) (fun x y w c ρ hV _ hRo => ⟨hRo, ⟨hV.2.1.1, ?_⟩, hV.2.2⟩)
    show (S.dW.rest w.2).1 = w.1.1.2
    rw [P.restW S hS.sndW]
    exact hV.2.1.2
  · exact exactV_local P.X0 P.X1 P.E0 P.E1 P.sW P.WA P.W1 P.Sh0 (ldSendFamHon P.SdW P.X0 P.E0 S.dW)
      (P.jA on0).rel (P.VA qa N on0).rel _ N hW.good.exact hW.noHid (fun _ _ _ h => h.1)
  · refine bearsV_local P.X0 P.X1 P.E0 P.E1 P.sW (RoundSplits.allLocal _) N _
      (fun _ => True) (P.NW.qFam (fun _ => True) S.tW) (P.qv0 qa N) (P.qv1 S qa N)
      (ldSendFam_bears P.NW P.SdW P.X0 P.E0 S.tW _)
      (fun J Us h j => ⟨trivial, h.2 j⟩) fun J ρ Us h => ?_
    have e : (fun j : J => P.sW.need (ρ.slot j.1) (Us j)) = fun j => (Us j).toLeft :=
      funext fun j => ldk_need_send _ _ _ _ _ _
    rw [e]
    exact h.1

end

/-! ### The rounds in which nobody speaks, and the shared part's sendings -/

/-- nothing is read and the oracles are copied: what is needed is what follows needs -/
theorem ldk_need_peek_id {Xi Xo : Type} {Ex : ExtSpec} (V : PeekV Xi Ex Xo Ex)
    (hr : ∀ c, V.rd c = ∅) (hg : V.g = ExtMap.id Ex) (ρ : Rho [drawRound V.D]) (U : Finset Ex.Pos) :
    (IOR.peek V).need ρ U = U := by
  ext p
  rw [ldk_mem_need_peek, hr, hg]
  constructor
  · rintro (h | ⟨u, hu, h⟩)
    · exact absurd h (Finset.notMem_empty _)
    · rw [Finset.mem_singleton.1 h]
      exact hu
  · exact fun h => Or.inr ⟨p, h, Finset.mem_singleton_self p⟩

/-- the run of a family's honest sender reads its witness through "put" (and "rest") alone -/
theorem ldk_send_run {E : Type} [Field E] {N : Sig E} (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec)
    {W W' : Type} (D : N.Sender W W') (x : X) (w w' : W) (c : D.Mk × D.Nn.Rnd)
    (ρ : Rho (N.sh Sd)) (h : D.put w c.1 = D.put w' c.1) :
    (((ldSendFamHon Sd X E₀ D).strat w x c).run ρ).1 =
      (((ldSendFamHon Sd X E₀ D).strat w' x c).run ρ).1 ∧
    (((ldSendFamHon Sd X E₀ D).strat w x c).run ρ).2.1 =
      (((ldSendFamHon Sd X E₀ D).strat w' x c).run ρ).2.1 ∧
    (((ldSendFamHon Sd X E₀ D).strat w x c).run ρ).2.2.1 =
      (((ldSendFamHon Sd X E₀ D).strat w' x c).run ρ).2.2.1 := by
  obtain ⟨sd, u, v⟩ := ρ
  have ha : D.ans Sd sd w c.1 = D.ans Sd sd w' c.1 := by
    unfold Sig.Sender.ans
    rw [h]
  refine ⟨?_, ?_, ?_⟩
  · show ((D.Nn.enc (D.put w c.1) c.2, ()), sd, ((), D.ans Sd sd w c.1), u, ()) =
      ((D.Nn.enc (D.put w' c.1) c.2, ()), sd, ((), D.ans Sd sd w' c.1), u, ())
    rw [h, ha]
  · show (x, fun a => (Sd.sd a sd, D.ans Sd sd w c.1 a)) =
      (x, fun a => (Sd.sd a sd, D.ans Sd sd w' c.1 a))
    rw [ha]
  · show (fun a => (D.upM (D.put w c.1) a, D.upR c.2 a)) =
      fun a => (D.upM (D.put w' c.1) a, D.upR c.2 a)
    rw [h]

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]
variable (P : LdLinP E ι κ J Y)
  (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (N : ℕ) (S : P.Snd) (qa : Finset P.Ea.Pos → Prop)

omit [Nonempty ι] in
theorem LdLinP.pvPt (εf : ℕ) (hF : P.FoldErr on0 εf) (ya : P.Ea.Str) :
    (P.lvPt S qa N on0 εf).PV := by
  have hP := ldk_pieceTr_cf (ldLin_pt P on0 εf (fun _ => True) hF)
  refine ⟨⟨hP.good.isLocal, ?_, ?_, ?_⟩, (ldLinV_her P S qa N).2.1⟩
  · exact accV_shared P.X1 P.X2 P.E1 P.E1 P.pt P.W1 P.W2 P.Sh0 P.Sh2 P.hPt P.sPt0 (P.j1 on0).rel
      (P.j2 on0).rel (P.V1 S qa N on0).rel (P.V2 S qa N on0).rel hP.good.acc hP.noHid
      (fun _ _ _ h => h.1) (fun _ _ _ _ _ _ => rfl) (fun x y w c ρ hV _ hRo => ⟨hRo, hV.2, rfl⟩)
  · exact exactV_shared P.X1 P.X2 P.E1 P.E1 P.pt P.W1 P.W2 P.Sh0 P.Sh2 P.hPt P.sPt0 (P.j1 on0).rel
      (P.V1 S qa N on0).rel _ N (fun s p => P.E1.rd ((s.1.1, ya), fun a => (P.NW.om a).sy0) p)
      hP.good.exact hP.noHid (fun _ _ _ h => h.1) (fun _ _ _ _ _ _ => rfl)
      (fun x y w ρ T p _ hp =>
        absurd ((ldk_mem_given_peek P.vPt ρ T p).1 hp) (Finset.notMem_empty _))
  · refine bearsV_shared P.X1 P.X2 P.E1 P.E1 P.pt N _ (fun _ => True) (fun _ => True) (P.qv1 S qa N)
      (P.qv1 S qa N) (ldk_bears_true _) (fun _ _ _ => trivial) fun J ρ Us h => ?_
    have e : (fun j : J => P.pt.need (ρ.slot j.1) (Us j)) = Us :=
      funext fun j => ldk_need_peek_id P.vPt (fun _ => rfl) rfl _ _
    rw [e]
    exact h

omit [Nonempty ι] in
theorem LdLinP.pvZeta (hpy : Function.Injective P.D.py) (ya : P.Ea.Str) : (P.lvZeta S qa N).PV := by
  have hZ := ldk_pieceTr_cf (ldLin_zeta P (fun _ => True) hpy)
  refine ⟨⟨hZ.good.isLocal, ?_, ?_, ?_⟩, (ldLinV_her P S qa N).2.2.2.2⟩
  · exact accV_shared P.X5 P.X6 P.E5 P.E5 P.zeta P.W5 P.W5 P.Sh5 P.Sh6 P.hZeta P.sZeta0 P.j5.rel
      P.j6.rel (P.V5 S qa N).rel (P.V6 S qa N).rel hZ.good.acc hZ.noHid (fun _ _ _ h => h.1)
      (fun _ _ _ _ _ _ => rfl) (fun x y w c ρ hV _ hRo => ⟨hRo, hV.2, rfl⟩)
  · exact exactV_shared P.X5 P.X6 P.E5 P.E5 P.zeta P.W5 P.W5 P.Sh5 P.Sh6 P.hZeta P.sZeta0 P.j5.rel
      (P.V5 S qa N).rel _ N
      (fun s p => P.E5.rd (((ya, fun a => (P.NW.om a).sy0), s.1.1.2.2.1), s.2.2.1) p)
      hZ.good.exact hZ.noHid (fun _ _ _ h => h.1) (fun _ _ _ _ _ _ => rfl)
      (fun x y w ρ T p _ hp =>
        absurd ((ldk_mem_given_peek P.vZeta ρ T p).1 hp) (Finset.notMem_empty _))
  · refine bearsV_shared P.X5 P.X6 P.E5 P.E5 P.zeta N _ (fun _ => True) (fun _ => True)
      (P.qv5 S qa N) (P.qv5 S qa N) (ldk_bears_true _) (fun _ _ _ => trivial) fun J ρ Us h => ?_
    have e : (fun j : J => P.zeta.need (ρ.slot j.1) (Us j)) = Us :=
      funext fun j => ldk_need_peek_id P.vZeta (fun _ => rfl) rfl _ _
    rw [e]
    exact h

omit [Fintype E] [Nonempty ι] in
theorem LdLinP.pvU (hS : S.OK) (hA : S.Apart) (ya : P.Ea.Str) : (P.lvU S qa N on0).PV := by
  have hU := ldSendFam_piece E P.NU P.SdU Unit P.X2 P.W2 P.W1 P.E1 (P.j2 on0) P.backU S.dU S.LU S.tU
    (fun _ => True) hS.lawsU hS.fairU hS.listU hS.evU hS.sndU hS.blU hS.hidU
  have hput : ∀ (x : P.X2) (y : P.E1.Str) (w : P.Sh2 × P.W2) k,
      (P.V2 S qa N on0).rel x y w → S.dU.put w.2 k = S.dU.put (P.wU S w.1) k := by
    intro x y w k hV
    refine hA.putU _ _ k ?_
    have h1 : w.2.1 = foldAll x.2.1 w.2.2.2.1 := hV.1.2
    have h2 : w.2.2.2.1 = w.1.1.1.2 := hV.2.1.1.2
    have h3 : x.2 = w.1.2 := hV.2.2
    show w.2.1 = foldAll w.1.2.1 w.1.1.1.2
    rw [h1, h2, h3]
  refine ⟨⟨hU.good.isLocal, ?_, ?_, ?_⟩, (ldLinV_her P S qa N).2.2.1⟩
  · refine accV_shared P.X2 P.X3 P.E1 P.E3 P.sU P.W2 P.W3 P.Sh2 P.Sh3
      (ldSendFamHon P.SdU P.X2 P.E1 S.dU) (P.sU0 S) (P.j2 on0).rel (P.j3 on0).rel
      (P.V2 S qa N on0).rel (P.V3 S qa N on0).rel hU.good.acc hU.noHid (fun _ _ _ h => h.1)
      (fun x y w c ρ hV =>
        (ldk_send_run P.SdU P.X2 P.E1 S.dU x w.2 (P.wU S w.1) c ρ (hput x y w c.1 hV)).1)
      (fun x y w c ρ hV _ hRo => ⟨hRo, ⟨⟨⟨hV.2.1.1.1, ?_⟩, hV.2.1.2⟩, hV.2.2⟩, ?_, ?_, ?_⟩)
    · show (S.dU.rest w.2).2.1 = w.1.1.1.2
      rw [P.restU S hS.sndU]
      exact hV.2.1.1.2
    · exact congrArg Prod.snd
        (ldk_send_run P.SdU P.X2 P.E1 S.dU x w.2 (P.wU S w.1) c ρ (hput x y w c.1 hV)).2.1
    · exact congrArg (fun τ : Tr (P.NU.sh P.SdU) => τ.1.1)
        (ldk_send_run P.SdU P.X2 P.E1 S.dU x w.2 (P.wU S w.1) c ρ (hput x y w c.1 hV)).1
    · exact (ldk_send_run P.SdU P.X2 P.E1 S.dU x w.2 (P.wU S w.1) c ρ (hput x y w c.1 hV)).2.2
  · exact exactV_shared P.X2 P.X3 P.E1 P.E3 P.sU P.W2 P.W3 P.Sh2 P.Sh3
      (ldSendFamHon P.SdU P.X2 P.E1 S.dU) (P.sU0 S) (P.j2 on0).rel (P.V2 S qa N on0).rel _ N
      (fun s p => P.E1.rd ((s.1.1.1, ya), fun a => (P.NW.om a).sy0) p) hU.good.exact
      hU.noHid (fun _ _ _ h => h.1)
      (fun x y w c ρ hV =>
        (ldk_send_run P.SdU P.X2 P.E1 S.dU x w.2 (P.wU S w.1) c ρ (hput x y w c.1 hV)).1)
      (fun x y w ρ T p _ hp => absurd hp (ldk_given_send _ _ _ _ _ _ _))
  · refine bearsV_shared P.X2 P.X3 P.E1 P.E3 P.sU N _ (fun _ => True)
      (P.NU.qFam (fun _ => True) S.tU) (P.qv1 S qa N) (P.qv3 S qa N)
      (ldSendFam_bears P.NU P.SdU P.X2 P.E1 S.tU _)
      (fun J Us h => ⟨trivial, fun a => (cnt_mono fun x hx => ?_).trans (h.2 a)⟩) fun J ρ Us h => ?_
    · obtain ⟨j, _, hj⟩ := ldSendP_mem_biUnion.1 hx
      exact ⟨j, hj⟩
    · have e : (fun j : J => P.sU.need (ρ.slot j.1) (Us j)) = fun j => (Us j).toLeft :=
        funext fun j => ldk_need_send _ _ _ _ _ _
      rw [e]
      exact h.1

omit [Fintype E] [Fintype ι] [Nonempty ι] in
theorem LdLinP.pvO [Fintype ι] (hS : S.OK) (hA : S.Apart) (ya : P.Ea.Str) : (P.lvO S qa N).PV := by
  have hO := ldSendFam_piece E P.NO P.SdO Unit P.X4 P.W4 P.W3 P.E4 P.j4 P.backO S.dO S.LO S.tO
    (fun _ => True) hS.lawsO hS.fairO hS.listO hS.evO hS.sndO hS.blO hS.hidO
  have hput : ∀ (x : P.X4) (y : P.E4.Str) (w : P.Sh4 × P.W4) k,
      (P.V4 S qa N).rel x y w → S.dO.put w.2 k = S.dO.put (P.wO S w.1) k := by
    intro x y w k hV
    refine hA.putO _ _ k ?_
    have h1 : w.2.1 = P.D.omOf (P.D.X.view w.2.2.2.2.1) x.1.1.2 := hV.1.2.2.2.2.2.2.2.2
    have h2 : w.2.2.2.2.1 = w.1.1.1.1.1.2 := hV.2.1.1.1.1
    have h3 : x.1.1.2 = w.1.1.1.2 := hV.2.1.1.2
    show w.2.1 = P.D.omOf (P.D.X.view w.1.1.1.1.1.2) w.1.1.1.2
    rw [h1, h2, h3]
  refine ⟨⟨hO.good.isLocal, ?_, ?_, ?_⟩, (ldLinV_her P S qa N).2.2.2.2⟩
  · refine accV_shared P.X4 P.X5 P.E4 P.E5 P.sO P.W4 P.W5 P.Sh4 P.Sh5
      (ldSendFamHon P.SdO P.X4 P.E4 S.dO) (P.sO0 S) P.j4.rel P.j5.rel (P.V4 S qa N).rel
      (P.V5 S qa N).rel hO.good.acc hO.noHid (fun _ _ _ h => h.1)
      (fun x y w c ρ hV =>
        (ldk_send_run P.SdO P.X4 P.E4 S.dO x w.2 (P.wO S w.1) c ρ (hput x y w c.1 hV)).1)
      (fun x y w c ρ hV _ hRo => ⟨hRo, ?_, ?_, ?_, ?_⟩)
    · have hr : S.dO.rest w.2 = w.2.2 := P.restO S hS.sndO w.2
      show ((((S.dO.rest w.2).2.2.1 = w.1.1.1.1.1.2 ∧ x.1.1.1.1.2 = w.1.1.1.1.2) ∧
            x.1.1.2 = w.1.1.1.2) ∧
          x.1.2 = w.1.1.2.1 ∧ y.2 = w.1.1.2.2.1 ∧
          (S.dO.rest w.2).1 = w.1.1.2.2.2) ∧
        x.2 = w.1.2
      rw [hr]
      exact hV.2
    · exact congrArg Prod.snd
        (ldk_send_run P.SdO P.X4 P.E4 S.dO x w.2 (P.wO S w.1) c ρ (hput x y w c.1 hV)).2.1
    · exact congrArg (fun τ : Tr (P.NO.sh P.SdO) => τ.1.1)
        (ldk_send_run P.SdO P.X4 P.E4 S.dO x w.2 (P.wO S w.1) c ρ (hput x y w c.1 hV)).1
    · exact (ldk_send_run P.SdO P.X4 P.E4 S.dO x w.2 (P.wO S w.1) c ρ (hput x y w c.1 hV)).2.2
  · exact exactV_shared P.X4 P.X5 P.E4 P.E5 P.sO P.W4 P.W5 P.Sh4 P.Sh5
      (ldSendFamHon P.SdO P.X4 P.E4 S.dO) (P.sO0 S) P.j4.rel (P.V4 S qa N).rel _ N
      (fun s p => P.E4.rd ((ya, fun a => (P.NW.om a).sy0), s.1.2.2.1) p)
      hO.good.exact hO.noHid (fun _ _ _ h => h.1)
      (fun x y w c ρ hV =>
        (ldk_send_run P.SdO P.X4 P.E4 S.dO x w.2 (P.wO S w.1) c ρ (hput x y w c.1 hV)).1)
      (fun x y w ρ T p _ hp => absurd hp (ldk_given_send _ _ _ _ _ _ _))
  · refine bearsV_shared P.X4 P.X5 P.E4 P.E5 P.sO N _ (fun _ => True)
      (P.NO.qFam (fun _ => True) S.tO) (P.qv4 S qa N) (P.qv5 S qa N)
      (ldSendFam_bears P.NO P.SdO P.X4 P.E4 S.tO _)
      (fun J Us h => ⟨trivial, fun a => (cnt_mono fun x hx => ?_).trans (h.2 a)⟩) fun J ρ Us h => ?_
    · obtain ⟨j, _, hj⟩ := ldSendP_mem_biUnion.1 hx
      exact ⟨j, hj⟩
    · have e : (fun j : J => P.sO.need (ρ.slot j.1) (Us j)) = fun j => (Us j).toLeft :=
        funext fun j => ldk_need_send _ _ _ _ _ _
      rw [e]
      exact h.1


/-! ### The locations -/

omit [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y] in
/-- what the locations need of the old oracles, component by component -/
theorem LdLinP.loc_mem (Q : Fin P.t → ι) (U : Finset P.E4.Pos) (V : Finset P.E3.Pos)
    (hm : ∀ p, p ∈ V ↔ (∃ i, p = .inl (.inl (.inl (Q i)))) ∨ ∃ u ∈ U, p ∈ P.dropIx.src u) :
    (∀ z, (Sum.inr z : P.E3.Pos) ∈ V ↔ (Sum.inr z : P.E4.Pos) ∈ U) ∧
    (∀ z, (Sum.inl (Sum.inr z) : P.E3.Pos) ∈ V ↔ (Sum.inl (Sum.inr z) : P.E4.Pos) ∈ U) ∧
    (∀ z, (Sum.inl (Sum.inl (Sum.inr z)) : P.E3.Pos) ∈ V ↔ (Sum.inl (Sum.inl z) : P.E4.Pos) ∈ U) ∧
    ∀ i, (Sum.inl (Sum.inl (Sum.inl i)) : P.E3.Pos) ∈ V ↔ ∃ k, i = Q k := by
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, fun i => ?_⟩
  · rw [hm]
    constructor
    · rintro (⟨i, hi⟩ | ⟨u, hu, hp⟩)
      · exact absurd hi (by simp)
      · rcases u with (u | u) | u
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · obtain rfl : z = u := Sum.inr.inj (Finset.mem_singleton.1 hp)
          exact hu
    · exact fun h => Or.inr ⟨_, h, Finset.mem_singleton_self _⟩
  · rw [hm]
    constructor
    · rintro (⟨i, hi⟩ | ⟨u, hu, hp⟩)
      · exact absurd hi (by simp)
      · rcases u with (u | u) | u
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · obtain rfl : z = u := Sum.inr.inj (Sum.inl.inj (Finset.mem_singleton.1 hp))
          exact hu
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
    · exact fun h => Or.inr ⟨_, h, Finset.mem_singleton_self _⟩
  · rw [hm]
    constructor
    · rintro (⟨i, hi⟩ | ⟨u, hu, hp⟩)
      · exact absurd hi (by simp)
      · rcases u with (u | u) | u
        · obtain rfl : z = u := Sum.inr.inj (Sum.inl.inj (Sum.inl.inj (Finset.mem_singleton.1 hp)))
          exact hu
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
    · exact fun h => Or.inr ⟨_, h, Finset.mem_singleton_self _⟩
  · rw [hm]
    constructor
    · rintro (⟨k, hk⟩ | ⟨u, hu, hp⟩)
      · exact ⟨k, Sum.inl.inj (Sum.inl.inj (Sum.inl.inj hk))⟩
      · rcases u with (u | u) | u
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
        · exact absurd (Finset.mem_singleton.1 hp) (by simp)
    · rintro ⟨k, rfl⟩
      exact Or.inl ⟨k, rfl⟩

omit [Fintype E] in
theorem LdLinP.pvLoc (ya : P.Ea.Str) : (P.lvLoc S qa N on0).PV := by
  classical
  have hL := ldk_pieceTr_cf (ldLin_loc P on0 S qa)
  refine ⟨⟨hL.good.isLocal, ?_, ?_, ?_⟩, (ldLinV_her P S qa N).2.2.2.1⟩
  · refine accV_shared P.X3 P.X4 P.E3 P.E4 P.loc P.W3 P.W4 P.Sh3 P.Sh4 P.hLoc P.sLoc0
      (P.j3 on0).rel P.j4.rel (P.V3 S qa N on0).rel (P.V4 S qa N).rel hL.good.acc hL.noHid
      (fun _ _ _ h => h.1) (fun _ _ _ _ _ _ => rfl) (fun x y w c ρ hV _ hRo =>
        ⟨hRo, ⟨⟨⟨hV.2.1.1.1.2, hV.2.1.1.2⟩, hV.2.1.2⟩, hV.2.2.1, hV.2.2.2.1, hV.2.2.2.2⟩, ?_⟩)
    have h2 : w.2.2.2.1 = w.1.1.1.1.2 := hV.2.1.1.1.2
    have h3 : x.1.2 = w.1.1.2 := hV.2.1.2
    show ((show (Fin P.t → ι) × Unit from ρ).1,
        fun i =>
          P.D.X.G.mulVec (foldAll x.1.2.1 w.2.2.2.1) ((show (Fin P.t → ι) × Unit from ρ).1 i)) =
      ((show (Fin P.t → ι) × Unit from ρ).1,
        fun i =>
          P.D.X.G.mulVec (foldAll w.1.1.2.1 w.1.1.1.1.2) ((show (Fin P.t → ι) × Unit from ρ).1 i))
    rw [h2, h3]
  · refine exactV_shared P.X3 P.X4 P.E3 P.E4 P.loc P.W3 P.W4 P.Sh3 P.Sh4 P.hLoc P.sLoc0
      (P.j3 on0).rel (P.V3 S qa N on0).rel _ N
      (fun s p => P.E3.rd (((s.1.1.1.1, ya), fun a => (P.NW.om a).sy0), s.2.2.1) p) hL.good.exact
      hL.noHid (fun _ _ _ h => h.1) (fun _ _ _ _ _ _ => rfl) (fun x y w ρ T p hV hp => ?_)
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ((ldk_mem_given_peek P.vLoc ρ T p).1 hp)
    have h1 : y.1.1.1 = w.1.1.1.1.1 := hV.2.1.1.1.1
    show (Sum.inl (Sum.inl (Sum.inl (y.1.1.1 _))) : P.E3.Sym) =
      Sum.inl (Sum.inl (Sum.inl (w.1.1.1.1.1 _)))
    rw [h1]
  · refine bearsV_shared P.X3 P.X4 P.E3 P.E4 P.loc N _ (fun _ => True) (fun _ => True)
      (P.qv3 S qa N) (P.qv4 S qa N) (ldk_bears_true _) (fun _ _ _ => trivial) fun J ρ Us h => ?_
    have hm : ∀ j : J, ∀ p,
        p ∈ P.loc.need (ρ.slot j.1) (Us j) ↔
        (∃ i, p = .inl
            (.inl (.inl
                ((show (Fin P.t → ι) × Unit from RhoSh.all P.loc.shape (BRho.shared ρ)).1 i)))) ∨
        ∃ u ∈ Us j, p ∈ P.dropIx.src u := by
      intro j p
      rw [BatchSeqZk.slot_eq ρ j.1]
      refine (ldk_mem_need_peek P.vLoc _ (Us j) p).trans (or_congr ?_ Iff.rfl)
      constructor
      · intro hp
        obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hp
        exact ⟨i, hi.symm⟩
      · rintro ⟨i, rfl⟩
        exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
    have hk := fun j : J => P.loc_mem _ (Us j) _ (hm j)
    refine ⟨⟨⟨fun T hT => ?_, fun j => ?_⟩, fun j a => ?_⟩, fun a => ?_⟩
    · have hsub : T ⊆
          Finset.univ.image
            (show (Fin P.t → ι) × Unit
              from RhoSh.all P.loc.shape (BRho.shared ρ)).1 := fun i hi => by
        obtain ⟨j, hj⟩ := hT i hi
        obtain ⟨k, hk'⟩ := ((hk j).2.2.2 i).1 (Finset.mem_toLeft.1 (Finset.mem_toLeft.1 hj))
        exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk'.symm⟩
      refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
      rw [Finset.card_univ, Fintype.card_fin]
    · have e : (P.loc.need (ρ.slot j.1) (Us j)).toLeft.toLeft.toRight = (Us j).toLeft.toLeft := by
        ext z
        rw [Finset.mem_toRight, Finset.mem_toLeft, Finset.mem_toLeft,
          Finset.mem_toLeft, Finset.mem_toLeft]
        exact (hk j).2.2.1 z
      rw [e]
      exact h.1.1 j
    · refine le_of_eq_of_le (cnt_congr fun x => ?_) (h.1.2 j a)
      rw [Finset.mem_toLeft, Finset.mem_toLeft]
      exact (hk j).2.1 ⟨a, x⟩
    · refine le_of_eq_of_le (cnt_congr fun x => exists_congr fun j => ?_) (h.2 a)
      exact (hk j).1 ⟨a, x⟩

end

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLinV_pv : Spec.ldLinV_pv E ι κ J Y := fun P on0 εf N S qa ya hF hpy hS hA =>
  ⟨P.pv0 on0 N qa, P.pvW on0 N S qa hS, P.pvPt on0 N S qa εf hF ya, P.pvU on0 N S qa hS hA ya,
    P.pvLoc on0 N S qa ya, P.pvO N S qa hS hA ya, P.pvZeta N S qa hpy ya⟩

theorem ldLinV_core : Spec.ldLinV_core E ι κ J Y := by
  intro P on0 εf N S qa ya hF hpy hS hA
  obtain ⟨h0, hW, hP, hU, hL, hO, hZ⟩ := ldLinV_pv P on0 εf N S qa ya hF hpy hS hA
  unfold LdLinP.chainV
  simp only [ChainV.allPV_snoc, ChainV.allPV_one]
  exact ⟨⟨⟨⟨⟨⟨h0, hW⟩, hP⟩, hU⟩, hL⟩, hO⟩, hZ⟩

end
end Cb
