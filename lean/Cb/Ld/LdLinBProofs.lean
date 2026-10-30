-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinBProofs.lean: the proofs of the statements of Cb/Ld/LdLinB.lean.

These statements are on, or (`knowB_peek`, `knowB_peek_key`, `ldLinB_send_shared`) are generic steps
toward, the test for linear constraints on the encoded index for at most N instances that share the
encoded index and its record: each under the hypotheses of its statement, round-by-round knowledge
soundness in the form `KnowB` (Ior/BatchSeq.lean), at the `adm` and `on` of its statement (limits:
the head of Cb/Ld/LdLinB.lean). A key is a function of the statement; a vector has one key if all
its statements agree under it (`SameKey`, Ior/BatchSeq.lean); admissible: the argument `adm` of
`KnowB`.

The counts are those of the one-instance proofs, but for the shared point's (`LdLinP.errPtB`: the
instances' term N times). Those proofs are in Cb/Ld/LdLinProofs.lean; for the sendings:
`ldSendFam_within`, Cb/Ld/LdSendFamProofs.lean. In the rounds without a prover message the counts
stand here as inclusions of bad sets.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinB
import Cb.Ld.LdLinProofsChain

set_option autoImplicit false

namespace Iop
open Prob IOR

/-! ## 1. Generic -/

/-- The first of the two parts of a transcript of a whole batch over two shapes in a row;
`ldk_sndB` is the second. -/
def ldk_fstB {N : ℕ} :
    {s t : Shape} → {A : RoundSplits s} → {A' : RoundSplits t} → BTr N (s ++ t) (RoundSplits.app A A') → BTr N s A
  | [], _, _, _, _ => ()
  | _ :: _, _, (_, _), _, (m, v, τ) => (m, v, ldk_fstB τ)

def ldk_sndB {N : ℕ} :
    {s t : Shape} → {A : RoundSplits s} → {A' : RoundSplits t} → BTr N (s ++ t) (RoundSplits.app A A') → BTr N t A'
  | [], _, _, _, τ => τ
  | _ :: _, _, (_, _), _, (_, _, τ) => ldk_sndB τ

theorem ldk_slot_fstB {N : ℕ} (j : Fin N) :
    ∀ {s t : Shape} {A : RoundSplits s} {A' : RoundSplits t} (τ : BTr N (s ++ t) (RoundSplits.app A A')),
      Tr.fst (τ.slot j) = (ldk_fstB τ).slot j
  | [], _, _, _, _ => rfl
  | _ :: _, _, (a, _), _, (m, v, τ) =>
    congrArg (fun z => (a.join m.1 (m.2 j), a.kind.slot v j, z)) (ldk_slot_fstB j τ)

theorem ldk_slot_sndB {N : ℕ} (j : Fin N) :
    ∀ {s t : Shape} {A : RoundSplits s} {A' : RoundSplits t} (τ : BTr N (s ++ t) (RoundSplits.app A A')),
      Tr.snd (s := s) (τ.slot j) = (ldk_sndB τ).slot j
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, _), _, (_, _, τ) => ldk_slot_sndB j τ

/-- What an admissible vector is taken to, along two links in a row. -/
theorem ldk_adm_seq {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} (R₁ : IOR X₁ E₁ X₂ E₂)
    (R₂ : IOR X₂ E₂ X₃ E₃) (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) {N : ℕ}
    {adm₁ : (Fin N → Option (X₁ × E₁.Str)) → Prop} {adm₂ : (Fin N → Option (X₂ × E₂.Str)) → Prop}
    {adm₃ : (Fin N → Option (X₃ × E₃.Str)) → Prop}
    (h₁ : ∀ a,
      adm₁ a → ∀ τ : BTr N R₁.shape A₁, adm₂ fun j => (a j).bind fun aj => R₁.red.out aj (τ.slot j))
    (h₂ : ∀ a, adm₂ a →
      ∀ τ : BTr N R₂.shape A₂, adm₃ fun j => (a j).bind fun aj => R₂.red.out aj (τ.slot j)) :
    ∀ a, adm₁ a →
      ∀ τ : BTr N (R₁.seq R₂).shape (RoundSplits.app A₁ A₂),
        adm₃ fun j => (a j).bind fun aj => (R₁.seq R₂).red.out aj (τ.slot j) := by
  intro a ha τ
  have h := h₂ _ (h₁ a ha (ldk_fstB τ)) (ldk_sndB τ)
  refine cast (congrArg adm₃ (funext fun j => ?_)) h
  rw [Option.bind_assoc]
  refine congrArg (a j).bind (funext fun aj => ?_)
  rw [IOR.red_seq_out, ← ldk_slot_fstB, ← ldk_slot_sndB]
  rfl

/-- What the verifier of a round without a prover message outputs. -/
theorem ldk_peek_out {Xi Xo : Type} {Ei Eo : ExtSpec} (V : PeekV Xi Ei Xo Eo)
    (a : Xi × Ei.Str) (τ : Tr [drawRound V.D]) :
    (IOR.peek V).red.out a τ = some (V.nx a.1 a.2 (drawn τ), V.g.map a.2) := rfl

theorem knowB_peek : Spec.knowB_peek := by
  classical
  intro K Xi Xo Ei Eo Wi Wo V back A B N err adm hon hcnt
  refine ⟨fun a =>
      ((fun _ =>
          {c | A.on a ∧ ∃ w', B.relR (V.nx a.1 a.2 c, V.g.map a.2) w' ∧ ¬ A.relR a (back a c w')},
        fun _ _ => ()) : BadFam [drawRound V.D]),
    ?_, ?_⟩
  · intro a τ b w' _ hc hb hw'
    obtain rfl : _ = b := Option.some.inj ((ldk_peek_out V a τ).symm.trans hb)
    by_cases ha : A.on a
    · refine Or.inl ?_
      by_contra hn
      rcases hw' with hw' | hoff
      · exact hc.1 ⟨ha, w', hw', hn⟩
      · exact hoff (hon a.1 a.2 _ ha)
    · exact Or.inr ha
  · intro a ha m0 m
    refine ⟨?_, fun _ => trivial⟩
    refine le_trans (cnt_mono ?_) (hcnt a ha)
    rintro c ⟨j, p, hp, -, hc⟩
    obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
    exact ⟨j, aj, haj, hc⟩

theorem knowB_peek_key : Spec.knowB_peek_key := by
  intro K Xi Xo κ Ei Eo Wi Wo V back A B N err key Bk hon hB hsub
  refine knowB_peek K Xi Xo Ei Eo Wi Wo V back A B N err (SameKey key) hon fun a ha => ?_
  by_cases hne : ∃ j aj, a j = some aj
  · obtain ⟨j₀, a₀, h₀⟩ := hne
    refine le_trans (cnt_mono ?_) (hB (key a₀))
    rintro c ⟨j, aj, haj, hon', w', hw', hn⟩
    rw [← ha j j₀ aj a₀ haj h₀]
    exact hsub aj c w' hon' hw' hn
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro c ⟨j, aj, haj, -⟩
      exact hne ⟨j, aj, haj⟩

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E : Type} [Field E]

theorem ldLinB_send_shared : Spec.ldLinB_send_shared E := by
  intro M Sd X W W' E₀ A back L t N hF hL hE
  refine knowB_conseq _ _ _ _ _ _ _ _ N (SameKey fun _ => ()) (fun _ => True) (fun _ => True)
    (fun _ => True) _ _ _ _ _ _ ?_ (fun _ _ _ _ _ _ _ _ => rfl) (fun _ h => h)
    (fun _ _ _ h => h) (fun _ _ h => h)
  refine knowB_of_key X (X × M.Smp) Unit E₀ (E₀.prod M.ext) W (M.Wit × W') (ldSendFam M Sd X E₀) N
    (fun _ => ()) (fun _ => ldSendFamBad M Sd) (fun _ => True) A.cf.relR
    (M.over (M.pull A back)).cf.relR _ _ (fun _ => ldSendFam_within E M Sd L hF hL hE) ?_
  intro a τ b w _ hτ hb hw
  by_cases ha : A.on a
  · rcases hw with hw | hoff
    · exact Or.inl (ldSendFam_back E M Sd Unit X W W' E₀ A back a τ b w hb hw)
    · exact absurd (ldSendFam_out_on E M Sd Unit X W W' E₀ A back a τ b ha hτ hb) hoff
  · exact Or.inr ha

end
end Cb

/-! ## 2. The links of the test -/

namespace Iop
open IOR

/-- All members of the image of a vector with one key have one key, if the new key is one and the
same function `F` of the old in all slots. -/
theorem ldk_sameKey_bind {α β κ κ' : Type} {N : ℕ} {key : α → κ} {key' : β → κ'}
    {a : Fin N → Option α} (out : Fin N → α → Option β) (F : κ → κ')
    (h : ∀ j aj b, out j aj = some b → key' b = F (key aj)) (ha : SameKey key a) :
    SameKey key' fun j => (a j).bind (out j) := by
  intro j j' b b' hb hb'
  obtain ⟨aj, haj, ho⟩ := Option.bind_eq_some_iff.1 hb
  obtain ⟨aj', haj', ho'⟩ := Option.bind_eq_some_iff.1 hb'
  rw [h j aj b ho, h j' aj' b' ho', ha j j' aj aj' haj haj']

/-- A link of a chain in a batch, with keys: knowledge sound for the vectors with one key, and it
takes such vectors to vectors with one key. -/
structure ldk_LinkB {Xi Xo κ κ' : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} (R : IOR Xi Ei Xo Eo)
    (A : RoundSplits R.shape) (N : ℕ) (key : Xi × Ei.Str → κ) (key' : Xo × Eo.Str → κ')
    (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
    (ext : Xi × Ei.Str → Tr R.shape → Wo → Wi) (ε : Err R.shape) : Prop where
  know : R.KnowB A N (SameKey key) (fun _ => True) RA RB ext ε
  adm  : ∀ a, SameKey key a →
    ∀ τ : BTr N R.shape A, SameKey key' fun j => (a j).bind fun aj => R.red.out aj (τ.slot j)

theorem ldk_linkB_seq {X₁ X₂ X₃ κ₁ κ₂ κ₃ : Type} {E₁ E₂ E₃ : ExtSpec} {W₁ W₂ W₃ : Type}
    {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {A₁ : RoundSplits R₁.shape} {A₂ : RoundSplits R₂.shape} {N : ℕ}
    {k₁ : X₁ × E₁.Str → κ₁} {k₂ : X₂ × E₂.Str → κ₂} {k₃ : X₃ × E₃.Str → κ₃}
    {RA : X₁ × E₁.Str → W₁ → Prop} {RB : X₂ × E₂.Str → W₂ → Prop} {RC : X₃ × E₃.Str → W₃ → Prop}
    {e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁} {e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂}
    {ε₁ : Err R₁.shape} {ε₂ : Err R₂.shape} (d : W₁) (h₁ : ldk_LinkB R₁ A₁ N k₁ k₂ RA RB e₁ ε₁)
    (h₂ : ldk_LinkB R₂ A₂ N k₂ k₃ RB RC e₂ ε₂) :
    ldk_LinkB (R₁.seq R₂) (RoundSplits.app A₁ A₂) N k₁ k₃ RA RC
      (IOR.extSeq R₁ R₂ e₁ e₂ d) (Err.app ε₁ ε₂) :=
  ⟨knowB_seq _ _ _ _ _ _ _ _ _ R₁ R₂ A₁ A₂ N _ _ _ _ RA RB RC e₁ e₂ ε₁ ε₂ d h₁.know h₂.know
      (fun _ _ _ _ _ => trivial) h₁.adm,
    ldk_adm_seq R₁ R₂ A₁ A₂ h₁.adm h₂.adm⟩

/-- `KnowB` with every vector admissible gives `KnowB` with any `adm'`. -/
theorem ldk_knowB_adm {Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {A : RoundSplits R.shape} {N : ℕ} (adm' : (Fin N → Option (Xi × Ei.Str)) → Prop)
    {RA : Xi × Ei.Str → Wi → Prop} {RB : Xo × Eo.Str → Wo → Prop}
    {ext : Xi × Ei.Str → Tr R.shape → Wo → Wi} {ε : Err R.shape}
    (h : R.KnowB A N (fun _ => True) (fun _ => True) RA RB ext ε) :
    R.KnowB A N adm' (fun _ => True) RA RB ext ε :=
  knowB_conseq _ _ _ _ _ _ R A N _ adm' _ _ _ _ _ _ ext ε h (fun _ _ => trivial) (fun _ h => h)
    (fun _ _ _ h => h) (fun _ _ h => h)

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (N : ℕ)

omit [Fintype E] [Nonempty ι] in
theorem LdLinP.link0 :
    ldk_LinkB P.step0 (RoundSplits.allLocal _) N P.k0 P.k0 (P.j0 on0).cf.relR (P.jA on0).cf.relR
      (fun _ _ w => w.2) () :=
  ⟨ldk_knowB_adm _
      (knowB_local _ _ _ _ _ _ P.step0 RAnn.allLocal (fun _ => rfl) N _ _ _ _ _
        (ldk_pieceTr_cf (ldLin_step0 P on0 fun _ => True)).good.know),
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.step0.red.out aj (τ.slot j)) id
        (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩

omit [Fintype E] [Nonempty ι] in
theorem LdLinP.linkW (S : P.Snd) (hS : S.OK) :
    ldk_LinkB P.sW (RoundSplits.allLocal _) N P.k0 P.k1 (P.jA on0).cf.relR (P.j1 on0).cf.relR
      (fun _ _ w => P.backW (P.NW.msgs w.1) w.2)
      (ldSendFamNums P.NW P.SdW P.X0 P.E0 Unit S.LW S.tW).err :=
  ⟨ldk_knowB_adm _
      (knowB_local _ _ _ _ _ _ P.sW RAnn.allLocal (fun _ => rfl) N _ _ _ _ _
        (ldSendFam_piece E P.NW P.SdW Unit P.X0 P.WA P.W0 P.E0 (P.jA on0) P.backW S.dW S.LW S.tW
          (fun _ => True) hS.lawsW hS.fairW hS.listW hS.evW hS.sndW hS.blW hS.hidW).good.know),
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.sW.red.out aj (τ.slot j)) id
        (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩

omit [Nonempty ι] in
theorem LdLinP.linkPt (εf : ℕ) (hF : P.FoldErr on0 εf) :
    ldk_LinkB P.pt (shAnn _) N P.k1 P.k2 (P.j1 on0).cf.relR (P.j2 on0).cf.relR
      (fun _ _ w => w.2) ((P.errPtB εf N, ()) : ℕ × Unit) := by
  classical
  refine ⟨knowB_peek Unit P.X1 P.X2 P.E1 P.E1 P.W1 P.W2 P.vPt (fun _ _ w => w.2) (P.j1 on0)
      (P.j2 on0) N (P.errPtB εf N) (SameKey P.k1) (fun x y c h => h) fun a ha => ?_,
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.pt.red.out aj (τ.slot j)) (fun k => (k, τ.2.1))
        (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩
  by_cases hne : ∃ j aj, a j = some aj ∧ (P.j1 on0).on aj
  · obtain ⟨j₀, a₀, h₀, hon₀⟩ := hne
    have hf : cnt (P.D.X.Bad (P.tab a₀.2.1.1) a₀.1.1.2 P.e') ≤ εf := hF _ _ hon₀.2.1
    refine le_trans (cnt_mono fun c hc => ?_)
      (ldk_cnt_badSh P.D (N := N) (P.tab a₀.2.1.1) a₀.1.1.2
        (fun j =>
          (a j).bind fun aj =>
            if h : ∃ m,
              P.NW.DecTo aj.1.2 aj.2.2 m then some (P.g aj.1.1.1, P.wv h.choose) else none) hf)
    obtain ⟨j, aj, haj, -, w', ⟨hd, haa, hev, hn, hr, hdot⟩, hnot⟩ := hc
    have hk : P.k1 aj = P.k1 a₀ := ha j j₀ aj a₀ haj h₀
    have hk' : (aj.2.1.1, aj.1.1.2) = (a₀.2.1.1, a₀.1.1.2) := hk
    have hk1 : aj.2.1.1 = a₀.2.1.1 := (Prod.mk.inj hk').1
    have hk2 : aj.1.1.2 = a₀.1.1.2 := (Prod.mk.inj hk').2
    by_contra hbad
    refine hnot
      ⟨hd, haa,
        P.pt_back aj.1.1 (P.tab aj.2.1.1) w'.2.2.2 _ c w'.1 (fun h1 => hbad ?_) hev hn hr hdot⟩
    rw [← hk1, ← hk2]
    rcases h1 with h1 | ⟨U, hU, _, gw, hgw, hb⟩
    · exact Or.inl h1
    · refine Or.inr ⟨U, hU, j, gw, ?_, hb⟩
      show ((a j).bind fun aj =>
          if h : ∃ m,
            P.NW.DecTo aj.1.2 aj.2.2 m then some (P.g aj.1.1.1, P.wv h.choose) else none) = some gw
      have hd' : P.NW.DecTo aj.1.2 aj.2.2 (P.NW.msgs w'.2.1) := hd
      have hex : ∃ m, P.NW.DecTo aj.1.2 aj.2.2 m := ⟨_, hd'⟩
      rw [haj, Option.bind_some, dif_pos hex, hex.choose_spec.unique hd']
      exact hgw
  · rw [cnt_false]
    · exact Nat.zero_le _
    · rintro c ⟨j, aj, haj, hon, -⟩
      exact hne ⟨j, aj, haj, hon⟩

omit [Fintype E] [Nonempty ι] in
theorem LdLinP.linkU (S : P.Snd) (hS : S.OK) :
    ldk_LinkB P.sU (shAnn _) N P.k2 P.k3 (P.j2 on0).cf.relR (P.j3 on0).cf.relR
      (fun _ _ w => P.backU (P.NU.msgs w.1) w.2)
      (ldSendFamNums P.NU P.SdU P.X2 P.E1 Unit S.LU S.tU).err :=
  ⟨ldk_knowB_adm _
      (ldLinB_send_shared P.NU P.SdU P.X2 P.W2 P.W1 P.E1 (P.j2 on0)
        P.backU S.LU S.tU N hS.fairU hS.listU hS.evU),
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.sU.red.out aj (τ.slot j))
        (fun k => (k, ((fun a => (P.SdU.sd a τ.2.1, τ.2.2.1.1.2 a)), τ.1.1.1)))
        (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩

omit [Fintype E] in
theorem LdLinP.linkLoc :
    ldk_LinkB P.loc (shAnn _) N P.k3 P.k4 (P.j3 on0).cf.relR P.j4.cf.relR
      (fun _ _ w => w.2) ((P.errLoc, ()) : ℕ × Unit) := by
  classical
  refine ⟨knowB_peek_key Unit P.X3 P.X4 _ P.E3 P.E4 P.W3 P.W4 P.vLoc (fun _ _ w => w.2)
      (P.j3 on0) P.j4 N P.errLoc P.k3
      (fun k Q =>
        ∃ mU,
          P.NU.DecTo k.2.1 k.2.2 mU ∧
          ¬ P.D.X.NearW P.e' (foldAll k.1.2.1 (P.tab k.1.1.1)) (P.uv mU) ∧
          ∀ i, P.D.X.G.mulVec (P.uv mU) (Q i) = foldAll k.1.2.1 (P.tab k.1.1.1) (Q i))
      ?_ ?_ ?_,
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.loc.red.out aj (τ.slot j))
        (fun k =>
          (((k.1.1.2, k.1.2), k.2), (τ.2.1, fun i => foldAll k.1.2.1 (P.tab k.1.1.1) (τ.2.1 i))))
        (fun j aj b h => ?_) ha⟩
  · intro x y Q h
    rw [P.loc_nx]
    exact ⟨h.2.2.2, h.2.1, h.1⟩
  · intro k
    refine cnt_exists_unique_le (P := fun mU => P.NU.DecTo k.2.1 k.2.2 mU)
      (fun _ _ hb hb' => hb.unique hb') fun mU _ => ?_
    exact cnt_and_le fun hn => P.D.X.cnt_far_lists P.t hn
  · intro a Q w' _ h hnot
    rw [P.loc_nx] at h
    obtain ⟨hdU, hdW, haa, hev, hrec, hdot, hcol⟩ := h
    exact ⟨P.NU.msgs w'.2.1, hdU, fun hn => hnot ⟨hdU, hdW, haa, hev, hn, hrec, hdot⟩, hcol⟩
  · have h' : some (P.vLoc.nx aj.1 aj.2 τ.2.1, P.dropIx.map aj.2) = some b := h
    rw [P.loc_nx] at h'
    obtain rfl := Option.some.inj h'
    rfl

omit [Fintype E] [Fintype ι] [Nonempty ι] in
theorem LdLinP.linkO (S : P.Snd) (hS : S.OK) :
    ldk_LinkB P.sO (shAnn _) N P.k4 P.k5 P.j4.cf.relR P.j5.cf.relR
      (fun _ _ w => P.backO (P.NO.msgs w.1) w.2)
      (ldSendFamNums P.NO P.SdO P.X4 P.E4 Unit S.LO S.tO).err :=
  ⟨ldk_knowB_adm _
      (ldLinB_send_shared P.NO P.SdO P.X4 P.W4 P.W3 P.E4 P.j4 P.backO S.LO S.tO N
        hS.fairO hS.listO hS.evO),
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.sO.red.out aj (τ.slot j))
        (fun k => (k, ((fun a => (P.SdO.sd a τ.2.1, τ.2.2.1.1.2 a)), τ.1.1.1)))
        (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩

omit [Fintype ι] [Nonempty ι] in
theorem LdLinP.linkZeta [Fintype ι] (hpy : Function.Injective P.D.py) :
    ldk_LinkB P.zeta (shAnn _) N P.k5 P.k6 P.j5.cf.relR P.j6.cf.relR
      (fun _ _ w => w) ((P.errZeta, ()) : ℕ × Unit) := by
  classical
  refine ⟨knowB_peek_key Unit P.X5 P.X6 _ P.E5 P.E5 P.W5 P.W5 P.vZeta (fun _ _ w => w)
      P.j5 P.j6 N P.errZeta P.k5
      (fun k ζ =>
        ∃ mO,
          P.NO.DecTo k.2.1 k.2.2 mO ∧
          ∃ mU,
            P.NU.DecTo k.1.1.2.1 k.1.1.2.2 mU ∧
            P.D.BadZeta (P.D.X.msg (P.uv mU)) k.1.1.1.2.2 (P.ov mO) ζ)
      (fun x y c h => h) ?_ ?_,
    fun _ ha τ =>
      ldk_sameKey_bind (fun j aj => P.zeta.red.out aj (τ.slot j)) (fun k => (k, τ.2.1))
        (fun _ _ _ h => by obtain rfl := Option.some.inj h; rfl) ha⟩
  · intro k
    refine cnt_exists_unique_le (P := fun mO => P.NO.DecTo k.2.1 k.2.2 mO)
      (fun _ _ hb hb' => hb.unique hb') fun mO _ => ?_
    refine cnt_exists_unique_le (P := fun mU => P.NU.DecTo k.1.1.2.1 k.1.1.2.2 mU)
      (fun _ _ hb hb' => hb.unique hb') fun mU _ => ?_
    exact ldLin_cnt_zeta P.D _ _ _ hpy
  · intro a c w' _ h hnot
    obtain ⟨hdO, hdU, hdW, haa, hrec, hcol, hfold, hev, hdot⟩ := h
    refine ⟨P.NO.msgs w'.1, hdO, P.NU.msgs w'.2.1, hdU,
      fun hom => hnot ⟨hdO, hdU, hdW, haa, hev, hrec, ?_, hcol⟩, hfold⟩
    have hom' : P.ov (P.NO.msgs w'.1) =
        P.D.omU (P.D.X.msg (P.uv (P.NU.msgs w'.2.1))) a.1.1.1.1.2.2 := hom
    show P.D.Dot (P.g a.1.1.1.1.1.1.1) (P.D.omU (P.D.X.msg (P.uv (P.NU.msgs w'.2.1))) a.1.1.1.1.2.2)
      a.1.1.1.1.2 (P.wv (P.NW.msgs w'.2.2.1))
    rw [← hom']
    exact hdot

end

section
variable {E : Type} [Field E] {ι κ J Y : Type} [Fintype E] [Fintype ι] [Nonempty ι]
  [Fintype κ] [Fintype J] [Fintype Y]

theorem LdLinP.linkCore (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (εf N : ℕ) (S : P.Snd) (d : P.W0 × P.WA × P.W1 × P.W2 × P.W3 × P.W4) (hF : P.FoldErr on0 εf)
    (hpy : Function.Injective P.D.py) (hS : S.OK) :
    ldk_LinkB P.core P.annCore N P.k0 P.k6 (P.j0 on0).cf.relR P.j6.cf.relR
      (P.extCore d) (P.errCoreB S εf N) :=
  ldk_linkB_seq d.1 (P.link0 on0 N)
    (ldk_linkB_seq d.2.1 (P.linkW on0 N S hS)
      (ldk_linkB_seq d.2.2.1 (P.linkPt on0 N εf hF)
        (ldk_linkB_seq d.2.2.2.1 (P.linkU on0 N S hS)
          (ldk_linkB_seq d.2.2.2.2.1 (P.linkLoc on0 N)
            (ldk_linkB_seq d.2.2.2.2.2 (P.linkO N S hS) (P.linkZeta N hpy))))))

theorem ldLinB_core : Spec.ldLinB_core E ι κ J Y := fun P on0 εf N S d hF hpy hS =>
  ⟨(P.linkCore on0 εf N S d hF hpy hS).know, (P.linkCore on0 εf N S d hF hpy hS).adm⟩

theorem ldLinB_know : Spec.ldLinB_know E ι κ J Y := by
  intro P on0 εf N S d Z aT εT hF hpy hS hT
  have hc := P.linkCore on0 εf N S d hF hpy hS
  have h := knowB_seq _ _ _ _ _ _ _ _ _ P.core Z.T P.annCore aT N _ _ _ _ _ _ _ (P.extCore d)
    Z.ext _ εT d.1 hc.know hT (fun _ _ _ _ _ => trivial) hc.adm
  exact (knowB_iff_orOff _ _ _ _ _ _ (P.lin Z) (P.annLin Z aT) N _ (P.j0 on0).on
    (P.j0 on0).relR _ (P.extLin Z d) _).2 h

end
end Cb
