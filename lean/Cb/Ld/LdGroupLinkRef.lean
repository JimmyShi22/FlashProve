-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupLinkRef.lean: this file states, of the group's own link bridge-to-fold in the
parameters in which the reference request asks for a closing's link: its format; the clauses on
demands; and "it reads the group's members only and hands the rest on" (said of the honest prover's
witness: see `ldGroup_link_run` under "Main names").

In standard terms: the link bridge-to-fold (`Hd.link ..`, Cb/Ld/LdGroupSeg.lean) is a batching round
and a fold on several oracle messages, as one step of a chain of reductions, with its honest side,
extractor and numbers. A link has the format (`Link.Fmt`, Cb/Req1/LdReqFormat.lean) between a format
at its input joint and one at its output joint, each with its demand.

Statements as theorems, proofs: wiring of Cb/Ld/LdGroupNewFmt.lean, Cb/Ld/LdGroupFold.lean,
Cb/Ld/LdGroupBlind.lean; `qFam_sum_le` has a proof of its own. Nothing of a text is rendered here.
In all statements on the link the group's set of common long positions, `G.P`, is nonempty, and
every oracle message is a member of the group or kept (hc) (the link needs both);
`ldGroup_qSrc_sum3` has the first alone.

Why: the reference request (Cb/Req1/LdReqRef*.lean) takes each closing's link as a parameter and
asks of it: hypotheses (Cb/Req1/LdReqProtoStd.lean: met at (`Hd.foldD ..`, `Hd.link ..`) under the
premises of `Spec.ldReqProtoStd_selfFold`), a format with three clauses on demands
(Cb/Req1/LdReqRefFmtL.lean: `S.FmtAt`), two clauses on its honest prover (Cb/Req1/LdReqRefLay.lean:
`ldReqRefLay_cross`), errors, as probabilities, at most a number (Cb/Ld/LdGroupLinkBelow.lean). This
file has the second and the third, at the term `Hd.link ..` (Cb/Ld/LdGroupSeg.lean), each under the
hypotheses named below.

Main names:
  `qFam_sum_le`: a bound on each member of two families side by side gives "the old part; at most t
    a of each new member" (`Sig.qSum`), under hq (q holds wherever the bound on the old family does)
    and ht (the bound on a new member a is at most t a).
  `Hd.qMid .. q₂ t`: the demand after the link: at most t long positions of the folded word; of what
    is carried: q₂, nothing of the held messages.
  `ldGroup_link_fmt_le`: under hS, hY, hZ, hLi, hF (hypotheses of `Spec.ldGroup_fold`,
    Cb/Ld/LdGroupFold.lean), the link has the format from any source demand qi that holds wherever
    `Hd.qSrc .. q₂ t` does.
  `ldGroup_fmtAt`: under hq, hS, hY, hZ, hLi, hF as in `ldGroup_link_fmt_le`, the three clauses on
    demands of `S.FmtAt`, for any second half Q with Q.t ≤ t.
  `ldGroup_qSrc_sum3`: the source demand of `S.FmtAt`, in numbers, under the hypotheses of its
    statement.
  `ldGroup_link_run`, `ldGroup_link_carry`: two witnesses with the same pairs of the group's members
    give, at the same explicit part, coins and verifier messages, the same transcript, the same new
    explicit part, the same pair of the folded word; what is carried is handed on as it is.

Limits: this file says nothing on the transport along the equation (D, l) = (Hd.foldD .., Hd.link
..). (For the two clauses on the honest prover: `ldReqRefLayStd_link`, Cb/Req1/LdReqRefLayStd.lean;
for the hypotheses: `ldReqProtoStd_fold`, Cb/Req1/LdReqProtoStd.lean.)

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewFmt
import Cb.Ld.LdGroupBlind

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

/-! ## 1. A bound on each member of two families side by side, as "the old part; the new members" -/

open Classical in
theorem qFam_sum_le {E : Type} [Field E] (S N : Sig E) {E₀ : ExtSpec} (q₀ : Finset E₀.Pos → Prop)
    (b : (S.sum N).O → ℕ) (q : Finset (E₀.prod S.ext).Pos → Prop) (t : N.O → ℕ)
    (hq : ∀ V, S.qFam q₀ (fun a => b (.inl a)) V → q V) (ht : ∀ a, b (.inr a) ≤ t a)
    (U : Finset (E₀.prod (S.sum N).ext).Pos) (hU : (S.sum N).qFam q₀ b U) : S.qSum N q t U := by
  refine ⟨fun V hV => hq V ⟨?_, fun a => le_trans (cnt_mono fun x hx => ?_) (hU.2 (.inl a))⟩,
    fun a => (hU.2 (.inr a)).trans (ht a)⟩
  · have e : V.toLeft = U.toLeft := Finset.ext fun p => by
      rw [Finset.mem_toLeft, Finset.mem_toLeft, hV]
      constructor
      · rintro ⟨u, hu, hs⟩
        rcases u with p' | ⟨a | a, x⟩
        · obtain rfl : p = p' := Sum.inl.inj (Sum.inl.inj (Finset.mem_singleton.1 hs))
          exact hu
        · cases Sum.inl.inj (Finset.mem_singleton.1 hs)
        · cases Finset.mem_singleton.1 hs
      · exact fun hp => ⟨.inl p, hp, Finset.mem_singleton_self _⟩
    rw [e]
    exact hU.1
  · obtain ⟨u, hu, hs⟩ := (hV _).1 hx
    rcases u with p' | ⟨a' | a', x'⟩
    · cases Sum.inl.inj (Finset.mem_singleton.1 hs)
    · obtain ⟨ha, hz⟩ := Sigma.mk.inj (Sum.inr.inj (Sum.inl.inj (Finset.mem_singleton.1 hs)))
      subst ha
      obtain rfl := eq_of_heq hz
      exact hu
    · cases Finset.mem_singleton.1 hs

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type)
  (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) {St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) {E0 : ExtSpec} {Rc Pw : Type} (i : IxAt E0 E₀)
  (rc : St₀ → Rc) (px : Wp → Pw) (q₂ : Finset (E₀.prod (Hd.foldD Sb sl Z A₀).S₂.ext).Pos → Prop)
  (hc : ∀ o, G.mem o ∨ kp o) (dw : S.Wit × Wp) (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ)

/-! ## 2. The formats, in the parameters of a reference segment -/

/-- the demand on (the folded word, what is carried) after the link -/
abbrev GHeld.qMid : Finset (Hd.foldD Sb sl Z A₀).mid.E.Pos → Prop :=
  besideQ (fun X : Finset Sh.Cf.ext.Pos => X.card ≤ t) ((Hd.foldD Sb sl Z A₀).qCar q₂)

open Classical in
/-- For `G.P` nonempty and under `hc`, `hS`, `hY`, `hZ`, `hLi`, `hF`: the link has the format from
any demand that holds of the sources of what it needs (`hq`). -/
theorem ldGroup_link_fmt_le (qi : Finset (Hd.foldD Sb sl Z A₀).src.Ex.Pos → Prop)
    (hq : ∀ W, Hd.qSrc Sb sl Z A₀ q₂ t W → qi W) (hS : Sh.OK) (hY : Sh.par.Hyp d G.e t Lst mC mS mW)
    (hZ : Z.OK) (hLi : G.C.ListAt G.e L) (hF : G.Fits) :
    (Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).Fmt
      ((Hd.foldD Sb sl Z A₀).src.fmt i (fun st => rc st.2) px qi)
      ((Hd.foldD Sb sl Z A₀).fmtMid i rc px (Hd.qMid Sb sl Z A₀ q₂ t)) where
  idx := ldFmt_run_idx E B _ S G kp Sb sl Z _ _ _ _ i
  pass := ldFmt_run_pass E B _ _ S G kp Sb sl Z _ _ _ rc
  hands := ldFmt_run_hands E B _ _ _ S G kp Sb sl Z _ _ _ px _
  bears := (ldGroup_fold E B Kc _ _ S G Sh kp Sb sl Z L _ A₀ hc dw d t Lst mC mS mW qi
    ((Hd.foldD Sb sl Z A₀).qCar q₂) hS hY hZ hLi hF fun U hU =>
      hq _ ⟨U, hU, Finset.ext fun _ => (mem_biUnion_at _).trans (mem_biUnion_at _).symm⟩).1.bears

open Classical in
/-- The three clauses on demands of a reference segment's format, at the group's own link and any
second half Q with Q.t ≤ t. (not all hypotheses are named here: see the statement below) -/
theorem ldGroup_fmtAt (Q : LdCloseD (Hd.foldD Sb sl Z A₀))
    (qi : Finset (Hd.foldD Sb sl Z A₀).src.Ex.Pos → Prop)
    (hq : ∀ W, Hd.qSrc Sb sl Z A₀ q₂ t W → qi W) (hS : Sh.OK) (hY : Sh.par.Hyp d G.e t Lst mC mS mW)
    (hZ : Z.OK) (hLi : G.C.ListAt G.e L) (hF : G.Fits) (ht : Q.t ≤ t) :
    (Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).Fmt
      ((Hd.foldD Sb sl Z A₀).src.fmt i (fun st => rc st.2) px qi)
      ((Hd.foldD Sb sl Z A₀).fmtMid i rc px (Hd.qMid Sb sl Z A₀ q₂ t)) ∧
    (∀ U V, (∀ x, x ∈ V ↔ ∃ u ∈ U, x ∈ (Hd.foldD Sb sl Z A₀).pE.src u) →
      (Hd.foldD Sb sl Z A₀).qOpen q₂ Q.t U → Hd.qMid Sb sl Z A₀ q₂ t V) ∧
    (∀ ρ' U, (Hd.foldD Sb sl Z A₀).S₂.qSum Q.N (E₀ := E₀) q₂ Q.tN U →
      (Hd.foldD Sb sl Z A₀).tgt.S.qSum
        Q.N ((Hd.foldD Sb sl Z A₀).qOpen q₂ Q.t) Q.tN (Q.loc.link.R.need ρ' U)) :=
  ⟨ldGroup_link_fmt_le Hd Sb sl Z A₀ i rc px q₂ hc dw d t Lst mC mS mW L qi hq hS hY hZ hLi hF,
    fun U V hV hU => (Hd.foldD Sb sl Z A₀).open_need q₂ Q.t t ht U V hV hU,
    fun ρ' U hU => LdCloseD.loc_need _ q₂ Q ρ' U hU⟩

/-! ## 3. Of its witness, the link's honest prover reads the group's members only, and hands the
rest on -/

theorem ldGroup_link_run (w w' : (Hd.foldD Sb sl Z A₀).src.J.W) (x) (c)
    (ρ) (h : G.wit w'.1 = G.wit w.1) :
    (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w' x c).run ρ).1 =
      (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w x c).run ρ).1 ∧
    (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w' x c).run ρ).2.1 =
      (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w x c).run ρ).2.1 ∧
    (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w' x c).run ρ).2.2.1 =
      (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w x c).run ρ).2.2.1 :=
  ldGroup_blind_run E B St₀ Wp S G kp Sb sl Z E₀ _ (Sh.block Sb sl Z d t Lst mC mS mW) w w' x c ρ h

theorem ldGroup_link_carry (w : (Hd.foldD Sb sl Z A₀).src.J.W) (x) (c) (ρ) :
    (((Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).H.strat w x c).run ρ).2.2.2 =
      (S.res (T := OMsg.Wit) kp w.1, w.2) :=
  ldGroup_blind_carry E B St₀ Wp S G kp Sb sl Z E₀ _ (Sh.block Sb sl Z d t Lst mC mS mW) w x c ρ

end

/-! ## 4. The source demand of a reference segment: a family and the body's two sendings -/

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S₀ N N' : Sig E}
  {G : Grp ((S₀.sum N).sum N')} [Nonempty G.P] {Sh : GShape G} {kp : ((S₀.sum N).sum N').O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
  (Z : Evader E (G.Row B)) {St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((((S₀.sum N).sum N').sub kp).Msg × Wp))
  (q₂ : Finset (E₀.prod (Hd.foldD Sb sl Z A₀).S₂.ext).Pos → Prop) (t : ℕ)

open Classical in
/-- Under the hypotheses of its statement: what the link needs is within what the body's two
sendings bear, and a bound on each member of the first family: in numbers. -/
theorem ldGroup_qSrc_sum3 (q₀ : Finset E₀.Pos → Prop) (b₂ : (Hd.foldD Sb sl Z A₀).S₂.O → ℕ)
    (h2 : ∀ U₂, q₂ U₂ → (Hd.foldD Sb sl Z A₀).S₂.qFam q₀ b₂ U₂) (t₁ : N.O → ℕ) (t₁' : N'.O → ℕ)
    (h₁ : ∀ a, Hd.bSrc Sb sl Z A₀ t b₂ (.inl (.inr a)) ≤ t₁ a)
    (h₁' : ∀ a, Hd.bSrc Sb sl Z A₀ t b₂ (.inr a) ≤ t₁' a)
    (W : Finset (Hd.foldD Sb sl Z A₀).src.Ex.Pos) (hW : Hd.qSrc Sb sl Z A₀ q₂ t W) :
    (S₀.sum N).qSum N'
      (S₀.qSum N (S₀.qFam q₀ fun a => Hd.bSrc Sb sl Z A₀ t b₂ (.inl (.inl a))) t₁) t₁' W :=
  qFam_sum_le (S₀.sum N) N' q₀ _ _ t₁'
    (fun V hV => qFam_sum_le S₀ N q₀ _ _ t₁ (fun _ h => h) h₁ V hV) h₁' W
    (ldGroup_qSrc_le Sb sl Z A₀ q₂ t q₀ b₂ h2 W hW)

end
end Cb
