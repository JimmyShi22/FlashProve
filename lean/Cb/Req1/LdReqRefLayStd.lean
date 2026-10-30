-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqRefLayStd.lean: under the hypotheses of `Spec.ldReqRefLayStd_cross`, the wide fact
crosses a reference segment whose senders are standard and whose link is the group's own: no premise
on a sender or on the closing's link is left, but for `IsStdB` and `IsGrp`: equations that say which
terms stand there, with the further clauses of these two definitions. (Left, of terms: the entry
step's own condition, `S.Enters`; the body's bundle `S.A.OK pp` (it holds `d1.Hyp`, `d3.Hyp` of the
body's two senders), which Cb/Req1/LdReqModel.lean sorts.)

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs: an assembly.
S is a reference segment (`LdRefS`, Cb/Req1/LdReqRef.lean). Wide facts: `LdStage.wideFact`
(Cb/Req1/LdSegCarry.lean); crossing: `S.Carries` (Cb/Req1/LdReqRefLay.lean). `W : LdRefW S.A`,
`Fr : LdRefF S.A`: Cb/Req1/LdSegRefCross.lean; `D : LdFoldD E Kc` with `l : Link Kc D.src.J D.mid`:
Cb/Req1/LdSegKit.lean (`Link`: Ior/KnowCollRulesChain.lean).
`Spec.ldReqRefLay_cross` (Cb/Req1/LdReqRefLay.lean) asks, beside places and readings: of the
closing's link: of the witness it reads the group's members only, it hands the rest on; of the one
sending's sender: its laws, it does not look; of the body's two senders: they do not look. (not all
hypotheses are named here: see its statement) Under `D.IsGrp l` (Cb/Req1/LdReqProtoStd.lean) and
`d.IsStdB F Rd Rr own` (Cb/Req1/LdReqStdLay.lean: the standard sending whose data do not look) these
are theorems.

Main names:
  `D.Reads l`: the two clauses on a link bridge-to-fold.
  `Spec.ldReqRefLayStd_link`: `D.IsGrp l → D.Reads l`.
  `W.PassS F' Fr own Mk val`: quiet for the front; the body's two sendings are standard and their
    data do not look.
  `Spec.ldReqRefLayStd_cross`: under `[CharP E pp]`, `[Nonempty I.C.E0.Str]`, `[Nonempty Mk]`,
    `S.A.Xa.A.MaskOK S.A.Xa.Dt`, `S.A.X.Own`: `S.Carries g'` (the wide fact at S's last stage, sets
    written out), from: `S.A.OK pp`, the core is the ghost (`S.A.Ghost κ`), the front's conditions,
    among them on places, on numbers and on the claim Cc (`F.OK pp`);
    `W.PassS`; neither late block reads an own entry (each reads only entries of the wide reading
    that are not own); `S.K.R.c1.fold.IsGrp S.l`; every member of the group is seen whole and holds
    no own entry; `S.Qc.snd.IsStdB` at the sets that cross; the cut reads new entries in RdN only;
    `S.Enters g'` (the wide fact at the body's entry); and whatever the arguments hold as proofs.

So, under the hypotheses of `Spec.ldReqRefLayStd_cross`, "carried across a closing" follows from:
equations that say which terms stand there; places and readings; "the data that are sent do not
look"; the cut's condition; the entry step's own condition.

Limits: no instance in this form. This file gives no instance that meets its hypotheses, so as far
as this file shows its theorems may hold of nothing.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqRefLayProofs
import Cb.Req1.LdReqStdLay
import Cb.Ld.LdGroupLinkRef

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

/-- Of the witness the link reads the group's members only, and hands the rest on. -/
def LdFoldD.Reads {E Kc : Type} [Field E] [Fintype E]
    (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) : Prop :=
  (∀ (w w' : D.src.J.W) x c ρ, D.G.wit w'.1 = D.G.wit w.1 →
    ((l.H.strat w' x c).run ρ).1 = ((l.H.strat w x c).run ρ).1 ∧
    ((l.H.strat w' x c).run ρ).2.1 = ((l.H.strat w x c).run ρ).2.1 ∧
    ((l.H.strat w' x c).run ρ).2.2.1 = ((l.H.strat w x c).run ρ).2.2.1) ∧
  ∀ (w : D.src.J.W) x c ρ, ((l.H.strat w x c).run ρ).2.2.2 = (D.S.res (T := OMsg.Wit) D.kp w.1, w.2)

/-- What is asked of a wide fact in the body. -/
structure LdRefW.PassS (F' : Type) {E Kc : Type} [Field F'] [Fintype F'] [Field E]
    [Fintype E] [Algebra F' E] {I : LdRefIx E} {A : LdRefD E Kc I} (W : LdRefW A)
    (Fr : LdRefF A) (own : A.Xa.Q.D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
    [Nonempty Mk] (val : Mk → A.Xa.Q.D.S.Ent → E) : Prop where
  quiet  : Fr.Quiet (W.fact own Mk val)
  send1  : A.Xa.Q.D.d1.IsStdB F' W.Rd W.Rr own
  send3  : A.Xa.Q.D.d3.IsStdB F' (A.Xa.Q.D.S.sumP A.Xa.Q.D.N W.Rd W.RdN)
    (A.Xa.Q.D.S.sumO A.Xa.Q.D.N W.Rr W.RrN) (A.Xa.Q.D.S.sumP A.Xa.Q.D.N own fun _ => False)

namespace Spec

def ldReqRefLayStd_link : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid),
    D.IsGrp l → D.Reads l

/-- Under the hypotheses below, the wide fact crosses. -/
def ldReqRefLayStd_cross : Prop :=
  ∀ (F' E Kc : Type) [Field F'] [Fintype F'] [Field E] [Fintype E] [Algebra F' E] (pp : ℕ)
      [CharP E pp] (I : LdRefIx E) (a : LdStage E Kc) (S : LdRefS E Kc I a) [Nonempty I.C.E0.Str]
      (W : LdRefW S.A) (F : LdRefF S.A) (κ : S.A.Gh → Kc) (own : S.A.Xa.Q.D.S.Ent → Prop)
      (Mk : Type) [Fintype Mk] [Nonempty Mk] (val : Mk → S.A.Xa.Q.D.S.Ent → E)
      (RdN : S.Qc.N.Ent → Prop) (RrN : S.Qc.N.O → Prop) (g' : MaskFact a.J.W),
    S.A.OK pp → S.A.Ghost κ → F.OK pp → W.PassS F' F own Mk val → S.A.Xa.A.MaskOK S.A.Xa.Dt →
    (∀ n, S.A.Xa.A.srAll S.A.Xa.Dt n → W.Rd2 n ∧ ¬ S.A.own2 own n) → S.A.X.Own →
    (∀ n, S.A.Rdt n → W.Rd2 n ∧ ¬ S.A.own2 own n) → S.K.R.c1.fold.IsGrp S.l →
    (∀ o, S.K.R.c1.fold.G.mem o → W.Rr2 o ∧ ∀ j, W.Rd2 ⟨o, j⟩ ∧ ¬ S.A.own2 own ⟨o, j⟩) →
    S.Qc.snd.IsStdB F' (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp W.Rd2))
      (fun o => W.Rr2 o.1.1)
      (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp (S.A.own2 own))) →
    (∀ m m' : S.Qc.N.Msg,
      (∀ n : S.Qc.N.Ent, RdN n → m' n.1 n.2 = m n.1 n.2) → S.Qc.cutN m' = S.Qc.cutN m) →
    S.Enters g' (W.fact own Mk val) →
    S.Carries g'
      (S.Qc.loc.tgt.wideFact
        (S.K.R.c1.fold.tgt.S.sumP S.Qc.N
          (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp W.Rd2)) RdN)
        (S.K.R.c1.fold.tgt.S.sumO S.Qc.N (fun a => W.Rr2 a.1.1) RrN)
        (S.K.R.c1.fold.tgt.S.sumP S.Qc.N
          (S.K.R.c1.fold.S₁.subQ _ (S.K.R.c1.fold.S.subQ S.K.R.c1.fold.kp (S.A.own2 own)))
          fun _ => False)
        Mk fun M =>
          S.K.R.c1.fold.tgt.S.sumV S.Qc.N
            (S.K.R.c1.fold.S₁.subF _ (S.K.R.c1.fold.S.subF S.K.R.c1.fold.kp (S.A.val2 val M)))
            fun _ => 0)

end Spec

/-- The two clauses pass along an equation of pairs. -/
theorem ldFoldD_readsAt {E Kc : Type} [Field E] [Fintype E]
    (x x' : Σ D : LdFoldD E Kc, Link Kc D.src.J D.mid) (e : x = x') (h : x'.1.Reads x'.2) :
    x.1.Reads x.2 := e ▸ h

theorem ldReqRefLayStd_link : Spec.ldReqRefLayStd_link := by
  intro E Kc _ _ D l ⟨_, _, Sh, Hd, Z, hc, dw, d, t, Lst, mC, mS, mW, L, e, _⟩
  exact ldFoldD_readsAt ⟨D, l⟩ _ e ⟨fun w w' x c ρ h =>
      ldGroup_link_run Hd D.Sb D.sl Z D.A₀ hc dw d t Lst mC mS mW L w w' x c ρ h,
    fun w x c ρ => ldGroup_link_carry Hd D.Sb D.sl Z D.A₀ hc dw d t Lst mC mS mW L w x c ρ⟩

theorem ldReqRefLayStd_cross : Spec.ldReqRefLayStd_cross := by
  intro F' E Kc _ _ _ _ _ pp _ I a S _ W F κ own Mk _ _ val RdN RrN g' hA hG hF hq hM hL
    hO hT hg hmem hs hcut hE
  obtain ⟨c1, c2⟩ := ldReqRefLayStd_link E Kc _ _ hg
  obtain ⟨c4, c5⟩ := ldReqStdLay_cross F' E Kc I a S W own hs
  exact ldReqRefLay_cross E Kc pp I a S W F κ own Mk val RdN RrN g' hA hG hF
    ⟨hq.quiet,
      (ldReqStdLay_noLook F' E Kc _ _ _ _ _ hq.send1).2,
      (ldReqStdLay_noLook F' E Kc _ _ _ _ _ hq.send3).2⟩
    hM hL hO hT c1 c2 hmem c4 c5 hcut hE

end Cb
