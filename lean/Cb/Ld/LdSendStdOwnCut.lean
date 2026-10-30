-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSendStdOwnCut.lean: under the hypotheses of its statements, at a standard sender, one free
entry is the mask of a coming splitting: the conditions on the sender's coins in the letters of the
closings with splittings; and so, for the test for linear constraints, the three lemmas "one entry
is fresh at the start of the front" with, in the place of the hypotheses on a sender, `T.Places` and
the three layouts' conditions (`Y.OK t`: its field `hides` among them).

This file is book-keeping for those coins of an honest prover that go into its messages
(`Sig.Sender.Mk`). One free coordinate of the prover's messages is taken as the scalar mask that one
later step of a chain, a splitting, will use; under `Y.OK t` and two conditions on the set Rd of
entries that is read, the three conditions on the coins that Cb/Ld/LdSendFresh.lean asks are proved.

Definitions, statements and proofs.
Cb/Ld/LdSendStdOwn.lean has, under the hypotheses of its statement, the conditions (`Own.Laws`) for
masks at any injective family of free entries, for the reading "all entries that are no pads", masks
as a vector. Cb/Ld/LdLinCloseSplit.lean asks them for one entry, the mask a scalar, and for the
reading "the messages cut to a set Rd of entries" (`Sig.cut`), overwritten by `Sig.ow`. Two rules
lead from the one to the other.

Main names, each under the hypotheses of its statement:
  `U.mapM e`: the same split of the coins, the own masks named through a bijection e.
  `Spec.own_laws_mapM`: the conditions go with it.
  `Spec.own_laws_conseq`: the conditions go over to a coarser reading g that commutes with the
    overwriting (and whose overwriting, done twice, is done once).
  `Y.ownOne dat rest w0 x₀`: the split for one free entry x₀: own mask: that entry, a scalar.
  `Spec.stdL_ownOne`: `Y.OK t`; Rd holds no pad entry; Rd holds the entry ⇒ `(Y.ownOne ..).Laws Sd`
    (messages cut to Rd, the further witness handed on) (that entry overwritten).
  `Spec.ldLinStdSp_entO`, `Spec.ldLinStdSp_entU`, `Spec.ldLinStdSp_entW`:
    Cb/Ld/LdLinCloseSplit.lean's `ldLinSp_entO`, `ldLinSp_entU`, `ldLinSp_entW` at the standard
    senders `T.snd` (Cb/Ld/LdLinStd.lean), for a free entry of a member of Ω's, G_u's, W's family:
    from `T.Places`, the three layouts' conditions, Rd holds no pad entry of that family, and the
    lemmas' own conditions on Rd, Rr. (They conclude `Chain.FreshFor`: Ior/KnowCollRulesChain.lean.)

Notation: `Rr`: a set of members (`O → Prop`); `LW`, `LU`, `LO`, `tW`, `tU`, `tO`: a number for each
member of W's, of G_u's, of Ω's family (W, G_u, Ω: the head of Cb/Ld/LdLin.lean).

Limits: that layouts with these conditions exist is not said here (Cb/Ld/LdSendStdMFree.lean:
stdMFamF_ok). This file says nothing on sets of slots (Cb/Ld/LdLinStdSpV.lean).
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSendStdOwn
import Cb.Ld.LdLinStdFresh
import Cb.Ld.LdLinCloseSplitProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E : Type} [Field E] {N : Sig E} {W W' : Type} {D : N.Sender W W'} {Mb Mb' : Type}

/-- the same split, the own masks named through a bijection -/
def Sig.Sender.Own.mapM (U : D.Own Mb) (e : Mb ≃ Mb') : D.Own Mb' where
  M0 := U.M0
  Pd := U.Pd
  κ := U.κ.trans ((e.prodCongr (Equiv.refl U.M0)).prodCongr (Equiv.refl U.Pd))

omit [Field E] in
theorem Sig.Sender.Own.mapM_mk' (U : D.Own Mb) (e : Mb ≃ Mb') (M : Mb') (k₀ : U.M0) (η : U.Pd) :
    (U.mapM e).mk' M k₀ η = U.mk' (e.symm M) k₀ η := rfl

end

namespace Spec

def own_laws_mapM : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (W W' : Type) (D : N.Sender W W')
      (Mb Mb' : Type) (U : D.Own Mb) (e : Mb ≃ Mb') (Sd : N.Seeds) (Kc : Type)
      (rd : N.Msg → W' → Kc) (put : Mb → Kc → Kc),
    U.Laws Sd rd put → (U.mapM e).Laws Sd rd fun M k => put (e.symm M) k

/-- A coarser reading. -/
def own_laws_conseq : Prop :=
  ∀ (E : Type) [Field E] (N : Sig E) (W W' : Type) (D : N.Sender W W') (Mb : Type)
      (U : D.Own Mb) (Sd : N.Seeds) (Kc Kc' : Type) (rd : N.Msg → W' → Kc) (put : Mb → Kc → Kc)
      (g : Kc → Kc') (put' : Mb → Kc' → Kc'),
    (∀ M k, g (put M k) = put' M (g k)) → (∀ M M' k, put' M (put' M' k) = put' M k) →
    U.Laws Sd rd put → U.Laws Sd (fun m w' => g (rd m w')) put'

end Spec

theorem own_laws_mapM : Spec.own_laws_mapM := fun _ _ _ _ _ _ _ _ _ e _ _ _ _ h =>
  ⟨fun _ _ k => h.over _ _ k,
    h.lay.elim fun body hb => ⟨body, fun w M k₀ η => hb w (e.symm M) k₀ η⟩,
    fun s w w' M M' k₀ k₀' => h.pad s w w' (e.symm M) (e.symm M') k₀ k₀'⟩

theorem own_laws_conseq : Spec.own_laws_conseq := fun _ _ _ _ _ _ _ _ _ _ _ _ _ g _ hg ho h =>
  ⟨ho, h.lay.elim fun body hb =>
      ⟨fun w k₀ => g (body w k₀), fun w M k₀ η => (congrArg g (hb w M k₀ η)).trans (hg _ _)⟩,
    h.pad⟩

theorem ldk_ow_at {E : Type} {N : Sig E} (own : N.Ent → Prop) (v : N.Ent → E) (m : N.Msg) (a : N.O)
    (j : (N.om a).C.J) (h : own ⟨a, j⟩) :
    N.ow own v m a j = v ⟨a, j⟩ := by
  unfold Sig.ow
  exact if_pos h

theorem ldk_ow_off {E : Type} {N : Sig E} (own : N.Ent → Prop) (v : N.Ent → E) (m : N.Msg) (a : N.O)
    (j : (N.om a).C.J) (h : ¬ own ⟨a, j⟩) : N.ow own v m a j = m a j := by
  unfold Sig.ow
  exact if_neg h

namespace Sig.StdL
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {N : Sig E}
  (Y : N.StdL F) {W W' : Type} (dat : W → ∀ a, Y.Dt a → E) (rest : W → W') (w0 : W)

/-- The split of the sender's coins for one free entry. -/
@[reducible] def ownOne (x₀ : Σ a, Y.Fr a) : (Y.snd dat rest w0).Own E :=
  (Y.ownAt (fun _ : Unit => x₀) (fun _ _ _ => rfl) dat rest w0).mapM (Equiv.funUnique Unit E)

end Sig.StdL

namespace Spec

open Classical in
/-- One free entry as the mask of a coming splitting. -/
def stdL_ownOne : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (N : Sig E)
      (Y : N.StdL F) (t : N.O → ℕ) (W W' : Type) (dat : W → ∀ a, Y.Dt a → E) (rest : W → W')
      (w0 : W) (x₀ : Σ a, Y.Fr a) (Sd : N.Seeds) (Rd : N.Ent → Prop),
    Y.OK t → (∀ n, Rd n → Y.NoPad n) → Rd (Y.entF x₀) →
    (Y.ownOne dat rest w0 x₀).Laws Sd (fun m w' => (N.cut Rd m, w'))
      (fun u k => (N.ow (fun n => n = Y.entF x₀) (fun _ => u) k.1, k.2))

end Spec

theorem stdL_ownOne : Spec.stdL_ownOne := by
  classical
  intro F E _ _ _ _ _ N Y t W W' dat rest w0 x₀ Sd Rd h hR h0
  have l1 := own_laws_mapM E N W W' (Y.snd dat rest w0) (Unit → E) E _ (Equiv.funUnique Unit E)
    Sd _ _ _ (stdL_own F E N Y t W W' dat rest w0 Unit (fun _ => x₀) (fun _ _ _ => rfl) Sd h)
  have hinj : Function.Injective fun _ : Unit => Y.entF x₀ := fun _ _ _ => rfl
  have l2 := own_laws_conseq E N W W' (Y.snd dat rest w0) E (Y.ownOne dat rest w0 x₀) Sd _ _
    Y.rdNoPad (fun (u : E) k => Y.putAt (fun _ : Unit => x₀) ((Equiv.funUnique Unit E).symm u) k)
    (fun k : (N.Ent → E) × W' => ((fun a j => if Rd ⟨a, j⟩ then k.1 ⟨a, j⟩ else 0 : N.Msg), k.2))
    (fun u k => (N.ow (fun n => n = Y.entF x₀) (fun _ => u) k.1, k.2))
    (fun u k => Prod.ext (funext fun a => funext fun j => by
      show (if Rd ⟨a, j⟩ then Function.extend (fun _ : Unit => Y.entF x₀) (fun _ => u) k.1 ⟨a, j⟩
          else 0) =
        N.ow (fun n => n = Y.entF x₀) (fun _ => u)
          (fun a j => if Rd ⟨a, j⟩ then k.1 ⟨a, j⟩ else 0) a j
      by_cases hn : (⟨a, j⟩ : N.Ent) = Y.entF x₀
      · rw [ldk_ow_at _ _ _ a j hn, hn, if_pos h0]
        exact hinj.extend_apply (fun _ => u) k.1 ()
      · rw [ldk_ow_off _ _ _ a j hn, Function.extend_apply' _ _ _ fun ⟨_, hi⟩ => hn hi.symm]) rfl)
    (fun u u' k => Prod.ext (funext fun a => funext fun j => by
      show N.ow (fun n => n = Y.entF x₀) (fun _ => u)
          (N.ow (fun n => n = Y.entF x₀) (fun _ => u') k.1) a j =
        N.ow (fun n => n = Y.entF x₀) (fun _ => u) k.1 a j
      by_cases hn : (⟨a, j⟩ : N.Ent) = Y.entF x₀
      · rw [ldk_ow_at _ _ _ a j hn, ldk_ow_at _ _ _ a j hn]
      · rw [ldk_ow_off _ _ _ a j hn, ldk_ow_off _ _ _ a j hn, ldk_ow_off _ _ _ a j hn]) rfl) l1
  have e : (fun (m : N.Msg) (w' : W') =>
        (((fun a j => if Rd ⟨a, j⟩ then (Y.rdNoPad m w').1 ⟨a, j⟩ else 0 : N.Msg),
          (Y.rdNoPad m w').2) : N.Msg × W')) =
      fun m w' => (N.cut Rd m, w') := by
    funext m w'
    refine Prod.ext (funext fun a => funext fun j => ?_) rfl
    show (if Rd ⟨a, j⟩ then cutTo Y.NoPad (N.ents m) ⟨a, j⟩ else 0) = N.cut Rd m a j
    unfold Sig.cut
    by_cases hn : Rd ⟨a, j⟩
    · rw [if_pos hn, if_pos hn]
      exact if_pos (hR _ hn)
    · rw [if_neg hn, if_neg hn]
  rw [← e]
  exact l2

namespace Spec
section
variable (F E ι κ J Y : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype ι]
  [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

open Classical in
/-- One free entry of a member of the family of Ω. -/
def ldLinStdSp_entO : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (T : C.P.Std F) (LW : C.P.NW.O → ℕ) (LU : C.P.NU.O → ℕ)
      (LO : C.P.NO.O → ℕ) (tW : C.P.NW.O → ℕ) (tU : C.P.NU.O → ℕ) (tO : C.P.NO.O → ℕ)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (x : FSt C.S C.E₀ C.Wpa Unit)
      (fq : C.St6 → x.St) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop) (x₀ : Σ a, T.YO.Fr a),
    T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO → (∀ n, Rd (C.eO n) → T.YO.NoPad n) →
    (∀ a, ¬ Rr (.inr a)) → Rd (C.eO (T.YO.entF x₀)) →
    ((C.P.chain on0 (T.snd LW LU LO tW tU tO) εf).append (C.chain fq x.A)).FreshFor
      (x.stage.wideFact Rd Rr (fun n => n = C.eO (T.YO.entF x₀)) E fun u _ => u).kc E
      (x.stage.wideFact Rd Rr (fun n => n = C.eO (T.YO.entF x₀)) E fun u _ => u).put

open Classical in
/-- One free entry of a member of the family of G_u. -/
def ldLinStdSp_entU : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (T : C.P.Std F) (LW : C.P.NW.O → ℕ) (LU : C.P.NU.O → ℕ)
      (LO : C.P.NO.O → ℕ) (tW : C.P.NW.O → ℕ) (tU : C.P.NU.O → ℕ) (tO : C.P.NO.O → ℕ)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (x : FSt C.S C.E₀ C.Wpa Unit)
      (fq : C.St6 → x.St) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop) (x₀ : Σ a, T.YU.Fr a),
    T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO → (∀ n, Rd (C.eU n) → T.YU.NoPad n) →
    (∀ a, ¬ Rr (.inl (.inr a))) → Rd (C.eU (T.YU.entF x₀)) →
    ((C.P.chain on0 (T.snd LW LU LO tW tU tO) εf).append (C.chain fq x.A)).FreshFor
      (x.stage.wideFact Rd Rr (fun n => n = C.eU (T.YU.entF x₀)) E fun u _ => u).kc E
      (x.stage.wideFact Rd Rr (fun n => n = C.eU (T.YU.entF x₀)) E fun u _ => u).put

open Classical in
/-- One free entry of a member of the family of W. -/
def ldLinStdSp_entW : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (T : C.P.Std F) (LW : C.P.NW.O → ℕ) (LU : C.P.NU.O → ℕ)
      (LO : C.P.NO.O → ℕ) (tW : C.P.NW.O → ℕ) (tU : C.P.NU.O → ℕ) (tO : C.P.NO.O → ℕ)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (x : FSt C.S C.E₀ C.Wpa Unit)
      (fq : C.St6 → x.St) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop) (x₀ : Σ a, T.YW.Fr a),
    T.Places → T.YW.OK tW → T.YU.OK tU → T.YO.OK tO → (∀ n, Rd (C.eW n) → T.YW.NoPad n) →
    (∀ a, ¬ Rr (.inl (.inl (.inr a)))) → Rd (C.eW (T.YW.entF x₀)) →
    ((C.P.chain on0 (T.snd LW LU LO tW tU tO) εf).append (C.chain fq x.A)).FreshFor
      (x.stage.wideFact Rd Rr (fun n => n = C.eW (T.YW.entF x₀)) E fun u _ => u).kc E
      (x.stage.wideFact Rd Rr (fun n => n = C.eW (T.YW.entF x₀)) E fun u _ => u).put

end
end Spec

section
variable {F E ι κ J Y : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Fintype ι]
  [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLinStdSp_entO : Spec.ldLinStdSp_entO F E ι κ J Y := by
  classical
  intro C T LW LU LO tW tU tO on0 εf x fq Rd Rr x₀ hP hW hU hO hR hr h0
  obtain ⟨-, -, -, hdO⟩ := T.sndLaws LW LU LO hP hW hU hO
  exact ldLinSp_entO E ι κ J Y C on0 εf (T.snd LW LU LO tW tU tO) x fq
    (T.YO.ownOne T.datO (fun w => w.2) (fun _ => 0, T.w3) x₀) Rd Rr (T.YO.entF x₀)
    (stdL_ownOne F E C.P.NO T.YO tO C.P.W4 C.P.W3 T.datO (fun w => w.2) (fun _ => 0, T.w3)
      x₀ C.P.SdO (fun n => Rd (C.eO n)) hO hR h0)
    hdO hr h0

theorem ldLinStdSp_entU : Spec.ldLinStdSp_entU F E ι κ J Y := by
  classical
  intro C T LW LU LO tW tU tO on0 εf x fq Rd Rr x₀ hP hW hU hO hR hr h0
  obtain ⟨⟨-, lO⟩, -, hdU, -⟩ := T.sndLaws LW LU LO hP hW hU hO
  exact ldLinSp_entU E ι κ J Y C on0 εf (T.snd LW LU LO tW tU tO) x fq
    (T.YU.ownOne T.datU (fun w => w.2) (fun _ => 0, T.w1) x₀) Rd Rr (T.YU.entF x₀)
    (stdL_ownOne F E C.P.NU T.YU tU C.P.W2 C.P.W1 T.datU (fun w => w.2) (fun _ => 0, T.w1)
      x₀ C.P.SdU (fun n => Rd (C.eU n)) hU hR h0)
    hdU lO (ldLinStd_apart C.P T LW LU LO tW tU tO) hr h0

theorem ldLinStdSp_entW : Spec.ldLinStdSp_entW F E ι κ J Y := by
  classical
  intro C T LW LU LO tW tU tO on0 εf x fq Rd Rr x₀ hP hW hU hO hR hr h0
  obtain ⟨⟨lU, lO⟩, hdW, -, -⟩ := T.sndLaws LW LU LO hP hW hU hO
  exact ldLinSp_entW E ι κ J Y C on0 εf (T.snd LW LU LO tW tU tO) x fq
    (T.YW.ownOne T.datW (fun w => w.2) (fun _ => 0, T.w0) x₀) Rd Rr (T.YW.entF x₀)
    (stdL_ownOne F E C.P.NW T.YW tW C.P.WA C.P.W0 T.datW (fun w => w.2) (fun _ => 0, T.w0)
      x₀ C.P.SdW (fun n => Rd (C.eW n)) hW hR h0)
    hdW lU lO (ldLinStd_apart C.P T LW LU LO tW tU tO) hr h0

end
end Cb
