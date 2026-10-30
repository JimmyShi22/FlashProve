-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkStd.lean: for small example instances: the test that two encodings hold the same
index, built from standard parts, so that what the theorem `Cb.ldOl_full`
(Cb/Obj/LdObjectLinkFull.lean) assumes of sender and last part (`S.OK`, `Kc.OK`) follows from
conditions on codes and the sample's conditions.

Definitions, one statement and its proof. A tool for guards against empty theorems; no parameter of
a protocol.

The data (`StdLk Cf P`): `M`: a standard oracle message (`StdM`, Cb/Obj/LdObjectToyKit.lean) whose
data are the entries of one full message of the configuration's code (`dt`); the link's own numbers
(l, pl, e₀, e₁, t₀, t₁); the base case's (tb drawn positions; d, bad, L2); Lc: a bound on the list
of the complex.

Main names:
  `D.N`: the family: two members, both `M.om`: G_u0 (false) and G_u1 (true) (`LdLkP.N`,
    Cb/Ld/LdLink.lean).
  `D.S L t`: the sending: independent seeds; the family's sender from the two members' senders with
    independent coins (Cb/Ld/LdSendMem.lean).
  `Spec.ldOl_std`: the code and P have a position (`Nonempty`); `Cf.OK L₀`; the bounds ε₀, ε₁ on the
    folds' bad points; pl injective; `M.OK L t` (laws, lists, zero knowledge of the member's code;
    the sample's conditions); the member's code has distance d above its radius and is
    transparent; every code at these positions with its laws and distance d has lists of at most
    Lc (L2) at the radius, and every code at these positions with its laws has at most "bad"
    exceptional coefficients at the radius; the test needs no more positions than the sent words
    bear (tb ≤ t) ⇒ `LinkListR` ∧ `LinkKnowR`.

Limits: this file does not say that the conditions can be met. For that see
Cb/Obj/LdObjectLinkToy.lean. The standard parts are no proposal for a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinkFull
import Cb.Obj.LdObjectToyKit
import Cb.Ld.LdTowerMain
import Cb.Gen.BatEvaderProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The link with standard parts: the data. -/
structure StdLk {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E)
    (P : Type) [Fintype P] where
  M  : StdM E P
  dt : Fin Cf.C₀.k ≃ M.Dt
  l  : ℕ
  pl : Cf.Lay → Fin l → Bool
  e₀ : ℕ
  e₁ : ℕ
  t₀ : ℕ
  t₁ : ℕ
  tb : ℕ
  d  : ℕ
  bad : ℕ
  L2 : ℕ
  Lc : ℕ

namespace StdLk
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] [Nonempty P] (D : StdLk Cf P)

/-- the family: two members -/
@[reducible] def N : Sig E := { O := Bool, om := fun _ => D.M.om }

/-- The link's parameters. -/
@[reducible] def K : Cf.LinkPar where
  l := D.l
  pl := D.pl
  e₀ := D.e₀
  e₁ := D.e₁
  t₀ := D.t₀
  t₁ := D.t₁
  N := D.N
  i₀ := false
  l₀ := fun i => D.M.place (Sum.inl (D.dt i))
  i₁ := true
  l₁ := fun i => D.M.place (Sum.inl (D.dt i))

/-- a fixed witness -/
def w1 : D.K.P.W1 := ((fun _ => 0, fun _ => 0), (fun _ _ => 0, fun _ _ => 0))

/-- the data of a member: the entries of its folded full message -/
def dat (a : Bool) (w : D.K.P.W1) : D.M.Dt → E := fun i =>
  (if a then w.1.2 else w.1.1) (D.dt.symm i)

/-- the members' senders -/
@[reducible] def mem : ∀ a, (D.N.om a).Sender D.K.P.W1 Unit := fun a => D.M.snd (D.dat a) D.w1

/-- The sending. -/
@[reducible] def S (L t : ℕ) : D.K.P.Snd where
  Sd := Sig.Seeds.indep D.N
  dS := Sig.Sender.ofMem D.mem (fun w => w.2) D.w1
  L := fun _ => L
  t := fun _ => t

/-- the one group: both members, read where they stand -/
@[reducible] def G : Grp D.N := { P := P, mem := fun _ => True, pos := fun _ => id, e := D.M.e }

/-- The closing: the bridge with independent coefficients, then the base case. -/
@[reducible] def Kc [Nonempty (Fin Cf.C₀.n)] : D.K.P.Cl where
  G := D.G
  neP := inferInstanceAs (Nonempty P)
  all := fun _ => trivial
  Z := @Evader.indep E (D.G.Row D.K.P.RowB) _ _ _ (Classical.decEq _)
  T := ldBaseEnd _ D.tb (fun _ => Classical.arbitrary P) D.d D.bad D.L2
  L := D.Lc
  t := D.tb

end StdLk

def Spec.ldOl_std (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLk Cf P)
      (L₀ ε₀ ε₁ L t : ℕ) (d₂ : D.K.P.W2) (d₀ : D.K.P.W0),
    Cf.OK L₀ → D.K.P.FoldErr D.K.free D.K.free ε₀ ε₁ → Function.Injective D.pl → D.M.OK L t →
    D.M.Cm.Dist D.d → D.M.Cm.Transparent → D.M.e < D.d →
    (∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.M.e D.Lc) →
    (∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.M.e D.L2) →
    (∀ C : LdCode E P, C.Laws → C.MCAat D.M.e D.bad) → D.tb ≤ t →
    LinkListR (C := Cf.conf) (D.K.link (D.K.full (D.S L t) ε₀ ε₁ D.Kc d₂ d₀))
      (D.K.hLink (D.K.full (D.S L t) ε₀ ε₁ D.Kc d₂ d₀))
      (D.K.nums (D.K.full (D.S L t) ε₀ ε₁ D.Kc d₂ d₀)) ∧
    LinkKnowR (C := Cf.conf) (D.K.link (D.K.full (D.S L t) ε₀ ε₁ D.Kc d₂ d₀))
      (D.K.nums (D.K.full (D.S L t) ε₀ ε₁ D.Kc d₂ d₀)).err

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] [Nonempty P] (D : StdLk Cf P)

omit [Nonempty P] in
/-- what the sending asks -/
theorem stdLk_snd {L t : ℕ} (h : D.M.OK L t) : (D.S L t).OK where
  laws := fun _ => h.laws
  fair := (ldSendFam_fair_indep E D.N).1
  list := fun _ => stdM_list D.M h
  ev := fun _ => stdM_evades D.M h
  snd := ldSendMem_laws E D.N D.K.P.W1 D.K.P.W0 D.mem (fun w => w.2) D.w1 D.K.P.back (fun a m r => stdM_enc D.M (D.dat a) D.w1 m r) (by
    intro w k
    refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun i => ?_)) rfl
    · exact (stdM_put D.M (D.dat false) D.w1 w (k false) (D.dt i)).trans
        (congrArg w.1.1 (D.dt.symm_apply_apply i))
    · exact (stdM_put D.M (D.dat true) D.w1 w (k true) (D.dt i)).trans
        (congrArg w.1.2 (D.dt.symm_apply_apply i)))
  bl := ldSendMem_blind E D.N D.K.P.W1 D.K.P.W0 D.mem (fun w => w.2) D.w1 _ fun a =>
    stdM_blind D.M h (D.dat a) D.w1
  hid := ldSendMem_hides E D.N D.K.P.W1 D.K.P.W0 D.mem (fun w => w.2) D.w1 (fun _ => t)
    fun a => stdM_hides D.M h (D.dat a) D.w1

/-- what the closing asks -/
theorem stdLk_cl [Nonempty (Fin Cf.C₀.n)] {L t : ℕ} (h : D.M.OK L t) (hd : D.M.Cm.Dist D.d)
    (htr : D.M.Cm.Transparent) (he : D.M.e < D.d)
    (hl : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.M.e D.Lc)
    (hl2 : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.M.e D.L2)
    (hm : ∀ C : LdCode E P, C.Laws → C.MCAat D.M.e D.bad) : D.Kc.OK := by
  have hL : D.G.C.Laws := ld_laws_fam E P _ _ fun _ => h.laws
  have hD : D.G.C.Dist D.d := ld_dist_fam _ D.d fun _ => hd
  exact
    { ev := by
        letI : DecidableEq (D.G.Row D.K.P.RowB) := Classical.decEq _
        exact ok_indep E (D.G.Row D.K.P.RowB)
      list := hl _ hL hD
      fits := fun _ _ _ hn => hn
      tail := ldTower_base E _ D.tb _ D.d D.bad D.L2
        ⟨hL, ld_transp_fam _ fun _ => htr, he, hm _ hL,
          hl2 _ (ld_laws_il E P _ Bool hL) (ld_dist_il E P _ Bool D.d hD)⟩ }

end

theorem ldOl_std (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldOl_std F E :=
  fun Cf _ _ _ _ D L₀ ε₀ ε₁ L t d₂ d₀ hOK hF hpl hM hd htr he hl hl2 hm ht =>
    ldOl_full F E Cf D.K (D.S L t) L₀ ε₀ ε₁ D.Kc d₂ d₀ hOK hF hpl (stdLk_snd D hM)
      (stdLk_cl D hM hd htr he hl hl2 hm) fun _ => ht

end Cb
