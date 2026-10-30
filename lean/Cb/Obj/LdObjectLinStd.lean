-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinStd.lean: for toys: the test for linear constraints on the encoded index with
standard parts, for any configuration, an abstract field and variable codes: its two lists
(`LinListR`, `LinKnowR`), under the hypotheses of `Spec.ldOLF_std`.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation, one of the four sub-protocols of the library's holographic interactive oracle
proof; there it follows a preamble (Hiop/RecSubs.lean, Hiop/RecBuild.lean). This file fills the
test's open parameters (senders, plan, tests on groups) with standard parts, so that the hypotheses
on protocols in `Spec.ldOLF_lin` (Cb/Obj/LdObjectLinFull.lean) follow from hypotheses on codes,
sample maps and numbers.

Definitions, one statement (`Cb.Spec.ldOLF_std`) and its proof. A tool for guards against empty
theorems; no parameter of a protocol. The analogue, for this test, of Cb/Obj/LdObjectLinkStd.lean
(the link).

`Spec.ldOLF_lin` (Cb/Obj/LdObjectLinFull.lean) requires: that the index code has a position
(`Nonempty (Fin O.Cf.C₀.n)`), distance and radius of the index code, agreement and lists at the
fold's radius (`O.e' ≤ O.Cf.eM`), distinct places, what the three sendings ask (`Sn.OK`), a plan of
whole tests that says exactly the rows that are left and what the preamble left (`C.Says`,
Cb/Ld/LdLinClosePre.lean), is made of tests that meet their conditions (`Qt.OK`: every link of the
chain `Qt.c` is `GoodT` (Ior/KnowCollGood.lean: `acc`, `know` and `exact` among its clauses), and
`SidesCT` (Cb/Ld/LdTowerKitChain.lean)), and needs no more positions than the sent words bear, and
of the oracles left only what qa allows (`O.toC.P.q5 Sn qa`).
Here senders, plan and tests are built, from standard parts, and these four (`Sn.OK`, `C.Says`,
`Qt.OK`, the demand on positions) are proved from `D.Hyp`, `Nonempty P` and
`Nonempty (Fin Cf.C₀.n)`.
The plan without a splitting is `LdLinPl` (Cb/Ld/LdLinClosePlan.lean); `LdLinPlT`
(Cb/Ld/LdLinCloseDemand.lean) adds the tests and a closing `Q'` of what is then left, and its
`Q : LdTc` is the closing made of all of them.

Main names:
  `StdLn Cf P`: the data. The claims Cl with the tensor row (g, ψ, τ); the layout of the index
    matrix (Y, klo, l, lay, py); e', t. The preamble leaves nothing (no oracle message, no further
    claim, "rest" is 0).
    MW, MU, MO: three standard oracle messages (Cb/Obj/LdObjectToyKit.lean: data and one pad entry;
    the row with a pad as sample), all read at the positions P; their data are the entries of w, of
    the folded full message u, of ω (dW, dU, dO). Below, W, G_u, Ω are these three oracle messages,
    in this order.
    er: the joint radius of both groups; tb₁, tb₂: the numbers of positions that the two base cases
    draw; d, bad, L2, Lc: threshold, exceptional coefficients, list of a doubled complex, list of a
    complex.
  `D.pl`: the plan without a splitting (Cb/Ld/LdLinClosePlan.lean). Ω is in both tests.
  `D.Hyp L tW tU tO`: the conditions:
    `M.OK` for the three (laws, lists, zero knowledge of the code; the sample's conditions);
    distance d, transparent; er at most each member's radius and below d;
    every code at these positions with its laws and distance d has lists of at most Lc (L2) at er,
    and every code with its laws at most "bad" exceptional coefficients at er;
    tb₁ + tb₂ ≤ tW, tU, tO: each encoding hides as many positions as both tests draw
    (only Ω needs the sum).
  `Spec.ldOLF_std`: the index code and P have a position (`Nonempty (Fin Cf.C₀.n)`, `Nonempty P`),
    the conditions on the index code, `Function.Injective D.py` and `D.Hyp` ⇒ `LinListR` ∧
    `LinKnowR` for the test with its closing.

Limits: this file does not say that the conditions can be met (Cb/Obj/LdObjectLinToy.lean). The
standard parts are no proposal for a protocol. One instance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinFullProofs
import Cb.Ld.LdLinCloseDemandProofs
import Cb.Obj.LdObjectToyKit
import Cb.Ld.LdTowerMain
import Cb.Gen.BatEvaderProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The test with standard parts: the data. -/
structure StdLn {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E)
    (P : Type) [Fintype P] where
  Cl  : Type
  Y   : Type
  [finY : Fintype Y]
  klo : ℕ
  l   : ℕ
  lay : Y × (Fin klo → Bool) → Cf.J₀
  py  : Y → Fin l → Bool
  g   : Cl → Y → E
  ψ   : Cl → (Fin Cf.X.v → E) × (Fin klo → E)
  τ   : Cl → E
  e'  : ℕ
  t   : ℕ
  MW  : StdM E P
  MU  : StdM E P
  MO  : StdM E P
  dW  : ((Fin Cf.X.v ⊕ Fin klo) → Bool) ≃ MW.Dt
  dU  : Fin Cf.C₀.k ≃ MU.Dt
  dO  : Y ≃ MO.Dt
  er  : ℕ
  tb₁ : ℕ
  tb₂ : ℕ
  d   : ℕ
  bad : ℕ
  L2  : ℕ
  Lc  : ℕ

attribute [instance] StdLn.finY

namespace StdLn
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] (D : StdLn Cf P)

/-- The test over the configuration. -/
@[reducible] def O : LdOL F E where
  Cf := Cf
  S := Sig.nil E
  Cl := D.Cl
  Y := D.Y
  klo := D.klo
  l := D.l
  lay := D.lay
  py := D.py
  g := D.g
  ψ := D.ψ
  τ := D.τ
  restM := fun _ _ => 0
  more := fun _ _ => True
  e' := D.e'
  t := D.t
  NW := Sig.one D.MW.om
  SdW := Sig.Seeds.indep _
  iW := ()
  lW := fun c => D.MW.place (Sum.inl (D.dW c))
  NU := Sig.one D.MU.om
  SdU := Sig.Seeds.indep _
  iU := ()
  lU := fun k => D.MU.place (Sum.inl (D.dU k))
  NO := Sig.one D.MO.om
  SdO := Sig.Seeds.indep _
  iO := ()
  lO := fun y => D.MO.place (Sum.inl (D.dO y))

/-- the same, over a signature -/
@[reducible] def C : LdLinC E (Fin Cf.C₀.n) (Fin Cf.C₀.k) Cf.J D.Y := D.O.toC

/-- fixed witnesses (`w0`, `w1`, `w3`) -/
def w0 : D.C.P.W0 := (fun _ _ => 0, (fun a => a.elim, ()))
def w1 : D.C.P.W1 := (fun _ => (fun _ => 0, fun _ => 0), D.w0)
def w3 : D.C.P.W3 := (fun _ => (fun _ => 0, fun _ => 0), D.w1)

/-- the data of the three messages: the entries of w, of u, of ω (`datW`, `datU`, `datO`) -/
def datW (w : D.C.P.WA) : D.MW.Dt → E := fun i => w.1 (D.dW.symm i)
def datU (w : D.C.P.W2) : D.MU.Dt → E := fun i => w.1 (D.dU.symm i)
def datO (w : D.C.P.W4) : D.MO.Dt → E := fun i => w.1 (D.dO.symm i)

@[reducible] def memW : ∀ a, (D.C.NW.om a).Sender D.C.P.WA Unit := fun _ =>
  D.MW.snd D.datW (fun _ => 0, D.w0)
@[reducible] def memU : ∀ a, (D.C.NU.om a).Sender D.C.P.W2 Unit := fun _ =>
  D.MU.snd D.datU (fun _ => 0, D.w1)
@[reducible] def memO : ∀ a, (D.C.NO.om a).Sender D.C.P.W4 Unit := fun _ =>
  D.MO.snd D.datO (fun _ => 0, D.w3)

/-- The three senders. -/
@[reducible] def Sn (L tW tU tO : ℕ) : D.C.P.Snd where
  dW := Sig.Sender.ofMem D.memW (fun w => w.2) (fun _ => 0, D.w0)
  dU := Sig.Sender.ofMem D.memU (fun w => w.2) (fun _ => 0, D.w1)
  dO := Sig.Sender.ofMem D.memO (fun w => w.2) (fun _ => 0, D.w3)
  LW := fun _ => L
  LU := fun _ => L
  LO := fun _ => L
  tW := fun _ => tW
  tU := fun _ => tU
  tO := fun _ => tO

/-- every oracle message at the end of the test is read at the positions P, as it stands -/
def posAll : ∀ o : D.C.S.O, P → (D.C.S.om o).P
  | .inl (.inl (.inl e)) => e.elim
  | .inl (.inl (.inr _)) => id
  | .inl (.inr _) => id
  | .inr _ => id

/-- The plan: first group: G_u and Ω; kept: W and Ω; second group: both; nothing is kept then. -/
@[reducible] def pl : LdLinPl D.C where
  G₁ := { P := P, mem := fun o => o ≠ D.C.nW, pos := fun a => D.posAll a.1, e := D.er }
  hU := by simp
  hO := by simp
  kp₁ := fun o => o ≠ D.C.nU
  kW := by simp
  kO := by simp
  G₂ := { P := P, mem := fun _ => True, pos := fun a => D.posAll a.1.1, e := D.er }
  hW₂ := trivial
  hO₂ := trivial
  kp₂ := fun _ => False
  restG := fun _ _ => 0

instance : IsEmpty D.pl.S₂.O := ⟨fun a => a.2⟩

variable [Nonempty P]

/-- The tests: bridges with independent coefficients; each whole test is the base case on the
complex. -/
@[reducible] def T : LdLinPlT D.pl where
  ne₁ := inferInstanceAs (Nonempty P)
  hc₁ := fun o => by
    by_cases h : o = D.C.nW
    · exact Or.inr (by rw [h]; simp)
    · exact Or.inl h
  Z₁ := @Evader.indep E (D.pl.G₁.Row D.C.B₁) _ _ _ (Classical.decEq _)
  T₁ := ldBaseEnd _ D.tb₁ (fun _ => Classical.arbitrary P) D.d D.bad D.L2
  L₁ := D.Lc
  t₁ := D.tb₁
  ne₂ := inferInstanceAs (Nonempty P)
  hc₂ := fun _ => Or.inl trivial
  Z₂ := @Evader.indep E (D.pl.G₂.Row LinB₂) _ _ _ (Classical.decEq _)
  T₂ := ldBaseEnd _ D.tb₂ (fun _ => Classical.arbitrary P) D.d D.bad D.L2
  L₂ := D.Lc
  t₂ := D.tb₂
  Q' := LdTc.nil _ _ _ (fun a => a.2.elim, ())
  fa := fun _ => ()
  d₁ := (fun _ => (fun _ => 0, fun _ => 0), ())
  d₁' := ((fun _ => 0, fun _ => 0), (fun _ => (fun _ => 0, fun _ => 0), ()))
  d₂ := (fun _ => (fun _ => 0, fun _ => 0), ())
  d₂' := ((fun _ => 0, fun _ => 0), (fun a => a.2.elim, ()))

end StdLn

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] (D : StdLn Cf P)

/-- what the three sendings ask -/
theorem stdLn_snd {L tW tU tO : ℕ} (hW : D.MW.OK L tW) (hU : D.MU.OK L tU) (hO : D.MO.OK L tO) :
    (D.Sn L tW tU tO).OK where
  lawsW := fun _ => hW.laws
  fairW := (ldSendFam_fair_indep E _).1
  listW := fun _ => stdM_list D.MW hW
  evW := fun _ => stdM_evades D.MW hW
  sndW := ldSendMem_laws E _ _ _ D.memW (fun w => w.2) _ D.C.P.backW (fun _ m r => stdM_enc D.MW _ _ m r) (by
    intro w k
    refine Prod.ext (funext fun c => ?_) rfl
    exact (stdM_put D.MW D.datW (fun _ => 0, D.w0) w (k ()) (D.dW c)).trans
      (congrArg w.1 (D.dW.symm_apply_apply c)))
  blW := ldSendMem_blind E _ _ _ D.memW (fun w => w.2) _ _ fun _ => stdM_blind D.MW hW _ _
  hidW :=
    ldSendMem_hides E _ _ _ D.memW (fun w => w.2) _ (fun _ => tW) fun _ => stdM_hides D.MW hW _ _
  lawsU := fun _ => hU.laws
  fairU := (ldSendFam_fair_indep E _).1
  listU := fun _ => stdM_list D.MU hU
  evU := fun _ => stdM_evades D.MU hU
  sndU := ldSendMem_laws E _ _ _ D.memU (fun w => w.2) _ D.C.P.backU (fun _ m r => stdM_enc D.MU _ _ m r) (by
    intro w k
    refine Prod.ext (funext fun c => ?_) rfl
    exact (stdM_put D.MU D.datU (fun _ => 0, D.w1) w (k ()) (D.dU c)).trans
      (congrArg w.1 (D.dU.symm_apply_apply c)))
  blU := ldSendMem_blind E _ _ _ D.memU (fun w => w.2) _ _ fun _ => stdM_blind D.MU hU _ _
  hidU :=
    ldSendMem_hides E _ _ _ D.memU (fun w => w.2) _ (fun _ => tU) fun _ => stdM_hides D.MU hU _ _
  lawsO := fun _ => hO.laws
  fairO := (ldSendFam_fair_indep E _).1
  listO := fun _ => stdM_list D.MO hO
  evO := fun _ => stdM_evades D.MO hO
  sndO := ldSendMem_laws E _ _ _ D.memO (fun w => w.2) _ D.C.P.backO (fun _ m r => stdM_enc D.MO _ _ m r) (by
    intro w k
    refine Prod.ext (funext fun c => ?_) rfl
    exact (stdM_put D.MO D.datO (fun _ => 0, D.w3) w (k ()) (D.dO c)).trans
      (congrArg w.1 (D.dO.symm_apply_apply c)))
  blO := ldSendMem_blind E _ _ _ D.memO (fun w => w.2) _ _ fun _ => stdM_blind D.MO hO _ _
  hidO :=
    ldSendMem_hides E _ _ _ D.memO (fun w => w.2) _ (fun _ => tO) fun _ => stdM_hides D.MO hO _ _

/-- what is asked of the three standard messages and of the codes at the positions P -/
structure StdLn.Hyp (L tW tU tO : ℕ) : Prop where
  okW  : D.MW.OK L tW
  okU  : D.MU.OK L tU
  okO  : D.MO.OK L tO
  dist : D.MW.Cm.Dist D.d ∧ D.MU.Cm.Dist D.d ∧ D.MO.Cm.Dist D.d
  tr   : D.MW.Cm.Transparent ∧ D.MU.Cm.Transparent ∧ D.MO.Cm.Transparent
  rad  : D.er ≤ D.MW.e ∧ D.er ≤ D.MU.e ∧ D.er ≤ D.MO.e
  lt   : D.er < D.d
  lc   : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.er D.Lc
  l2   : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.er D.L2
  mca  : ∀ C : LdCode E P, C.Laws → C.MCAat D.er D.bad
  pos  : D.tb₁ + D.tb₂ ≤ tW ∧ D.tb₁ + D.tb₂ ≤ tU ∧ D.tb₁ + D.tb₂ ≤ tO

variable {D} {L tW tU tO : ℕ} (h : D.Hyp L tW tU tO)
include h

theorem stdLn_laws : ∀ o : D.C.S.O, ((D.C.S.om o).C.atPos (D.posAll o)).Laws
  | .inl (.inl (.inl e)) => e.elim
  | .inl (.inl (.inr _)) => h.okW.laws
  | .inl (.inr _) => h.okU.laws
  | .inr _ => h.okO.laws

theorem stdLn_dist : ∀ o : D.C.S.O, ((D.C.S.om o).C.atPos (D.posAll o)).Dist D.d
  | .inl (.inl (.inl e)) => e.elim
  | .inl (.inl (.inr _)) => h.dist.1
  | .inl (.inr _) => h.dist.2.1
  | .inr _ => h.dist.2.2

theorem stdLn_tr : ∀ o : D.C.S.O, ((D.C.S.om o).C.atPos (D.posAll o)).Transparent
  | .inl (.inl (.inl e)) => e.elim
  | .inl (.inl (.inr _)) => h.tr.1
  | .inl (.inr _) => h.tr.2.1
  | .inr _ => h.tr.2.2

theorem stdLn_fits :
    ∀ (o : D.C.S.O) (f g : (D.C.S.om o).C.Word),
      ((D.C.S.om o).C.atPos (D.posAll o)).Near D.er f g → (D.C.S.om o).C.Near (D.C.S.om o).e f g
  | .inl (.inl (.inl e)), _, _, _ => e.elim
  | .inl (.inl (.inr _)), _, _, hn => le_trans hn h.rad.1
  | .inl (.inr _), _, _, hn => le_trans hn h.rad.2.1
  | .inr _, _, _, hn => le_trans hn h.rad.2.2

variable [Nonempty P]

theorem stdLn_d1 : D.T.D₁.OK := by
  have hL : D.pl.G₁.C.Laws := ld_laws_fam E P _ _ fun a => stdLn_laws h a.1
  have hD : D.pl.G₁.C.Dist D.d := ld_dist_fam _ D.d fun a => stdLn_dist h a.1
  exact
    { ev := by
        letI : DecidableEq (D.pl.G₁.Row D.C.B₁) := Classical.decEq _
        exact ok_indep E (D.pl.G₁.Row D.C.B₁)
      list := h.lc _ hL hD
      fits := fun a f g hn => stdLn_fits h a.1 f g hn
      tail := ldTower_base E _ D.tb₁ _ D.d D.bad D.L2
        ⟨hL, ld_transp_fam _ fun a => stdLn_tr h a.1, h.lt, h.mca _ hL,
          h.l2 _ (ld_laws_il E P _ Bool hL) (ld_dist_il E P _ Bool D.d hD)⟩ }

theorem stdLn_d2 : D.T.D₂.OK := by
  have hL : D.pl.G₂.C.Laws := ld_laws_fam E P _ _ fun a => stdLn_laws h a.1.1
  have hD : D.pl.G₂.C.Dist D.d := ld_dist_fam _ D.d fun a => stdLn_dist h a.1.1
  exact
    { ev := by
        letI : DecidableEq (D.pl.G₂.Row LinB₂) := Classical.decEq _
        exact ok_indep E (D.pl.G₂.Row LinB₂)
      list := h.lc _ hL hD
      fits := fun a f g hn => stdLn_fits h a.1.1 f g hn
      tail := ldTower_base E _ D.tb₂ _ D.d D.bad D.L2
        ⟨hL, ld_transp_fam _ fun a => stdLn_tr h a.1.1, h.lt, h.mca _ hL,
          h.l2 _ (ld_laws_il E P _ Bool hL) (ld_dist_il E P _ Bool D.d hD)⟩ }

theorem stdLn_q : D.T.Q.OK :=
  ldChain_cons E _ _ _ D.T.D₁ _ D.T.d₁ D.T.d₁' (stdLn_d1 h)
    (ldChain_cons E _ _ _ D.T.D₂ D.T.Q' D.T.d₂ D.T.d₂' (stdLn_d2 h) (ldChain_nil E _ _ _ _))

omit h in
theorem stdLn_says : D.C.Says D.T.Q.base D.T.fq :=
  ldLinPlan_says E _ _ _ _ D.C D.pl _ D.T.Q'.base D.T.fa (fun _ _ => by simp [Slf.val])
    ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial, fun _ _ _ => trivial⟩

open Classical in
theorem stdLn_demand [Nonempty (Fin Cf.C₀.n)] :
    ∀ V, D.T.Q.q V → D.C.P.q5 (D.Sn L tW tU tO) (fun _ => True) (V.biUnion D.C.toE.src) :=
  ldDemand_plan E _ _ _ _ D.C D.pl D.T (D.Sn L tW tU tO) (fun _ => True) (fun _ => True)
    (fun a => a.elim) (fun _ => 0) (ldDemand_nil E _ _ _ _ (fun _ => True) _ trivial)
    (fun _ _ => trivial) (fun a => a.elim)
    (fun _ => le_trans (ldDemand_plain E _ _ _ _ D.C D.pl D.T _ _ 0 fun _ _ => le_refl 0) h.pos.1)
    (fun _ => le_trans (ldDemand_plain E _ _ _ _ D.C D.pl D.T _ _ 0 fun _ _ => le_refl 0) h.pos.2.1)
    (fun _ => le_trans (ldDemand_plain E _ _ _ _ D.C D.pl D.T _ _ 0 fun _ _ => le_refl 0) h.pos.2.2)

end

/-- The two items of the object for the test with standard parts. -/
def Spec.ldOLF_std (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn Cf P)
      (badF LF L tW tU tO : ℕ) (d : D.C.P.W0) (d0 : D.O.left.AMsg),
    HasDist Cf.C₀.G Cf.C₀.d → HasDist Cf.X.G Cf.C₀.d → Cf.eM < Cf.C₀.d → D.e' ≤ Cf.eM →
    Cf.X.MCAeq D.e' badF → (∀ f : Cf.X.Row → Fin Cf.C₀.n → E, ListLE (DecodesTo Cf.X.G D.e' f) LF) →
    Function.Injective D.py → D.Hyp L tW tU tO →
    LinListR D.O.left
      (D.O.full (D.Sn L tW tU tO)
        (badF + LF * (Cf.X.v * Fintype.card E ^ (Cf.X.v - 1))) D.T.Q D.T.fq d)
      (D.O.hFull (D.Sn L tW tU tO) _ D.T.Q D.T.fq d)
      (D.O.numsF (D.Sn L tW tU tO) _ D.T.Q D.T.fq d) ∧
    LinKnowR D.O.left
      (D.O.full (D.Sn L tW tU tO)
        (badF + LF * (Cf.X.v * Fintype.card E ^ (Cf.X.v - 1))) D.T.Q D.T.fq d)
      d0 (D.O.numsF (D.Sn L tW tU tO) _ D.T.Q D.T.fq d).err

open Classical in
theorem ldOLF_std (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldOLF_std F E :=
  fun _ _ _ _ _ D badF LF L tW tU tO d d0 hd hdX he he' hm hL hpy h =>
    ldOLF_lin F E D.O badF LF (D.Sn L tW tU tO) (fun _ => True) D.T.Q D.T.fq d d0 hd hdX he he' hm
      hL hpy (stdLn_snd D h.okW h.okU h.okO) stdLn_says (stdLn_q h) (stdLn_demand h)

end Cb
