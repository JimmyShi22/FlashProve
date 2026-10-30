-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinStd2Proofs.lean: for toys: the test for linear constraints with standard parts,
over a preamble that leaves a family (Cb/Obj/LdObjectLinStd2.lean): its two lists (`LinListR`,
`LinKnowR`), and its tail with the bound on the oracles left, under the hypotheses of
`Spec.ldOLF_std2` and `Spec.ldOLF_std2_tail`.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation, one of the four sub-protocols of the library's holographic interactive oracle
proof; there it follows a preamble (Hiop/RecSubs.lean, Hiop/RecBuild.lean). For the filling of the
test's open parameters in Cb/Obj/LdObjectLinStd2.lean, this file proves that the hypotheses on
protocols in `Spec.ldOLF_lin` and `Spec.ldOLF_tailF` (Cb/Obj/LdObjectLinFull.lean) follow from
hypotheses on codes, sample maps and numbers.

The conditions (`StdLn2.Hyp`), statements (Cb.Spec.ldOLF_std2*) and proofs.

Main names:
  `D.Hyp L tW tU tO ba`: `M.OK` for the three standard messages; distance d, transparent, "er
    implies the member's radius" for them and for every member of the family that the preamble
    left, as it is read at the common positions; `lawsA`; er < d;
    every code at these positions with its laws and distance d has lists of at most Lc (L2) at er,
    and every code with its laws at most "bad" exceptional coefficients at er;
    each encoding of the three standard messages hides as many positions as the tests that hold it
    draw: Ω: tb₁ + tb₂; G_u: tb₁; W: tb₂;
    the message of index masks: tb₂ + tb₃ ≤ ba; any other member a of the family: tb₃ ≤ ba a
    (`posA`).
  `std2_snd`, `std2_d1`, `std2_d2`, `std2_d3`, `std2_q`, `std2_rest`, `std2_saysA`, `std2_says`,
    `std2_demand`: `Sn.OK`; the three tests; `Qt.OK`; restG is rest; the third test's claim says
    "more"; `C.Says`; the demand on positions.
  `Spec.ldOLF_std2`: the index code and P have a position (`Nonempty (Fin Cf.C₀.n)`, `Nonempty P`),
    the conditions on the index code, `Function.Injective D.py` and `D.Hyp` ⇒ `LinListR` ∧
    `LinKnowR` for the test with its closing.
  `Spec.ldOLF_std2_tail`: and, under the hypotheses of its statement, the test is a tail within: at
    most t positions of the encoded index, at most ba a long positions of each oracle message a
    that the preamble left.

Limits: this file does not say that the conditions can be met. The standard parts are no proposal
for a protocol. One instance.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinStd2
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the instance that decides equality of members of a group, as it stands in the group's complex
(for groups of a signature cut down several times the search does not find it) -/
def Grp.decMemEq {E : Type} {S : Sig E} (G : Grp S) : DecidableEq G.A := inferInstance

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] (D : StdLn2 Cf P)

instance std2_decG₃ : DecidableEq D.G₃.A := D.G₃.decMemEq

/-- what the three sendings ask -/
theorem std2_snd {L tW tU tO : ℕ} (hW : D.MW.OK L tW) (hU : D.MU.OK L tU) (hO : D.MO.OK L tO) :
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

/-- What is asked of the three standard messages, of the family that the preamble left, and of the
codes at the positions P. -/
structure StdLn2.Hyp (L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) : Prop where
  okW   : D.MW.OK L tW
  okU   : D.MU.OK L tU
  okO   : D.MO.OK L tO
  dist  : D.MW.Cm.Dist D.d ∧ D.MU.Cm.Dist D.d ∧ D.MO.Cm.Dist D.d
  tr    : D.MW.Cm.Transparent ∧ D.MU.Cm.Transparent ∧ D.MO.Cm.Transparent
  rad   : D.er ≤ D.MW.e ∧ D.er ≤ D.MU.e ∧ D.er ≤ D.MO.e
  lawsA : ∀ a, ((D.Sa.om a).C.atPos (D.posA a)).Laws
  distA : ∀ a, ((D.Sa.om a).C.atPos (D.posA a)).Dist D.d
  trA   : ∀ a, ((D.Sa.om a).C.atPos (D.posA a)).Transparent
  fitsA : ∀ a (f g : (D.Sa.om a).C.Word),
    ((D.Sa.om a).C.atPos (D.posA a)).Near D.er f g → (D.Sa.om a).C.Near (D.Sa.om a).e f g
  lt    : D.er < D.d
  lc    : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.er D.Lc
  l2    : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.er D.L2
  mca   : ∀ C : LdCode E P, C.Laws → C.MCAat D.er D.bad
  posO  : D.tb₁ + D.tb₂ ≤ tO
  posU  : D.tb₁ ≤ tU
  posW  : D.tb₂ ≤ tW
  posA  : ∀ a, (if a = D.iM then D.tb₂ else 0) + D.tb₃ ≤ ba a

variable {D} {L tW tU tO : ℕ} {ba : D.Sa.O → ℕ} (h : D.Hyp L tW tU tO ba)
include h

theorem std2_laws : ∀ o : D.C.S.O, ((D.C.S.om o).C.atPos (D.posAll o)).Laws
  | .inl (.inl (.inl a)) => h.lawsA a
  | .inl (.inl (.inr _)) => h.okW.laws
  | .inl (.inr _) => h.okU.laws
  | .inr _ => h.okO.laws

theorem std2_dist : ∀ o : D.C.S.O, ((D.C.S.om o).C.atPos (D.posAll o)).Dist D.d
  | .inl (.inl (.inl a)) => h.distA a
  | .inl (.inl (.inr _)) => h.dist.1
  | .inl (.inr _) => h.dist.2.1
  | .inr _ => h.dist.2.2

theorem std2_tr : ∀ o : D.C.S.O, ((D.C.S.om o).C.atPos (D.posAll o)).Transparent
  | .inl (.inl (.inl a)) => h.trA a
  | .inl (.inl (.inr _)) => h.tr.1
  | .inl (.inr _) => h.tr.2.1
  | .inr _ => h.tr.2.2

theorem std2_fits :
    ∀ (o : D.C.S.O) (f g : (D.C.S.om o).C.Word),
      ((D.C.S.om o).C.atPos (D.posAll o)).Near D.er f g → (D.C.S.om o).C.Near (D.C.S.om o).e f g
  | .inl (.inl (.inl a)), f, g, hn => h.fitsA a f g hn
  | .inl (.inl (.inr _)), _, _, hn => le_trans hn h.rad.1
  | .inl (.inr _), _, _, hn => le_trans hn h.rad.2.1
  | .inr _, _, _, hn => le_trans hn h.rad.2.2

variable [Nonempty P]

theorem std2_d1 : D.T.D₁.OK := by
  have hL : D.pl.G₁.C.Laws := ld_laws_fam E P _ _ fun a => std2_laws h a.1
  have hD : D.pl.G₁.C.Dist D.d := ld_dist_fam _ D.d fun a => std2_dist h a.1
  exact
    { ev := by
        letI : DecidableEq (D.pl.G₁.Row D.C.B₁) := Classical.decEq _
        exact ok_indep E (D.pl.G₁.Row D.C.B₁)
      list := h.lc _ hL hD
      fits := fun a f g hn => std2_fits h a.1 f g hn
      tail := ldTower_base E _ D.tb₁ _ D.d D.bad D.L2
        ⟨hL, ld_transp_fam _ fun a => std2_tr h a.1, h.lt, h.mca _ hL,
          h.l2 _ (ld_laws_il E P _ Bool hL) (ld_dist_il E P _ Bool D.d hD)⟩ }

theorem std2_d2 : D.T.D₂.OK := by
  have hL : D.pl.G₂.C.Laws := ld_laws_fam E P _ _ fun a => std2_laws h a.1.1
  have hD : D.pl.G₂.C.Dist D.d := ld_dist_fam _ D.d fun a => std2_dist h a.1.1
  exact
    { ev := by
        letI : DecidableEq (D.pl.G₂.Row LinB₂) := Classical.decEq _
        exact ok_indep E (D.pl.G₂.Row LinB₂)
      list := h.lc _ hL hD
      fits := fun a f g hn => std2_fits h a.1.1 f g hn
      tail := ldTower_base E _ D.tb₂ _ D.d D.bad D.L2
        ⟨hL, ld_transp_fam _ fun a => std2_tr h a.1.1, h.lt, h.mca _ hL,
          h.l2 _ (ld_laws_il E P _ Bool hL) (ld_dist_il E P _ Bool D.d hD)⟩ }

theorem std2_d3 : D.D₃.OK := by
  have hL : D.G₃.C.Laws := ld_laws_fam E P _ _ fun a => std2_laws h a.1.1.1
  have hD : D.G₃.C.Dist D.d := ld_dist_fam _ D.d fun a => std2_dist h a.1.1.1
  exact
    { ev := by
        letI : DecidableEq (D.G₃.Row D.BM) := Classical.decEq _
        exact ok_indep E (D.G₃.Row D.BM)
      list := h.lc _ hL hD
      fits := fun a f g hn => std2_fits h a.1.1.1 f g hn
      tail := ldTower_base E _ D.tb₃ _ D.d D.bad D.L2
        ⟨hL, ld_transp_fam _ fun a => std2_tr h a.1.1.1, h.lt, h.mca _ hL,
          h.l2 _ (ld_laws_il E P _ Bool hL) (ld_dist_il E P _ Bool D.d hD)⟩ }

instance std2_empty : IsEmpty (D.pl.S₂.sub D.D₃.kp).O := ⟨fun a => a.2⟩

theorem std2_q' : D.T.Q'.OK := ldChain_cons E _ _ _ D.D₃ _ _ _ (std2_d3 h) (ldChain_nil E _ _ _ _)

theorem std2_q : D.T.Q.OK :=
  ldChain_cons E _ _ _ D.T.D₁ _ D.T.d₁ D.T.d₁' (std2_d1 h)
    (ldChain_cons E _ _ _ D.T.D₂ D.T.Q' D.T.d₂ D.T.d₂' (std2_d2 h) (std2_q' h))

omit h

omit [Nonempty P] in
/-- restG is "rest" -/
theorem std2_rest (sa : D.C.Sta) (m : D.C.S.Msg) :
    D.pl.restG.val sa (D.pl.G₂.msg (D.C.S.res (T := OMsg.Msg) D.pl.kp₁ m)) =
      D.C.rest sa (D.C.aM m) :=
  ldForm_onMem E _ _ D.G₂ ⟨D.nM, D.kA D.iM⟩ (Or.inr (Or.inr rfl))
    D.cM sa (D.C.S.res (T := OMsg.Msg) D.pl.kp₁ m)

/-- the value of a filed row on the third group's message -/
theorem std2_row (b : D.BM) (st : D.SbM b) (m : D.C.S.Msg) :
    (D.D₃.sl b).val st (D.G₃.msg (D.pl.last m)) = (D.slM b).val st (D.Sa.ents (D.C.aM m)) :=
  @ldForm_push E (D.SbM b) D.Sa.Ent D.G₃.C.J _ _ _ (Classical.decEq _) D.φ₃ (D.slM b)
    st (D.G₃.msg (D.pl.last m))

theorem std2_saysA : D.pl.SaysA D.T.Q'.base D.T.fa where
  fwd := fun _ _ m _ hm => ⟨fun b => (std2_row b _ m).trans (hm b), trivial⟩
  bwd := fun _ _ m _ _ hm b => (std2_row b _ m).symm.trans (hm.1 b)
  on := fun _ _ _ => trivial

theorem std2_says : D.C.Says D.T.Q.base D.T.fq :=
  ldLinPlan_says E _ _ _ _ D.C D.pl _ D.T.Q'.base D.T.fa std2_rest std2_saysA

end

section
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] [Nonempty P] {D : StdLn2 Cf P}

/-- what the three tests need of each oracle message -/
theorem std2_needA (a : D.Sa.O) :
    D.T.D₁.need (D.T.D₂.need (D.D₃.need fun _ => 0)) (D.nA a) =
      (if a = D.iM then D.tb₂ else 0) + D.tb₃ := by
  simp [LdRunD.need, StdLn2.isA]

theorem std2_needW : D.T.D₁.need (D.T.D₂.need (D.D₃.need fun _ => 0)) D.C.nW = D.tb₂ := by
  simp [LdRunD.need, StdLn2.isA]

theorem std2_needU : D.T.D₁.need (D.T.D₂.need (D.D₃.need fun _ => 0)) D.C.nU = D.tb₁ := by
  simp [LdRunD.need]

theorem std2_needO : D.T.D₁.need (D.T.D₂.need (D.D₃.need fun _ => 0)) D.C.nO = D.tb₁ + D.tb₂ := by
  simp [LdRunD.need, StdLn2.isA]

end
section
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E} {P : Type}
  [Fintype P] [Nonempty P] {D : StdLn2 Cf P} {L tW tU tO : ℕ} {ba : D.Sa.O → ℕ}

open Classical in
/-- Under the hypotheses below, the demand on positions: what the plan needs is within what the sent
words bear, and within ba on what the preamble left. -/
theorem std2_demand [Nonempty (Fin Cf.C₀.n)] (h : D.Hyp L tW tU tO ba) :
    ∀ V, D.T.Q.q V →
      D.C.P.q5 (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba)
        (V.biUnion D.C.toE.src) :=
  ldDemand_plan E _ _ _ _ D.C D.pl D.T (D.Sn L tW tU tO)
    (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) (fun _ => True) ba (D.D₃.need fun _ => 0)
    (ldDemand_cons E _ _ _ D.D₃ _ _ _ (fun _ => True) (fun _ => 0)
      (ldDemand_nil E _ _ _ _ (fun _ => True) _ trivial))
    (fun _ hW => hW) (fun a => le_of_eq_of_le (std2_needA a) (h.posA a))
    (fun _ => le_of_eq_of_le std2_needW h.posW) (fun _ => le_of_eq_of_le std2_needU h.posU)
    (fun _ => le_of_eq_of_le std2_needO h.posO)

end

/-- The two items of the object, for the test with standard parts over a preamble that leaves a
family. -/
def Spec.ldOLF_std2 (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn2 Cf P)
      (badF LF L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) (d : D.C.P.W0) (d0 : D.O.left.AMsg),
    HasDist Cf.C₀.G Cf.C₀.d → HasDist Cf.X.G Cf.C₀.d → Cf.eM < Cf.C₀.d → D.e' ≤ Cf.eM →
    Cf.X.MCAeq D.e' badF → (∀ f : Cf.X.Row → Fin Cf.C₀.n → E, ListLE (DecodesTo Cf.X.G D.e' f) LF) →
    Function.Injective D.py → D.Hyp L tW tU tO ba →
    LinListR D.O.left
      (D.O.full (D.Sn L tW tU tO)
        (badF + LF * (Cf.X.v * Fintype.card E ^ (Cf.X.v - 1))) D.T.Q D.T.fq d)
      (D.O.hFull (D.Sn L tW tU tO) _ D.T.Q D.T.fq d)
      (D.O.numsF (D.Sn L tW tU tO) _ D.T.Q D.T.fq d) ∧
    LinKnowR D.O.left
      (D.O.full (D.Sn L tW tU tO)
        (badF + LF * (Cf.X.v * Fintype.card E ^ (Cf.X.v - 1))) D.T.Q D.T.fq d)
      d0 (D.O.numsF (D.Sn L tW tU tO) _ D.T.Q D.T.fq d).err

/-- The tail, with its bound: at most t positions of the encoded index, at most ba a long positions
of each oracle message a that the preamble left. -/
def Spec.ldOLF_std2_tail (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn2 Cf P)
      (badF LF L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) (d : D.C.P.W0) (d₀ : D.O.P.W0),
    HasDist Cf.X.G Cf.C₀.d → Cf.eM < Cf.C₀.d → D.e' ≤ Cf.eM → Cf.X.MCAeq D.e' badF →
    (∀ f : Cf.X.Row → Fin Cf.C₀.n → E, ListLE (DecodesTo Cf.X.G D.e' f) LF) →
    Function.Injective D.py → D.Hyp L tW tU tO ba →
    TailTr (D.O.full (D.Sn L tW tU tO)
        (badF + LF * (Cf.X.v * Fintype.card E ^ (Cf.X.v - 1))) D.T.Q D.T.fq d)
      (D.O.hFull0 (D.Sn L tW tU tO) _ D.T.Q D.T.fq d) (D.O.P.j0 D.O.on0) trivRels
      (D.O.extF (D.Sn L tW tU tO) _ D.T.Q D.T.fq d d₀)
      (D.O.numsF0 (D.Sn L tW tU tO) _ D.T.Q D.T.fq d)
      (D.Sa.qFam (E₀ := D.O.P.ix) (fun V => V.card ≤ D.t) ba)

open Classical in
theorem ldOLF_std2 (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldOLF_std2 F E :=
  fun _ _ _ _ _ D badF LF L tW tU tO ba d d0 hd hdX he he' hm hL hpy h =>
    ldOLF_lin F E D.O badF LF (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba)
      D.T.Q D.T.fq d d0 hd hdX he he' hm hL hpy (std2_snd D h.okW h.okU h.okO) std2_says
      (std2_q h) (std2_demand h)

open Classical in
theorem ldOLF_std2_tail (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Spec.ldOLF_std2_tail F E :=
  fun Cf _ _ _ _ D badF LF L tW tU tO ba d d₀ hdX he he' hm hL hpy h =>
    ldOLF_tailF F E D.O _ (D.Sn L tW tU tO) (fun _ => True) ba D.T.Q D.T.fq d d₀ trivial
      (ldLin_foldErr D.C.P Cf.C₀.d badF LF hdX he he' hm hL) hpy (std2_snd D h.okW h.okU h.okO)
      std2_says (std2_q h) (std2_demand h)

end Cb
