-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectNull.lean: for small example instances: trivial sub-protocols without rounds, for
three of the five sub-protocol terms of the holographic IOP; each meets, under the hypotheses of its
statement, its term's own condition (its OK).

Definitions, statements as theorems, proofs. Generic: any configuration, an abstract field. A tool
for a degenerate guard; no parameter of a protocol.

The structure `LdObj` (Cb/Obj/LdObject.lean) takes any term of each of five kinds with its own OK.
To show that its conditions are consistent, the smallest terms will do. Over the data
`D : StdLn Cf P` (Cb/Obj/LdObjectLinStd.lean: the preamble leaves no oracle message), where the
claim reads nothing of the index and the model is trivial:
  `D.nullWf cl₀ z0`: weights-formedness without rounds: the verifier writes the claim cl₀.
    `stdLn_nullWf`: its OK, if the row of cl₀ is trivial (g = 0, target 0) and every message holds
    an index.
  `D.nullReq cl₀ c0`: the preamble of a request without rounds: the same. `stdLn_nullReq`: its OK,
    if the row of cl₀ is trivial and every cell value is a witness in Rno.
  `D.nullLinB N w₀`: the batch test without rounds: the verifier accepts. `stdLn_nullLinB`: its OK,
    if all claims have trivial rows: on the statements whose index decodes (the second regime) the
    relaxed relation holds outright.

Limits: what these terms show: under the hypotheses above, that the conditions which the structure
`LdObj` puts on a preamble and on the batch test, each by itself (the fields wf, req, linB of
`LdObj.OK`), can be met, and that their types fit the two "what a preamble leaves". They do not show
anything about the lots' terms (lookups, segments, the real batch test). With them the online phase
has no round.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObject
import Cb.Obj.LdObjectLinStd
import Cb.Req1.LdReqStart
import Ior.LinkVRules
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace StdLn
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  {P : Type} [Fintype P] (D : StdLn Cf P)

/-- The data in the form of the fields of `LdObj`. -/
@[reducible] def Od : LdOLd Cf where
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

omit [Fintype F] in
theorem od_ol : D.Od.ol = D.O := rfl

/-- the row of the claim reads nothing and has the target 0 -/
def Triv (cl : D.Cl) : Prop := (∀ y, D.g cl y = 0) ∧ D.τ cl = 0

theorem holds_triv {cl : D.Cl} (h : D.Triv cl) (rec : Cf.conf.Rec)
    (U : Cf.conf.Msg) (m : (Sig.nil E).Msg) : D.Od.ol.holds cl rec U m := by
  refine ⟨?_, trivial⟩
  show ∑ y, ∑ c, D.g cl y * _ * _ + 0 = D.τ cl
  rw [h.2]
  simp [h.1]

/-- Weights-formedness without rounds. -/
def nullWf (cl₀ : D.Cl) (z0 : Cf.conf.PIdx) : D.Od.ol.WfT Unit where
  Wp := Cf.conf.PIdx
  pi := id
  z0 := z0
  B := idxRelsK Cf.conf D.Od.ol.holds D.Od.ol.holds fun _ => ()
  F := IOR.pure (fun rec => some ((cl₀, rec), Sig.nilFam E)) (ldStartE E Cf.conf.E0)
  H := IOR.Honest.pure _ _ fun a => (((cl₀, a.1), Sig.nilFam E), (Sig.nilFam E, a.2))
  ext := fun _ _ w => w.2
  P := IOR.Nums.pure Unit _ _

/-- The preamble of a request without rounds. -/
def nullReq (cl₀ : D.Cl) (c0 : Cf.conf.Cells) : D.Od.ol.ReqT Unit where
  Wp := Cf.conf.PIdx
  pi := id
  B := D.Od.ol.bEnd fun _ => ()
  F := IOR.pure (fun x => some ((cl₀, x.2), Sig.nilFam E)) (ldStartE E Cf.conf.E0)
  H := IOR.Honest.pure _ _ fun a => (((cl₀, a.1.2), Sig.nilFam E), (Sig.nilFam E, a.2.1))
  ext := fun _ _ w => (w.2, c0)
  P := IOR.Nums.pure Unit _ _

/-- the second regime: the index decodes with its record -/
def onDec : (D.Od.ol.P.D.X.Row → Fin Cf.C₀.n → E) → D.Od.ol.P.D.X.Rec → Prop := fun f rec =>
  Cf.X.dec f rec ≠ none

/-- the test without rounds, for one instance -/
@[reducible] def nullR :
    IOR (D.Od.ol.left.Xl × Cf.conf.Rec) D.Od.ol.left.El Unit extNone :=
  IOR.pure (fun _ => some ()) (ExtMap.toNone _)
@[reducible] def nullH : D.nullR.Honest D.Od.ol.P.W0 Unit :=
  IOR.Honest.pure _ _ fun _ => ((), ())

/-- The batch test without rounds. -/
def nullLinB (N : ℕ) (w₀ : D.Od.ol.P.W0) : D.Od.ol.LinBT N where
  R := D.nullR
  A := RoundSplits.allLocal D.nullR.shape
  Wi := D.Od.ol.P.W0
  W0' := Cf.conf.PIdx
  Wo := Unit
  H := D.nullH.localV Cf.conf.PIdx
  mkW := fun p a => D.Od.ol.fi (p, a)
  RiV := fun x y w => (D.Od.ol.P.j0 D.onDec).rel x y w.2
  RoV := fun _ _ _ => True
  P := ⟨(), 0, 0,
    fun J ρs Ts =>
      ∀ j : J, (IOR.Nums.pure Unit (fun _ : D.Od.ol.left.Xl × Cf.conf.Rec => some ())
          (ExtMap.toNone D.Od.ol.left.El)).bud
        (ρs j) (Ts j)⟩
  on0 := D.onDec
  ext := fun _ _ _ => w₀
  qi := fun _ => True

end StdLn

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  {P : Type} [Fintype P] (D : StdLn Cf P)

omit [Field E] [Fintype E] in
/-- a step that adds the empty families is a prefix (`IOR.IdxPrefix`, Cb/Ld/LdWfPre.lean) -/
theorem null_prefix {X X' : Type} (E0 : ExtSpec) (f : X → Option X') :
    (IOR.pure f (ldStartE E E0)).IdxPrefix :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ q => q.1.elim⟩

theorem nullWf_step (cl₀ : D.Cl) (h : D.Triv cl₀) (hh : ∀ U, (Cf.conf.held U).isSome) :
    StepT (fun rec : Cf.conf.Rec => some ((cl₀, rec), Sig.nilFam E)) (ldStartE E Cf.conf.E0)
      (fun a : Cf.conf.Rec × Cf.conf.PIdx => (((cl₀, a.1), Sig.nilFam E), (Sig.nilFam E, a.2)))
      (fun _ w => w.2) (ldWfRels Cf.conf fun _ => ())
      ((Sig.nil E).over (idxRelsK Cf.conf D.Od.ol.holds D.Od.ol.holds fun _ => ())).cf where
  isLocal := ldStartE_isLocal
  acc := fun x y w hw => ⟨rfl, fun a => a.elim, fun a => a.elim, hw.1, D.holds_triv h _ _ _⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ => rfl
  know := by
    intro x y x' w' hon hf hw
    have hx : x' = ((cl₀, x), Sig.nilFam E) := (Option.some.inj hf).symm
    subst hx
    show (Cf.conf.D y x).isSome
    have hc : ¬ Cf.conf.coll y x.1 := hon
    rcases hw with hw | hw
    · obtain ⟨-, U, hU, -⟩ := hw
      have hU' : Cf.conf.dcd y x = some U := hU
      unfold ConfigurationWithOutOfDomainSample.D
      rw [if_neg hc, hU']
      exact hh U
    · exact absurd ⟨fun a => a.elim, hc⟩ hw

theorem stdLn_nullWf (cl₀ : D.Cl) (z0 : Cf.conf.PIdx)
    (h : D.Triv cl₀) (hh : ∀ U, (Cf.conf.held U).isSome) :
    (D.nullWf cl₀ z0).OK fun _ => () where
  good := goodT_pure _ _ _ _ _ _ _ _ _ _ _ _ _ (nullWf_step D cl₀ h hh)
  prefx := null_prefix _ _
  passes := fun x _ _ x' hx => by
    have : x' = ((cl₀, x), Sig.nilFam E) := (Option.some.inj hx).symm
    rw [this]
    rfl
  hands := fun _ _ _ _ _ _ _ => rfl
  relB := fun _ _ _ hB => hB
  relRB := fun _ _ U hU hl => ⟨U, hU, hl⟩
  onB := fun _ hon => hon

theorem nullReq_step (cl₀ : D.Cl) (c0 : Cf.conf.Cells)
    (h : D.Triv cl₀) (hno : ∀ i x c, Cf.conf.Rno i x c) :
    StepT (fun x : Cf.conf.X × Cf.conf.Rec => some ((cl₀, x.2), Sig.nilFam E))
      (ldStartE E Cf.conf.E0)
      (fun a : (Cf.conf.X × Cf.conf.Rec) × (Cf.conf.PIdx × Cf.conf.Cells) =>
        (((cl₀, a.1.2), Sig.nilFam E), (Sig.nilFam E, a.2.1)))
      (fun _ w => (w.2, c0)) (D.Od.ol.jReq fun _ => ())
      ((Sig.nil E).over (D.Od.ol.bEnd fun _ => ())).cf where
  isLocal := ldStartE_isLocal
  acc := fun x y w hw => ⟨rfl, fun a => a.elim, fun a => a.elim, hw.1, D.holds_triv h _ _ _⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ => rfl
  know := by
    intro x y x' w' hon _ _
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 (show (Cf.conf.D y x.2).isSome from hon)
    exact ⟨i, hi, hno i x.1 c0⟩

theorem stdLn_nullReq (cl₀ : D.Cl) (c0 : Cf.conf.Cells)
    (h : D.Triv cl₀) (hno : ∀ i x c, Cf.conf.Rno i x c) :
    (D.nullReq cl₀ c0).OK fun _ => () where
  good := goodT_pure _ _ _ _ _ _ _ _ _ _ _ _ _ (nullReq_step D cl₀ c0 h hno)
  prefx := null_prefix _ _
  passes := fun x _ _ x' hx => by
    have : x' = ((cl₀, x.2), Sig.nilFam E) := (Option.some.inj hx).symm
    rw [this]
  hands := fun _ _ _ _ _ _ _ => rfl
  last := D.Od.ol.endOK _

/-- the test without rounds, for one instance: a step from the test's first joint, in the second
regime, to the trivial statement -/
theorem nullLin_step (w₀ : D.Od.ol.P.W0) (h : ∀ cl, D.Triv cl) :
    StepT (fun _ : D.Od.ol.left.Xl × Cf.conf.Rec => some ()) (ExtMap.toNone D.Od.ol.left.El)
      (fun _ : (D.Od.ol.left.Xl × Cf.conf.Rec) × D.Od.ol.P.W0 => ((), ())) (fun _ _ => w₀)
      (D.Od.ol.P.j0 D.onDec) trivRels where
  isLocal := fun _ _ q => q.elim
  acc := fun _ _ _ _ => ⟨rfl, trivial⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ => rfl
  know := by
    intro x y _ _ hon _ _
    obtain ⟨U, hU⟩ := Option.ne_none_iff_exists'.1 hon.1
    refine ⟨⟨fun a => a.elim, trivial⟩, U, hU, ?_⟩
    show ∑ y, ∑ c, D.g x.1.1 y * _ * _ + 0 = D.τ x.1.1
    rw [(h x.1.1).2]
    simp [(h x.1.1).1]

theorem stdLn_nullLinB (N : ℕ) (w₀ : D.Od.ol.P.W0) (h : ∀ cl, D.Triv cl) :
    (D.nullLinB N w₀).OK := by
  have hG := goodT_pure _ _ _ _ _ _ _ _ _ _ _ _ _ (nullLin_step D w₀ h)
  exact
    { point := ⟨()⟩
      isLocal := hG.isLocal
      coherent := trivial
      tied := fun _ _ hp => absurd hp (Finset.notMem_empty _)
      idxShared := fun _ _ _ => rfl
      idxReads := fun _ => Nat.zero_le _
      acc := accV_local _ _ _ _ D.nullR _ _ Cf.conf.PIdx D.nullH
        (D.Od.ol.P.j0 D.onDec).rel (fun _ _ _ => True) _ _ hG.acc (fun _ _ => rfl)
        (fun _ _ _ hw => hw) (fun _ _ _ _ _ _ _ _ => trivial)
      exact := exactV_local _ _ _ _ D.nullR _ _ Cf.conf.PIdx D.nullH (D.Od.ol.P.j0 D.onDec).rel
        _ _ N hG.exact (fun _ _ => rfl) (fun _ _ _ hw => hw)
      bud0 := fun _ _ _ => trivial
      prBad := prRho_empty _ fun ρ hρ => by
        rcases hρ with hρ | hρ
        · exact hρ
        · cases hρ
      bridge := fun x y w hw => ldOL_rel F E D.Od.ol x y w hw
      fits := fun _ _ hd _ => hd
      know := ⟨fun _ => (),
        fun a τ b w hon _ _ _ => (nullLin_step D w₀ h).know a.1 a.2 () () hon rfl trivial,
        fun _ _ => trivial⟩
      reads := fun _ => ⟨trivial, fun _ hp => absurd hp (Finset.notMem_empty _)⟩
      mono := fun _ _ _ _ => trivial }

end
end Cb
