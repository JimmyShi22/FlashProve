-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Carry.lean: WHAT IS CARRIED BEHIND THE CLOSING OF A LINK (kind K10), IN
VECTORS: a proposition on what the closing's text hands on and on a word; that it is the relaxed
relation of the library's joint behind the batching and the fold, at the form with room; and the two
halves of K10's law at one caller and one form. Definitions, statements and proofs.

  `CarryAt R N rows word`: there is a message with its randomness whose encoding, under the folded
    code of the group R, is within the joint radius of the word, and on which the vector `outVec` of
    the claim `rows` (Border.lean) has the reading of the claim's target as its value. It is said by
    the library's own relation (`LdCode.rels`, Cb/Ld/LdRel.lean) at the form "the state is the
    vector" (`Slf.idf`). It names no typed state, no seed and no form.
  `carry_iff`: at any form F on the fold's input code and any statement x behind the fold at F whose
    target is the reading of the claim's and whose form, at its state, is `outVec` of the claim: the
    relaxed relation of the joint behind the fold at F has a witness at (x, word) exactly if
    `CarryAt` holds.
  `tied_and_known`: at the caller `R.foldCaller ..` and F = "arranged plus the batched further
    weights": (1) the proved block's own reduction, at its own errors, is knowledge sound from the
    joint in front into the joint behind at F (`know_plus`); (2) where `closing` says yes on the
    reading of a written stretch, that reduction puts out a' on the stretch's image, with what the
    batching round carries and the words of `word_at`; and THE RELATION OF (1) has a witness at a'
    exactly if `CarryAt R N out` holds of the folded word a'.2.1 and the kept messages' own joint
    has a witness at what is carried (`law_tied`, `carry_iff`, `outAt_relR`).
  `outAt_relR`: the relation of (1), taken apart, by definition.
  `foldedAt Y g y z`, `word_at`: THE WORD: where `closing` says yes, the folded word that the proved
    block's reduction makes is the fold, at the reading of the point `out.gamma` that the closing
    hands on, of the group's word, arranged (the library's `ldBrG`, then the arrangement's map), and
    of the fresh mask's word; what is carried beside is the kept messages' words, untouched.

Limits. The words in front (a.2: the oracles of the typed joint in front) are letters: nothing reads
them off a description's oracles yet. THE KEPT TERM: on a kept slot `outVec` holds the kept form on
the main table of the oracle message whose number N.orc names, at the entries that N.idx names: N is
a letter: which copy of a message that is sent again that number means, and whether the pad's places
are among these entries, is whoever fills N's to say; that message's own joint stands beside,
unopened. ALL PREMISES of `tied_and_known`: the readings' `Scal`, `StepOK`, the power left out
(hfx), `DefAt`; `BatFoldOKAt`, `Reshape.Fix`, the shape's laws; the further weights 0 off the free
rows (asked outside, and again inside `OrderedV`); `OrderedV` (a clause a row), `RowFits`,
`MaskFits`, and four comparisons of public numbers. ONE family fr of further weights stands in front
of all statements: fr sees a typed row's state alone; so does the form F, and the extractor in (1),
which is that of the kind at F, not the proved block's own: for a rule without a witness
(`leads_of_know`) that costs nothing. Called at no value. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.AtForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)

variable {S : Sig GE} (R : RowsK S) (N : SlotNames R)

/-- **What is carried behind a closing**: a code word within the joint radius of the word, whose
message meets the one claim. -/
def CarryAt (rows : SingleRows) (word : R.Sh.Cf.ext.Str) : Prop :=
  ∃ u : R.Sh.Cf.N.Wit, (R.Sh.Cf.rels Slf.idf R.G.e fun _ => ()).relR
    ((readE rows.target, outVec N rows), word) u

/-- It is the relaxed relation of the joint behind the fold, at any form that reads the claim. -/
theorem carry_iff {St : Type} (F : Slf GE St R.Sh.Cin.J) (x : (R.Sh.par.reform F).Xo)
    (word : R.Sh.Cf.ext.Str) (rows : SingleRows) (ht : x.1 = readE rows.target)
    (hv : (R.Sh.par.reform F).slOut x.2 = outVec N rows) :
    (∃ u, (Tower.outJ (R.Sh.par.reform F) R.G.e).relR (x, word) u) ↔ CarryAt R N rows word := by
  constructor
  · rintro ⟨u, h1, h2⟩
    refine ⟨u, h1, ?_⟩
    show ∑ j, outVec N rows j * u.1 j = readE rows.target
    rw [← hv, ← ht]
    exact h2
  · rintro ⟨u, h1, h2⟩
    refine ⟨u, h1, ?_⟩
    show ∑ j, (R.Sh.par.reform F).slOut x.2 j * u.1 j = x.1
    rw [hv, ht]
    exact h2

/-- The relaxed relation of the joint behind the proved block at a form F, taken apart: the joint
behind the fold on the folded word, and the kept messages' own joint on what is carried. -/
theorem outAt_relR {K : Type} [Field K] [Fintype K] (s : Cb.Pv.Bat.Size K) [Nonempty s.G.P]
    (Sh : GShape s.G) (F : Slf K (Tower.BSt s.Sb s.Z) Sh.Cin.J) {St₀ : Type} {E₀ : ExtSpec}
    {Kc Wp : Type} (A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp))
    (a' : ((Sh.par.reform F).Xo × Tower.CarX s St₀) ×
      ((Sh.par.reform F).Cout.ext.prod (Tower.CarE s E₀)).Str)
    (w : (Sh.par.reform F).Cout.N.Wit × ((s.S.sub s.kp).Wit × Wp)) :
    (Tower.batFoldOutAt s Sh F A₀).relR a' w ↔
      (Tower.outJ (Sh.par.reform F) s.G.e).relR (a'.1.1, a'.2.1) w.1 ∧
        ((s.S.sub s.kp).over A₀).relR (a'.1.2, a'.2.2) w.2 := Iff.rfl

/-- The three tables in front of a fold, folded at the point g: the words of the library's
`SumPar.imp`. y: the arranged word (main rows, mask rows); z: the fresh mask's word. -/
noncomputable def foldedAt {K P : Type} [Field K] [Fintype K] [Fintype P] (Y : SumPar K P)
    (g : Fin Y.k → K) (y : Y.Cin.Word) (z : Y.Cw.Word) : Y.Cout.Word :=
  LdCode.mkW (SumPar.foldW Y.C g (LdCode.fstW y))
    (LdCode.mkW (C₁ := Y.Z) (C₂ := Y.Zw) (SumPar.foldW Y.Z (Y.pre g) (LdCode.sndW y))
      (SumPar.foldW Y.Zw (Y.pre g) z))

/-- **THE WORDS BEHIND THE PROVED BLOCK, WRITTEN OUT**, where `closing` says yes: the folded word is
the fold, AT THE READING OF THE POINT THAT THE CLOSING HANDS ON, of the group's word, arranged, and
of the fresh mask's word; what is carried is the kept messages' words, untouched. -/
theorem word_at (L : List (BatFoldCaller GE)) (c : BatFoldCaller GE) (rB rE rR : Round)
    (ρ : Rd c rB rE rR) (hS : ρ.Scal) (hst : StepOK (Yc c).val (Yc c).n c.fx (rd2 c))
    (hfx : c.fx.2 * (HVar.plain GE (Yc c).n).mon c.fx.1 = 1)
    (P : Plan) (T T' : Statement) (g : Nat) (mask : Option Nat) (out : SingleRows)
    (a : ((kBatFoldRide L).src c).X × ((kBatFoldRide L).src c).E.Str)
    (τ : Tr (rB :: rE :: List.replicate (Yc c).k rR)) (ht : ρ.DefAt (ρ.V τ))
    (h : closing P T g mask (ρ.V τ) = .ok (out, T'))
    (hO : ∀ G e z, T.groups[g]? = some G → (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
      ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z →
      Ordered c a.1 z e ((runRows T G).toList.map fun w => readE w.target))
    (hR : ∀ G, T.groups[g]? = some G → ∀ w ∈ (runRows T G).toList, RowFits (begun T g G) w)
    (τ' : Tr ((kBatFoldRide L).block c).R.red.shape)
    (a' : ((kBatFoldRide L).dst c).X × ((kBatFoldRide L).dst c).E.Str)
    (h1 : ρ.carS.tr τ = some τ') (h2 : ((kBatFoldRide L).block c).R.red.out a τ' = some a') :
    a'.2.1 = foldedAt (Yc c) (readP (Yc c).k out.gamma)
        (c.Sh.rho.map.map ((ldBrG c.s.G c.s.kp c.E₀).map a.2.1).1) a.2.2 ∧
      a'.2.2 = ((ldBrG c.s.G c.s.kp c.E₀).map a.2.1).2 := by
  obtain ⟨_, _, _, _, _, _, _, _, τ2, a2, -, -, -, -, -, -, -, -, -, -, -, -, -, t1, t2, t3⟩ :=
    law_whole L c rB rE rR ρ hS hst hfx P T T' g mask out a τ ht h hO hR
  obtain rfl := Option.some.inj (t1.symm.trans h1)
  obtain rfl := Option.some.inj (t2.symm.trans h2)
  obtain ⟨⟨⟨⟩, ⟨⟩⟩, z', ⟨⟨⟩, sum⟩, e, τk⟩ := τ2
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 t2
  have hx' := (batFoldRide_out_eq c hfx a.1 a.2 z' sum e τk).symm.trans hx
  have hp : sPt (Yc c).n (Yc c).k (sG (Yc c).val (Yc c).n (Yc c).k
      (sUpRho (Yc c).n (Yc c).k τk.rho)) = readP (Yc c).k out.gamma := by
    have e1 := (Option.some.inj hx').trans t3
    exact congrArg (fun q => q.1.2.2.2) e1
  refine ⟨?_, rfl⟩
  rw [← hp]
  rfl

section Caller
variable (keep : S.O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))
  (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- **THE TWO HALVES OF K10's LAW AT ONE CALLER AND ONE FORM.** -/
theorem tied_and_known (L : List (BatFoldCaller GE)) (rB rE rR : Round)
    (ρ : Rd (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) rB rE rR) (hS : ρ.Scal)
    (hst : StepOK (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n fx
      (rd2 (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)))
    (hfx : fx.2 * (HVar.plain GE (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).n).mon fx.1 = 1)
    (hOK : BatFoldOKAt (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁))
    (hFix : R.Sh.rho.Fix R.G.e) (hL : R.Sh.rho.Laws)
    (fr : ∀ ν, Slf GE (R.G.RowSt Sb ν) R.Sh.Cin.J)
    (hfr : ∀ ν s j, ¬ FreeAt R.Sh j → fr ν s j = 0)
    (F : Slf GE (Tower.BSt Sb Z) R.Sh.Cin.J) (hFe : F = R.Sh.form Sb sl Z + Slf.bat Z.ze fr) :
    (Tower.batFoldRide (R.sizeB keep Sb sl Z) R.Sh fx St₀ E₀).red.Know
        ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).on
        ((Cb.Pv.Bat.inJ (R.sizeB keep Sb sl Z) A₀).keepE R.Sh.par.Cw.nat).relR
        (Tower.batFoldOutAt (R.sizeB keep Sb sl Z) R.Sh F A₀).relR
        (Tower.batFoldExtRideAt (R.sizeB keep Sb sl Z) R.Sh F fx R.s.d w₀ w₁)
        (Tower.batFoldErrRide (R.sizeB keep Sb sl Z) R.Sh fx (fun _ => lstJ R.s R.e)
          (fun _ => bC) (fun _ => bZ) fun _ => bZ) ∧
    ∀ (P : Plan) (T T' : Statement) (g : Nat) (mask : Option Nat) (out : SingleRows)
      (a : ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
        ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
      (τ : Tr (rB :: rE ::
        List.replicate (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k rR)),
      ρ.DefAt (ρ.V τ) → closing P T g mask (ρ.V τ) = .ok (out, T') →
      (∀ G e z lay, T.groups[g]? = some G →
        (ρ.viewB τ.1 τ.2.1).drawn.elems = [e.triple] →
        ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z → (begun T g G).layout g = some lay →
        OrderedV R Sb sl Z N fr a.1.1.1 a.1.2 z e (begun T g G) lay (runRows T G).toList) →
      (∀ G lay, T.groups[g]? = some G → (begun T g G).layout g = some lay →
        R.s.Z.l ≤ 2 ^ lay.logEllZk ∧
        ∀ w ∈ (runRows T G).toList, MaskFits (begun T g G) lay w) →
      (∀ G, T.groups[g]? = some G → ∀ w ∈ (runRows T G).toList, RowFits (begun T g G) w) →
      P.k = R.s.h + R.s.g → P.h = R.s.h →
      (T.codes.mask.getD P.maskCode default).ell = R.s.Z.l →
      ∃ (z : Z.D) (τ' : Tr (Tower.batFoldRide (R.sizeB keep Sb sl Z) R.Sh fx St₀ E₀).red.shape)
        (a' : ((kBatFoldRide L).dst (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
          ((kBatFoldRide L).dst (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str),
        ρ.rdZ (drawnOf (ρ.viewB τ.1 τ.2.1)) = some z ∧ ρ.carS.tr τ = some τ' ∧
        (Tower.batFoldRide (R.sizeB keep Sb sl Z) R.Sh fx St₀ E₀).red.out a τ' = some a' ∧
        a'.1.2 = (batX (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) a.1 z).2 ∧
        a'.2.1 = foldedAt (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁))
          (readP (Yc (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).k out.gamma)
          (R.Sh.rho.map.map ((ldBrG R.G (R.sizeB keep Sb sl Z).kp E₀).map a.2.1).1) a.2.2 ∧
        a'.2.2 = ((ldBrG R.G (R.sizeB keep Sb sl Z).kp E₀).map a.2.1).2 ∧
        ((∃ w, (Tower.batFoldOutAt (R.sizeB keep Sb sl Z) R.Sh F A₀).relR a' w) ↔
          CarryAt R N out a'.2.1 ∧
            ∃ v, ((S.sub (R.sizeB keep Sb sl Z).kp).over A₀).relR (a'.1.2, a'.2.2) v) := by
  refine ⟨know_plus (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) hOK hFix fr hfr F hFe, ?_⟩
  intro P T T' g mask out a τ ht h hO hM hR hk hh hZ
  obtain ⟨z, τ', a', h1, h2, h3, h4, h5, h6⟩ := law_tied R keep Sb sl Z fx A₀ bC bZ w₀ w₁ L rB rE rR
    ρ hS hst hfx hL N fr P T T' g mask out a τ ht h hO hM hR hk hh hZ
  have hc := carry_iff R N F a'.1.1 a'.2.1 out h4 (by rw [hFe]; exact h6)
  have hi := word_at L (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) rB rE rR ρ hS hst hfx P T T' g
    mask out a τ ht h
    (fun G e z hG hd hz => by
      obtain ⟨G', _, _, lay', _, _, _, _, _, _, _, _, -, -, hG', -, -, hl', -⟩ := closing_inv2 h
      obtain rfl := Option.some.inj (hG.symm.trans hG')
      obtain ⟨ord, o1, o2, o3, o4, -, -⟩ := hO G e z lay' hG hd hz hl'
      exact ⟨ord, o1, o2, o3, o4⟩) hR τ' a' h2 h3
  refine ⟨z, τ', a', h1, h2, h3, h5, hi.1, hi.2, ?_⟩
  constructor
  · rintro ⟨w, k1, k2⟩
    exact ⟨hc.1 ⟨w.1, k1⟩, w.2, k2⟩
  · rintro ⟨k1, v, k2⟩
    obtain ⟨u, k3⟩ := hc.2 k1
    exact ⟨(u, v), k3, k2⟩

end Caller

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.word_at
#print axioms VerifiableInference.Desc.First.Close.outAt_relR
#print axioms VerifiableInference.Desc.First.Close.tied_and_known
#print axioms VerifiableInference.Desc.First.Close.carry_iff
