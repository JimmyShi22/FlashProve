-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/BatFold.lean: the kind of block "the round before a proximity test, then its first
fold" (in a plan of rounds: "BAT", "FOLD epsilon", "FOLD round" once for each variable) as a value
of `Kind` (Johnson/Top/Kind.lean), at any written list of callers, in its two forms, with the kind's
hypothesis and the three facts beside it.

The reductions, their extractors, errors and knowledge soundness are those of
Cb/Pv/Tower/First.lean. A block of the kind is two blocks in a row, or three: the round before the
test; where the fold's mask was sent earlier, a step without rounds that sets it next to the group's
word; and the arrangement, the cut and the fold, beside what is carried. The three facts beside
knowledge soundness are shown of these parts and carried over. A size is a caller: the record of the
round before the test (`Cb.Pv.Bat.Size`), the group's shape (`GShape`, Cb/Ld/LdGroupFold.lean),
which coefficient is left out, the joint on the kept messages that is carried, the numbers of the
statement, and two fixed witnesses for the extractor.
Main names:
  `gfOwn_point`, `gfRide_point`, `gfOwn_local`, `gfRide_local`: arrangement, cut and fold in a row.
  `onOut_two`: two reductions in a row carry a condition if each does.
  `BatFoldCaller`: who calls the block. `kBatFoldOwn L`, `kBatFoldRide L`: the kinds: the fold sends
    its fresh mask; the mask was sent earlier and stands behind the input's oracles.
  `BatFoldOKAt c`, `BatFoldOK L`: the conditions, a field a clause: those of the round before the
    test, the laws of the shape, and the fold's.
  `kBatFoldOwn_know`, `_point`, `_local`, `_onOut`, `_good`, and the same for `kBatFoldRide`:
    `_know`, `_local`, `_onOut` and `_good` under `BatFoldOK L`.
  `HBatFoldOwn`, `HBatFoldRide`: closed, over the field `Cb.Gl.E`: for every list of callers that
    meet the conditions the kind is knowledge sound. `hBatFoldOwn`, `hBatFoldRide`: they hold.
Limits: no list of callers is written here, so the conditions are proved of no value. Nothing says
that a block of the kind is the step that the programs run, or that its errors are small. Nothing on
an honest prover.

-/
import Johnson.Top.Kind
import Cb.Pv.Tower.First
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv Cb.Pv.Tower

/-! ### arrangement, cut and fold: the two facts on the verifier alone -/

section GroupFold
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (fx : Fin ((Sh.fold Sb sl Z).n + 1) × E)

theorem gfOwn_point : Nonempty (gfOwn Sh Sb sl Z fx).shape.IsPoint :=
  (foldOwn_point (Sh.fold Sb sl Z) fx).elim fun q =>
    ⟨Shape.IsPoint.append (s := (arrOwn Sh Sb sl Z).shape) ()
      (Shape.IsPoint.append (s := (cutOwn Sh.par (Sh.form Sb sl Z) G.e).shape) () q)⟩

theorem gfRide_point : Nonempty (gfRide Sh Sb sl Z fx).shape.IsPoint :=
  (foldRide_point (Sh.fold Sb sl Z) fx).elim fun q =>
    ⟨Shape.IsPoint.append (s := (arrRide Sh Sb sl Z).shape) ()
      (Shape.IsPoint.append (s := (cutRide Sh.par (Sh.form Sb sl Z) G.e).shape) () q)⟩

theorem gfOwn_local (h : Sh.OK) (hC : Sh.par.C.Laws) (hZ : Sh.par.Z.Laws)
    (hW : Sh.par.Zw.Laws) : (gfOwn Sh Sb sl Z fx).IsLocal :=
  (arrOwn_local Sh Sb sl Z h).seq
    ((cutOwn_local Sh.par (Sh.form Sb sl Z) G.e).seq
      (foldOwn_local (Sh.fold Sb sl Z) fx hC hZ hW))

theorem gfRide_local (h : Sh.OK) (hC : Sh.par.C.Laws) (hZ : Sh.par.Z.Laws)
    (hW : Sh.par.Zw.Laws) : (gfRide Sh Sb sl Z fx).IsLocal :=
  (arrRide_local Sh Sb sl Z h).seq
    (((cutOwn_local Sh.par (Sh.form Sb sl Z) G.e).keepE Sh.par.Cw.nat).seq
      (foldRide_local (Sh.fold Sb sl Z) fx hC hZ hW))

end GroupFold

/-- Two reductions in a row carry a condition if each does. -/
theorem onOut_two {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} (R₁ : IOR X₁ E₁ X₂ E₂)
    (R₂ : IOR X₂ E₂ X₃ E₃) (o₁ : X₁ × E₁.Str → Prop) (o₂ : X₂ × E₂.Str → Prop)
    (o₃ : X₃ × E₃.Str → Prop) (h₁ : ∀ a τ b, o₁ a → R₁.red.out a τ = some b → o₂ b)
    (h₂ : ∀ a τ b, o₂ a → R₂.red.out a τ = some b → o₃ b) :
    ∀ a τ c, o₁ a → (R₁.seq R₂).red.out a τ = some c → o₃ c := by
  intro a τ c ha hc
  obtain ⟨b, hb, hc'⟩ := Option.bind_eq_some_iff.1 ((IOR.red_seq_out R₁ R₂ a τ).symm.trans hc)
  exact h₂ b _ c (h₁ a _ b ha hb) hc'

/-! ### the kinds -/

/-- Who calls the round before a test with the test's first fold. -/
structure BatFoldCaller (E : Type) [Field E] [Fintype E] : Type 1 where
  s : Cb.Pv.Bat.Size E
  [neP : Nonempty s.G.P]
  Sh : GShape s.G
  fx : Fin ((Sh.fold s.Sb s.sl s.Z).n + 1) × E
  Kc : Type
  St₀ : Type
  Wp : Type
  E₀ : ExtSpec
  /-- the joint on the kept messages -/
  A₀ : Rels Kc St₀ E₀ ((s.S.sub s.kp).Msg × Wp)
  d : ℕ
  Lst : ℕ → ℕ
  mC : ℕ → ℕ
  mS : ℕ → ℕ
  mW : ℕ → ℕ
  /-- the extractor's values where a verifier has rejected -/
  w₀ : s.S.Wit × Wp
  w₁ : LdBrW s.G s.kp Wp

attribute [instance] BatFoldCaller.neP

section
variable {E : Type} [Field E] [Fintype E]

/-- The fold sends its fresh mask. -/
@[reducible] noncomputable def kBatFoldOwn (L : List (BatFoldCaller E)) : Kind.{1} where
  Size := BatFoldCaller E
  sizes := L
  src := fun c => jOf (Cb.Pv.Bat.inJ c.s c.A₀)
  dst := fun c => jOf (batFoldOut c.s c.Sh c.A₀)
  block := fun c =>
    ⟨batFoldOwn c.s c.Sh c.fx c.St₀ c.E₀, batFoldExtOwn c.s c.Sh c.fx c.d c.w₀,
      batFoldErrOwn c.s c.Sh c.fx c.Lst c.mC c.mS c.mW⟩

/-- The fold's mask was sent earlier. -/
@[reducible] noncomputable def kBatFoldRide (L : List (BatFoldCaller E)) : Kind.{1} where
  Size := BatFoldCaller E
  sizes := L
  src := fun c => jOf ((Cb.Pv.Bat.inJ c.s c.A₀).keepE c.Sh.par.Cw.nat)
  dst := fun c => jOf (batFoldOut c.s c.Sh c.A₀)
  block := fun c =>
    ⟨batFoldRide c.s c.Sh c.fx c.St₀ c.E₀, batFoldExtRide c.s c.Sh c.fx c.d c.w₀ c.w₁,
      batFoldErrRide c.s c.Sh c.fx c.Lst c.mC c.mS c.mW⟩

/-- The conditions at one caller, a field a clause, on public data alone. -/
structure BatFoldOKAt (c : BatFoldCaller E) : Prop where
  /-- the coefficients of the round before the test evade zero -/
  z : c.s.Z.OK
  /-- the lists of the group's code at the joint radius are bounded -/
  list : c.s.G.C.ListAt c.s.G.e c.s.L
  /-- the joint radius implies each member's own -/
  fits : c.s.G.Fits
  /-- the laws of the group's shape -/
  shape : c.Sh.OK
  /-- the fold's conditions -/
  fold : (c.Sh.fold c.s.Sb c.s.sl c.s.Z).HypK c.d c.s.G.e c.Lst c.mC c.mS c.mW

/-- The conditions. -/
def BatFoldOK (L : List (BatFoldCaller E)) : Prop := ∀ c ∈ L, BatFoldOKAt c

variable (L : List (BatFoldCaller E))

theorem kBatFoldOwn_know (h : BatFoldOK L) : (kBatFoldOwn L).Know := fun c hc =>
  batFoldOwn_know c.s c.Sh c.fx c.A₀ c.d c.Lst c.mC c.mS c.mW c.w₀ (h c hc).z (h c hc).list
    (h c hc).fits (h c hc).shape (h c hc).fold

theorem kBatFoldOwn_point : (kBatFoldOwn L).Point := fun c _ =>
  (Cb.Pv.Bat.point c.s c.St₀ c.E₀).elim fun p =>
    (gfOwn_point c.Sh c.s.Sb c.s.sl c.s.Z c.fx).elim fun q => ⟨Shape.IsPoint.append p q⟩

theorem kBatFoldOwn_local (h : BatFoldOK L) : (kBatFoldOwn L).Local := fun c hc =>
  (Cb.Pv.Bat.isLocal c.s c.St₀ c.E₀).seq
    (IsLocal.keepE (CarE c.s c.E₀)
      (isLocal_keepX
        (gfOwn_local c.Sh c.s.Sb c.s.sl c.s.Z c.fx (h c hc).shape (h c hc).fold.codes.1.1
          (h c hc).fold.codes.1.2.1 (h c hc).fold.codes.1.2.2) (CarX c.s c.St₀)))

theorem kBatFoldOwn_onOut (h : BatFoldOK L) : (kBatFoldOwn L).OnOut := fun c hc a τ x hx ha =>
  onOut_two (Cb.Pv.Bat.R c.s c.St₀ c.E₀)
    ((gfOwn c.Sh c.s.Sb c.s.sl c.s.Z c.fx).keep (CarX c.s c.St₀) (CarE c.s c.E₀))
    (Cb.Pv.Bat.inJ c.s c.A₀).on (Cb.Pv.Bat.outJ c.s c.A₀).on (batFoldOut c.s c.Sh c.A₀).on
    (Cb.Pv.Bat.onOut c.s (h c hc).z (h c hc).list (h c hc).fits c.A₀)
    (onOut_beside c.Kc _ _ _ _ _ _ (gfOwn c.Sh c.s.Sb c.s.sl c.s.Z c.fx) _ _ _
      (firstInOwn c.s.Sb c.s.sl c.s.Z) (outJ (c.Sh.fold c.s.Sb c.s.sl c.s.Z) c.s.G.e)
      ((c.s.S.sub c.s.kp).over c.A₀) fun _ _ _ _ _ => trivial)
    a τ x ha hx

theorem kBatFoldOwn_good (h : BatFoldOK L) : ∀ c ∈ L, ((kBatFoldOwn L).block c).Good :=
  Kind.good (kBatFoldOwn_know L h) (kBatFoldOwn_point L) (kBatFoldOwn_local L h)
    (kBatFoldOwn_onOut L h)

theorem kBatFoldRide_know (h : BatFoldOK L) : (kBatFoldRide L).Know := fun c hc =>
  batFoldRide_know c.s c.Sh c.fx c.A₀ c.d c.Lst c.mC c.mS c.mW c.w₀ c.w₁ (h c hc).z (h c hc).list
    (h c hc).fits (h c hc).shape (h c hc).fold

theorem kBatFoldRide_point : (kBatFoldRide L).Point := fun c _ =>
  (Cb.Pv.Bat.point c.s c.St₀ c.E₀).elim fun p =>
    (gfRide_point c.Sh c.s.Sb c.s.sl c.s.Z c.fx).elim fun q =>
      ⟨Shape.IsPoint.append p
        (Shape.IsPoint.append
          (s := (IOR.pure some (setR c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat)).shape) () q)⟩

theorem kBatFoldRide_local (h : BatFoldOK L) : (kBatFoldRide L).Local := fun c hc =>
  ((Cb.Pv.Bat.isLocal c.s c.St₀ c.E₀).keepE c.Sh.par.Cw.nat).seq
    (IsLocal.seq
      (⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun y y' _ _ q _ _ hE _ =>
        setR_isLocal c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat y y' q hE⟩ :
        (IOR.pure some (setR c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat)).IsLocal)
      (IsLocal.keepE (CarE c.s c.E₀)
        (isLocal_keepX
          (gfRide_local c.Sh c.s.Sb c.s.sl c.s.Z c.fx (h c hc).shape (h c hc).fold.codes.1.1
            (h c hc).fold.codes.1.2.1 (h c hc).fold.codes.1.2.2) (CarX c.s c.St₀))))

theorem kBatFoldRide_onOut (h : BatFoldOK L) : (kBatFoldRide L).OnOut := fun c hc a τ x hx ha =>
  onOut_two ((Cb.Pv.Bat.R c.s c.St₀ c.E₀).keepE c.Sh.par.Cw.nat)
    ((IOR.pure some (setR c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat)).seq
      ((gfRide c.Sh c.s.Sb c.s.sl c.s.Z c.fx).keep (CarX c.s c.St₀) (CarE c.s c.E₀)))
    ((Cb.Pv.Bat.inJ c.s c.A₀).keepE c.Sh.par.Cw.nat).on (batMid₁ c.s c.Sh c.A₀).on
    (batFoldOut c.s c.Sh c.A₀).on
    (onOut_keepE c.Sh.par.Cw.nat (Cb.Pv.Bat.R c.s c.St₀ c.E₀) (Cb.Pv.Bat.inJ c.s c.A₀)
      (Cb.Pv.Bat.outJ c.s c.A₀)
      (Cb.Pv.Bat.onOut c.s (h c hc).z (h c hc).list (h c hc).fits c.A₀))
    (onOut_two (IOR.pure some (setR c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat))
      ((gfRide c.Sh c.s.Sb c.s.sl c.s.Z c.fx).keep (CarX c.s c.St₀) (CarE c.s c.E₀))
      (batMid₁ c.s c.Sh c.A₀).on (batMid₂ c.s c.Sh c.A₀).on (batFoldOut c.s c.Sh c.A₀).on
      (setR_onOut c.s c.Sh c.A₀)
      (onOut_beside c.Kc _ _ _ _ _ _ (gfRide c.Sh c.s.Sb c.s.sl c.s.Z c.fx) _ _ _
        (firstInRide c.Sh c.s.Sb c.s.sl c.s.Z) (outJ (c.Sh.fold c.s.Sb c.s.sl c.s.Z) c.s.G.e)
        ((c.s.S.sub c.s.kp).over c.A₀) fun _ _ _ _ _ => trivial))
    a τ x ha hx

theorem kBatFoldRide_good (h : BatFoldOK L) : ∀ c ∈ L, ((kBatFoldRide L).block c).Good :=
  Kind.good (kBatFoldRide_know L h) (kBatFoldRide_point L) (kBatFoldRide_local L h)
    (kBatFoldRide_onOut L h)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of callers that
meet the conditions. -/
def HBatFoldOwn : Prop := ∀ L : List (BatFoldCaller Cb.Gl.E), BatFoldOK L → (kBatFoldOwn L).Know

theorem hBatFoldOwn : HBatFoldOwn := kBatFoldOwn_know

/-- The same with the fold's mask sent earlier. -/
def HBatFoldRide : Prop :=
  ∀ L : List (BatFoldCaller Cb.Gl.E), BatFoldOK L → (kBatFoldRide L).Know

theorem hBatFoldRide : HBatFoldRide := kBatFoldRide_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hBatFoldOwn
#print axioms VerifiableInference.OnPublicFiles.hBatFoldRide
#print axioms VerifiableInference.OnPublicFiles.kBatFoldOwn_good
#print axioms VerifiableInference.OnPublicFiles.kBatFoldRide_good
