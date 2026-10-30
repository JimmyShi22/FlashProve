-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/BatFoldAtForm.lean: the kind of block "the round before a proximity test, then its
first fold" with the cut and the fold at any form on the fold's input code, as a value of `Kind`
(Johnson/Top/Kind.lean), at any written list of callers, in its two forms, with the kind's
hypothesis and the three facts beside it.

Johnson/Top/H/BatFold.lean lays that kind with the cut and the fold at the batched form carried
along by the arrangement, which is 0 on every row that holds no member's row. Here the form is a
field F of the caller, and one clause more is asked: that the arrangement is knowledge sound into
the first stage's joint at F (`ArrRideInto`, Cb/Pv/Tower/TestAt.lean). The joint before
the block is that file's. The joint behind it is the fold's at F. The errors are that file's
numbers. The reductions are those of Cb/Pv/Tower/BatFoldAtForm.lean. The typed statement behind the
fold holds a state, a point and a coefficient, not a vector: the form is applied in the relation of
the joint behind the block alone. Definitions, statements and proofs.
Main names:
  `BatFoldCallerAt`: who calls: `BatFoldCaller` with the field F.
  `kBatFoldOwnAt L`, `kBatFoldRideAt L`: the kinds.
  `BatFoldCallerAt.OK c`, `BatFoldCallersOK L`: the conditions, a field a clause: those of
    `BatFoldOKAt`, the fold's at F, and `into`. One set serves both kinds.
  `kBatFoldRideAt_know`, `_point`, `_local`, `_onOut`, `_good`, and the same for `kBatFoldOwnAt`:
    `_know`, `_local`, `_onOut` and `_good` under `BatFoldCallersOK L`.
  `BatFoldCaller.atForm c F`, `BatFoldCaller.toAt`: a caller of Johnson/Top/H/BatFold.lean as a
    caller here, at a form F; at the arranged form. `kBatFoldRideAt_toAt`, `kBatFoldOwnAt_toAt`: at
    the arranged form its joints and its block are that file's, by definition (`BK.Same`).
    `BatFoldOKAt.toAt`, `toAt_iff`: its conditions are that file's. `BatFoldCallerAt.forget`: a
    caller here with F forgotten; `forget_atForm`, `atForm_forget`.
  `HBatFoldOwnAt`, `HBatFoldRideAt`: closed, over the field `Cb.Gl.E`. They hold.
Limits: no list of callers is written here, so the conditions are proved of no value. `into` is
shown at the arranged form alone. Nothing says that a form is any program's, that a block of the
kind is the step that the programs run, or that its errors are small. That the block's reduction at
F is its reduction at any other form is not proved here. Cb/Pv/Tower/BatFoldAtForm.lean proves it
where the fold's mask was sent earlier (`batFoldRideAt_anyForm`), of the reduction alone: not where
the fold sends its mask, and not of an extractor or of the errors. Nothing on an honest prover.

-/
import Johnson.Top.H.BatFold
import Johnson.E.KObj.PFile
import Cb.Pv.Tower.BatFoldAtForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv Cb.Pv.Tower

/-! ### the kinds -/

/-- Who calls the round before a test with the test's first fold, the fold at a form F. -/
structure BatFoldCallerAt (E : Type) [Field E] [Fintype E] : Type 1 where
  s : Cb.Pv.Bat.Size E
  [neP : Nonempty s.G.P]
  Sh : GShape s.G
  /-- the form at which the cut and the fold stand -/
  F : Slf E (BSt s.Sb s.Z) Sh.Cin.J
  fx : Fin ((Sh.par.reform F).n + 1) × E
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

attribute [instance] BatFoldCallerAt.neP

section
variable {E : Type} [Field E] [Fintype E]

/-- The fold sends its fresh mask. -/
@[reducible] noncomputable def kBatFoldOwnAt (L : List (BatFoldCallerAt E)) : Kind.{1} where
  Size := BatFoldCallerAt E
  sizes := L
  src := fun c => jOf (Cb.Pv.Bat.inJ c.s c.A₀)
  dst := fun c => jOf (batFoldOutAt c.s c.Sh c.F c.A₀)
  block := fun c =>
    ⟨batFoldOwnAt c.s c.Sh c.F c.fx c.St₀ c.E₀, batFoldExtOwnAt c.s c.Sh c.F c.fx c.d c.w₀,
      batFoldErrOwnAt c.s c.Sh c.F c.fx c.Lst c.mC c.mS c.mW⟩

/-- The fold's mask was sent earlier. -/
@[reducible] noncomputable def kBatFoldRideAt (L : List (BatFoldCallerAt E)) : Kind.{1} where
  Size := BatFoldCallerAt E
  sizes := L
  src := fun c => jOf ((Cb.Pv.Bat.inJ c.s c.A₀).keepE c.Sh.par.Cw.nat)
  dst := fun c => jOf (batFoldOutAt c.s c.Sh c.F c.A₀)
  block := fun c =>
    ⟨batFoldRideAt c.s c.Sh c.F c.fx c.St₀ c.E₀,
      batFoldExtRideAt c.s c.Sh c.F c.fx c.d c.w₀ c.w₁,
      batFoldErrRideAt c.s c.Sh c.F c.fx c.Lst c.mC c.mS c.mW⟩

/-- The conditions at one caller, a field a clause. The clause `into` is a statement of knowledge
soundness, so these are not all tests on public data. -/
structure BatFoldCallerAt.OK (c : BatFoldCallerAt E) : Prop where
  /-- the coefficients of the round before the test evade zero -/
  z : c.s.Z.OK
  /-- the lists of the group's code at the joint radius are bounded -/
  list : c.s.G.C.ListAt c.s.G.e c.s.L
  /-- the joint radius implies each member's own -/
  fits : c.s.G.Fits
  /-- the laws of the group's shape -/
  shape : c.Sh.OK
  /-- the arrangement is knowledge sound into the first stage's joint at the form -/
  into : ArrRideInto c.Sh c.s.Sb c.s.sl c.s.Z c.F
  /-- the fold's conditions -/
  fold : (c.Sh.par.reform c.F).HypK c.d c.s.G.e c.Lst c.mC c.mS c.mW

/-- The conditions. -/
def BatFoldCallersOK (L : List (BatFoldCallerAt E)) : Prop := ∀ c ∈ L, c.OK

variable (L : List (BatFoldCallerAt E))

/-- The kind whose fold sends its mask is knowledge sound under the conditions. -/
theorem kBatFoldOwnAt_know (h : BatFoldCallersOK L) : (kBatFoldOwnAt L).Know := fun c hc =>
  batFoldOwnAt_know c.s c.Sh c.F c.fx c.A₀ c.d c.Lst c.mC c.mS c.mW c.w₀ (h c hc).z (h c hc).list
    (h c hc).fits (arrOwnInto_of_ride c.Sh c.s.Sb c.s.sl c.s.Z c.F (h c hc).into) (h c hc).fold

/-- Every query of its verifiers is a point query. -/
theorem kBatFoldOwnAt_point : (kBatFoldOwnAt L).Point := fun c _ =>
  (Cb.Pv.Bat.point c.s c.St₀ c.E₀).elim fun p =>
    (gfOwnAt_point c.Sh c.s.Sb c.s.sl c.s.Z c.F c.fx).elim fun q => ⟨Shape.IsPoint.append p q⟩

/-- Under the conditions its verifiers are local. -/
theorem kBatFoldOwnAt_local (h : BatFoldCallersOK L) : (kBatFoldOwnAt L).Local := fun c hc =>
  (Cb.Pv.Bat.isLocal c.s c.St₀ c.E₀).seq
    (IsLocal.keepE (CarE c.s c.E₀)
      (isLocal_keepX
        (gfOwnAt_local c.Sh c.s.Sb c.s.sl c.s.Z c.F c.fx (h c hc).shape (h c hc).fold.codes.1.1
          (h c hc).fold.codes.1.2.1 (h c hc).fold.codes.1.2.2) (CarX c.s c.St₀)))

/-- Under the conditions what its blocks leave meets the condition of the joint behind. -/
theorem kBatFoldOwnAt_onOut (h : BatFoldCallersOK L) : (kBatFoldOwnAt L).OnOut :=
  fun c hc a τ x hx ha =>
  onOut_two (Cb.Pv.Bat.R c.s c.St₀ c.E₀)
    ((gfOwnAt c.Sh c.s.Sb c.s.sl c.s.Z c.F c.fx).keep (CarX c.s c.St₀) (CarE c.s c.E₀))
    (Cb.Pv.Bat.inJ c.s c.A₀).on (Cb.Pv.Bat.outJ c.s c.A₀).on
    (batFoldOutAt c.s c.Sh c.F c.A₀).on
    (Cb.Pv.Bat.onOut c.s (h c hc).z (h c hc).list (h c hc).fits c.A₀)
    (onOut_beside c.Kc _ _ _ _ _ _ (gfOwnAt c.Sh c.s.Sb c.s.sl c.s.Z c.F c.fx) _ _ _
      (firstInOwn c.s.Sb c.s.sl c.s.Z) (outJ (c.Sh.par.reform c.F) c.s.G.e)
      ((c.s.S.sub c.s.kp).over c.A₀) fun _ _ _ _ _ => trivial)
    a τ x ha hx

/-- Under the conditions every block of the kind has the property that a list of blocks asks. -/
theorem kBatFoldOwnAt_good (h : BatFoldCallersOK L) :
    ∀ c ∈ L, ((kBatFoldOwnAt L).block c).Good :=
  Kind.good (kBatFoldOwnAt_know L h) (kBatFoldOwnAt_point L) (kBatFoldOwnAt_local L h)
    (kBatFoldOwnAt_onOut L h)

/-- The kind whose fold's mask was sent earlier is knowledge sound under the conditions. -/
theorem kBatFoldRideAt_know (h : BatFoldCallersOK L) : (kBatFoldRideAt L).Know := fun c hc =>
  batFoldRideAt_know c.s c.Sh c.F c.fx c.A₀ c.d c.Lst c.mC c.mS c.mW c.w₀ c.w₁ (h c hc).z
    (h c hc).list (h c hc).fits (h c hc).into (h c hc).fold

/-- Every query of its verifiers is a point query. -/
theorem kBatFoldRideAt_point : (kBatFoldRideAt L).Point := fun c _ =>
  (Cb.Pv.Bat.point c.s c.St₀ c.E₀).elim fun p =>
    (gfRideAt_point c.Sh c.s.Sb c.s.sl c.s.Z c.F c.fx).elim fun q =>
      ⟨Shape.IsPoint.append p
        (Shape.IsPoint.append
          (s := (IOR.pure some (setR c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat)).shape) () q)⟩

/-- Under the conditions its verifiers are local. -/
theorem kBatFoldRideAt_local (h : BatFoldCallersOK L) : (kBatFoldRideAt L).Local := fun c hc =>
  ((Cb.Pv.Bat.isLocal c.s c.St₀ c.E₀).keepE c.Sh.par.Cw.nat).seq
    (IsLocal.seq
      (⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun y y' _ _ q _ _ hE _ =>
        setR_isLocal c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat y y' q hE⟩ :
        (IOR.pure some (setR c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat)).IsLocal)
      (IsLocal.keepE (CarE c.s c.E₀)
        (isLocal_keepX
          (gfRideAt_local c.Sh c.s.Sb c.s.sl c.s.Z c.F c.fx (h c hc).shape
            (h c hc).fold.codes.1.1 (h c hc).fold.codes.1.2.1 (h c hc).fold.codes.1.2.2)
          (CarX c.s c.St₀))))

/-- Under the conditions what its blocks leave meets the condition of the joint behind. -/
theorem kBatFoldRideAt_onOut (h : BatFoldCallersOK L) : (kBatFoldRideAt L).OnOut :=
  fun c hc a τ x hx ha =>
  onOut_two ((Cb.Pv.Bat.R c.s c.St₀ c.E₀).keepE c.Sh.par.Cw.nat)
    ((IOR.pure some (setR c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat)).seq
      ((gfRideAt c.Sh c.s.Sb c.s.sl c.s.Z c.F c.fx).keep (CarX c.s c.St₀) (CarE c.s c.E₀)))
    ((Cb.Pv.Bat.inJ c.s c.A₀).keepE c.Sh.par.Cw.nat).on (batMid₁ c.s c.Sh c.A₀).on
    (batFoldOutAt c.s c.Sh c.F c.A₀).on
    (onOut_keepE c.Sh.par.Cw.nat (Cb.Pv.Bat.R c.s c.St₀ c.E₀) (Cb.Pv.Bat.inJ c.s c.A₀)
      (Cb.Pv.Bat.outJ c.s c.A₀)
      (Cb.Pv.Bat.onOut c.s (h c hc).z (h c hc).list (h c hc).fits c.A₀))
    (onOut_two (IOR.pure some (setR c.s.G.C.ext (CarE c.s c.E₀) c.Sh.par.Cw.nat))
      ((gfRideAt c.Sh c.s.Sb c.s.sl c.s.Z c.F c.fx).keep (CarX c.s c.St₀) (CarE c.s c.E₀))
      (batMid₁ c.s c.Sh c.A₀).on (batMid₂ c.s c.Sh c.A₀).on (batFoldOutAt c.s c.Sh c.F c.A₀).on
      (setR_onOut c.s c.Sh c.A₀)
      (onOut_beside c.Kc _ _ _ _ _ _ (gfRideAt c.Sh c.s.Sb c.s.sl c.s.Z c.F c.fx) _ _ _
        (firstInRide c.Sh c.s.Sb c.s.sl c.s.Z) (outJ (c.Sh.par.reform c.F) c.s.G.e)
        ((c.s.S.sub c.s.kp).over c.A₀) fun _ _ _ _ _ => trivial))
    a τ x ha hx

/-- Under the conditions every block of the kind has the property that a list of blocks asks. -/
theorem kBatFoldRideAt_good (h : BatFoldCallersOK L) :
    ∀ c ∈ L, ((kBatFoldRideAt L).block c).Good :=
  Kind.good (kBatFoldRideAt_know L h) (kBatFoldRideAt_point L) (kBatFoldRideAt_local L h)
    (kBatFoldRideAt_onOut L h)

/-! ### the callers at the arranged form -/

section Arranged
variable (c : BatFoldCaller E)

/-- A caller of Johnson/Top/H/BatFold.lean, at a form F. -/
def BatFoldCaller.atForm (F : Slf E (BSt c.s.Sb c.s.Z) c.Sh.Cin.J) : BatFoldCallerAt E where
  s := c.s
  Sh := c.Sh
  F := F
  fx := c.fx
  Kc := c.Kc
  St₀ := c.St₀
  Wp := c.Wp
  E₀ := c.E₀
  A₀ := c.A₀
  d := c.d
  Lst := c.Lst
  mC := c.mC
  mS := c.mS
  mW := c.mW
  w₀ := c.w₀
  w₁ := c.w₁

/-- The same at the arranged form. -/
noncomputable def BatFoldCaller.toAt : BatFoldCallerAt E :=
  c.atForm (c.Sh.form c.s.Sb c.s.sl c.s.Z)

/-- Its joints and its block are those of Johnson/Top/H/BatFold.lean. -/
theorem kBatFoldRideAt_toAt (L : List (BatFoldCaller E)) (L' : List (BatFoldCallerAt E)) :
    ((kBatFoldRideAt L').block c.toAt).Same ((kBatFoldRide L).block c) := rfl

/-- The same where the fold sends its mask. -/
theorem kBatFoldOwnAt_toAt (L : List (BatFoldCaller E)) (L' : List (BatFoldCallerAt E)) :
    ((kBatFoldOwnAt L').block c.toAt).Same ((kBatFoldOwn L).block c) := rfl

/-- Its conditions hold where those of Johnson/Top/H/BatFold.lean do. -/
theorem BatFoldOKAt.toAt {c : BatFoldCaller E} (h : BatFoldOKAt c) : c.toAt.OK where
  z := h.z
  list := h.list
  fits := h.fits
  shape := h.shape
  into := arrRide_know c.Sh c.s.Sb c.s.sl c.s.Z h.shape
  fold := h.fold

/-- And only there. -/
theorem BatFoldOKAt.toAt_iff {c : BatFoldCaller E} : c.toAt.OK ↔ BatFoldOKAt c :=
  ⟨fun h => ⟨h.z, h.list, h.fits, h.shape, h.fold⟩, BatFoldOKAt.toAt⟩

/-- A caller here with the form forgotten. -/
def BatFoldCallerAt.forget (c : BatFoldCallerAt E) : BatFoldCaller E where
  s := c.s
  Sh := c.Sh
  fx := c.fx
  Kc := c.Kc
  St₀ := c.St₀
  Wp := c.Wp
  E₀ := c.E₀
  A₀ := c.A₀
  d := c.d
  Lst := c.Lst
  mC := c.mC
  mS := c.mS
  mW := c.mW
  w₀ := c.w₀
  w₁ := c.w₁

/-- To lay a form and to forget it changes nothing. -/
theorem BatFoldCaller.forget_atForm (F : Slf E (BSt c.s.Sb c.s.Z) c.Sh.Cin.J) :
    (c.atForm F).forget = c := rfl

/-- A caller here is a caller of Johnson/Top/H/BatFold.lean at a form. -/
theorem BatFoldCallerAt.atForm_forget (c : BatFoldCallerAt E) : c.forget.atForm c.F = c := rfl

end Arranged

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of callers that
meet the conditions. -/
def HBatFoldOwnAt : Prop :=
  ∀ L : List (BatFoldCallerAt Cb.Gl.E), BatFoldCallersOK L → (kBatFoldOwnAt L).Know

/-- It holds. -/
theorem hBatFoldOwnAt : HBatFoldOwnAt := kBatFoldOwnAt_know

/-- The same with the fold's mask sent earlier. -/
def HBatFoldRideAt : Prop :=
  ∀ L : List (BatFoldCallerAt Cb.Gl.E), BatFoldCallersOK L → (kBatFoldRideAt L).Know

/-- It holds. -/
theorem hBatFoldRideAt : HBatFoldRideAt := kBatFoldRideAt_know

end VerifiableInference.OnPublicFiles
