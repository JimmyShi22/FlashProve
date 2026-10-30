-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/StageSim.lean: a protocol with its simulator, and nothing else. (Words of this library:
lean/GLOSSARY.md.)

A stage (Blocks/Stage.lean) is one record of protocol, simulator, errors, sets of pads and two
probabilities. A simulator that is written `T.Sim` for a stage T therefore mentions the errors and
the probabilities, and, where T comes out of a record of the analysis, the relations too. That
affects only the form of the term; but an explicit simulator is there to be read. So, as the
definition of a scheme mentions protocols only (`Core`), the definition of a simulator mentions
protocols with their simulators only.

Notation: `Rho`: the verifier's randomness of a whole execution; `Plains`: the plain parts of all
prover messages (Iop/Shape.lean).

Limit: a protocol (`Core`) holds the honest prover too. So a simulator that is defined through `CS`
still mentions the terms of the honest prover. Its type, Rho B.shape → PMF (Plains B.shape), gives
it no state of the prover, and the state is where the index lives; that its body uses none of the
prover's terms is seen by reading it, not from the type.

 * `CS P E a b`: a protocol (`Core`) with a simulator of its plain parts. `Stage.toCS`: these two
   parts of a stage.
 * `CS.seq`, `CS.id`, `CS.on`, `CS.mapP`: as for protocols. The simulator of two in a row samples
   independently; on a part of a larger statement, and over a larger index type of pads, it is
   unchanged.
 * For each stage X of Blocks/StageLib.lean, VecFlatTrack.lean, VecJoinTrack.lean: `CS.X`, with the
   arguments of `Core.X`, and by rfl `CS.toCore_X` : (CS.X ..).toCore = Core.X .. and `Stage.toCS_X`
   : (Stage.X ..).toCS = CS.X .. . `Stage.toCS_both`: larger errors change nothing here.
 * `Stage.simOn_eq`: the link to Blocks/StageOnCore.lean.
-/
import Blocks.StageOnCore
import Blocks.StageMap
import Blocks.StageBoth
import Blocks.VecJoinTrack
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob
open scoped ENNReal

/-- A protocol with its simulator. -/
structure CS (P E : Type) (a b : Sorts) extends Core P E a b where
  /-- the simulator of the plain parts -/
  Sim : Rho B.shape → PMF (Plains B.shape)

/-- The protocol and the simulator of a stage. -/
@[reducible] def Stage.toCS {P E : Type} {a b : Sorts} (S : Stage P E a b) : CS P E a b :=
  ⟨S.toCore, S.Sim⟩

section General

variable {P P' E : Type} {a b c a' b' : Sorts}

theorem Stage.toCore_toCS (S : Stage P E a b) : S.toCS.toCore = S.toCore := rfl
theorem Stage.Sim_toCS (S : Stage P E a b) : S.toCS.Sim = S.Sim := rfl

/-- Two in a row: independent samples. -/
def CS.seq (K₁ : CS P E a b) (K₂ : CS P E b c) : CS P E a c :=
  ⟨K₁.toCore.seq K₂.toCore, Hon.simSeq K₁.Sim K₂.Sim⟩

/-- No round. -/
def CS.id (a : Sorts) : CS P E a a := ⟨Core.id a, fun _ => PMF.pure ()⟩

/-- On a part of a larger statement. -/
def CS.on (K : CS P E a b) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X) (gy : a'.Y → a.Y)
    (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) : CS P E a' b' :=
  ⟨K.toCore.on gx px gy py ga pa, K.Sim⟩

/-- Over a larger index type of pads. -/
def CS.mapP (K : CS P E a b) (ip : P → P') : CS P' E a b := ⟨K.toCore.mapP ip, K.Sim⟩

theorem CS.toCore_seq (K₁ : CS P E a b) (K₂ : CS P E b c) :
    (K₁.seq K₂).toCore = K₁.toCore.seq K₂.toCore := rfl
theorem CS.toCore_id (a : Sorts) : (CS.id (P := P) (E := E) a).toCore = Core.id a := rfl
theorem CS.toCore_on (K : CS P E a b) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X) (gy : a'.Y → a.Y)
    (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) :
    (K.on gx px gy py ga pa).toCore = K.toCore.on gx px gy py ga pa := rfl
theorem CS.toCore_mapP (K : CS P E a b) (ip : P → P') : (K.mapP ip).toCore = K.toCore.mapP ip := rfl
theorem CS.Sim_seq (K₁ : CS P E a b) (K₂ : CS P E b c) :
    (K₁.seq K₂).Sim = Hon.simSeq K₁.Sim K₂.Sim := rfl
theorem CS.Sim_on (K : CS P E a b) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X) (gy : a'.Y → a.Y)
    (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) :
    (K.on gx px gy py ga pa).Sim = K.Sim := rfl
theorem CS.Sim_mapP (K : CS P E a b) (ip : P → P') : (K.mapP ip).Sim = K.Sim := rfl

theorem Stage.toCS_seq (S₁ : Stage P E a b) (S₂ : Stage P E b c) :
    (S₁.seq S₂).toCS = S₁.toCS.seq S₂.toCS := rfl
theorem Stage.toCS_id (a : Sorts) : (Stage.id (P := P) (E := E) a).toCS = CS.id a := rfl
theorem Stage.toCS_mapP (S : Stage P E a b) (ip : P → P') : (S.mapP ip).toCS = S.toCS.mapP ip := rfl
theorem Stage.toCS_both (S : Stage P E a b) (ε' : Err S.B.shape) : (S.both ε').toCS = S.toCS := rfl

/-- Equations between stages and protocols with simulators compose. -/
theorem Stage.toCS_seq_of {S₁ : Stage P E a b} {S₂ : Stage P E b c} {K₁ : CS P E a b}
    {K₂ : CS P E b c} (h₁ : S₁.toCS = K₁) (h₂ : S₂.toCS = K₂) :
    (S₁.seq S₂).toCS = K₁.seq K₂ := by
  subst h₁ h₂
  rfl

/-- If T.toCS = ⟨C, s⟩, `Stage.simOn` of T is s. -/
theorem Stage.simOn_eq {T : Stage P E a b} {C : Core P E a b}
    {s : Rho C.B.shape → PMF (Plains C.B.shape)} (hc : T.toCS = ⟨C, s⟩) :
    T.simOn (congrArg CS.toCore hc) = s := by
  cases hc
  rfl

end General

/-! ## The stages of Blocks/StageLib.lean, VecFlatTrack.lean, VecJoinTrack.lean -/

section Lib

variable {F P E : Type} [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E] [Fintype P]
  [DecidableEq P] {a b a' b' : Sorts}

omit [Field E] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCS_on (S : Stage P E a b) (gx : a'.X → a.X) (px : a'.X → b.X → b'.X)
    (gy : a'.Y → a.Y) (py : a'.Y → b.Y → b'.Y) (ga : a'.I → a.I) (pa : a'.I → b.I → b'.I) :
    (S.on gx px gy py ga pa).toCS = S.toCS.on gx px gy py ga pa := rfl

def CS.pads (a : Sorts) {n : ℕ} (idx : Fin n → P) :
    CS P E a ⟨a.X, a.Y × (Fin n → E), a.I⟩ :=
  ⟨Core.pads a idx, fun _ => PMF.pure ((fun k => Empty.elim k), ())⟩
def CS.nameVec (a : Sorts) (r : Round) (p₀ : r.Plain) (msg : a.I → r.Orc) :
    CS P E a ⟨a.X, a.Y × r.Orc, a.I⟩ :=
  ⟨Core.nameVec a r p₀ msg, fun _ => PMF.pure (p₀, ())⟩
def CS.send (a : Sorts) (X' Z : Type) (r : Round) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') : CS P E a ⟨X', a.Y × Z, a.I⟩ :=
  ⟨Core.send a X' Z r p₀ msg φ fx, fun _ => PMF.pure (p₀, ())⟩
/-- masked scalars: uniform scalars -/
def CS.nameScalars
    (a : Sorts) {K : Type} [Fintype K] [DecidableEq K] (idx : K → P) (val : a.I → K → E) :
    CS P E a ⟨a.X × (K → E), a.Y, a.I⟩ :=
  ⟨Core.nameScalars a idx val, Hon.simOne (r := Stage.scRound E K) E _root_.id⟩
def CS.sample (a : Sorts) (I' : Type) (C : Type) [Fintype C] [Nonempty C]
    (ok : C → Bool) (nx : a.I → C → I') : CS P E a ⟨a.X × C, a.Y, I'⟩ :=
  ⟨Core.sample a I' C ok nx, fun _ => PMF.pure ((fun k => Empty.elim k), ())⟩
def CS.pure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I) : CS P E a b :=
  ⟨Core.pure f g nx, fun _ => PMF.pure ()⟩

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem CS.toCore_pads (a : Sorts) {n : ℕ} (idx : Fin n → P) :
    (CS.pads (E := E) a idx).toCore = Core.pads a idx := rfl
omit [Field E] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem CS.toCore_nameVec (a : Sorts) (r : Round) (p₀ : r.Plain) (msg : a.I → r.Orc) :
    (CS.nameVec (P := P) (E := E) a r p₀ msg).toCore = Core.nameVec a r p₀ msg := rfl
omit [Field E] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem CS.toCore_send (a : Sorts) (X' Z : Type) (r : Round) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') :
    (CS.send a X' Z r p₀ msg φ fx).toCore = Core.send a X' Z r p₀ msg φ fx := rfl
omit [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem CS.toCore_nameScalars
    (a : Sorts) {K : Type} [Fintype K] [DecidableEq K] (idx : K → P) (val : a.I → K → E) :
    (CS.nameScalars a idx val).toCore = Core.nameScalars a idx val := rfl
omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem CS.toCore_sample (a : Sorts) (I' : Type) (C : Type) [Fintype C] [Nonempty C]
    (ok : C → Bool) (nx : a.I → C → I') :
    (CS.sample (P := P) (E := E) a I' C ok nx).toCore = Core.sample a I' C ok nx := rfl
omit [Field E] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem CS.toCore_pure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I) :
    (CS.pure (P := P) (E := E) f g nx).toCore = Core.pure f g nx := rfl

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCS_pads (a : Sorts) {n : ℕ} (idx : Fin n → P) :
    (Stage.pads (E := E) a idx).toCS = CS.pads a idx := rfl
omit [Field E] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCS_nameVec (a : Sorts) (r : Round) (p₀ : r.Plain) (msg : a.I → r.Orc) :
    (Stage.nameVec (P := P) (E := E) a r p₀ msg).toCS = CS.nameVec a r p₀ msg := rfl
omit [Field E] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCS_send (a : Sorts) (X' Z : Type) (r : Round) (p₀ : r.Plain)
    (msg : a.I → (P → E) → r.Orc) (φ : r.Orc → Z) (fx : a.X → X') :
    (Stage.send a X' Z r p₀ msg φ fx).toCS = CS.send a X' Z r p₀ msg φ fx := rfl
omit [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCS_nameScalars
    (a : Sorts) {K : Type} [Fintype K] [DecidableEq K] (idx : K → P) (val : a.I → K → E) :
    (Stage.nameScalars a idx val).toCS = CS.nameScalars a idx val := rfl
omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCS_sample (a : Sorts) (I' : Type) (C : Type) [Fintype C] [Nonempty C]
    (ok : C → Bool) (nx : a.I → C → I') (e : ℕ) (pBad : ℝ≥0∞) :
    (Stage.sample (P := P) (E := E) a I' C ok nx e pBad).toCS = CS.sample a I' C ok nx := rfl
omit [Field E] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCS_pure (f : a.X → Option b.X) (g : a.Y → b.Y) (nx : a.I → b.I) :
    (Stage.pure (P := P) (E := E) f g nx).toCS = CS.pure f g nx := rfl

/-! ### Matrices written end to end, and in one vector -/

variable {X' Z : Type} (A : Type) (overF : A → Bool) (rows len M : A → ℕ) (K C : Type)
  [Fintype C] [Nonempty C]

def CS.sendFlat (a : Sorts) (X' Z : Type) (p₀ : K → E)
    (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') : CS P E a ⟨X', a.Y × Z, a.I⟩ :=
  CS.send a X' Z (Flat.rFlat E F A overF rows len M K C) p₀ (fun s π => Flat.flat M K C (msg s π))
    (fun o => φ (Flat.unflat o)) fx

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem CS.toCore_sendFlat (p₀ : K → E) (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') :
    (CS.sendFlat A overF rows len M K C a X' Z p₀ msg φ fx).toCore =
      Core.sendFlat A overF rows len M K C a X' Z p₀ msg φ fx := rfl
omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCS_sendFlat (p₀ : K → E) (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') :
    (Stage.sendFlat A overF rows len M K C a X' Z p₀ msg φ fx).toCS =
      CS.sendFlat A overF rows len M K C a X' Z p₀ msg φ fx := rfl

end Lib

section LibJoin

variable {F P E : Type} [Field F] [Field E] [Fintype E] [DecidableEq E] [Algebra F E] [Fintype P]
  [DecidableEq P] {a : Sorts} {X' Z : Type} {A : Type} (b : Bool) (rows len : A → ℕ)
  (L : Join.Lay A) (M : ℕ) (ord : List A) (K C : Type) [Fintype C] [Nonempty C]

/-- the arguments are in the order of `Core.sendJoin` -/
def CS.sendJoin (a : Sorts) (X' Z : Type) (p₀ : K → E)
    (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') : CS P E a ⟨X', a.Y × Z, a.I⟩ :=
  CS.send a X' Z (Join.rJoin E F b L M K C) p₀ (fun s π => Join.join L M K C ord (msg s π))
    (fun o => φ (Join.unjoin o)) fx

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem CS.toCore_sendJoin (p₀ : K → E) (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') :
    (CS.sendJoin b rows len L M ord K C a X' Z p₀ msg φ fx).toCore =
      Core.sendJoin b rows len L M ord K C a X' Z p₀ msg φ fx := rfl
omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCS_sendJoin (p₀ : K → E) (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') :
    (Stage.sendJoin b rows len L M ord K C a X' Z p₀ msg φ fx).toCS =
      CS.sendJoin b rows len L M ord K C a X' Z p₀ msg φ fx := rfl

end LibJoin

end Blocks
