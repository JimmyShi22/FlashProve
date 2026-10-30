-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowWidePass.lean: the wide witness map through three transformations of a batch IOP: verifier
messages made from other values, tests (proof of work), rounds cut and joined.
The three main statements (`Spec.sndBKT_pull`, `Spec.sndBKT_grind`, `Spec.sndBKT_recut`) say that
round-by-round knowledge soundness of a batch IOP (`SndBKT`) gives that of the transformed batch
IOP, under their hypotheses, with the errors named below.

Definitions, statements and proofs. The wide forms of CompileK/KnowPull.lean, Ior/GrindK.lean,
CompileK/KnowRecut.lean for one batch IOP (`BatchInteractiveOracleProof`, Iop/Batch.lean).
`SndBKT` (Ior/KnowWide.lean) is round-by-round knowledge soundness for the instances of a batch,
with a witness map that may read the instance, the external oracle and the whole local transcript.
Each transformation comes with a map from transcripts of the new shape to transcripts of the old one
(`Tr.push`, `Tr.strip`, `Tr.old`), and its verifier decides as the old one does on the transcript
read back (with tests, for a type Nn of nonces with a fixed element: and only if all test bits are
0, `Rho.pass`). A witness map on transcripts (Ior/KnowWide.lean: `SndBKT`) is carried by the same
map.

Main names:
  `Spec.sndBKT_pull`: if `σ.Fib`, every count is multiplied by the bound on the fibres of its
    round's sampler (`Err.pull`).
  `Spec.sndBKT_grind`: wit is applied to `Tr.strip g τ`; the same counts, now out of |C| 2^b values
    (`Err.grind`): nonces and test bits are not read.
  `Spec.sndBKT_recut`: late becomes `late.map P.idx`; the errors `Err.recut`; under the hypotheses
    of its statement, the conditions of CompileK/KnowRecut.lean.
By parts (Ior/KnowWide.lean: `witOf w`):
  `WitP.push σ w`, `WitP.strip g w`; `Spec.witOf_push`, `Spec.witOf_strip`: the carried map is again
    given by parts, each part read back by its own map. (For cuts and joins: `WitP.old`,
    CompileK/KnowWidePass.lean; the oracles' map `Orcs.old` is in CompileK/KnowRecut.lean.)
Which verifier messages are read:
  `Rho.AgreeTo j ρ ρ'`, `WitP.BlindFrom j w` (rounds are counted from 0): see their docstrings.
  `Spec.blindFrom_push`, `blindFrom_strip`: kept, with the same j (these transformations keep
    the rounds and their order).
  `Spec.agreeTo_old`: cuts and joins; see its docstring and that of `XPlan.idx`
    (Iop/BatchRecut.lean).
  `Spec.blindFrom_mono`: a larger j is weaker.

Limits: this file says nothing on the honest side. It says nothing on how an extractor of a compiled
argument learns verifier messages, nor on which j it can afford.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowWide
import Ior.GrindK
import Ior.SubProofs
import Iop.BatchRecutProofs
import Blocks.GrindSmallMsg

set_option autoImplicit false

namespace Iop
open Prob

/-- a witness map by parts -/
abbrev WitP (X : Type) (E : ExtSpec) (s : Shape) (W : Type) : Type :=
  X → E.Str → Orcs s → Plains s → Rho s → W

/-- The verifier messages of the rounds before round j agree. -/
def Rho.AgreeTo : {s : Shape} → ℕ → Rho s → Rho s → Prop
  | [], _, _, _ => True
  | _ :: _, 0, _, _ => True
  | _ :: _, j + 1, (c, ρ), (c', ρ') => c = c' ∧ Rho.AgreeTo j ρ ρ'

namespace WitP
variable {X W : Type} {E : ExtSpec} {s : Shape}

/-- after "verifier messages are made from other values" -/
def push (σ : Samplers s) (w : WitP X E s W) : WitP X E (s.pull σ) W := fun x y o pl ρ =>
  w x y (Orcs.push σ o) (Plains.push σ pl) (Rho.push σ ρ)

/-- after "tests are added": nonces and test bits are dropped -/
def strip {Nn : Type} [Inhabited Nn] (g : GBits s) (w : WitP X E s W) : WitP X E (s.grind Nn g) W :=
  fun x y o pl ρ => w x y (Orcs.strip g o) (Plains.strip g pl) (Rho.strip g ρ)

/-- w does not read the verifier messages from round j on. -/
def BlindFrom (j : ℕ) (w : WitP X E s W) : Prop :=
  ∀ x y o pl ρ ρ', Rho.AgreeTo j ρ ρ' → w x y o pl ρ = w x y o pl ρ'

end WitP

namespace Spec

def guardP_pull : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (σ : Samplers Q.loc.shape),
    (Q.guardP ok).pull σ = (Q.pull σ).guardP (fun x y τ => ok x y (Tr.push σ τ))

def guardP_grind : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E)
      (ok : X → E.Str → Tr Q.loc.shape → Prop) (g : GBits Q.loc.shape),
    (Q.guardP ok).grind Nn g = (Q.grind Nn g).guardP (fun x y τ => ok x y (Tr.strip g τ))

def guardP_recut : Prop :=
  ∀ (X : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (ok : X → E.Str → Tr Q.loc.shape → Prop)
      (P : XPlan Q.loc.shape) (Z : AXPlan P Q.ann),
    (Q.guardP ok).recut P Z = (Q.recut P Z).guardP (fun x y τ => ok x y (Tr.old P τ))

/-- Verifier messages are made from other values. -/
def sndBKT_pull : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (σ : Samplers Q.loc.shape), σ.Fib →
    ∀ (N : ℕ) (early : X → X) (late : Option ℕ) (R : X → E.Str → W → Prop)
        (wit : X → E.Str → Tr Q.loc.shape → W) (ε : Err Q.loc.shape),
      Q.SndBKT N early late R wit ε →
      (Q.pull σ).SndBKT N early late R (fun x y τ => wit x y (Tr.push σ τ)) (Err.pull σ ε)

/-- Tests are added: the same counts. -/
def sndBKT_grind : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E)
      (g : GBits Q.loc.shape) (N : ℕ) (early : X → X) (late : Option ℕ) (R : X → E.Str → W → Prop)
      (wit : X → E.Str → Tr Q.loc.shape → W) (ε : Err Q.loc.shape),
    Q.SndBKT N early late R wit ε →
    (Q.grind Nn g).SndBKT N early late R (fun x y τ => wit x y (Tr.strip g τ)) (Err.grind g ε)

/-- Rounds are cut and joined. -/
def sndBKT_recut : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (Q : BatchInteractiveOracleProof X E) (P : XPlan Q.loc.shape) (Z : AXPlan P Q.ann),
    P.OK → AXPlan.OK P Q.ann Z → AXPlan.Kinds P Q.ann Z →
    ∀ (N : ℕ), 0 < N →
      ∀ (early : X → X) (late : Option ℕ), (∀ n, late = some n → AXPlan.Late P Q.ann Z n) →
        ∀ (R : X → E.Str → W → Prop) (wit : X → E.Str → Tr Q.loc.shape → W) (ε : Err Q.loc.shape),
          ε.UnitZero → Q.SndBKT N early late R wit ε →
          (Q.recut P Z).SndBKT N early (late.map P.idx) R
            (fun x y τ => wit x y (Tr.old P τ)) (Err.recut P ε)

/-- States: the carried map is again given by parts -/
def witOf_push : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (s : Shape) (σ : Samplers s) (w : WitP X E s W),
    (fun x y (τ : Tr (s.pull σ)) => witOf w x y (Tr.push σ τ)) = witOf (w.push σ)

def witOf_strip : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (X W : Type) (E : ExtSpec) (s : Shape)
      (g : GBits s) (w : WitP X E s W),
    (fun x y (τ : Tr (s.grind Nn g)) => witOf w x y (Tr.strip g τ)) = witOf (w.strip g)

def blindFrom_push : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (s : Shape) (σ : Samplers s) (w : WitP X E s W) (j : ℕ),
    w.BlindFrom j → (w.push σ).BlindFrom j

def blindFrom_strip : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (X W : Type) (E : ExtSpec) (s : Shape) (g : GBits s)
      (w : WitP X E s W) (j : ℕ),
    w.BlindFrom j → (w.strip (Nn := Nn) g).BlindFrom j

/-- States: cuts and joins, no two verifier messages joined (`P.NoChal`): agreement before the new
round in which the old round j begins gives agreement before the old round j. -/
def agreeTo_old : Prop :=
  ∀ (s : Shape) (P : XPlan s), P.NoChal →
    ∀ (j : ℕ) (ρ ρ' : Rho P.shape),
      Rho.AgreeTo (P.idx j) ρ ρ' → Rho.AgreeTo j (Rho.old P ρ) (Rho.old P ρ')

/-- States: j = 0: no verifier message is read -/
def blindFrom_zero : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (s : Shape) (w : WitP X E s W),
    w.BlindFrom 0 ↔ ∀ x y o pl ρ ρ', w x y o pl ρ = w x y o pl ρ'

def blindFrom_mono : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (s : Shape) (w : WitP X E s W) (j j' : ℕ),
    j ≤ j' → w.BlindFrom j → w.BlindFrom j'

end Spec

theorem guardP_pull : Spec.guardP_pull := fun _ _ _ _ _ => rfl

open Classical in
/-- the two verifiers decide alike -/
theorem KnowWide.accept_grind {Nn : Type} [Inhabited Nn] {X : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof X E) (ok : X → E.Str → Tr Q.loc.shape → Prop) (g : GBits Q.loc.shape) :
    (fun (x : X) (y : E.Str) (τ : Tr (Q.loc.shape.grind Nn g)) =>
        Rho.pass g τ.rho && (Q.loc.accept x y (Tr.strip g τ) && !decide (ok x y (Tr.strip g τ)))) =
      fun x y τ =>
        (Rho.pass g τ.rho && Q.loc.accept x y (Tr.strip g τ)) &&
            !decide (ok x y (Tr.strip g τ)) := by
  funext x y τ
  rw [Bool.and_assoc]

theorem guardP_grind : Spec.guardP_grind := fun Nn _ X E Q ok g =>
  congrArg (fun acc : X → E.Str → Tr (Q.loc.shape.grind Nn g) → Bool =>
      (⟨{ Q.loc.grind Nn g with accept := acc }, Q.ann.grind Nn g⟩ : BatchInteractiveOracleProof X E))
    (KnowWide.accept_grind Q ok g)

theorem guardP_recut : Spec.guardP_recut := fun _ _ _ _ _ _ => rfl

theorem sndBKT_pull : Spec.sndBKT_pull := fun _ _ _ Q _ hσ _ _ _ R wit _ h =>
  BatchPull.sndBL_pull (Q := Q.guardP fun x y τ => R x y (wit x y τ)) hσ h

theorem sndBKT_grind : Spec.sndBKT_grind := by
  intro Nn _ X W E Q g N early late R wit ε h
  have h' : ((Q.guardP fun x y τ => R x y (wit x y τ)).grind Nn g).SndBL
      N early late (fun _ _ => False) (Err.grind g ε) :=
    BatchGrind.sndBL_grind (Q := Q.guardP fun x y τ => R x y (wit x y τ)) g h
  exact cast
    (congrArg (fun acc : X → E.Str → Tr (Q.loc.shape.grind Nn g) → Bool =>
        (⟨{ Q.loc.grind Nn g with accept := acc }, Q.ann.grind Nn g⟩ : BatchInteractiveOracleProof X E).SndBL
          N early late (fun _ _ => False) (Err.grind g ε))
      (KnowWide.accept_grind Q (fun x y τ => R x y (wit x y τ)) g)) h'

theorem sndBKT_recut : Spec.sndBKT_recut := fun _ _ _ Q _ _ hP hZ hK _ hN _ _ hl R wit _ hε h =>
  BatchRecut.sndBL_recut (Q := Q.guardP fun x y τ => R x y (wit x y τ)) hP hZ hK hN hl hε h

theorem witOf_push : Spec.witOf_push := by
  intro X W E s σ w
  funext x y τ
  show w x y (Tr.push σ τ).read (Tr.push σ τ).plains (Tr.push σ τ).rho =
    w x y (Orcs.push σ τ.read) (Plains.push σ τ.plains) (Rho.push σ τ.rho)
  rw [Tr.plains_push, Tr.rho_push,
    show (Tr.push σ τ).read = Orcs.push σ τ.read from funext fun p => Tr.read_push_orcs σ τ p]

theorem witOf_strip : Spec.witOf_strip := by
  intro Nn _ X W E s g w
  funext x y τ
  show w x y (Tr.strip g τ).read (Tr.strip g τ).plains (Tr.strip g τ).rho =
    w x y (Orcs.strip g τ.read) (Plains.strip g τ.plains) (Rho.strip g τ.rho)
  rw [Tr.plains_strip, Tr.rho_strip, read_stripO]

theorem Rho.AgreeTo.push :
    ∀ {s : Shape} (j : ℕ) (σ : Samplers s) {ρ ρ' : Rho (s.pull σ)},
      Rho.AgreeTo j ρ ρ' → Rho.AgreeTo j (Rho.push σ ρ) (Rho.push σ ρ')
  | [], _, _, _, _, _ => trivial
  | _ :: _, 0, _, _, _, _ => trivial
  | _ :: _, j + 1, (a, σs), (_, _), (_, _), h => ⟨congrArg a.φ h.1, Rho.AgreeTo.push j σs h.2⟩

theorem Rho.AgreeTo.strip {Nn : Type} [Inhabited Nn] :
    ∀ {s : Shape} (j : ℕ) (g : GBits s) {ρ ρ' : Rho (s.grind Nn g)},
      Rho.AgreeTo j ρ ρ' → Rho.AgreeTo j (Rho.strip g ρ) (Rho.strip g ρ')
  | [], _, _, _, _, _ => trivial
  | _ :: _, 0, _, _, _, _ => trivial
  | _ :: _, j + 1, (_, g), (_, _), (_, _), h => ⟨congrArg GChal.old h.1, Rho.AgreeTo.strip j g h.2⟩

theorem blindFrom_push : Spec.blindFrom_push := fun _ _ _ _ σ _ j h x y _ _ _ _ hρ =>
  h x y _ _ _ _ (Rho.AgreeTo.push j σ hρ)

theorem blindFrom_strip : Spec.blindFrom_strip := fun _ _ _ _ _ _ g _ j h x y _ _ _ _ hρ =>
  h x y _ _ _ _ (Rho.AgreeTo.strip j g hρ)

theorem Rho.agreeTo_zero : ∀ {s : Shape} (ρ ρ' : Rho s), Rho.AgreeTo 0 ρ ρ'
  | [], _, _ => trivial
  | _ :: _, _, _ => trivial

theorem Rho.AgreeTo.anti :
    ∀ {s : Shape} {j j' : ℕ} {ρ ρ' : Rho s}, j ≤ j' → Rho.AgreeTo j' ρ ρ' → Rho.AgreeTo j ρ ρ'
  | [], _, _, _, _, _, _ => trivial
  | _ :: _, 0, _, _, _, _, _ => trivial
  | _ :: _, _ + 1, 0, _, _, h, _ => absurd h (Nat.not_succ_le_zero _)
  | _ :: _, _ + 1, _ + 1, (_, _), (_, _), h, h' => ⟨h'.1, Rho.AgreeTo.anti (Nat.le_of_succ_le_succ h) h'.2⟩

theorem agreeTo_old : Spec.agreeTo_old := by
  intro s P
  induction P with
  | nil => intro _ _ _ _ _; trivial
  | keep r P ih =>
      rintro hn j ⟨c, ρ⟩ ⟨c', ρ'⟩ h
      cases j with
      | zero => trivial
      | succ n => exact ⟨h.1, ih hn n ρ ρ' h.2⟩
  | cut k P ih =>
      rintro hn j ⟨c, ρ⟩ ⟨c', ρ'⟩ h
      cases j with
      | zero => trivial
      | succ n => exact ih hn (n + 1) ρ ρ' h.2
  | msg r1 r2 u P ih =>
      intro hn j ρ ρ' h
      cases j with
      | zero => trivial
      | succ n =>
          refine ⟨rfl, ?_⟩
          have h' := ih hn n ρ ρ' h
          cases n with
          | zero => trivial
          | succ m => exact h'
  | chal r1 r2 np P ih => intro hn; exact hn.elim

theorem blindFrom_zero : Spec.blindFrom_zero := fun _ _ _ _ _ =>
  ⟨fun h x y o pl ρ ρ' => h x y o pl ρ ρ' (Rho.agreeTo_zero ρ ρ'),
    fun h x y o pl ρ ρ' _ => h x y o pl ρ ρ'⟩

theorem blindFrom_mono : Spec.blindFrom_mono := fun _ _ _ _ _ _ _ hj h x y o pl ρ ρ' hρ =>
  h x y o pl ρ ρ' (Rho.AgreeTo.anti hj hρ)

end Iop
