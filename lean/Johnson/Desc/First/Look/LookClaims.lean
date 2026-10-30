-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/LookClaims.lean: the lookup's claims that read no plane, as plain functions
on data. Definitions with code. No theorem.

The program's lookup (OnBytes/Model/Look.lean) hears its messages first (`Forest.pad`; as a plain
function: `lkPad`, OnBytes/K/Kc/FlatHear.lean) and returns what it heard (`Forest.Heard`). Its
claims are made and added later, behind the draw that batches them, by the routines that stand here
and in LookPlanes.lean. None of those here takes a round: each reads `Heard` and public numbers and
changes the ledger (`Fork`, OnBytes/Model/Hide.lean) alone. They stand over the carrier `Fl`
(OnBytes/K/Kc/Flat.lean): from a ledger and a tape to nothing, or to a value, the new ledger and
what is left of the tape. Each is typed after the program's text line by line; the pure functions of
Look.lean and of `Fork` are called by name. No routine that runs in a context is called.

Main names:
  `linF`, `paidF`: `Fork.lin` and `Fork.paid` as steps.
  `uEntF`: entry x of a vector that is stored as an array of the sub-proof (`uEnt`).
  `objectsOn`, `objectsF`: adds the claims that read only mask entries (`Forest.objects`); the first
    is a function on the ledger alone.
  `planesAddedF`, `joinAddedF`: the two marks. `paddingLaidF`: the guard on the padding's two
    counts. `joinF`: the claim on the calls' key vectors.

Limits: that a step returns what the program's routine returns is tried by tests
(TestLookClaims.lean [not in this library]) and by runs, not shown. The names of refusals are left out, as in `Fl`. THE
LIST OF GUARDS stands at LookPlanes.lean's foot.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Kc.FlatHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Look
open OnBytes OnBytes.Model OnBytes.K.Kc

/-- `SubM.lin` (Hide.lean:546): adds a claim. -/
def linF (f : Aff) : Fl Unit := Fl.change (·.lin f)

/-- `SubM.paid` (Hide.lean:561): marks an owed claim as added. -/
def paidF (i : Nat) : Fl Unit := Fl.change fun F => some (F.paid i)

/-- `uEnt` (Look.lean:58-61). -/
def uEntF (t x : Nat) : Fl Aff := do
  let cols ← Fl.ask fun F => some (((F.trees[t]?).map (·.K)).getD 0)
  Fl.must (cols != 0 && x / cols < 2 ^ 32)
  pure (Aff.ent t (x / cols) (x % cols))

/-- `Forest.objects` (Look.lean:425-427) as a function on the ledger alone. -/
def objectsOn (g : Forest.Heard) (F : Fork) : Option Fork :=
  (g.rows.foldlM (fun (G : Fork) f => G.lin f) F).map (·.paid g.owedObjects)

/-- `Forest.objects` (Look.lean:425-427). -/
def objectsF (g : Forest.Heard) : Fl Unit := do
  g.rows.forM linF
  paidF g.owedObjects

/-- `Forest.planesAdded` (Look.lean:431). -/
def planesAddedF (g : Forest.Heard) : Fl Unit := paidF g.owedPlanes

/-- `Forest.joinAdded` (Look.lean:435). -/
def joinAddedF (g : Forest.Heard) : Fl Unit := paidF g.owedJoin

/-- `Forest.paddingLaid` (Look.lean:447-448). -/
def paddingLaidF (g : Forest.Heard) (laid : Array Nat) : Fl Unit := do
  Fl.must (laid == g.shape.pub)

/-- `Forest.join` (Look.lean:455-468). -/
def joinF (g : Forest.Heard) (KF : Array Aff) : Fl Aff := do
  let h := g.shape
  Fl.must (KF.size == h.calls.size && g.e.size == h.calls.size)
  joinAddedF g
  let onCalls := (List.range KF.size).foldl
    (fun (f : Aff) c =>
      let key := KF.getD c (Aff.ofConst zeroE)
      Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) - key)
        (g.e.getD c zeroE))
    (Aff.ofConst zeroE)
  let ey := eqTab g.zy
  let empty := (List.range (2 ^ h.rK - h.NT)).foldl
    (fun s i => addE s (mulE (ey.getD (h.NT + i) zeroE) (subE g.alpha (g.padKey 0)))) zeroE
  pure (onCalls + Aff.ofConst empty - g.cEnd)

end VerifiableInference.Desc.First.Look
