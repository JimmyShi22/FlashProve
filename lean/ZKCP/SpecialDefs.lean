-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/SpecialDefs.lean: the translation between Defs.lean and Gen.lean, definitions only.

ZKCP/Gen.lean has families of oracles, two relations and batches. `toPair`, `toGen`, `extTo`,
`advTo`, `envTo` translate a relation, a scheme, an extractor, an adversarial verifier and an
environment of ZKCP/Defs.lean into its form; `extOf`, `viewOf`, `simOf` translate an extractor, a
view and a simulator back. The theorems about them are in ZKCP/Special.lean.
-/
import ZKCP.Gen
import Rom.Bridge
noncomputable section -- Lean tags what it cannot compile

namespace ZKCP.Special

open Rom (rom toRom ofRom trTo trOf)

variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-- R_yes = R_no = R. -/
def toPair (R : IndexedRelation I X W PP) : Gen.RelPair I X W PP :=
  ⟨R.rel, R.rel, fun _ _ _ h => h, R.pp⟩

/-- A batch is proved slot by slot, with the prover of Defs.lean. -/
def proveAll (A : Arg lam I X W IVK ISK Pf) (isk : ISK) :
    (b : List (X × W)) → Rom.OComp (rom lam) (Gen.Slots Pf b)
  | [] => .pure ⟨[], rfl⟩
  | (x, w) :: rest =>
      (toRom (A.P isk x w)).bind fun π => (proveAll A isk rest).bind fun πs =>
        .pure ⟨π :: πs.val, by simp [πs.property]⟩

def toGen (A : Arg lam I X W IVK ISK Pf) : Gen.Arg (rom lam) I X W IVK ISK Pf where
  C i := toRom (A.C i)
  P := proveAll A
  V ivk x π := toRom (A.V ivk x π)

def extTo (E : Extractor lam I X W IVK Pf) : Gen.Extractor (rom lam) I X W IVK Pf where
  Ei ivk tr := E.Ei ivk (trOf tr)
  Ew ivk trC x π trP := E.Ew ivk (trOf trC) x π (trOf trP)

def extOf (E : Gen.Extractor (rom lam) I X W IVK Pf) : Extractor lam I X W IVK Pf where
  Ei ivk tr := E.Ei ivk (trTo tr)
  Ew ivk trC x π trP := E.Ew ivk (trTo trC) x π (trTo trP)

/-- An adversarial verifier of Defs.lean in the form of Gen.lean: it expects one (x, π) for each
request, and halts on any other list. -/
def advTo : AdvVerifier lam X Pf → Gen.AdvVerifier (rom lam) X Pf
  | .halt => .halt
  | .query q k => .query () q fun r => advTo (k r)
  | .sample n k => .sample n fun r => advTo (k r)
  | .request k => .request fun l =>
      match l with
      | [(x, π)] => advTo (k x π)
      | _ => .halt

/-- The view of Gen.lean, read as a view of Defs.lean. -/
def viewOf (v : Gen.View (rom lam) IVK X Pf) : View lam IVK X Pf :=
  ⟨v.ivk, v.sessions.flatten, trOf v.trace, v.coins⟩

/-- An environment of Defs.lean (strong form): each pair becomes a batch of one, which is the
adversary's own. (The third entry, `true`: see `Gen.Batch`, ZKCP/Gen.lean.) -/
def envTo (Z : ViewEnv lam IVK X W Pf) : Gen.ViewEnv (rom lam) IVK X W Pf :=
  fun v => (Z (viewOf v)).map fun xw => [(xw.1, xw.2, true)]

/-- The one entry of a list of length one. -/
def head1 {x : X} (l : Gen.Slots Pf [x]) : Pf :=
  l.val.head (by intro h; have := l.property; simp [h] at this)

/-- A simulator of Gen.lean, used on batches of one. -/
def simOf (Sim : Gen.Simulator (rom lam) PP IVK X Pf) :
    Simulator lam PP IVK X Pf where
  St := Sim.St
  init := Sim.init
  answer s q := Sim.answer s () q
  prove s x := (Sim.prove s [x]).map fun out => (head1 out.1, out.2)

end ZKCP.Special
