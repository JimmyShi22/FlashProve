-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/HearGrows.lean: K4's HEAR LEADS TO A LATER LEDGER. Wherever `hearFl`
(OnBytes/Desc/First/K4/Plain.lean) returns, the ledger that it leaves is later than the one that it
was handed (`OnBytes.PscRun.Later`). Statements and proofs.

How. Every field of the plain engine `engFl` leads to a later ledger
(OnBytes/Desc/First/FlGrows.lean has the functions behind them); the parts of HEAR
(OnBytes/Desc/First/K4/Hear.lean, Engine.lean) are do-blocks over these fields, walked by the tactic
`grows`.

Main names: `hearFl_later`; an instance of `Grows` for each field of `engFl` and for
`sumcheckClaim`, `shownRun`, `plainRounds`, `paddingFits`, `hearNorms`, `hearTerms`, `joinStart`,
`hearStack`, `hearGated`, `hear`, each at `engFl`.

NO PREMISE ON THE ARRAYS' SIZES: `Later` itself says that a ledger whose arrays have their size
keeps it. Limits: one direction, from a return; nothing on which values lie under the slots, on the
claims, on soundness or on hiding.
-/
import OnBytes.Desc.First.K4.Plain
import OnBytes.Desc.First.FlGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.Grow

variable {α : Type}

/-! ### The engine's fields -/

instance (x : Option α) : Grows (engFl.get x) := inferInstanceAs (Grows (Fl.need x))
instance (b : Bool) : Grows (engFl.must b) := inferInstanceAs (Grows (Fl.must b))
instance (n : String) (b : Bool) : Grows (engFl.mustAs n b) := inferInstanceAs (Grows (Fl.must b))
instance (n : String) (b : Bool) : Grows (engFl.check n b) := inferInstanceAs (Grows (Fl.must b))
instance : Grows engFl.fork := inferInstanceAs (Grows (Fl.ask some))
instance (j : Nat) : Grows (engFl.shown j) := inferInstanceAs (Grows (Fl.shown j))
instance (a : Aff) : Grows (engFl.lin a) := inferInstanceAs (Grows (Fl.change fun F => F.lin a))

instance (r : RoundName) (n : Nat) : Grows (engFl.point r n) :=
  inferInstanceAs (Grows (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : Nat) : Grows (engFl.claimsIn n) := inferInstanceAs (Grows (Fl.claimsIn n))
instance (n : Nat) : Grows (engFl.batch n) := inferInstanceAs (Grows (Fl.batch n))

instance (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Grows (engFl.levelIn mu rho C order) := inferInstanceAs (Grows (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : Nat) : Grows (engFl.tscIn P lt n d) :=
  inferInstanceAs (Grows (Fl.tscIn P lt n d))

instance (C : Aff) : Grows (engFl.pscBegin C) := inferInstanceAs (Grows (Fl.pscBegin C))

instance (f : RoundForm) (p : Psc) (z : E) (d : Nat) : Grows (engFl.roundIn f p z d) :=
  inferInstanceAs (Grows (Fl.roundIn f p z d))

instance (p : Psc) (d n : Nat) : Grows (engFl.pscEnds p d n) :=
  inferInstanceAs (Grows (Fl.pscEnds p d n))

instance (p : Psc) (s : E) (k : Aff) : Grows (engFl.pscRow p s k) :=
  inferInstanceAs (Grows (Fl.pscRow p s k))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) : Grows (engFl.wsForkEnd lay cl sv) :=
  inferInstanceAs (Grows (flatForkEnd lay cl sv))

/-! ### The parts of HEAR -/

instance (p : Psc) (S0 : E) : Grows (sumcheckClaim engFl p S0) := by
  unfold sumcheckClaim; infer_instance

instance (first n : Nat) : Grows (shownRun engFl first n) := by
  unfold shownRun
  exact grows_mapM_array (fun _ => inferInstance) _

instance (st : Stack) : Grows (plainRounds engFl st) := by
  unfold plainRounds
  refine Grows.bind (grows_foldlM (fun s z => ?_) _ _) fun x => ?_
  · grows
  · grows

instance (g : Forest.Heard) (laid : Array Nat) : Grows (paddingFits engFl g laid) := by
  unfold paddingFits; infer_instance

instance (P : Pub) (g : Nat) (fo : Forest.Heard) : Grows (hearNorms engFl P g fo) := by
  unfold hearNorms; grows

instance (P : Pub) (H : Heard) : Grows (hearTerms engFl P H) := by
  unfold hearTerms; grows

instance (v : Env) (H : Heard) (om : Array E) : Grows (joinStart engFl v H om) := by
  unfold joinStart; grows

instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) :
    Grows (hearStack engFl P v H lamS NCLp) := by
  unfold hearStack; grows

instance (P : Pub) (H : Heard) (K : HeardStack) : Grows (hearGated engFl P H K) := by
  unfold hearGated; grows

instance (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : Grows (hear engFl P hp g fo) := by
  unfold hear; grows

/-- **Wherever HEAR returns, its ledger is later.** -/
theorem hearFl_later {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hearFl P hp g fo F t = some (o, G, u)) : Later F G := by
  have i : Grows (hear engFl P hp g fo) := inferInstance
  exact i.later h

end OnBytes.Desc.First.K4
