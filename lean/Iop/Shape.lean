-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Shape.lean: the list of rounds of a public-coin protocol (`Shape`).

Everything that depends on it (transcripts, verifier randomness, strategies, lists of errors,
families of bad sets) is defined by recursion on the list. So appending two lists unfolds by
definition on cons, and no cast is needed for it.
A rule for whoever extends the library: never unfold a concrete list. Work with [], ::, ++,
`List.replicate` and the lemmas about them (a test with two lists of 40,000 rounds showed no
slowdown).
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic

namespace Iop

open Lean Elab Tactic Meta in
/-- Closes a goal `Unit → C`, C a class, by a new top-level definition
`aux x₁ … x_n u := the instance` (x₁ … x_n: what the instance depends on), applied to x₁ … x_n alone.
Why not `fun _ => inferInstance`: in Lean 4.29.1 the compiler's pass `pullInstances` moves a value
whose type is a class out of a local function that it does not depend on, so that the instance is
computed where the function is made, not where it is called. An application of a top-level
definition that lacks its last argument comes through that pass as it is, and the compiled code
computes the instance inside the function. Both were seen in that version's own traces
(`trace.Compiler.init`, `trace.Compiler.pullInstances`, `trace.Compiler.result`) for a record that
holds such a function. No theorem says so, and another version of Lean may do otherwise. -/
elab "lazy_instance" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let .forallE _ d b _ := t | throwError "lazy_instance: the goal is not a function type"
  let inst ← synthInstance b
  let v ← instantiateMVars (.lam `u d inst .default)
  let n ← mkAuxDeclName `_lazy
  let e ← mkAuxDefinition n (← inferType v) v (compile := false)
  setReducibleAttribute n
  try
    withOptions (fun o => o.setBool `compiler.extract_closed false) do
      compileDecls #[n] (logErrors := false)
  catch _ => pure ()
  g.assign e

/-- One round: a prover message, which consists of an oracle part and a plain part that is read in
full, and then a challenge, uniform in the finite set `Chal`.
The oracle part is abstract: an element of `Orc` that is read by queries p : `Pos` with answers in
`Sym p`.
* oracles that are strings: Orc = ∀ p, Sym p and rd = application (see `Round.IsPoint`); this is
  what the compiler (Compile/) takes;
* linear oracles (Orc = a vector, Pos = linear functionals) also fit the type; no other file of this
  library names them.
A message without oracles has Pos = Empty and Orc = Unit; one without a plain part has Plain = Unit;
a round without a challenge has Chal = Unit. -/
structure Round where
  Orc   : Type
  Pos   : Type
  Sym   : Pos → Type
  rd    : Orc → (p : Pos) → Sym p
  Plain : Type
  Chal  : Type
  /-- a fixed message of the right format: what is sent where there is no honest message, and after
  a rejection of an earlier part, when the later rounds still take place (by convention) -/
  dOrc   : Orc
  dPlain : Plain
  /-- the list of all challenges, behind a function of `Unit`: compiled Lean is strict, and builds
  the list only where this function is called -/
  finChalT : Unit → Fintype Chal := by lazy_instance
  [neChal  : Nonempty Chal]

/-- The instance of the round. -/
@[reducible] def Round.finChal (r : Round) : Fintype r.Chal := r.finChalT ()

attribute [instance] Round.finChal Round.neChal

/-- A prover message of the round. -/
abbrev Round.Msg (r : Round) : Type := r.Orc × r.Plain

/-- A `Shape` is the list of a protocol's rounds, in order. -/
abbrev Shape : Type 1 := List Round

/-- Full transcripts. -/
def Tr : Shape → Type
  | [] => Unit
  | r :: s => r.Msg × r.Chal × Tr s

/-- The verifier's randomness of a whole execution. -/
def Rho : Shape → Type
  | [] => Unit
  | r :: s => r.Chal × Rho s

/-- The plain parts of all prover messages. -/
def Plains : Shape → Type
  | [] => Unit
  | r :: s => r.Plain × Plains s

/-- Positions of all prover oracles. -/
def OPos : Shape → Type
  | [] => Empty
  | r :: s => r.Pos ⊕ OPos s

/-- The alphabet at a position. -/
def OSym : (s : Shape) → OPos s → Type
  | _ :: _, .inl p => Round.Sym _ p
  | _ :: s, .inr p => OSym s p

/-- Deterministic prover strategies that end with a result in β (the prover's output, or its state
for what follows). -/
def Strat : Shape → Type → Type
  | [], β => β
  | r :: s, β => r.Msg × (r.Chal → Strat s β)

instance instFintypeRho : ∀ s : Shape, Fintype (Rho s)
  | [] => inferInstanceAs (Fintype Unit)
  | r :: s => by
      haveI := instFintypeRho s
      exact inferInstanceAs (Fintype (r.Chal × Rho s))

instance instNonemptyRho : ∀ s : Shape, Nonempty (Rho s)
  | [] => inferInstanceAs (Nonempty Unit)
  | r :: s => by
      haveI := instNonemptyRho s
      exact inferInstanceAs (Nonempty (r.Chal × Rho s))

namespace Tr

def rho : {s : Shape} → Tr s → Rho s
  | [], _ => ()
  | _ :: _, (_, c, a) => (c, rho a)

def plains : {s : Shape} → Tr s → Plains s
  | [], _ => ()
  | _ :: _, (m, _, a) => (m.2, plains a)

/-- The answer to a query to a prover oracle. -/
def read : {s : Shape} → Tr s → (p : OPos s) → OSym s p
  | _ :: _, (m, _, _), .inl p => Round.rd _ m.1 p
  | _ :: _, (_, _, a), .inr p => read a p

/-- Concatenation of transcripts. -/
def app : {s t : Shape} → Tr s → Tr t → Tr (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (m, c, a), b => (m, c, app a b)

def fst : {s t : Shape} → Tr (s ++ t) → Tr s
  | [], _, _ => ()
  | _ :: _, _, (m, c, a) => (m, c, fst a)

def snd : {s t : Shape} → Tr (s ++ t) → Tr t
  | [], _, b => b
  | _ :: s, _, (_, _, a) => snd (s := s) a

theorem app_fst_snd : ∀ {s t : Shape} (τ : Tr (s ++ t)), app (fst τ) (snd (s := s) τ) = τ
  | [], _, _ => rfl
  | _ :: s, _, (m, c, a) => by
      show (m, c, app (fst a) (snd (s := s) a)) = (m, c, a)
      rw [app_fst_snd a]

theorem fst_app : ∀ {s t : Shape} (a : Tr s) (b : Tr t), fst (app a b) = a
  | [], _, (), _ => rfl
  | _ :: _, _, (m, c, a), b => by
      show (m, c, fst (app a b)) = (m, c, a)
      rw [fst_app a b]

theorem snd_app : ∀ {s t : Shape} (a : Tr s) (b : Tr t), snd (s := s) (app a b) = b
  | [], _, _, _ => rfl
  | _ :: s, _, (_, _, a), b => snd_app (s := s) a b

end Tr

namespace Rho

def app : {s t : Shape} → Rho s → Rho t → Rho (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (c, a), b => (c, app a b)

def fst : {s t : Shape} → Rho (s ++ t) → Rho s
  | [], _, _ => ()
  | _ :: _, _, (c, a) => (c, fst a)

def snd : {s t : Shape} → Rho (s ++ t) → Rho t
  | [], _, b => b
  | _ :: s, _, (_, a) => snd (s := s) a

end Rho

namespace Strat

/-- Run a strategy against given verifier randomness: the transcript and the result. -/
def run : {s : Shape} → {β : Type} → Strat s β → Rho s → Tr s × β
  | [], _, b, _ => ((), b)
  | _ :: _, _, (m, k), (c, ρ) => let p := run (k c) ρ; ((m, c, p.1), p.2)

/-- Sequential composition of strategies. -/
def bind : {s t : Shape} → {β γ : Type} → Strat s β → (β → Strat t γ) → Strat (s ++ t) γ
  | [], _, _, _, b, g => g b
  | _ :: _, _, _, _, (m, k), g => (m, fun c => bind (k c) g)

/-- The strategy that sends the fixed messages in every round and ends with b. -/
def dflt : (s : Shape) → {β : Type} → β → Strat s β
  | [], _, b => b
  | r :: s, _, b => ((r.dOrc, r.dPlain), fun _ => dflt s b)

def map : {s : Shape} → {β γ : Type} → (β → γ) → Strat s β → Strat s γ
  | [], _, _, g, b => g b
  | _ :: _, _, _, g, (m, k) => (m, fun c => map g (k c))

end Strat

/-- A round whose oracle part is a string that is read symbol by symbol, over a finite set of
positions.
The compiler takes lists of rounds that are all of this kind. -/
structure Round.IsPoint (r : Round) where
  finPos : Fintype r.Pos
  decPos : DecidableEq r.Pos
  /-- a string is given by its symbols -/
  ofSyms : (∀ p, r.Sym p) → r.Orc
  rd_ofSyms : ∀ f p, r.rd (ofSyms f) p = f p
  ofSyms_rd : ∀ o, ofSyms (r.rd o) = o
  /-- the fixed symbol 0 with which the extractor fills undetermined leaves -/
  zero : ∀ p, r.Sym p

/-- Every round's oracle part is a string. -/
def Shape.IsPoint : Shape → Type
  | [] => Unit
  | r :: s => r.IsPoint × Shape.IsPoint s

end Iop
