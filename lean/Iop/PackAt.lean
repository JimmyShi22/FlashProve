-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/PackAt.lean: a packing (Iop/Pack.lean) whose datum is the map of positions alone.

Definitions and proofs. The datum of a round is a `PackAt`: the columns, in which column a position
lies (`colOf`), a flag at each column, equality and finiteness of the columns. The alphabet at a
column is derived: the tuple of the old symbols over the positions that lie in it.
`PackAt.toPacking` gives the record of Iop/Pack.lean, and its two laws hold for every datum. So
soundness, locality and the point structure of Iop/PackProofs.lean hold without a premise on the
datum. Also here, for every `Packings`: the bounds on lists of errors, the proof-of-work bits, and
strategies and the honest prover as data.
Main names:
  `PackAt`, `PackAts`: the datum of a round, of a list of rounds.
  `PackAt.toPacking`, `PackAts.toPackings`: the records of Iop/Pack.lean.
  `PackAt.toPacking_ok`, `PackAt.toPacking_exact`, `PackAts.ok`, `PackAts.exact`: the two laws.
  `Shape.IsPoint.packAt`, `InteractiveOracleProof.Sound.pack`, `InteractiveOracleProof.IsLocal.packAt`: what is kept.
  `Err.Below.pack`, `GBits.pack`, `Err.BelowG.pack`, `GBits.AllLe.pack`: the same numbers.
  `Strat.pack`, `Honest.pack`: the same messages, coins and sets of verifier randomness.
Limits: nothing on completeness or on what a view discloses. `blinded` is by type any map.

-/
import Iop.PackProofs
import Iop.Grind
import Iop.GBitsLe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- In which column each position of a round lies. -/
structure PackAt (r : Round) where
  /-- the columns -/
  Pos : Type
  colOf : r.Pos → Pos
  /-- by type any map (`InteractiveOracleProof.blinded`, Iop/InteractiveOracleProof.lean) -/
  blinded : Pos → Bool
  dec : DecidableEq Pos
  fin : Fintype Pos

/-- The symbol at a column is the tuple of the old symbols at the positions that lie in it. -/
def PackAt.toPacking {r : Round} (k : PackAt r) : Packing r where
  Pos := k.Pos
  Sym := fun q => (p : {p : r.Pos // k.colOf p = q}) → r.Sym p.1
  col := fun o _ p => r.rd o p.1
  colOf := k.colOf
  prj := fun p f => f ⟨p, rfl⟩
  blinded := k.blinded
  dec := k.dec

theorem PackAt.toPacking_ok {r : Round} (k : PackAt r) : k.toPacking.OK := ⟨fun _ _ => rfl⟩

theorem PackAt.toPacking_exact {r : Round} (k : PackAt r) : k.toPacking.Exact :=
  ⟨fun g g' h => by
    funext q
    show (g q : (p : {p : r.Pos // k.colOf p = q}) → r.Sym p.1) = g' q
    funext ⟨p, hp⟩
    subst hp
    exact h p⟩

/-- One datum for each round. -/
def PackAts : Shape → Type 1
  | [] => PUnit
  | r :: s => PackAt r × PackAts s

def PackAts.toPackings : {s : Shape} → PackAts s → Packings s
  | [], _ => PUnit.unit
  | _ :: _, (k, ks) => (k.toPacking, PackAts.toPackings ks)

theorem PackAts.ok : ∀ {s : Shape} (k : PackAts s), k.toPackings.OK
  | [], _ => trivial
  | _ :: _, (k, ks) => ⟨k.toPacking_ok, PackAts.ok ks⟩

theorem PackAts.exact : ∀ {s : Shape} (k : PackAts s), k.toPackings.Exact
  | [], _ => trivial
  | _ :: _, (k, ks) => ⟨k.toPacking_exact, PackAts.exact ks⟩

def PackAts.pt : {s : Shape} → (k : PackAts s) → k.toPackings.Pt
  | [], _ => ()
  | _ :: _, (k, ks) => (k.fin, PackAts.pt ks)

/-- The point structure of the packed rounds, from the old one. No law of the datum is asked. -/
def Shape.IsPoint.packAt {s : Shape} (pts : s.IsPoint) (k : PackAts s) :
    (s.pack k.toPackings).IsPoint :=
  Shape.IsPoint.pack pts k.toPackings k.pt k.ok k.exact

variable {X : Type} {E : ExtSpec}

theorem InteractiveOracleProof.Sound.pack {Q : InteractiveOracleProof X E} {L : X → E.Str → Prop} {ε : Err Q.shape}
    (h : Q.Sound L ε) (k : Packings Q.shape) : (Q.pack k).Sound L (Err.pack k ε) :=
  pack_sound X E Q k L ε h

/-- Locality, for every datum. -/
theorem InteractiveOracleProof.IsLocal.packAt {Q : InteractiveOracleProof X E} (h : Q.IsLocal) (k : PackAts Q.shape) :
    (Q.pack k.toPackings).IsLocal :=
  pack_local X E Q k.toPackings k.ok h

/-! ## Lists of errors and of proof-of-work bits -/

theorem Err.Below.pack :
    ∀ {s : Shape} (k : Packings s) {ε : Err s} {c : ℝ≥0∞},
      Err.Below ε c → Err.Below (Err.pack k ε) c
  | [], _, _, _, _ => trivial
  | _ :: _, (_, ks), (_, _), _, h => ⟨h.1, Err.Below.pack ks h.2⟩

/-- The same numbers of proof-of-work bits. -/
def GBits.pack : {s : Shape} → (k : Packings s) → GBits s → GBits (s.pack k)
  | [], _, _ => ()
  | _ :: _, (_, ks), (b, g) => (b, GBits.pack ks g)

theorem Err.BelowG.pack :
    ∀ {s : Shape} (k : Packings s) {g : GBits s} {ε : Err s} {c : ℝ≥0∞},
      Err.BelowG g ε c → Err.BelowG (GBits.pack k g) (Err.pack k ε) c
  | [], _, _, _, _, _ => trivial
  | _ :: _, (_, ks), (_, _), (_, _), _, h => ⟨h.1, Err.BelowG.pack ks h.2⟩

theorem GBits.AllLe.pack {n : ℕ} :
    ∀ {s : Shape} (k : Packings s) {g : GBits s}, g.AllLe n → (GBits.pack k g).AllLe n
  | [], _, _, _ => trivial
  | _ :: _, (_, ks), (_, _), h => ⟨h.1, GBits.AllLe.pack ks h.2⟩

/-! ## Strategies and the honest prover, as data -/

/-- The same messages. -/
def Strat.pack : {s : Shape} → {β : Type} → (k : Packings s) → Strat s β → Strat (s.pack k) β
  | [], _, _, b => b
  | _ :: _, _, (_, ks), (m, f) => (m, fun c => Strat.pack ks (f c))

/-- The same coins, external string and messages; the same sets of verifier randomness. -/
def Honest.pack {Q : InteractiveOracleProof X E} {Wt : Type} (H : Honest Q Wt) (k : Packings Q.shape) :
    Honest (Q.pack k) Wt where
  Coin  := H.Coin
  ext   := H.ext
  strat := fun w x c => Strat.pack k (H.strat w x c)
  Bad   := {ρ | Rho.unpack k ρ ∈ H.Bad}
  Hid   := fun w x => {ρ | Rho.unpack k ρ ∈ H.Hid w x}

end Iop

#print axioms Iop.PackAt.toPacking_ok
#print axioms Iop.PackAt.toPacking_exact
#print axioms Iop.Shape.IsPoint.packAt
#print axioms Iop.InteractiveOracleProof.IsLocal.packAt
#print axioms Iop.Err.Below.pack
#print axioms Iop.Err.BelowG.pack
