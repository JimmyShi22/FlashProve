-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Runs.lean: the two runs of claims on a lookup that read what the calling
kind hands in: "planes", which the kind "lookup" states, and "join", which the calling kind states
as one line that calls the function here. Definitions with code. No theorem.

Behind its rounds a lookup leaves three debts in the sub-proof's ledger. The first is paid by the
run "objects" (Johnson/Desc/First/Look/K3Lookup.lean). The two others are paid here. Both formulas are the
lookup's own: functions of what was heard. What they are handed is the caller's.
  "join": one claim on the calls' key vectors: the sum over the calls c of e_c (alpha - c theta -
    KF_c), and a public term for the trees that hold padding alone, is the hidden value at the end
    of the key side. KF_c: the caller's form of call c's key vector at the point zk[c].
  "planes": three claims on the planes of the counts' bits: what the leaves' sumcheck left, with the
    planes' value at its point; the planes' value at the bits' sumcheck's point is what that
    sumcheck has shown; the counts sum to the number of keys that are no padding. `bit e col` and
    `pin col`: the caller's forms that read the planes' matrix, column by column, in its own tables.

Main names:
  `Readers S`: what the calling kind hands in for "planes": `bit` and `pin` as a pair, made once a
    run: a plain function of the carried record.
  `joinRun seat keys`: FOR THE CALLING KIND'S RUN "join": keys: its form of each call's key vector.
  `planesRun seat lm readers`: the kind's own run. Each of the two hands out forms as claims, lays
    the ledger back and marks its debt. Each is made once. Each refusal bears a name.
  `withCaller seat p readers b`: the kind's block b with "planes" stated behind its own runs.

Limits: the formulas are those of Johnson/Desc/First/Look/LookClaims.lean (`joinF`),
LookPlanesOwn.lean (`planeClaimsOwn`) and LookPlanes.lean (`planesAddedF`), typed after
`Forest.join`, `planeClaims`, `planesAdded` (OnBytes/Model/Look.lean:455-468, :496-506,
:431) line by line; runs alone hold them against these.
(`planesAddedF` is defined in LookClaims.lean; LookPlanes.lean calls it.)
"planes" TURNS THE LEDGER BESIDE ITS MARK:
the leaves' sumcheck's claim fills the slots of its hiding polynomial's coefficients. A second call
of either run is refused by the debt's mark: stricter than `verify-on-bytes`, which refuses a second
"join" nowhere. Where the ledger has no debt of that number nothing is marked, as in that text,
and a second call is not seen by the mark. THAT THE CALLER'S FORMS READ WHAT THEY ARE MEANT TO READ,
AND ONLY WHAT WAS SENT OR FIXED IN FRONT OF THE FIRST DRAW THAT THEY BORROW, IS THE CALLER'S FILES'
TO SHOW: nothing here can test it: they are called late, on the whole record, as a guest's form is.
That the caller's count of padding places is the lookup's is asked on the plan (`planOk`'s `laid`),
not here. In which order the runs are called is the link's to say: at an attention link "join"
behind the caller's keys, "planes" last. All that a formula refuses bears one name.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Lookup
import Johnson.Desc.First.Look.LookPlanesOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff)
open First.Look (P)

/-- What the calling kind hands in for "planes": bit e col (e: 0 or 1: at which of the two points;
the column) and pin col. Asked once a run: so a caller that must make its tables to read them makes
them once. -/
abbrev Readers (S : Type) : Type := S → Option ((Nat → Nat → Option Aff) × (Nat → Option Aff))

/-- The debt of that number in the ledger is not yet marked as paid. -/
def unpaid (F : Fork) (i : Nat) : Bool := ((F.owed[i]?).map (·.added)) != some true

variable {S Cl : Type}

/-- **"join"**: the claim on the calls' key vectors. keys: one form a call: the call's key vector
at its point: the calling kind's. -/
def joinRun (seat : Seat S Cl) (keys : S → Option (Array Aff)) (_ : Nat) (s : S) :
    Except String (List Cl × S) := do
  let F ← named "K3 join: no sub-proof is open" (seat.fork s)
  let g ← named "K3 join: nothing was heard" (seat.heard s)
  need "K3 join: it is made once" (unpaid F g.owedJoin)
  let KF ← named "K3 join: the caller's keys" (keys s)
  let x ← named "K3 join: one form and one weight a call" (First.Look.joinF g KF F [])
  pure ([seat.claim x.1], seat.mark s x.2.1)

/-- **"planes"**: the three claims on the planes of the counts' bits. lm: the planes' matrix has
2 ^ lm rows. -/
def planesRun (seat : Seat S Cl) (lm : Nat) (readers : Readers S) (_ : Nat) (s : S) :
    Except String (List Cl × S) := do
  let F ← named "K3 planes: no sub-proof is open" (seat.fork s)
  let g ← named "K3 planes: nothing was heard" (seat.heard s)
  need "K3 planes: they are made once" (unpaid F g.owedPlanes)
  let r ← named "K3 planes: the caller's readers" (readers s)
  let all : Fl (Array Aff) := do
    let fs ← First.Look.planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col))
      fun col => Fl.need (r.2 col)
    First.Look.planesAddedF g
    pure fs
  let x ← named "K3 planes: the matrix, the caller's forms or the leaves' claim" (all F [])
  pure (x.1.toList.map seat.claim, seat.mark s x.2.1)

/-- The kind's block with "planes" stated behind its own runs. -/
def withCaller (seat : Seat S Cl) (p : P) (readers : Readers S) (b : Block S Cl) : Block S Cl :=
  { b with claims := b.claims ++ [("planes", planesRun seat p.lm readers)] }

end VerifiableInference.Desc.K3
