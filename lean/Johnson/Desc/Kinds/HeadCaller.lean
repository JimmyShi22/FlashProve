-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadCaller.lean: the output head's own rounds as the caller of the lookup whose
calls they fill. It shows nothing by itself: definitions with code, no theorem, nothing on
soundness.

Behind its rounds the lookup owes two runs of claims that read what the calling kind hands in. Both
formulas are the lookup's own (Johnson/Desc/First/Look/K3Runs.lean).
  "join": one claim on the calls' key vectors. STATED BY THE CALLER, as one line that calls the
    lookup's function on callerKeys: one form a call: the key vectors of HeadFrame.lean, at what
    was heard and where the reads lie. So the kind states FOUR runs: kindWithJoin.
  "planes": three claims on the planes of the counts' bits. STATED BY THE LOOKUP. THE CALLER HANDS
    callerReaders: bit e col and pin col: forms that read the planes' matrix, column by column:
    entries of three further reads that stand in the head's vector of reads. Their weights are the
    lookup's, not this kind's.
That the number of padding places is the lookup's is asked on the plan (HeadFrame.lean:
Par.paddingPlaces). In which order the runs are called is the link's to say, by their names; the
order in the block's list says nothing. No run of this kind lays what "join" reads: callerKeys makes
the key vectors itself, and a run of claims leaves the ledger as it is; "join" marks its debt in the
ledger.
NEVER TWO "join"s AT ONCE: no test on names can see a claim that is added twice under two blocks: a
lookup's block that states "join" itself must not stand in one link with kindWithJoin.

-/
import Johnson.Desc.Kinds.HeadKind
import Johnson.Desc.First.Look.K3Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

variable {S : Type}

/-- The three further reads: the planes' matrix at the lookup's two points, and under the weights
that count. -/
inductive PlaneRead | bits0 | bits1 | pin

/-- Where the carried record keeps them: entry col of a read, as a variable of a form; nothing from
the matrix's number of columns on; nothing at all until the reads' places are laid. -/
abbrev PlaneSeat (S : Type) : Type := S → Option (PlaneRead → Nat → Option Form)

/-- One form a call: the call's key vector at its point. -/
def callerKeys (p : Par) (L : Seat S) (s : S) : Option (Array Form) :=
  let keys : Given → Behind → Places → List Form :=
    fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2
  (lettersAt p L s).toOption.map fun x => (keys x.1 x.2.1 x.2.2).toArray

/-- bit e col (e: 0 or 1: at which of the lookup's two points) and pin col. -/
def callerReaders (X : PlaneSeat S) (s : S) :
    Option ((Nat → Nat → Option Form) × (Nat → Option Form)) :=
  (X s).map fun at_ => (fun e col => at_ (if e == 0 then .bits0 else .bits1) col, at_ .pin)

/-- THE KIND WITH ITS FOUR RUNS: "norm" · "join" · "policy" · "logits". look: where the carried
record keeps what the lookup reads and writes. -/
def kindWithJoin {Cl : Type} (look : K3.Seat S Cl) (L : Seat S) (link piece : Nat) :
    Kind Par S Cl := fun p =>
  let b := kind look.claim L link piece p
  { b with claims := b.claims.take 1 ++ [("join", K3.joinRun look (callerKeys p L))] ++
      b.claims.drop 1 }

end VerifiableInference.Desc.Kinds.Head
