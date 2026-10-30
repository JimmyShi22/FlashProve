-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Borders.lean
(kind K9's soundness lemma): DEFINITIONS, and two small theorems: what kind K9 says
at its borders in the proof file's first chain, BY NAME, at the state S that the chain carries
(through the lens atS, Batch/AtS.lean), for a table of what each block hands to the next.
THE RELATIONS (tab: the tables that the witness holds; which they are is not K9's to say):
  k9TotalBehind   behind the batching: the runs behind the batching return, and the ledger's value,
                  READ AT THE STATE THAT THEY RETURN, on the data that the tables hold, is 0.
  k9Total         behind these runs, in front of the one equation: the ledger's value, read at its
                  own state, is 0. (Two sentences: the virtual rows' weights are laid between them.)
  k9Rows          behind the one equation: every open row of the segment's group holds on the
                  tables.
They are K9's OWN ITEMS in the relations of Law/Row3.lean (relAt) at j + 1, j + 2 and j + 3, at the
lens atS; relAt carries beside them the group's open rows (at j + 1 and j + 2) and the context ctx.
THE BOOK-KEEPING, each a test with code on S:
  k9OnA   in front of the batching: a segment is open; nothing is owed; the draw has not run; claims
          are planned; the ledger is empty; no claim is counted; ONE COEFFICIENT FOR EACH SLOT.
  k9OnB   in front of the one equation: the draw has run; the door has not been walked.
  sized_of_onA    k9OnA gives "one coefficient for each slot" (which the draw tests too).
  own_of_goodIn   a piece that is good between two relations is good between two sets of items whose
                  meanings fit these relations: the form "from its ins to its outs".
WHERE atS GIVES NO PART, k9Total AND k9TotalBehind SAY "0 = 0" (oneK's value there) AND k9Rows HOLDS
IDLY: so in a table's row they stand never alone, always beside k9OnA or k9OnB.
No block of the chain is named here, and k9OnA | k9OnB are evaluated at no run.

-/
import Johnson.Desc.First.Batch.Law.AtSLens
import Johnson.Desc.First.Batch.Law.Row3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.First (S)

variable {K : Type} [CommRing K]

/-- Behind the batching. after: the runs behind the batching, one after the other. -/
def k9TotalBehind (ρ : Reading K) (after : S → Except String S) (s : S)
    (tab : Nat → OnBytes.Part → Nat → K) : Prop :=
  ∃ t, after s = .ok t ∧ oneK atS ρ t s (dataAt atS s tab) = 0

/-- In front of the one equation. -/
def k9Total (ρ : Reading K) (s : S) (tab : Nat → OnBytes.Part → Nat → K) : Prop :=
  oneK atS ρ s s (dataAt atS s tab) = 0

/-- Behind the one equation. N: at least the number of oracle messages sent. -/
def k9Rows (ρ : Reading K) (N : Nat) (s : S) (tab : Nat → OnBytes.Part → Nat → K) : Prop :=
  GroupHoldsAt atS ρ N s tab

/-- The book-keeping in front of the batching. -/
def k9OnA (s : S) : Bool :=
  (atS.get? s).any fun a =>
    a.owed.isNone && !a.L.handed && !a.F.thetaDrawnF && a.F.planClaimsF != 0 &&
      K9.ledgerEmpty a.F && a.F.nClaim == 0 && a.F.LS.size == a.F.ns

/-- The book-keeping in front of the one equation. -/
def k9OnB (s : S) : Bool :=
  (atS.get? s).any fun a => a.L.handed && a.F.thetaDrawnF && !a.F.doorShutF

theorem sized_of_onA (s : S) (h : k9OnA s = true) :
    ∀ a, atS.get? s = some a → a.F.LS.size = a.F.ns := by
  intro a ha
  simp only [k9OnA, ha, Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- **From two relations to two sets of items.** -/
theorem own_of_goodIn {T Cl W ι : Type} {C : _root_.Run.PQ.CK} {F : Frame} (p : Piece C F T Cl W)
    {on on' : T × F.E.Str → Prop} {R R' : T × F.E.Str → W → Prop} (h : p.GoodIn on on' R R')
    (means : ι → T × F.E.Str → W → Prop) (In Out : ι → Prop)
    (hin : ∀ a w, on a → R a w → ∀ i, In i → means i a w)
    (hout : ∀ b w, on' b → (∀ i, Out i → means i b w) → R' b w) :
    p.GoodIn on on' (fun a w => ∀ i, In i → means i a w) (fun b w => ∀ i, Out i → means i b w) :=
  goodIn_conseq p h (fun _ h => h) (fun _ h => h) hin hout

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.sized_of_onA
#print axioms VerifiableInference.Desc.K9L.own_of_goodIn
