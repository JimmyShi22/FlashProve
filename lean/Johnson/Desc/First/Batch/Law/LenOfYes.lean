-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Batch/Law/LenOfYes.lean (kind K9's soundness lemma; the law of a link on the
road of moves): "THE RUNS' CLAIMS, AS THE TABLES OF LENGTHS COUNT THEM OFF THE FIXED PART, ARE AT
MOST THE PLAN's NUMBER OF CLAIMS", OUT OF THE BATCHING's OWN YES: THE SECOND HALF OF THE PREMISE
hR1 OF inMoves_rows (Law/RowsNumber.lean) AT THE PUBLIC SENTENCE C' := rowsFit AND THIS ONE.
Definitions; statements and proofs: calls. Beside Law/RowsRide.lean, which pays hR1, hR2, hR3 at
rowsFit.

Why. The field Anumbers of a link's law asks, of the promise on the fixed part, that the runs'
claims be at most the plan's number (`EqTake.hlen`, Link/Law/ExpsAt.lean). As a clause of the
promise it must be shown at every reached state in front of the batching, and there it comes down
to facts on the maker's plans that the head pins nowhere. But the verifier
tests it itself. So the sentence belongs where rowsFit stands: in the public sentence C that
inMoves_rows takes OUT OF the promise and proves from a piece's own yes.

WHICH YES. Not the door's (the road "the one equation accepts only if the count of
claims is the plan's number", handed backward as a second half of Rw): Rw is no private letter of
inMoves_rows: it stands in the three pieces' relations, the ties hold these against the table's
items, and at the closed constant the items carry the constant's own test rw and nothing more: that
road would turn the constant. THE BATCHING's OWN: hR1 has the first
piece's yes in hand: the adding takes each claim's weight by the ledger's map of weights, which the
draw has set up with the plan's number of places, and refuses a claim beyond it
(batch_bound, Law/AddBound.lean). Rw, hR2, hR3 stay as they are.

THE CIRCLE, AND HOW IT IS CUT. What ties the number of claims that the runs really return to the
tables' number is the clause "c.length = len q" of AddOk (Law/Moves.lean), which speaks under the
promise. In the joining the promise is fun q => Ok q ∧ C q: to prove C from that clause one would
need C. HERE THE CLAUSE IS TAKEN AT THE BARE PROMISE Ok₀, WITHOUT C: the runs' payers are general
in the promise.

What is said.
  `lenFit len q`: the sentence on the fixed part: len q ≤ the snapshot's plan's number (the text of
    `NumbersOk.hlen`, Link/Law/SortNumbers.lean).
  `len_of_add` (general in the state's type): at a draw with one adding move behind it, from a
    ready state: len of the fixed part ≤ the plan's number at the state in front.
  `len_hR1`: **the second half of hR1: from the first piece's yes: lenFit of the fixed part in
    front**, where the state in front is ready at the bare promise and the gatherer keeps the map
    (KeepsKap).
  `len_hR1_link`: the same at a link's own gatherer, from one RunOk a run AT THE BARE PROMISE:
    lenFit (fun q => lenRuns q rl).

Limits. hr (the state in front is ready at Ok₀) is a premise: in the joining it comes from the
field Aready, which may lean on rowsFit but must not lean on lenFit. SO Ok₀ MUST NOT ITSELF HOLD
THE SENTENCE: at the sorts' letters it is the named Ok with K3's promise and the three clauses
funs, heard, hmS of NumbersOk, WITHOUT the fourth, hlen: else the circle comes back through the
letter Kx. hk (KeepsKap at the gatherer) is a premise: a sentence on the runs' texts. Nothing is
turned by this file. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.AddBound
import Johnson.Desc.First.Batch.Law.RowsRide
import Johnson.Desc.First.Batch.Law.FitsAtS
import Johnson.Desc.First.Link.Law.JoinAtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Lens atS Where)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.JoinAtBlocks (claimsInBy_addOk runsIn)
open _root_.Run (ckP)

section General
variable {T P K : Type} [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K)
  (Fx : P → T → Prop)

/-- **AT THE YES OF A DRAW WITH ONE ADDING MOVE THE MOVE's LENGTH IS AT MOST THE PLAN's NUMBER.** -/
theorem len_of_add {Cl : Type} (p : Where) (H : FitsM X O Fx p)
    (g : T → Except String (List Claim × T)) (tm : ℕ → P → Bound K → List (ℕ × K)) (len : P → ℕ)
    (hg : AddOk ρ X O Fx g tm len) (hk : KeepsKap X g) (b : Block T Cl)
    (hb : DrawMoves X p [.add g] b) (ft : ℕ) (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (s' : T) (k : ℕ) (hr : O.ready s) (hs : b.step ft s rs cols = .ok (s', k)) :
    ∃ a, X.get? s = some a ∧ len (O.fixed s) ≤ a.F.planClaimsF := by
  obtain ⟨r, x, a, o, c, e₁, _, _, ha, ho, hge, hle⟩ := batch_bound X H.lens p g b hb hk hs
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, d12⟩ := drawnClean_ok _ _ _ _ _ _ _ ho
  obtain ⟨a₁, ha₁, hF⟩ := H.lens s { a with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
  have hF' : a₁.F = o.F := hF
  obtain ⟨f1, g1⟩ := H.atDraw s a o x hr ha ho
  obtain ⟨_, _, _, _, _, _, hl, _⟩ := hg (O.fixed s) _ a₁ c e₁ f1 g1 ha₁
    (by rw [hF']; exact d12) hge
  exact ⟨a, ha, hl ▸ hle⟩

end General

variable {α : Type}

/-- The sentence on the fixed part. -/
def lenFit (len : α × Option Pub9 → ℕ) (q : α × Option Pub9) : Prop :=
  ∀ v, q.2 = some v → len q ≤ v.F.planClaimsF

section
variable {W Cl : Type} {F : Frame}

/-- **THE SECOND HALF OF hR1.** -/
theorem len_hR1 (φ : S → α) (Ok₀ : α × Option Pub9 → Prop) (Fu : S → Prop) (p : Where)
    (H : FitsM atS (O9 (K := Cb.Gl.E) φ Ok₀ Fu) (Fx9 φ Ok₀) p)
    (g : S → Except String (List Claim × S))
    (tm : ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (len : α × Option Pub9 → ℕ)
    (hg : AddOk Reading.gl atS (O9 φ Ok₀ Fu) (Fx9 φ Ok₀) g tm len) (hk : KeepsKap atS g)
    (b₁ : Block S Cl) (hb₁ : DrawMoves atS p [.add g] b₁) (pb : Piece (ckP .two) F S Cl W)
    (hpb : pb.b = below b₁) (a b' : S × F.E.Str)
    (τ : _root_.Iop.Tr (uLT (ckP .two) pb.ds)) (hout : pb.ior.red.out a τ = some b')
    (hr : k9OnA a.1 = true ∧ Ok₀ (fixed9 φ a.1)) : lenFit len (fixed9 φ a.1) := by
  intro v hv
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨x, hx, hle⟩ := len_of_add Reading.gl atS (O9 φ Ok₀ Fu) (Fx9 φ Ok₀) p H g tm len hg hk
    b₁ hb₁ _ _ _ _ _ k hr hs
  simp only [fixed9, Option.map_eq_some_iff] at hv
  obtain ⟨x', hx', rfl⟩ := hv
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  exact hle

end

section
variable {W : Type} {F : Frame}

/-- **THE SAME AT A LINK's OWN GATHERER, FROM ONE RunOk A RUN AT THE BARE PROMISE.** -/
theorem len_hR1_link (φ : S → α) (Ok₀ : α × Option Pub9 → Prop) (Fu : S → Prop) (p : Where)
    (H : FitsM atS (O9 (K := Cb.Gl.E) φ Ok₀ Fu) (Fx9 φ Ok₀) p) (L : Link S Claim)
    (rl : List (TermedRun S (α × Option Pub9) Cb.Gl.E))
    (hrl : rl.map (·.run) = runsIn L.hear L.order)
    (hruns : ∀ r ∈ rl, RunOk Reading.gl atS (O9 φ Ok₀ Fu) (Fx9 φ Ok₀) r.run.2 r.tm r.len)
    (hk : KeepsKap atS (claimsInBy L.each L.hear L.order))
    (hb₁ : DrawMoves atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (pb : Piece (ckP .two) F S Claim W) (hpb : pb.b = below L.batchB) (a b' : S × F.E.Str)
    (τ : _root_.Iop.Tr (uLT (ckP .two) pb.ds)) (hout : pb.ior.red.out a τ = some b')
    (hr : k9OnA a.1 = true ∧ Ok₀ (fixed9 φ a.1)) :
    lenFit (fun q => lenRuns q rl) (fixed9 φ a.1) :=
  len_hR1 φ Ok₀ Fu p H (claimsInBy L.each L.hear L.order) (fun n q y => termsRuns q y rl n)
    (fun q => lenRuns q rl)
    (claimsInBy_addOk Reading.gl atS (O9 φ Ok₀ Fu) (Fx9 φ Ok₀) p H L.each L.hear L.order rl hrl
      hruns)
    hk L.batchB hb₁ pb hpb a b' τ hout hr

end

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.len_of_add
#print axioms VerifiableInference.Desc.K9L.len_hR1
#print axioms VerifiableInference.Desc.K9L.len_hR1_link
