-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/Clause.lean: the kind "lookup" (K3): a condition on what
a state holds as heard by a lookup. It is meant for the files on the lookup's runs of claims in this
folder, which are to show that under it the claims name the lookup's slots with coefficients that
are not 0; nothing of that is shown here. The condition as a definition, what it unfolds to, and
from what it follows at the hearing. Definitions and theorems.

Terms. Honest/K3/GLOSSARY.md ("face", "good samples", "sample", "slot", "ledger"). In this file: the
seated hearing is `hearVia` (Johnson/Desc/First/Look/Via/Via.lean); p holds a place's public
parameters (`P`, Johnson/Desc/First/Look/LookKind.lean); the test on the samples is `goodK3`
(Honest/K3/GoodDraws.lean); `canDraw` (Honest/K3/GoodDrawsLaw.lean) says that the samples are such
as the lookup's rounds can sample.

What is defined and shown.
  `HeardBy T p H`: H is what the seated hearing at p leaves, from some ledger whose next slot is the
    place's first slot, on some rounds whose samples pass `canDraw` and the test T at the face of
    the place's shape. T is a parameter, so that two tests can be asked of the same rounds.
  `HeardGood`, `HeardGoodOut`, `HeardGoodBoth`: the same at `goodK3`; at `goodK3Out`; at both.
  `ClauseBy T p o`, `Clause p o`, `ClauseOut p o`, `ClauseBoth p o`: the condition, on an optional
    value: o holds such an H. At the lookup on a link's
    calls o is meant to be `S.lookHeard?` of the state, at the lookup on the digits of a smallness
    test `s.tl?.bind (·.heard)`: what the two seats of Johnson/Desc/First/Look/K3Seat.lean read as
    heard (`calls_reads`, `digits_reads`). No ledger of the state is read.
  `shape_ok`, `level_of_shape`: a shape that a place's parameters make passes the library's test on
    a shape's numbers; with more than one call its table has a level.
  `via_parts`: a return of the seated hearing, taken apart.
  `HeardBy.parts`: what the condition unfolds to, in the terms of `hearV` and `toHeard`, with
    1 ≤ h.d.
  `HeardBy.mono`, `ClauseBy.mono`, `ClauseBoth.left`, `ClauseBoth.right`: a stronger test gives the
    condition at a weaker one. `clause_none`: the empty value does not meet the condition.
  `digits_reading`: what the lookup on the digits has heard can be read off the first of the three
    values of `K9L.numOf` (Johnson/Desc/First/Batch/Law/RowsRide.lean).
  `clauseBy_of`: the condition, from a return of the seated hearing on samples that pass `canDraw`
    and T.

Hypotheses that remain.
  In `clauseBy_of`: the place has a shape (`hp`); the ledger's next slot is the place's first
    (`hn`); the hearing returns (`hv`); `canDraw` and T accept the rounds' samples (`hc`, `hg`); o
    holds what was heard (`ho`).
  `hp`: (in `shape_ok`, `level_of_shape`, `via_parts` too) the place has a shape. `hN`: (in
    `level_of_shape`) more than one call. `hv`: (in `via_parts` too) the hearing returns.
  `J`: (in `HeardBy.mono`, `HeardBy.parts`, `ClauseBy.mono`, `ClauseBoth.left`, `ClauseBoth.right`)
    the condition in question. `hT`: (in the two theorems `mono`) where T accepts, T' accepts.

Users. Honest/K3/Good/Live/ClauseMark.lean; the files on the runs in this folder.

Limits. What the condition gives for a run's claims is not shown in this file. The condition says
"there are a ledger and rounds": it does not say which. Nothing is said on
how a state comes to hold what was heard, nor on the states between the hearing and a run of claims.
No instance of the condition is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.GoodDrawsLaw
import Johnson.Desc.First.Look.Via.Via
import Johnson.Desc.First.Look.K3Seat
import Johnson.Desc.First.Look.ShapeOwnAgrees2
import Johnson.Top.H.Keep.RunsMember
import Johnson.Desc.First.Batch.Law.RowsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes.Model (Aff Fork HTailF2)
open OnBytes.Model.Forest (Shape Heard)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG seatCalls seatDigits)
open VerifiableInference.Desc.K3.Law (hearVia)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## The condition -/

/-- **H is what the seated hearing at p leaves on samples that pass the test T**, from a ledger
whose next slot is the place's first slot. F and rs are bound by "∃" and held by what functions
return at them alone: some values: not said to be the step's own. -/
def HeardBy (T : LFace → List Fmt.Drawn → Bool) (p : P) (H : Heard) : Prop :=
  ∃ (h : Shape) (F G : Fork) (rs : List Fmt.RoundView), p.shape = some h ∧ F.next = p.first ∧
    hearVia p F rs = some (H, G) ∧ canDraw (faceOf h) (rs.map (·.drawn)) = true ∧
    T (faceOf h) (rs.map (·.drawn)) = true

/-- At the test for the lookup's own slots. -/
def HeardGood (p : P) (H : Heard) : Prop := HeardBy goodK3 p H

/-- At the test for other kinds' slots and entries. -/
def HeardGoodOut (p : P) (H : Heard) : Prop := HeardBy goodK3Out p H

/-- At both tests, on the same rounds. -/
def HeardGoodBoth (p : P) (H : Heard) : Prop :=
  HeardBy (fun f ds => goodK3 f ds && goodK3Out f ds) p H

/-- **The condition**, on what a state holds as heard; T is the test. -/
def ClauseBy (T : LFace → List Fmt.Drawn → Bool) (p : P) (o : Option Heard) : Prop :=
  ∃ H, o = some H ∧ HeardBy T p H

/-- **The condition at the test for the lookup's own slots.** -/
def Clause (p : P) (o : Option Heard) : Prop := ClauseBy goodK3 p o

/-- At the test for other kinds' slots and entries. -/
def ClauseOut (p : P) (o : Option Heard) : Prop := ClauseBy goodK3Out p o

/-- At both tests, on the same rounds. -/
def ClauseBoth (p : P) (o : Option Heard) : Prop :=
  ClauseBy (fun f ds => goodK3 f ds && goodK3Out f ds) p o

/-- The empty value does not meet the condition. -/
theorem clause_none (T : LFace → List Fmt.Drawn → Bool) (p : P) : ¬ ClauseBy T p none := by
  rintro ⟨H, e, _⟩
  exact nomatch e

/-- A stronger test gives the condition at a weaker one. -/
theorem HeardBy.mono {T T' : LFace → List Fmt.Drawn → Bool}
    (hT : ∀ f ds, T f ds = true → T' f ds = true) {p : P} {H : Heard} (J : HeardBy T p H) :
    HeardBy T' p H := by
  obtain ⟨h, F, G, rs, a1, a2, a3, a4, a5⟩ := J
  exact ⟨h, F, G, rs, a1, a2, a3, a4, hT _ _ a5⟩

theorem ClauseBy.mono {T T' : LFace → List Fmt.Drawn → Bool}
    (hT : ∀ f ds, T f ds = true → T' f ds = true) {p : P} {o : Option Heard}
    (J : ClauseBy T p o) : ClauseBy T' p o := by
  obtain ⟨H, e, J'⟩ := J
  exact ⟨H, e, J'.mono hT⟩

theorem ClauseBoth.left {p : P} {o : Option Heard} (J : ClauseBoth p o) : Clause p o :=
  ClauseBy.mono (fun _ _ h => (Bool.and_eq_true_iff.1 h).1) J

theorem ClauseBoth.right {p : P} {o : Option Heard} (J : ClauseBoth p o) : ClauseOut p o :=
  ClauseBy.mono (fun _ _ h => (Bool.and_eq_true_iff.1 h).2) J

/-- What the seat at the calls reads as heard. -/
theorem calls_reads {Cl : Type} (claim : Aff → Cl) (s : FS) :
    (seatCalls claim).heard s = s.lookHeard? := rfl

/-- What the seat at the digits reads as heard. -/
theorem digits_reads {Cl : Type} (claim : Aff → Cl) (s : FS) :
    (seatDigits claim).heard s = s.tl?.bind (·.heard) := rfl

/-! ## What it unfolds to -/

/-- A shape that a place's parameters make passes the library's test on a shape's numbers. -/
theorem shape_ok {p : P} {h : Shape} (hp : p.shape = some h) : FoNums.ok h = true := by
  unfold P.shape at hp
  obtain ⟨h0, e0, e1⟩ := Option.bind_eq_some_iff.1 hp
  split at e1
  · rename_i hb
    obtain rfl := Option.some.inj e1
    exact VerifiableInference.OnPublicFiles.ok_of_shapeOf
      ⟨h0, VerifiableInference.Desc.First.Look.shapeOwn_gives e0,
        VerifiableInference.Desc.First.Look.pubOk_gives hb, rfl⟩
  · exact nomatch e1

/-- With more than one call, the table of such a shape has a level. -/
theorem level_of_shape {p : P} {h : Shape} (hp : p.shape = some h) (hN : 1 < h.NC) : 1 ≤ h.d := by
  have h3 : h.NC ≤ 2 ^ h.cK := (Cb.Fo.ok_parts (shape_ok hp)).1.2.2.1
  have hc : h.cK ≠ 0 := by
    intro e
    rw [e] at h3
    simp at h3
    omega
  show 1 ≤ h.kT + h.cK
  omega

/-- A return of the seated hearing, taken apart. -/
theorem via_parts {p : P} {h : Shape} {F G : Fork} {rs : List Fmt.RoundView} {H : Heard}
    (hp : p.shape = some h) (hv : hearVia p F rs = some (H, G)) :
    1 < h.NC ∧ ∃ g, hearV (faceOf h) F rs = some (g, G) ∧ toHeard h (toHeardG g) = some H := by
  unfold hearVia at hv
  rw [hp] at hv
  simp only at hv
  split at hv
  · rename_i hN
    obtain ⟨x, hx, hm⟩ := Option.bind_eq_some_iff.1 hv
    obtain ⟨g', hg', e⟩ := Option.map_eq_some_iff.1 hm
    obtain ⟨gv, G'⟩ := x
    obtain rfl : G' = G := congrArg (·.2) e
    obtain rfl : g' = H := congrArg (·.1) e
    exact ⟨hN, gv, hx, hg'⟩
  · exact nomatch hv

/-- **What the condition unfolds to.** F and rs are bound by "∃" and held by what functions return
at them alone: some values: not said to be the step's own. -/
theorem HeardBy.parts {T : LFace → List Fmt.Drawn → Bool} {p : P} {H : Heard}
    (J : HeardBy T p H) :
    ∃ (h : Shape) (F G : Fork) (rs : List Fmt.RoundView) (g : HeardV), p.shape = some h ∧ 1 ≤ h.d ∧
      F.next = p.first ∧ hearV (faceOf h) F rs = some (g, G) ∧
      toHeard h (toHeardG g) = some H ∧ canDraw (faceOf h) (rs.map (·.drawn)) = true ∧
      T (faceOf h) (rs.map (·.drawn)) = true := by
  obtain ⟨h, F, G, rs, hp, hn, hv, hc, hg⟩ := J
  obtain ⟨hN, g, h1, h2⟩ := via_parts hp hv
  exact ⟨h, F, G, rs, g, hp, level_of_shape hp hN, hn, h1, h2, hc, hg⟩

/-! ## Where the state holds it -/

/-- What the lookup on the digits has heard can be read off the first of the three values of
`K9L.numOf`, at any u. -/
theorem digits_reading (u : HTailF2) (s : FS) :
    (VerifiableInference.Desc.K9L.numOf u s).1.bind (·.heard) = s.tl?.bind (·.heard) := by
  show (s.tl?.map (VerifiableInference.Desc.First.TailClaims.Law.blank u)).bind (·.heard) = _
  cases s.tl? <;> rfl

/-! ## From what it follows -/

/-- **The condition, from a return of the seated hearing on samples that pass both tests.** -/
theorem clauseBy_of {T : LFace → List Fmt.Drawn → Bool} {p : P} {h : Shape}
    (hp : p.shape = some h) {F G : Fork} {rs : List Fmt.RoundView} {H : Heard} (hn : F.next = p.first)
    (hv : hearVia p F rs = some (H, G)) (hc : canDraw (faceOf h) (rs.map (·.drawn)) = true)
    (hg : T (faceOf h) (rs.map (·.drawn)) = true) {o : Option Heard} (ho : o = some H) :
    ClauseBy T p o :=
  ⟨H, ho, h, F, G, rs, hp, hn, hv, hc, hg⟩

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.calls_reads
#print axioms ProofFile.Honest.K3.Good.Live.digits_reads
#print axioms ProofFile.Honest.K3.Good.Live.shape_ok
#print axioms ProofFile.Honest.K3.Good.Live.level_of_shape
#print axioms ProofFile.Honest.K3.Good.Live.via_parts
#print axioms ProofFile.Honest.K3.Good.Live.clause_none
#print axioms ProofFile.Honest.K3.Good.Live.HeardBy.mono
#print axioms ProofFile.Honest.K3.Good.Live.ClauseBy.mono
#print axioms ProofFile.Honest.K3.Good.Live.ClauseBoth.left
#print axioms ProofFile.Honest.K3.Good.Live.ClauseBoth.right
#print axioms ProofFile.Honest.K3.Good.Live.HeardBy.parts
#print axioms ProofFile.Honest.K3.Good.Live.digits_reading
#print axioms ProofFile.Honest.K3.Good.Live.clauseBy_of
