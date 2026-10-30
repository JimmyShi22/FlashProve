-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Statement.lean: THE LOOKUP'S LAW AT A KEY FILE, STATED: what the kind
"lookup" (Johnson/Desc/First/Look/K3LookupGeneral.lean) hears and leaves at a key file's face is what the
typed lookup with parts (Cb/Pv/KeyLookup/) puts out on the same rounds, read. Definitions, and the
statements as predicates on a hearing. Their proofs of the kind's own hearing, and the trials
against silly hearings, are in the files beside this one.

Why an equation. The typed lookup's verifier refuses nothing: "the kind says yes, so the typed
verifier says yes" is free and says nothing. What the typed block's soundness lemma speaks of is its
OUT: a claim on each part's keys, and rows. So the law must say that the claims and rows which the
kind leaves ARE that out.

How a form is read. The kind leaves forms over hidden values (Model.Aff); the hidden value under
slot j is vp j - mf j * (mask entry of slot j) (OnBytes/Model/Hide.lean). home says which mask entry
of which oracle message slot j has. mfOf, valOf: a form as a linear form in mask entries and a
public value: the form's hidden value is valOf - <mfOf, mask entries>. They are meant as the
readings in the field of what maskSide (Johnson/Desc/First/Look/K3Key.lean) computes; that they are
is maskSide_reads (MaskSide.lean beside this file). rowA, rowP, rowsF, keyF: the claims as rows and
as claims on leaves, in the order and under the signs of groupRows and keyClaims of that file.

Main names:
  flatRV rs: a stretch's rounds, read in the field.
  hearE f es F rs: the kind's hearing with the entries as an argument; hearG_eq: hearG is hearE at
    the planner's entries.
  FaceIs A st f: the face has the typed lookup's numbers and orders, no shift, and its three public
    functions (factor, count, leaf), read, are the typed lookup's. It is a condition on public data
    (at the face of a key file's lookup: faceIs_lookupOf, FaceAt.lean beside this file).
  HomeIs f first o k home: the hidden values' mask entries are K3Key's homes of the two messages'
    next free entries o and k.
  shapeG f: the rounds of a lookup: name, scalars sent, elements drawn, how many never 0.
  Rounds hear: K03key_rounds. Law hear: K03key_law. TypedShape, PlanShape: two statements on public
    data that read no hearing.
  The trials against silly hearings are in Silly.lean beside this file.

Limits. Nothing on soundness here: the typed block's lemma is lamS_know
(Cb/Pv/KeyLookup/Lam1Short.lean). The ledger handed in must have its three arrays at their size
(Sized): the kind's text does not test that of two of them. That the entries are the planner's is
hearG's own text; that the planner's entries have the shape shapeG is PlanShape. The conditions
FaceIs, Adm and Sized in Rounds.shape are the proof's road; by a reading of the kind's text, not by
a theorem, the tape's shape hangs on none of them. Law.out's clause on "planes" is idle until
Law.total gives a ledger from which "planes" returns: the row is the whole structure.

-/
import Johnson.Desc.First.Look.K3Key
import Johnson.Desc.First.Look.KeyLaw.Readings
import Cb.Pv.KeyLookup.PlStd
import OnBytes.Tie.Pv.Psc.PscLater
import Cb.Pv.KeyLookup.LamRunFm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Fork Aff RoundName)
open Lk6 (Dat Pub Pl)
open Lk6.Mid (RowF rdRow rdCl ordFirst ordDown)

/-! ## The readings -/

/-- A stretch's rounds, read in the field: the elements sent, the elements drawn. -/
def flatRV (rs : List Fmt.RoundView) : List (Lk6.Flat.RV GE) :=
  rs.map fun r => (((First.Tape.elemsOf r.vals).getD []).map readE,
    r.drawn.elems.map fun x => readE (E.ofTriple x))

/-- A form's share in mask entries: slot j with the coefficient c gives c * mf j at slot j's mask
entry. -/
def mfOf (G : Fork) (home : ℕ → Slot) (a : Aff) : PscF.MaskForm :=
  a.slots.toList.map fun t => (home t.1, readE t.2 * readE (G.mf.getD t.1 zeroE))

/-- A form's public value: the constant, and c * vp j for slot j with the coefficient c. -/
def valOf (G : Fork) (a : Aff) : GE :=
  readE a.const + (a.slots.toList.map fun t => readE t.2 * readE (G.vp.getD t.1 zeroE)).sum

/-- A claim "form = 0" that reads hidden values alone, as the row "- masks = - value". -/
def rowA (G : Fork) (home : ℕ → Slot) (a : Aff) : RowF :=
  ⟨PscF.scaleForm (-1) (mfOf G home a), [], - valOf G a⟩

/-- Pairs, read. -/
def pairsF (l : List (E × E)) : List (GE × GE) := l.map fun p => (readE p.1, readE p.2)

/-- A claim that reads the planes, as a row. turned: "scalar * <v, bits> - masks = - value"; else "-
scalar * <v, bits> + masks = value". -/
def rowP (G : Fork) (home : ℕ → Slot) (turned : Bool) (c : PlaneClaim) : RowF :=
  if turned then
    ⟨PscF.scaleForm (-1) (mfOf G home c.lead), [(readE c.scalar, pairsF c.pairs)],
      - valOf G c.lead⟩
  else ⟨mfOf G home c.lead, [(- readE c.scalar, pairsF c.pairs)], valOf G c.lead⟩

/-- The rows in the order of groupRows (K3Key.lean): the claims that read hidden values alone but
for the last; the leaves' row; the last; the bits' value; the counts'. -/
def rowsF (G : Fork) (home : ℕ → Slot) (objects : List Aff) (planes : List PlaneClaim) :
    List RowF :=
  match planes, objects.getLast? with
  | [leaves, value, counts], some bits =>
    objects.dropLast.map (rowA G home) ++
      [rowP G home true leaves, rowA G home bits, rowP G home false value,
        rowP G home true counts]
  | _, _ => []

/-- What a part's key tree leaves, as a claim on the leaves alpha - key: the point by variable. -/
def keyF (G : Fork) (home : ℕ → Slot) (k : Array E × Aff) : PscF.PointClaim :=
  ⟨k.1.toList.reverse.map readE, mfOf G home k.2, valOf G k.2⟩

/-- **What the kind leaves, read as an out of the typed lookup.** G: the ledger behind "planes". -/
def outOf (A : Dat GE) (sl : Slot → A.J) (st : A.St) (G : Fork) (home : ℕ → Slot) (g : HeardG)
    (planes : List PlaneClaim) : A.Out :=
  (st, fun i : Fin A.m => rdCl A sl (readE g.alpha) (A.v i) (keyF G home (g.keys.getD i (#[], {}))),
    (rowsF G home g.rows.toList planes).map (rdRow A sl))

/-- All forms that the readings above read. -/
def formsOf (g : HeardG) (planes : List PlaneClaim) : List Aff :=
  g.rows.toList ++ planes.map (·.lead) ++ g.keys.map (·.2)

/-! ## The hearing, with the entries as an argument -/

/-- The kind's hearing at a face, on a stretch with its entries. -/
def hearE (f : Face) (es : List Fmt.Entry) (F : Fork) (rs : List Fmt.RoundView) :
    Option (HeardG × Fork) :=
  if f.ok then First.Tape.flRun {} (messagesG f) es F rs else none

/-- The kind's hearing is that, at the planner's entries. -/
theorem hearG_eq (p : PG) (F : Fork) (rs : List Fmt.RoundView) :
    hearG p F rs = p.entries.bind fun es => hearE p.face es F rs := by
  unfold hearG hearE
  cases p.face.ok <;> cases p.entries <;> rfl

/-! ## The conditions on public data -/

/-- **The face is the typed lookup's.** -/
structure FaceIs (A : Dat GE) (st : A.St) (f : Face) : Prop where
  noShift : f.shifted = false
  mu : f.mu = A.mu
  planes : f.planes = A.pl
  parts : f.parts = A.parts
  d : f.d = A.d
  /-- a part's last key level binds the named variables first; every other level goes from the
  highest variable down -/
  orders : ∀ i m, f.orders i m = if m + 1 = A.v i then ordFirst A.order m else ordDown m
  /-- the public factor, computed from the face's padding -/
  factor : ∀ al, readE (f.factor zeroE al) = A.fac st (readE al)
  /-- the number of keys that are no padding, computed from the face's padding -/
  count : f.count = A.allKeys - A.padCount
  /-- the factor of a bit in a leaf: alpha - 1 - the extension of the typed lookup's table at the
  row's coordinates of the point -/
  leaf : ∀ al (z : Array E), readE (f.leaf zeroE al z) = readE al - 1 -
    Alg.mle (fun r : Fin A.d → Bool => A.tab st (Cb.LdLkp.numLE r))
      fun t : Fin A.d => ((z.toList.reverse.map readE).drop A.mu).getD t.val 0

/-- The hidden values' mask entries: slot first + j has entry j of K3Key's table of homes, made of
the next free entries o 0, o 1, .. of the first message and k 0, k 1, .. of the second. -/
def HomeIs (f : Face) (first : ℕ) (o k home : ℕ → Slot) : Prop :=
  ∀ j < f.slots, home (first + j) =
    (homes f ((List.range f.slots).map o) ((List.range f.slots).map k)).getD j default

/-- The places of the typed lookup's masks: the standard ones at these entries. -/
def placesAt (A : Dat GE) (sl : Slot → A.J) (o k : ℕ → Slot) : Pl A :=
  Pl.std A (fun n => sl (o n)) fun n => sl (k n)

/-- The ledger is ready for the lookup: the count stands at first; the arrays have their size; the
lookup's slots are there and free. -/
structure Ready (f : Face) (first : ℕ) (F : Fork) : Prop where
  next : F.next = first
  sized : PscRun.Sized F
  room : first + f.slots ≤ F.ns
  free : ∀ j < f.slots, F.gotF.getD (first + j) true = false

/-! ## The rounds' shape -/

/-- A round's shape: name, scalars sent, elements drawn, how many of these are never 0. -/
abbrev Shape : Type := String × ℕ × ℕ × ℕ

/-- A masked sumcheck: the scalars that each variable's round sends; for the further variable Y its
scalars and the number of end values, if there is one. -/
def pscShape (sent : List ℕ) (y : Option (ℕ × ℕ)) : List Shape :=
  (RoundName.pscEpsilon.name, 1, 1, 0) :: sent.map (fun g => (RoundName.pscRound.name, g, 1, 0)) ++
    match y with
    | none => []
    | some (dY, n) => [(RoundName.pscY.name, dY, 1, 1), (RoundName.pscValues.name, n, 0, 0)]

/-- The levels of a product tree with more, more + 1, .. variables. -/
def treeShape (more levels : ℕ) : List Shape :=
  (List.range levels).flatMap fun l =>
    pscShape (List.replicate (more + l) 2) (some (2, 2)) ++ [(RoundName.line.name, 0, 1, 0)]

/-- **The rounds of a lookup without a shift.** -/
def shapeG (f : Face) : List Shape :=
  [(RoundName.lkp.name, 0, 1, 0)] ++ pscShape [] (some (3, 3)) ++
    ((List.range (f.planes - 2)).flatMap fun _ => pscShape [] (some (3, 2))) ++
    ((List.range (f.parts.length - 1)).flatMap fun _ => pscShape [] (some (2, 2))) ++
    [(RoundName.lkpPlanes.name, 0, f.mu, 0)] ++
    (f.parts.flatMap fun v => treeShape 0 v) ++ treeShape f.mu f.d ++
    pscShape (List.replicate f.d 2 ++ List.replicate f.mu 1) none ++
    [(RoundName.zero.name, 0, f.mu + f.d, 0)] ++
    pscShape (List.replicate (f.mu + f.d) 2) (some (2, 1))

/-- The shape of a round on a tape. -/
def shapeOf (r : FlatRound) : Shape := (r.name.getD "", r.sent.length, r.drawn.length, r.nz)

/-- The typed format of a shape. -/
def fmOf (x : Shape) : Lk6.Flat.Fm := ⟨x.2.1, x.2.2.1, x.2.2.2 != 0⟩

/-! ## The two statements, as predicates on a hearing -/

/-- The type of a hearing. -/
abbrev Hearing : Type := Face → List Fmt.Entry → Fork → List Fmt.RoundView → Option (HeardG × Fork)

/-- The entry of a shape: 24 bytes a scalar; one round; no root, sample answer, position, matrix
entry or batched row; no work. -/
def entryOf (x : Shape) : Fmt.Entry :=
  { name := x.1, msg := 24 * x.2.1, drawE := x.2.2.1, drawNZ := x.2.2.2 }

/-- An entry without its bits of work and its logarithm of positions. -/
def bare (e : Fmt.Entry) : Fmt.Entry := { e with work := 0, logN := 0 }

/-- The shape's formats are the typed lookup's, round by round. -/
def TypedShape : Prop :=
  ∀ (A : Dat GE) (st : A.St) (P : Pl A) (f : Face), FaceIs A st f → A.toPub.Adm Cb.Gl.p →
    (A.runD P).fm = (shapeG f).map fmOf

/-- The planner's entries at a face's size are the entries of the lookup's shape, in every word but
the bits of work and the logarithm of positions. -/
def PlanShape : Prop :=
  ∀ (set : Params.Setting) (scope : Params.Scope) (f : Face) (es : List Fmt.Entry),
    f.shifted = false → f.ok = true → entriesG set scope f = some es →
    es.map bare = (shapeG f).map entryOf

/-- **K03key_rounds.** (1) What is heard, at a face that is an admissible typed lookup's and from a
ledger whose arrays have their size, is a stretch that the strict reading takes at its entries, and
its rounds have the lookup's shape. (2) Every such stretch is heard, from a ledger that is ready, at
a face without a shift that passes its tests. (3) A stretch that is heard and whose words are below
the prime, read in the field, fits the typed lookup's formats: so a typed transcript spells it. -/
structure Rounds (hear : Hearing) : Prop where
  shape : ∀ (A : Dat GE) (st : A.St) (f : Face) es F rs g G, FaceIs A st f →
    A.toPub.Adm Cb.Gl.p → PscRun.Sized F → hear f es F rs = some (g, G) →
    ∃ t, First.Tape.tapeT {} rs es = some t ∧ t.map shapeOf = shapeG f
  hears : ∀ f es F rs t first, f.shifted = false → f.ok = true → Ready f first F →
    First.Tape.tapeT {} rs es = some t → t.map shapeOf = shapeG f → (hear f es F rs).isSome = true
  fits : ∀ (A : Dat GE) (st : A.St) (P : Pl A) (f : Face) es F rs g G,
    FaceIs A st f → A.toPub.Adm Cb.Gl.p → PscRun.Sized F → viewWordsBelowPrime ⟨rs, []⟩ = true →
    hear f es F rs = some (g, G) → Lk6.Flat.fitsAll (A.runD P).fm (flatRV rs) = true

/-- **K03key_law.** At every typed lookup A that is admissible, every face that is A's, every table
of homes that is K3Key's, every stretch whose words are below the prime, from a ledger whose count
stands at first and whose arrays have their size: (1) [total] if the strict reading takes the
stretch and it has the lookup's shape, the hearing hears it from a ledger that is ready, and the run
"planes" behind it closes the leaves' sumcheck; (2) [out] whatever the hearing leaves: its shift is
0; its alpha, read, is the first round's one draw; the ledger that it leaves is later than the one
handed in, has its sizes, and has taken just the lookup's slots; and for the run "planes" from EVERY
later ledger H: the ledger H' that it leaves is later; no form that the hearing or "planes" leaves
names an entry of a virtual row (the readings mfOf and valOf do not look at such entries: so they
lose nothing); and AT EVERY LEDGER K LATER THAN H', WHAT THE HEARING AND "planes" LEAVE, READ AT K,
IS WHAT THE TYPED LOOKUP'S VERIFIER PUTS OUT ON THE STRETCH, READ: the state; for each part the
claim on its keys; the rows, in order. (A.lamRun is the typed verifier's out as a function of the
flat view: Lk6.lamS_out; by Rounds.fits a typed transcript spells the stretch: Lk6.lamS_spells.) -/
structure Law (hear : Hearing) : Prop where
  total : ∀ f es F rs t first, f.shifted = false → f.ok = true → Ready f first F →
    First.Tape.tapeT {} rs es = some t → t.map shapeOf = shapeG f →
    ∃ g G pl G', hear f es F rs = some (g, G) ∧ planesG f g G [] = some (pl, G', [])
  out : ∀ (A : Dat GE) (sl : Slot → A.J) (st : A.St) (f : Face) (first : ℕ) (o k home : ℕ → Slot)
    es F rs g G,
    FaceIs A st f → A.toPub.Adm Cb.Gl.p → HomeIs f first o k home → viewWordsBelowPrime ⟨rs, []⟩ = true →
    F.next = first → PscRun.Sized F → hear f es F rs = some (g, G) →
    g.theta = zeroE ∧ (flatRV rs).head? = some ([], [readE g.alpha]) ∧
    PscRun.Later F G ∧ PscRun.Sized G ∧ G.next = first + f.slots ∧
    ∀ (H H' : Fork) (pl : List PlaneClaim) (u : Tape), PscRun.Later G H →
      planesG f g H [] = some (pl, H', u) →
      PscRun.Later H H' ∧ (∀ a ∈ formsOf g pl, a.ents.isEmpty = true) ∧
      ∀ K, PscRun.Later H' K →
        A.lamRun (placesAt A sl o k) st (flatRV rs) = outOf A sl st K home g pl

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.hearG_eq
