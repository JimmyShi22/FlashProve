-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
rides_at_seat_plain, ridesAtR_of_plain: no meaning is shown here that has
the five facts.
Johnson/Desc/First/Look/K3RidesR.lean: the kind "lookup" (K3) AT THE TABLE OF JOINTS: WHAT RIDES
PAST A SEATED LOOKUP ON A LINK's CALLS, IN THE SECOND FORM OF THE CHAIN OF PROMISES (RidesAtR,
Johnson/Desc/First/Look/K3MeansDigR.lean), FROM THE TIGHT LIST OF WHAT THE ROW SPENDS: by Lean's
own evaluation on the table every item that rides there is of one of five sorts (pile, pinI, pinW,
constr, row): so five named facts on the meaning's fields are asked, and no more. Definitions,
statements and proofs; evaluations by Lean's kernel. Ties: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table of joints' own functions at the driver's own list of places.
Used by K3Rides.lean (Johnson/Desc/Sound/MgAt/) · K03RidesAt.lean (Johnson/P5J/) and others.
LETTERS: links, ps, k, q, N, Mg, Bst in the rule; at the end linksFull and flatPlacesOf linksFull
  true.


Compiled with the whole library.


Main names:
  `plain_of_test`: ridersPlain (K3Rides.lean) gives "every rider is plain", where the table's two
    tests accept.
  `relOf`, `rides_at_seat_rel`: what rides past a seat, over ANY relation Rel between the two states
    that an accepting of the seated piece gives (SameOut is too wide for the item pile: S.rows reads
    the sort of "here").
  `rides_at_seat_plain`: THE TIGHT RULE, in the first form, over Rel.
  `calls_seated_sameBut`: at the calls Rel := SameBut is given.
  `ridesAtR_of_plain`: THE SAME IN THE SECOND FORM, at the full list.
  `callsPlainB`, `callsPlain_full`, `readsOpen_full`, `rowsApart_full`: the evaluations at these
    very letters. `plain_at_calls`: what the first gives at a place.

Limits. The evaluations stand at one list of segments.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.RidesFields
import Johnson.Desc.First.Look.K3RidesCalls
import Johnson.Desc.First.Look.K3MeansDigR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Maker OnBytes.Flat KObj Fo.Peel
open _root_.Run.PQ (CK SgX)
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start openSets readsOpen rowOf SameOut
  ReadsOut flatPlacesOf)

/-- **What a yes of ridersPlain gives**, where the table's two tests accept. -/
theorem plain_of_test (links : List ModelPart) (ps : List Place) (k : ℕ) (hk : k ≤ ps.length)
    (h1 : ridersPlain links ps k = true) (h2 : readsOpen links ps (start links) = true)
    (h3 : rowsApart links ps = true) :
    ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → plainSort i = true := by
  intro i ho hn
  have hu : Item.unmarked ∈ start links := List.mem_append_left _ (List.mem_cons_self)
  have hL : i ∈ openL (insL links ps) (outsL links ps) (start links) k :=
    (openIsList Item (insL links ps) (outsL links ps) (start links) k i).1 ho
  have hO := (openL_iff_openSets links ps (start links) h2 h3 hu k hk i).1 hL
  have h4 := List.all_eq_true.1 h1 i hO
  rcases Eq.mp (Bool.or_eq_true _ _) h4 with h5 | h5
  · refine absurd ?_ hn
    show i ∈ (rowQ links ps k).ins ++ (rowQ links ps k).ctx ++ [.unmarked]
    exact List.contains_iff_mem.1 h5
  · exact h5

section
variable {Cl P W : Type} {C : CK} {Fr : Frame}

/-- What was handed to the chain is the same; the two states stand in Rel; the strings stay below
base. -/
def relOf (Rel : First.S → First.S → Prop) (base : ℕ) :
    P × First.S → Strs → P × First.S → Strs → Prop :=
  fun a y b y' => a.1 = b.1 ∧ Rel a.2 b.2 ∧ Johnson.Desc.First.Walk.Tied.Stays base y y'

/-- **WHAT RIDES PAST A SEAT, OVER ANY RELATION THAT AN ACCEPTING OF THE SEATED PIECE GIVES.** -/
theorem rides_at_seat_rel (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (P × First.S) Cl W) (N : Numbers) (Mg : Meaning P W)
    (Bst : Block First.S Cl) (hback : q.back = []) (Rel : First.S → First.S → Prop)
    (hRel : ∀ B', SeatOf Bst B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → Rel a.1 b.1)
    (hBack : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → GoesBack (relOf Rel q.base) (i.holds N Mg)) :
    ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w := by
  intro B' hS z a τ b w i _ _ hb _ hR ho hn
  refine rides_of_side N Mg links ps (fun s => (z, s)) k a b w i hR ho hn fun hm => ?_
  obtain ⟨-, e2, -, -⟩ := piece_below_plain (⟨below B', q.base, q.ds, q.back, fun _ _ w => w,
    q.err⟩ : Piece C Fr First.S Cl W) B' rfl hback a b τ hb
  refine hBack i ho hn (z, a.1) (strsOf Fr a.2) (z, b.1) (strsOf Fr b.2) w
    ⟨rfl, hRel B' hS a τ b hb, ?_⟩ hm
  rw [e2]
  exact Johnson.Desc.First.Walk.Tied.stays_behind C Fr q.base q.ds a.2 τ

/-- **THE TIGHT RULE: WHERE EVERY RIDER IS PLAIN, FIVE FACTS ON THE MEANING's FIELDS.** -/
theorem rides_at_seat_plain (links : List ModelPart) (ps : List Place) (k : ℕ)
    (q : Piece C Fr (P × First.S) Cl W) (N : Numbers) (Mg : Meaning P W)
    (Bst : Block First.S Cl) (hback : q.back = []) (Rel : First.S → First.S → Prop)
    (hRel : ∀ B', SeatOf Bst B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b → Rel a.1 b.1)
    (hPl : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → plainSort i = true)
    (bPile : GoesBack (relOf Rel q.base) Mg.pile)
    (bPinI : GoesBack (relOf Rel q.base) (Mg.pin N.index.1 N.index.2))
    (bPinW : GoesBack (relOf Rel q.base) Mg.pinW)
    (bRow : ∀ m c, GoesBack (relOf Rel q.base) (Mg.row m c))
    (bConstr : ∀ m p,
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k (.constr m p) →
      ¬ insQ links ps k (.constr m p) → GoesBack (relOf Rel q.base) (Mg.constr m p)) :
    ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece C Fr First.S Cl W).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w :=
  rides_at_seat_rel links ps k q N Mg Bst hback Rel hRel fun i ho hn => by
    have h := hPl i ho hn
    cases i with
    | pile => exact bPile
    | pinI => exact bPinI
    | pinW => exact bPinW
    | row m c => exact bRow m c
    | constr m p => exact bConstr m p ho hn
    | _ => simp [plainSort] at h

end

/-! ## The evaluations at the driver's own letters -/

/-- At every place of the kind K3 at piece 3 or below: every rider is plain. -/
def callsPlainB (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    (ps[k]?).all fun a => !decide (a.kind = .K3 ∧ a.piece ≤ 3) || ridersPlain links ps k

set_option maxRecDepth 100000 in
theorem callsPlain_full : callsPlainB linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem readsOpen_full :
    readsOpen linksFull (flatPlacesOf linksFull true) (start linksFull) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem rowsApart_full : rowsApart linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

/-- What the first evaluation gives at a place. -/
theorem plain_at_calls {k : ℕ} {a : Place} (ha : (flatPlacesOf linksFull true)[k]? = some a)
    (hK : a.kind = .K3) (hp : a.piece ≤ 3) :
    ridersPlain linksFull (flatPlacesOf linksFull true) k = true := by
  have hk : k < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 callsPlain_full k (List.mem_range.2 hk)
  rw [ha] at h
  simpa [hK, hp] using h

/-! ## An accepting of the seated piece is SameBut -/

section
variable {Cl P W : Type} {Fr : Frame}

/-- **At a link's lookup on the calls an accepting of the seated piece is SameBut.** -/
theorem calls_seated_sameBut (claim : OnBytes.Model.Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S)) (X : OnBytes.Model.Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (Bst : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some Bst) (hOk : Bst.planOk = true)
    (i : ℕ) (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    {x : Desc.First.Look.Place}
    (e : Desc.First.Look.placeAt X i false =
      some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x))
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl W) (hback : q.back = []) :
    ∀ B', SeatOf Bst B' → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl W).ior.red.out u τ = some v → SameBut u.1 v.1 := by
  intro B' hS u τ v hv
  obtain ⟨laid, sent, rs, cols, -, hd⟩ :=
    k3_calls_stated_yes claim readers codes shape a Bst B' h hOk hS.1
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl W) rfl hl hpc e hback u v τ hv
  exact k3_calls_sameBut claim a.piece laid sent _ [] u.1 v.1 rs cols hd

end

/-! ## The second form -/

section
variable {P Cl Cells Tok : Type} {Fr : Frame} (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

/-- **WHAT RIDES PAST A LOOKUP ON THE CALLS, SECOND FORM, FROM THE TIGHT LIST.** -/
theorem ridesAtR_of_plain (k : ℕ)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) {a : Place}
    (ha : (flatPlacesOf linksFull true)[k]? = some a) (hK : a.kind = .K3) (hp : a.piece ≤ 3)
    (hback : q.back = []) (Rel : Desc.First.S → Desc.First.S → Prop)
    (hRel : ∀ B', SeatOf b' B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      Rel a.1 b.1)
    (bPile : GoesBack (relOf Rel q.base) Mg.pile)
    (bPinI : GoesBack (relOf Rel q.base) (Mg.pin N.index.1 N.index.2))
    (bPinW : GoesBack (relOf Rel q.base) Mg.pinW)
    (bRow : ∀ m c, GoesBack (relOf Rel q.base) (Mg.row m c))
    (bConstr : ∀ m p,
      openAfter (insQ linksFull (flatPlacesOf linksFull true))
        (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) k (.constr m p) →
      ¬ insQ linksFull (flatPlacesOf linksFull true) k (.constr m p) →
      GoesBack (relOf Rel q.base) (Mg.constr m p)) :
    RidesAtR N Mg Rch k q b' :=
  fun B' hB z x τ y w i hx _ hu ho hy hr hop hn =>
    rides_at_seat_plain linksFull (flatPlacesOf linksFull true) k q N Mg b' hback Rel hRel
      (plain_of_test linksFull (flatPlacesOf linksFull true) k
        (Nat.le_of_lt (List.getElem?_eq_some_iff.1 ha).1) (plain_at_calls ha hK hp) readsOpen_full
        rowsApart_full)
      bPile bPinI bPinW bRow bConstr B' hB z x τ y w i hx hu ho hy hr hop hn

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.plain_of_test
#print axioms VerifiableInference.OnPublicFiles.rides_at_seat_rel
#print axioms VerifiableInference.OnPublicFiles.rides_at_seat_plain
#print axioms VerifiableInference.OnPublicFiles.calls_seated_sameBut
#print axioms VerifiableInference.OnPublicFiles.callsPlain_full
#print axioms VerifiableInference.OnPublicFiles.ridesAtR_of_plain
