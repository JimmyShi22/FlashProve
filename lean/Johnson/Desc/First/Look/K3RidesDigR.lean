-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ridesAtR_of_on, ridesAtR_of_sorted: no meaning is shown here that meets
their premises.
Johnson/Desc/First/Look/K3RidesDigR.lean: the kind "lookup" (K3) AT THE TABLE OF JOINTS: WHAT
RIDES PAST A SEATED LOOKUP ON THE DIGITS OF A LINK's APPROXIMATE RANGE PROOF, IN THE SECOND FORM
OF THE CHAIN OF PROMISES (RidesAtR, Johnson/Desc/First/Look/K3MeansDigR.lean), FROM THE TIGHT LIST
OF WHAT THE ROW SPENDS: by Lean's own evaluation on the table every item that rides there is plain
(pile, pinI, pinW, constr, row: K3Rides.lean) or is the open segment's own "wo" or one of its own
"forms". Definitions, statements and proofs; evaluations by Lean's kernel. Ties: no error term. NO
SOUNDNESS IS CLAIMED.

Why a second rule. rides_at_seat_rel (K3RidesR.lean) lets go of the promise in front. That a
sentence "forms" goes back wants a public test at the state in front, which the promise there
holds.

OBJECT: no text that runs: the table of joints' own functions at the driver's own list of places.
Used by K3RidesDig.lean, K3RidesDigStep.lean, K3RidesDigTight.lean (Johnson/Desc/Sound/MgAt/).
LETTERS: N, Mg, Rch, k, q, b', Rel, l.



  Compiled with the whole library.
Main names:
  `ridesAtR_of_on`: THE RULE WITH THE PROMISE IN HAND.
  `ownSort`, `ridersSorted`, `sorted_of_test`: a Bool on the table, and what its yes gives.
  `digitsSortedB`, `digitsSorted_full`, `sorted_at_digits`: the evaluation, and what it gives at a
    place.
  `digitsPlainB`, `digitsPlain_false`: a negative test: "every rider there is plain" is false.
  `ridesAtR_of_sorted`: THE END.

Limits. The evaluations stand at one list of segments.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3RidesR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Maker OnBytes.Flat KObj Fo.Peel
open _root_.Run.PQ (CK SgX)
open _root_.Run (ckP)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start openSets readsOpen
  flatPlacesOf)
open Johnson.Desc.First.Walk.Tied (Stays)

/-! ## 1 The rule with the promise in hand -/

section
variable {P Cl Cells Tok : Type} {Fr : Frame} (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "PS" => flatPlacesOf linksFull true

/-- **WHAT RIDES PAST A SEAT, SECOND FORM, WITH BOTH PROMISES AND "reached" IN HAND.** -/
theorem ridesAtR_of_on (k : ℕ)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) (hback : q.back = [])
    (Rel : Desc.First.S → Desc.First.S → Prop)
    (hRel : ∀ B', SeatOf b' B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      Rel a.1 b.1)
    (hBack : ∀ i, openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k i →
      ¬ insQ linksFull PS k i → ∀ (z : P) (a b : Desc.First.S × Fr.E.Str) w,
      onQ N Mg linksFull PS (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → onQ N Mg linksFull PS (fun s => (z, s)) (k + 1) b → Rel a.1 b.1 →
      Stays q.base (strsOf Fr a.2) (strsOf Fr b.2) →
      meansQ N Mg (fun s => (z, s)) i b w → meansQ N Mg (fun s => (z, s)) i a w) :
    RidesAtR N Mg Rch k q b' := by
  intro B' hS z a τ b w i ha hr hu hb hb' hR ho hn
  refine rides_of_side N Mg linksFull PS (fun s => (z, s)) k a b w i hR ho hn fun hm => ?_
  obtain ⟨-, e2, -, -⟩ := piece_below_plain (⟨below B', q.base, q.ds, q.back, fun _ _ w => w,
    q.err⟩ : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) B' rfl hback a b τ hb
  refine hBack i ho hn z a b w ha hr hu hb' (hRel B' hS a τ b hb) ?_ hm
  rw [e2]
  exact Johnson.Desc.First.Walk.Tied.stays_behind (ckP .two) Fr q.base q.ds a.2 τ

end

/-! ## 2 Who rides at the digits -/

/-- The open segment's own "wo", or one of its own "forms". -/
def ownSort (m : ℕ) : Item → Bool
  | .forms m' _ _ => m' == m
  | .wo m' => m' == m
  | _ => false

/-- Every rider at block k is plain or of these two sorts. -/
def ridersSorted (links : List ModelPart) (ps : List Place) (k m : ℕ) : Bool :=
  ((openSets links ps (start links))[k]?.getD []).all fun i =>
    (((ps[k]?.map (First.rowOf links)).getD {}).ins ++
      ((ps[k]?.map (First.rowOf links)).getD {}).ctx ++
      [Item.unmarked]).contains i || (plainSort i || ownSort m i)

/-- **What a yes gives**, where the table's two tests accept. -/
theorem sorted_of_test (links : List ModelPart) (ps : List Place) (k m : ℕ) (hk : k ≤ ps.length)
    (h1 : ridersSorted links ps k m = true) (h2 : readsOpen links ps (start links) = true)
    (h3 : rowsApart links ps = true) :
    ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → (plainSort i || ownSort m i) = true := by
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

/-- So at every place of the kind K3 at piece 7 or above. -/
def digitsSortedB (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    (ps[k]?).all fun a =>
      !decide (a.kind = .K3 ∧ 7 ≤ a.piece) || (a.link.any fun m => ridersSorted links ps k m)

set_option maxRecDepth 100000 in
theorem digitsSorted_full : digitsSortedB linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

/-- What the evaluation gives at a place. -/
theorem sorted_at_digits {k l : ℕ} {a : Place}
    (ha : (flatPlacesOf linksFull true)[k]? = some a) (hK : a.kind = .K3) (hp : 7 ≤ a.piece)
    (hl : a.link = some l) : ridersSorted linksFull (flatPlacesOf linksFull true) k l = true := by
  have hk : k < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 digitsSorted_full k (List.mem_range.2 hk)
  rw [ha] at h
  simpa [hK, hp, hl] using h

/-- A negative test: "every rider at a digits' place is plain" is false. -/
def digitsPlainB (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    (ps[k]?).all fun a => !decide (a.kind = .K3 ∧ 7 ≤ a.piece) || ridersPlain links ps k

set_option maxRecDepth 100000 in
theorem digitsPlain_false : digitsPlainB linksFull (flatPlacesOf linksFull true) = false := by
  decide +kernel

/-! ## 3 The end -/

section
variable {P Cl Cells Tok : Type} {Fr : Frame} (N : Numbers)
  (Mg : Meaning P (Desc.Wit Cells Tok MsgT))
  (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "PS" => flatPlacesOf linksFull true

/-- **WHAT RIDES PAST A LOOKUP ON THE DIGITS, SECOND FORM, FROM THE TIGHT LIST.** -/
theorem ridesAtR_of_sorted (k l : ℕ)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT))
    (b' : Desc.Block Desc.First.S Cl) {a : Place} (ha : PS[k]? = some a) (hK : a.kind = .K3)
    (hp : 7 ≤ a.piece) (hl : a.link = some l) (hback : q.back = [])
    (Rel : Desc.First.S → Desc.First.S → Prop)
    (hRel : ∀ B', SeatOf b' B' → ∀ a τ b,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      Rel a.1 b.1)
    (bPile : GoesBack (relOf Rel q.base) Mg.pile)
    (bPinI : GoesBack (relOf Rel q.base) (Mg.pin N.index.1 N.index.2))
    (bPinW : GoesBack (relOf Rel q.base) Mg.pinW)
    (bRow : ∀ m c, GoesBack (relOf Rel q.base) (Mg.row m c))
    (bConstr : ∀ m p,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k (.constr m p) →
      ¬ insQ linksFull PS k (.constr m p) → GoesBack (relOf Rel q.base) (Mg.constr m p))
    (bWo : openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k (.wo l) →
      ¬ insQ linksFull PS k (.wo l) → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str) w,
      onQ N Mg linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ N Mg linksFull PS (fun s => (z, s)) (k + 1) v → Rel u.1 v.1 →
      Stays q.base (strsOf Fr u.2) (strsOf Fr v.2) →
      Mg.wo l (z, v.1) (strsOf Fr v.2) w → Mg.wo l (z, u.1) (strsOf Fr u.2) w)
    (bForms : ∀ kk r,
      openAfter (insQ linksFull PS) (outsQ linksFull PS) (· ∈ start linksFull) k
        (.forms l kk r) →
      ¬ insQ linksFull PS k (.forms l kk r) → ∀ (z : P) (u v : Desc.First.S × Fr.E.Str) w,
      onQ N Mg linksFull PS (fun s => (z, s)) k u → Rch k ((z, u.1), u.2) →
      ¬ u.1.failed ≠ none → onQ N Mg linksFull PS (fun s => (z, s)) (k + 1) v → Rel u.1 v.1 →
      Stays q.base (strsOf Fr u.2) (strsOf Fr v.2) →
      Mg.forms l kk r (z, v.1) (strsOf Fr v.2) w → Mg.forms l kk r (z, u.1) (strsOf Fr u.2) w) :
    RidesAtR N Mg Rch k q b' := by
  refine ridesAtR_of_on N Mg Rch k q b' hback Rel hRel fun i ho hn z u v w hu hr hm hv hR hy => ?_
  have h := sorted_of_test linksFull PS k l (Nat.le_of_lt (List.getElem?_eq_some_iff.1 ha).1)
    (sorted_at_digits ha hK hp hl) readsOpen_full rowsApart_full i ho hn
  have plain : ∀ φ : P × Desc.First.S → Strs → Desc.Wit Cells Tok MsgT → Prop,
      GoesBack (relOf Rel q.base) φ →
      φ (z, v.1) (strsOf Fr v.2) w → φ (z, u.1) (strsOf Fr u.2) w :=
    fun φ hφ => hφ (z, u.1) (strsOf Fr u.2) (z, v.1) (strsOf Fr v.2) w ⟨rfl, hR, hy⟩
  cases i with
  | pile => exact plain _ bPile
  | pinI => exact plain _ bPinI
  | pinW => exact plain _ bPinW
  | row m c => exact plain _ (bRow m c)
  | constr m p => exact plain _ (bConstr m p ho hn)
  | wo m =>
    have e : m = l := by simpa [plainSort, ownSort] using h
    subst e
    exact bWo ho hn z u v w hu hr hm hv hR hy
  | forms m kk r =>
    have e : m = l := by simpa [plainSort, ownSort] using h
    subst e
    exact bForms kk r ho hn z u v w hu hr hm hv hR hy
  | _ => simp [plainSort, ownSort] at h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.ridesAtR_of_on
#print axioms VerifiableInference.OnPublicFiles.sorted_of_test
#print axioms VerifiableInference.OnPublicFiles.digitsSorted_full
#print axioms VerifiableInference.OnPublicFiles.sorted_at_digits
#print axioms VerifiableInference.OnPublicFiles.digitsPlain_false
#print axioms VerifiableInference.OnPublicFiles.ridesAtR_of_sorted
