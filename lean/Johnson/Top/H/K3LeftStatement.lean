-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3LeftStatement.lean: the kind "lookup" (K3): STATEMENTS, NOT PROVED HERE: (I) ONE
RECORD OF WHAT STANDS BEHIND A YES OF THE KIND's decide, for every kind that goes on from it;
(II) that what the relation behind the block says can ride to later records; (III) who pays the row
out's three items, each under its own premises alone. Definitions of type Prop.

(I) `K3Left ρ h lm F F' g rs`: F: the ledger in front; F', g: the ledger and the heard record that
the yes leaves; rs: the rounds, read in K. ELEVEN FIELDS. heardIs, padLeft: the library's two
records (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean). shape: what was heard has the place's own shape
(neither of the two says it). zx, zy, zkSize, zkRaw, zkLen: the sizes of the two points; one key
point a call; call c's key point is the last iota_c coordinates of zy, then ALL OF zx, AS ARRAYS OF
MACHINE WORDS; its size is the call's n. eRaw: the calls' weights are the library's callWeight at
zy, as machine words. cEndEnts, cEndFilled: the form that is left for the join names no entry of a
virtual row, and every slot that it names is filled in F' and lies below the number of slots.
  `K3DecideLeaves`: a decide's yes leaves the record, at the rounds that it was shown.
  `K3LeavesAtCalls`: K3.block's decide at the seat of the lookup on a link's calls is such; so is
    every decide that says yes only where that one does (the block that sits at the seat).
  `K3LeftAt`: THE SHARP PROMISE, for the piece DIRECTLY behind the lookup: the record, with the
    ledger of the record in hand BEING F': so what PadLeft says of the free slots above F'.next
    can be spent.
  `K3LeftOn`: THE PROMISE, IN A FORM THAT STANDS AT EVERY LATER RECORD (it keeps less: a later
    ledger may have filled what was free): there are F, F', g, rs with
    the record; Q holds of F (a letter: whatever the kinds behind want kept of the ledger in
    front); F's next free slot is the place's first; what was heard STAYS g; the ledger is LATER
    than F' and has its sizes.

(II) `HeardIsLater`: HeardIs passes to later ledgers. `K3OutBack`, `K3OutRiderBack`: SO THE ROW OUT
AT A LATER LEDGER GIVES THE ROW OUT AT AN EARLIER ONE (its items are asked at all rounds for which
the heard record stands AT THE LEDGER NAMED: at a later ledger that is asked of more rounds).
`K3StandsLater`. So the relation behind the block need not be worded anew to ride: read at a later
record it speaks of that record's ledger and says MORE; whoever pays it pays it at the last ledger
in front of the runs of claims.

(III) `K3RowsPaid`, `K3PlanesPaid`, `K3KeysPaid`: one run of claims said yes at a record later than
F0 at which g still stands; each of ITS claims is worth 0 at the one world (a ledger H later than
what the run leaves; the mask row ν ∘ .mask; the entries "entry"); then that item of the row out
holds at g, F0. Of the calling kind: NOTHING for the rows; for the planes three clauses on its
forms for the columns; for the keys one equation a call: EACH AT THAT ONE WORLD AND THAT ONE ν, AND
AT THE HEARD RECORD's OWN POINTS: no round is named in a premise.
  `K3KeysHanded`: for a calling kind that hands in no key forms and calls no run "join": the keys'
    item from ONE EQUATION ON THE WORTH OF THE FORM g.cEnd, which is that kind's own law's to give:
    the library's join (joinK, OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean: the sum over the calls of
    e_c (alpha - c theta - kf c), plus the padding trees' term, less the end form) at the heard
    record's own theta, alpha, zy, at kf c := the extension of call c's key vector at its own
    point, and at the WORTH of g.cEnd in the place of the end form, is 0. No form is asked.
  `laterFo_of_psc` (a theorem, one line): the sumchecks' "later" gives the lookup's.
  `K3PaidAtSeat`: the three at K3's own runs, at every seat whose functions fit.

Limits. NOTHING IS PROVED HERE but the one line named. Ties: no error term. In zkRaw "iota_c ≤ rK"
is a fact on the public shape alone. The relation behind the block holds no "it stands for some
rounds": that it is not empty is the promise's word: the two belong together. That the claims ARE
worth 0 is the link's one equation's; the three clauses on the planes are the law of the reads';
the keys' equations are each calling kind's own, with its own error.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutParts
import Johnson.Top.H.K3RowOutRider
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-! ### (I) what stands behind a yes -/

/-- **WHAT STANDS BEHIND A YES OF THE LOOKUP's decide.** -/
structure K3Left {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (h : Forest.Shape) (lm : ℕ)
    (F F' : Fork) (g : Forest.Heard) (rs : Rounds K) : Prop where
  /-- the heard record, with the ledger left, holds the end values of these rounds -/
  heardIs : HeardIs ρ g F' (endsOf h lm F.next rs)
  /-- what the run leaves in the ledger -/
  padLeft : PadLeft h F F' g
  /-- what was heard has the place's own shape -/
  shape : g.shape = h
  zx : g.zx.size = h.dT
  zy : g.zy.size = h.rK
  zkSize : g.zk.size = h.NC
  /-- call c's key point, as machine words -/
  zkRaw : ∀ c, c < h.NC → h.iota.getD c 0 ≤ h.rK ∧
    g.zk.getD c #[] = g.zy.extract (h.rK - h.iota.getD c 0) g.zy.size ++ g.zx
  zkLen : ∀ c, c < h.NC → (g.zk.getD c #[]).size = ((h.calls[c]?).map (·.n)).getD 0
  /-- the calls' weights, as machine words -/
  eRaw : g.e = (Array.range h.NC).map (Forest.callWeight h g.zy)
  /-- the form left for the join names no entry of a virtual row -/
  cEndEnts : g.cEnd.ents = #[]
  /-- every slot that it names is filled in the ledger left and lies below the number of slots -/
  cEndFilled : FilledA F' g.cEnd

/-- **A decide's yes leaves the record**, at the rounds that it was shown. NOT PROVED HERE. -/
def K3DecideLeaves {S : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (h : Forest.Shape)
    (decide : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S) : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (lm : ℕ) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64))),
    okRoundsE rs = true → decide s rs cols = .ok s' →
    ∃ F F' g, fork s = some F ∧ fork s' = some F' ∧ heard s' = some g ∧
      (OnBytes.PscRun.Sized F → K3Left ρ h lm F F' g (rs.map (rdRV ρ)))

/-- **K3.block's decide at the calls' seat is such.** NOT PROVED HERE. -/
def K3LeavesAtCalls : Prop :=
  ∀ (Cl : Type) (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (h : Forest.Shape), p.shape = some h →
    K3DecideLeaves (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard h
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide

/-- **THE SHARP PROMISE, for the piece directly behind the lookup**: the ledger in hand IS F'. -/
def K3LeftAt {S : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (h : Forest.Shape) (lm first : ℕ) (Q : Fork → Prop) (s : S) : Prop :=
  ∃ (F F' : Fork) (g : Forest.Heard) (rs : Rounds Cb.Gl.E), Q F ∧ F.next = first ∧
    K3Left Reading.gl h lm F F' g rs ∧ heard s = some g ∧ fork s = some F'

/-- **THE PROMISE, in a form that stands at every later record.** -/
def K3LeftOn {S : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (h : Forest.Shape) (lm first : ℕ) (Q : Fork → Prop) (s : S) : Prop :=
  ∃ (F F' G : Fork) (g : Forest.Heard) (rs : Rounds Cb.Gl.E), Q F ∧ F.next = first ∧
    K3Left Reading.gl h lm F F' g rs ∧ heard s = some g ∧ fork s = some G ∧
    _root_.Fo.Later F' G ∧ OnBytes.PscRun.Sized G

/-- The sharp promise gives the other. NOT PROVED HERE. -/
def K3LeftOnOfAt : Prop :=
  ∀ (S : Type) (fork : S → Option Fork) (heard : S → Option Forest.Heard) (h : Forest.Shape)
    (lm first : ℕ) (Q : Fork → Prop) (s : S), K3LeftAt fork heard h lm first Q s →
    K3LeftOn fork heard h lm first Q s

/-! ### (II) the crossing -/

/-- The sumchecks' "later" gives the lookup's: three of its four fields. -/
theorem laterFo_of_psc {F G : Fork} (h : OnBytes.PscRun.Later F G) : _root_.Fo.Later F G :=
  ⟨h.next, h.ns, h.keep⟩

/-- HeardIs passes to later ledgers. NOT PROVED HERE. -/
def HeardIsLater : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (g : Forest.Heard) (F G : Fork)
    (En : Ends K), _root_.Fo.Later F G → HeardIs ρ g F En → HeardIs ρ g G En

/-- **The row out at a later ledger gives the row out at an earlier one.** NOT PROVED HERE. -/
def K3OutBack : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (h : FoNums.Sh) (lm first : ℕ)
    (ν : _root_.Fo.Pl → K) (Kv : ℕ → ℕ → K) (g : Forest.Heard) (F G : Fork),
    _root_.Fo.Later F G → K3Out h lm first ν Kv ρ g G → K3Out h lm first ν Kv ρ g F

/-- And so does its fourth item. NOT PROVED HERE. -/
def K3OutRiderBack : Prop :=
  ∀ (r : LookupCRCaller) (lm first : ℕ) (st : r.c.St₀) (m : r.c.Sg.Msg) (g : Forest.Heard)
    (F G : Fork), _root_.Fo.Later F G → K3OutRider r lm first st m g G →
    K3OutRider r lm first st m g F

/-- What stands for some rounds at a ledger stands for them at a later one. NOT PROVED HERE. -/
def K3StandsLater : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (h : FoNums.Sh) (lm first : ℕ)
    (g : Forest.Heard) (F G : Fork), _root_.Fo.Later F G → K3Stands h lm first ρ g F →
    K3Stands h lm first ρ g G

/-! ### (III) who pays the row out -/

section
variable {S Cl : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
  (form : Cl → Aff) (lm : ℕ)

/-- **The rows.** Nothing is asked of the calling kind. NOT PROVED HERE. -/
def K3RowsPaid (objects : ℕ → S → Except String (List Cl × S)) : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (g : Forest.Heard) (F0 : Fork)
    (first : ℕ) (sO : S) (clO : List Cl) (GO H : Fork) (ν : _root_.Fo.Pl → K)
    (entry : ℕ → ℕ → ℕ → K), FoNums.ok g.shape = true →
    K3RanAt fork heard g F0 objects sO clO GO → _root_.Fo.Later GO H →
    (∀ c ∈ clO, (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0) →
    K3OutRows g.shape lm first ν ρ g F0

/-- **The planes**, under three clauses on the calling kind's forms for the columns, at the one
world and at the heard record's own two points. NOT PROVED HERE. -/
def K3PlanesPaid (planes : ℕ → S → Except String (List Cl × S)) (bit : S → ℕ → ℕ → Aff)
    (pin : S → ℕ → Aff) : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (g : Forest.Heard) (F0 : Fork)
    (first : ℕ) (sP : S) (clP : List Cl) (GP H : Fork) (ν : _root_.Fo.Pl → K)
    (entry : ℕ → ℕ → ℕ → K), FoNums.ok g.shape = true →
    K3RanAt fork heard g F0 planes sP clP GP → _root_.Fo.Later GP H →
    (∀ c ∈ clP, (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0) →
    (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
      (bit sP 0 col).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        colsK g.shape lm (rdA ρ g.zb0) ν col) →
    (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
      (bit sP 1 col).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        colsK g.shape lm (rdA ρ g.zb1) ν col) →
    (∀ col, col < g.shape.NC * 2 ^ (g.shape.kT + 5 - lm) →
      (pin sP col).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = pinColK lm ν col) →
    K3OutPlanes g.shape lm first ν ρ g F0

/-- **The keys**, under one equation a call on the calling kind's key forms, at the one world and at
the heard record's own key points. NOT PROVED HERE. -/
def K3KeysPaid (join : ℕ → S → Except String (List Cl × S)) (keys : S → Array Aff) : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (g : Forest.Heard) (F0 : Fork)
    (first : ℕ) (sJ : S) (clJ : List Cl) (GJ H : Fork) (ν : _root_.Fo.Pl → K)
    (entry : ℕ → ℕ → ℕ → K) (Kv : ℕ → ℕ → K), FoNums.ok g.shape = true →
    K3RanAt fork heard g F0 join sJ clJ GJ → _root_.Fo.Later GJ H →
    (∀ c ∈ clJ, (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0) →
    (∀ c, c < g.shape.NC →
      ((keys sJ).getD c (Aff.ofConst zeroE)).value ρ
          (H.worldOf ρ (fun j => ν (.mask j)) entry) =
        extL (Kv c) (rdA ρ (g.zk.getD c #[]))) →
    K3OutKeys g.shape lm first ν Kv ρ g F0

end

/-- **The keys, handed in**: for a calling kind that hands in no key forms and calls no "join": at a
ledger H later than F0 the library's join, at the heard record's own theta, alpha and zy, at the key
vectors' extensions at the heard record's own key points, and at the WORTH of the form left for the
join, is 0. NOT PROVED HERE. -/
def K3KeysHanded : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (lm : ℕ) (g : Forest.Heard)
    (F0 H : Fork) (first : ℕ) (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K) (Kv : ℕ → ℕ → K),
    FoNums.ok g.shape = true → _root_.Fo.Later F0 H →
    AffK.val (joinK g.shape (ρ.val g.theta) (ρ.val g.alpha) (eK g.shape (rdA ρ g.zy))
      (rdA ρ g.zy) (fun c => AffK.ofConst (extL (Kv c) (rdA ρ (g.zk.getD c #[]))))
      (AffK.ofConst (g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)))) ν = 0 →
    K3OutKeys g.shape lm first ν Kv ρ g F0

/-- **The three at K3's own runs**, at every seat whose functions fit. NOT PROVED HERE. -/
def K3PaidAtSeat : Prop :=
  ∀ (S Cl : Type) (seat : Desc.K3.Seat S Cl) (form : Cl → Aff), SeatFits seat form →
    ∀ (lm : ℕ) (readers : Desc.K3.Readers S) (keys : S → Option (Array Aff)),
      K3RowsPaid seat.fork seat.heard form lm (objectsRun seat) ∧
        K3PlanesPaid seat.fork seat.heard form lm (Desc.K3.planesRun seat lm readers)
          (bitOf readers) (pinOf readers) ∧
        K3KeysPaid seat.fork seat.heard form lm (Desc.K3.joinRun seat keys) (keysOf keys)

end VerifiableInference.OnPublicFiles
