-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3RunsLaw.lean: the kind "lookup" (K3): its three runs of claims are worth the members
of the library's list of claims: the law K3RunsAreWorth of Johnson/Top/H/K3LawKind.lean, proved of
the kind's own text: "objects" as it stands in K3.block (Johnson/Desc/First/Look/K3Lookup.lean),
`planesRun` and `joinRun` (Johnson/Desc/First/Look/K3Runs.lean). Theorems with their proofs.

What is said. Take a carried record s at which the lookup's "heard" g and the open ledger F stand,
and let g, with an earlier ledger F0, hold the record of end values (HeardIs). If a run of claims
says yes at s, then behind it the ledger G is a later one with the same next free slot, "heard"
still stands, and in every ledger later than G, for every reading of the places and all entries of
virtual rows, the claims' forms are worth: "objects": the residues of the record's rows; "planes":
claimLeaves, claimBits, countK at the values of the caller's forms; "join": claimJoin at the values
of the caller's key forms.

How the statement has turned against the listed one, and why. K3RunsAreWorth has the caller's forms
bit, pin, KF as fixed letters. The runs take them off the carried record (`readers s`, `keys s`): no
fixed letter fits a caller whose forms hang on s. So the law is proved with the forms read off s
(`K3RunIsWorthAt`, `bitOf`, `pinOf`, `keysOf`; `k3RunsAreWorthAt`), and the listed statement TO THE
LETTER is a corollary for a caller whose readers and keys give the fixed forms wherever they give
any (`k3RunsAreWorth`). KF.size = NC, which the listed statement lacks, is a CONCLUSION here
(`join_size`): "join" tests it.

Premises, and who pays. `SeatFits seat form`: three laws on the seat's functions: proved of both
real seats in Johnson/Top/H/K3SeatFits.lean. The rest are K3RunIsWorth's own: HeardIs: the law on
decide (K3DecideHears); Later F0 F: the link's steps between; FoNums.ok g.shape: from ShapeOf by the
library's shapeOf_ok; Sized F: whoever opens the ledger (slots_sized).

The member that says yes to all fails the law wherever its premises can be met: `yesToAll_fails`.

Limits. A tie: it has no error term: nothing here bounds a cheating prover's chance. A run that
always refuses meets the law emptily: that these runs say yes on real proofs is a matter of runs,
not of this file. In a run all three said yes at every lookup of two stored proofs
in a harness that calls each place alone, "planes" and "join" there with forms that the harness
hands in, and with a real caller's own forms at 2 and at 12 lookups alone; inside the whole fold
over blocks "objects" alone had run, "planes" and "join" had not. What the caller's forms are worth
is the caller's to state. In which order a link calls the runs, and that every claim enters the
link's one equation, is the link's law. The corollary's two premises hold of a caller with constant
readers and keys; a caller whose forms hang on the record is served by k3RunsAreWorthAt alone. Uses
of the library: pure lemmas on plain records (rows_claim, join_claim, onMasks_keyTop, evalL_muOf,
evalL_scale, ok_parts, paid_sized) and the carried planes_claim and join_ok of Johnson/Top/H/FlPort/
(of the flat functions planeClaimsF, joinF). The run "planes" calls planeClaimsOwn
(Johnson/Desc/First/Look/LookPlanesOwn.lean); that it is planeClaimsF is planeClaimsOwn_eq
(Johnson/Desc/First/Look/LookPlanesOwnAgrees.lean). No routine in a context is reached: held by
Johnson/Top/H/K3Walk.lean [not in this library].
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LawKind
import Johnson.Desc.First.Look.K3Runs
import Johnson.Desc.First.Look.LookPlanesOwnAgrees
import Johnson.Top.H.FlPort.FoClaimsMeet
import Johnson.Top.H.FlPort.FoJoinRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo
open Cb Cb.Fo Cb.Fo.PlaneClaims
open OnBytes.K.Kc
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.K3 (Seat joinRun planesRun Readers unpaid)
open VerifiableInference.Desc.First.Look (joinF planeClaimsF planesAddedF paidF)

/-! ## Refusals by name -/

theorem named_bind {α β : Type} (nm : String) (x : Option α) (f : α → Except String β) (b : β) :
    (named nm x >>= f) = .ok b ↔ ∃ a, x = some a ∧ f a = .ok b := by
  cases x with
  | none =>
    constructor
    · intro h
      have h' : (Except.error nm : Except String β) = .ok b := h
      cases h'
    · rintro ⟨_, e, _⟩
      cases e
  | some a =>
    constructor
    · intro h
      exact ⟨a, rfl, h⟩
    · rintro ⟨a', e, h⟩
      cases e
      exact h

theorem need_bind {β : Type} (nm : String) (c : Bool) (f : Unit → Except String β) (b : β) :
    (need nm c >>= f) = .ok b ↔ c = true ∧ f () = .ok b := by
  cases c with
  | false =>
    constructor
    · intro h
      have h' : (Except.error nm : Except String β) = .ok b := h
      cases h'
    · rintro ⟨e, _⟩
      cases e
  | true =>
    constructor
    · intro h
      exact ⟨rfl, h⟩
    · rintro ⟨_, h⟩
      exact h

/-! ## The seat, and the law with the caller's forms read off the record -/

/-- The seat's functions fit each other, as far as the runs of claims need it. form: what a claim
says is 0. -/
structure SeatFits {S Cl : Type} (seat : Seat S Cl) (form : Cl → Aff) : Prop where
  /-- where a ledger is open, a ledger that is laid is the one that is read -/
  markFork : ∀ s F G, seat.fork s = some F → seat.fork (seat.mark s G) = some G
  /-- laying a ledger leaves what was heard -/
  markHeard : ∀ s F G, seat.fork s = some F → seat.heard (seat.mark s G) = seat.heard s
  /-- a form that is laid as a claim is the claim's form -/
  form : ∀ a, form (seat.claim a) = a

/-- K3RunIsWorth (Johnson/Top/H/K3LawKind.lean), with a list that may hang on the record at which
the run is called. At a list that does not, it is K3RunIsWorth, by unfolding. -/
def K3RunIsWorthAt {S Cl : Type} (fork : S → Option Fork) (heard : S → Option Heard)
    (form : Cl → Aff) (lm : ℕ) (run : ℕ → S → Except String (List Cl × S))
    (want : S → (K : Type) → [CommRing K] → Heard → ℕ → Rounds K → (_root_.Fo.Pl → K) → (Aff → K) →
      List K) : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (g : Heard) (jLK : ℕ)
    (rsK : Rounds K) (F0 F : Fork) (n : ℕ) (s s' : S) (cl : List Cl),
    heard s = some g → fork s = some F →
    HeardIs ρ g F0 (endsOf g.shape lm jLK rsK) → _root_.Fo.Later F0 F → FoNums.ok g.shape = true →
    Sized F → run n s = .ok (cl, s') →
    ∃ G, fork s' = some G ∧ heard s' = some g ∧ _root_.Fo.Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∀ H, _root_.Fo.Later G H → ∀ (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K),
        cl.map (fun c => (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
          want s K g jLK rsK ν fun a => a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)

theorem worthAt_const {S Cl : Type} {fork : S → Option Fork} {heard : S → Option Heard}
    {form : Cl → Aff} {lm : ℕ} {run : ℕ → S → Except String (List Cl × S)}
    {want : (K : Type) → [CommRing K] → Heard → ℕ → Rounds K → (_root_.Fo.Pl → K) → (Aff → K) →
      List K} (h : K3RunIsWorthAt fork heard form lm run fun _ => want) :
    K3RunIsWorth fork heard form lm run want := h

/-- Marking an owed claim as added leads to a later ledger. -/
theorem paid_laterFo (F : Fork) (i : ℕ) : _root_.Fo.Later F (F.paid i) :=
  ⟨le_refl _, rfl, fun _ h => ⟨h, rfl, rfl⟩⟩

variable {S Cl : Type}

/-! ## "objects" -/

/-- The run "objects", as K3.block states it. -/
def objectsRun (seat : Seat S Cl) (_ : ℕ) (s : S) : Except String (List Cl × S) := do
  let F ← named "K3 objects: no sub-proof is open" (seat.fork s)
  let g ← named "K3 objects: nothing was heard" (seat.heard s)
  pure (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects))

/-- It is the first run of claims of the kind's block, to the letter. -/
theorem block_objects (seat : Seat S Cl) (piece : ℕ) (laid : Array ℕ) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) :
    (Desc.K3.block seat piece laid before p guests).claims.head? =
      some ("objects", objectsRun seat) := rfl

theorem objects_worth (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) (lm : ℕ) :
    K3RunIsWorth seat.fork seat.heard form lm (objectsRun seat)
      (fun _ _ g jLK rsK ν _ => (endsOf g.shape lm jLK rsK).rows.map (rowRes ν)) := by
  intro K _ ρ g jLK rsK F0 F n s s' cl hg hf hI h0 _ hF hrun
  unfold objectsRun at hrun
  rw [named_bind] at hrun
  obtain ⟨F1, e1, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨g1, e2, hrun⟩ := hrun
  obtain rfl : F = F1 := Option.some.inj (hf.symm.trans e1)
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans e2)
  have e3 : (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects)) = (cl, s') :=
    Except.ok.inj hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e3
  refine ⟨F.paid g.owedObjects, hs.markFork s F _ hf, (hs.markHeard s F _ hf).trans hg,
    paid_laterFo F _, paid_sized _ hF, rfl, fun H hH ν entry => ?_⟩
  beta_reduce
  rw [List.map_map, ← rows_claim ρ g lm jLK rsK F0 hI H ((h0.trans (paid_laterFo F _)).trans hH) ν
    entry]
  refine List.map_congr_left fun a _ => ?_
  show (form (seat.claim a)).value ρ _ = _
  rw [hs.form]

/-! ## "join" -/

/-- The caller's key forms at a record; none where it hands in none. -/
def keysOf (keys : S → Option (Array Aff)) (s : S) : Array Aff := (keys s).getD #[]

/-- What a yes of "join" is made of. -/
theorem joinRun_cut (seat : Seat S Cl) (keys : S → Option (Array Aff)) {n : ℕ} {s s' : S}
    {cl : List Cl} {F : Fork} {g : Heard} (hf : seat.fork s = some F) (hg : seat.heard s = some g)
    (hrun : joinRun seat keys n s = .ok (cl, s')) :
    ∃ KF, keys s = some KF ∧ KF.size = g.shape.calls.size ∧
      cl = [seat.claim (joinForm g KF)] ∧ s' = seat.mark s (F.paid g.owedJoin) := by
  unfold joinRun at hrun
  rw [named_bind] at hrun
  obtain ⟨F1, e1, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨g1, e2, hrun⟩ := hrun
  obtain rfl : F = F1 := Option.some.inj (hf.symm.trans e1)
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans e2)
  rw [need_bind] at hrun
  obtain ⟨_, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨KF, e3, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨⟨a, G, u⟩, e4, hrun⟩ := hrun
  have e4' : joinF g KF F [] = .ok ((a, G), u) := e4
  obtain ⟨k1, _, _, k4, k5⟩ := Fo.Tp.join_ok g KF F G [] u a e4'
  have e5 : ([seat.claim a], seat.mark s G) = (cl, s') := Except.ok.inj hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e5
  exact ⟨KF, e3, k1, by rw [k5], by rw [k4]⟩

/-- **KF.size = NC**: a yes of "join" at a lawful shape has one key form for each call. -/
theorem join_size (seat : Seat S Cl) (keys : S → Option (Array Aff)) {n : ℕ} {s s' : S}
    {cl : List Cl} {F : Fork} {g : Heard} (hf : seat.fork s = some F) (hg : seat.heard s = some g)
    (hok : FoNums.ok g.shape = true) (hrun : joinRun seat keys n s = .ok (cl, s')) :
    (keysOf keys s).size = g.shape.NC := by
  obtain ⟨KF, e, k, _⟩ := joinRun_cut seat keys hf hg hrun
  unfold keysOf
  rw [e]
  exact k.trans (Cb.Fo.ok_parts hok).1.2.2.2.2.2.2

theorem join_worth (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) (lm : ℕ)
    (keys : S → Option (Array Aff)) :
    K3RunIsWorthAt seat.fork seat.heard form lm (joinRun seat keys)
      (fun s _ _ g jLK rsK ν val =>
        [claimJoin g.shape lm jLK rsK ν fun k =>
          val ((keysOf keys s).getD k (Aff.ofConst zeroE))]) := by
  intro K _ ρ g jLK rsK F0 F n s s' cl hg hf hI h0 hok hF hrun
  have hsz := join_size seat keys hf hg hok hrun
  obtain ⟨KF, e, _, rfl, rfl⟩ := joinRun_cut seat keys hf hg hrun
  have ek : keysOf keys s = KF := by
    unfold keysOf
    rw [e]
    rfl
  rw [ek] at hsz
  refine ⟨F.paid g.owedJoin, hs.markFork s F _ hf, (hs.markHeard s F _ hf).trans hg,
    paid_laterFo F _, paid_sized _ hF, rfl, fun H hH ν entry => ?_⟩
  have hL : _root_.Fo.Later F0 H := (h0.trans (paid_laterFo F _)).trans hH
  have hcE : g.cEnd.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) =
      AffK.val ((endsOf g.shape lm jLK rsK).cEndF, (endsOf g.shape lm jLK rsK).cEndC) ν := by
    rw [(hI.cEnd H hL).2 (fun j => ν (.mask j)) entry,
      evalL_muOf (onMasks_keyTop g.shape lm jLK rsK) ν]
    show _ = evalL ν (scale (-1) (endsOf g.shape lm jLK rsK).cEndInc) + _
    rw [evalL_scale]
    ring
  have hJ := join_claim ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) g KF hok hsz lm jLK rsK ν
    hI.theta hI.alpha (fun k _ => by
      rw [rdL_getD, show rdL ρ g.e = _ from hI.e]) hI.zy hcE
  show [(form (seat.claim (joinForm g KF))).value ρ _] = [_]
  rw [hs.form, hJ, ek]

/-! ## "planes" -/

/-- The caller's form on column col of the planes' matrix at the leaves' point (e = 0) or the bits'
point (e = 1), at a record; the empty form where it hands in none. -/
def bitOf (readers : Readers S) (s : S) (e col : ℕ) : Aff :=
  ((readers s).bind fun r => r.1 e col).getD {}

/-- The caller's form for the counts on column col, at a record. -/
def pinOf (readers : Readers S) (s : S) (col : ℕ) : Aff :=
  ((readers s).bind fun r => r.2 col).getD {}

theorem quiet_need (x : Option Aff) : Fo.Tp.Quiet (Fl.need x) := by
  intro F c r h
  obtain ⟨a, _, rfl⟩ := (Fo.Tp.get_ok x F c r).1 h
  exact ⟨rfl, rfl⟩

theorem got_need (x : Option Aff) (F : Fork) (c : Tape) :
    Fo.Tp.got (Fl.need x) F c = x.getD {} := by
  cases x <;> rfl

/-- What a yes of "planes" is made of. -/
theorem planesRun_cut (seat : Seat S Cl) (lm : ℕ) (readers : Readers S) {n : ℕ} {s s' : S}
    {cl : List Cl} {F : Fork} {g : Heard} (hf : seat.fork s = some F) (hg : seat.heard s = some g)
    (hrun : planesRun seat lm readers n s = .ok (cl, s')) :
    ∃ r rows G u, readers s = some r ∧
      planeClaimsF g lm (fun e col => Fl.need (r.1 e col)) (fun col => Fl.need (r.2 col)) F [] =
        .ok ((rows, G), u) ∧
      cl = rows.toList.map seat.claim ∧ s' = seat.mark s (G.paid g.owedPlanes) := by
  unfold planesRun at hrun
  rw [named_bind] at hrun
  obtain ⟨F1, e1, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨g1, e2, hrun⟩ := hrun
  obtain rfl : F = F1 := Option.some.inj (hf.symm.trans e1)
  obtain rfl : g = g1 := Option.some.inj (hg.symm.trans e2)
  rw [need_bind] at hrun
  obtain ⟨_, hrun⟩ := hrun
  rw [named_bind] at hrun
  obtain ⟨r, e3, hrun⟩ := hrun
  dsimp only at hrun
  rw [named_bind] at hrun
  obtain ⟨⟨rows, G, u⟩, e4, hrun⟩ := hrun
  have e4' : (planeClaimsF g lm (fun e col => Fl.need (r.1 e col))
      (fun col => Fl.need (r.2 col)) >>=
        fun fs => planesAddedF g >>= fun _ => (pure fs : Fl (Array Aff))) F [] =
      .ok ((rows, G), u) := by
    rw [← Desc.First.Look.planeClaimsOwn_eq]
    exact e4
  obtain ⟨fs, G1, u1, h1, h2⟩ := (Fo.Tp.bind_ok _ _ F [] _).1 e4'
  obtain ⟨_, G2, u2, h3, h4⟩ := (Fo.Tp.bind_ok _ _ G1 u1 _).1 h2
  unfold planesAddedF paidF at h3
  obtain ⟨G3, k1, k2⟩ := (Fo.Tp.change_ok _ G1 u1 _).1 h3
  have k3 := (Fo.Tp.pure_ok _ G2 u2 _).1 h4
  have a1 : G1.paid g.owedPlanes = G3 := Option.some.inj k1
  have a2 : G2 = G3 := congrArg (fun x : (Unit × Fork) × Tape => x.1.2) k2
  have a3 : rows = fs := congrArg (fun x : (Array Aff × Fork) × Tape => x.1.1) k3
  have a4 : G = G2 := congrArg (fun x : (Array Aff × Fork) × Tape => x.1.2) k3
  have e5 : (rows.toList.map seat.claim, seat.mark s G) = (cl, s') := Except.ok.inj hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e5
  exact ⟨r, fs, G1, u1, e3, h1, by rw [a3], by rw [a4, a2, ← a1]⟩

theorem planes_worth (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) (lm : ℕ)
    (readers : Readers S) :
    K3RunIsWorthAt seat.fork seat.heard form lm (planesRun seat lm readers)
      (fun s _ _ g jLK rsK ν val =>
        [claimLeaves g.shape lm jLK rsK ν fun col => val (bitOf readers s 0 col),
          claimBits g.shape lm jLK rsK ν fun col => val (bitOf readers s 1 col),
          Pin.countK g.shape lm fun col => val (pinOf readers s col)]) := by
  intro K _ ρ g jLK rsK F0 F n s s' cl hg hf hI h0 hok hF hrun
  obtain ⟨r, rows, G, u, e, h1, rfl, rfl⟩ := planesRun_cut seat lm readers hf hg hrun
  obtain ⟨_, a2, a3, a4, hv⟩ := Fo.Tp.planes_claim ρ g lm jLK rsK
    (fun e col => Fl.need (r.1 e col)) (fun col => Fl.need (r.2 col))
    (fun _ _ => quiet_need _) (fun _ => quiet_need _) F0 F G [] u rows h1 hI h0 hok hF
  refine ⟨G.paid g.owedPlanes, hs.markFork s F _ hf, (hs.markHeard s F _ hf).trans hg,
    a2.trans (paid_laterFo G _), paid_sized _ a3, a4, fun H hH ν entry => ?_⟩
  have hb : ∀ e' col, bitOf readers s e' col = Fo.Tp.got (Fl.need (r.1 e' col)) F [] := by
    intro e' col
    rw [got_need]
    unfold bitOf
    rw [e]
    rfl
  have hp : ∀ col, pinOf readers s col = Fo.Tp.got (Fl.need (r.2 col)) F [] := by
    intro col
    rw [got_need]
    unfold pinOf
    rw [e]
    rfl
  rw [List.map_map]
  simp only [hb, hp]
  rw [← hv H ((paid_laterFo G _).trans hH) ν entry]
  refine List.map_congr_left fun a _ => ?_
  show (form (seat.claim a)).value ρ _ = _
  rw [hs.form]

/-! ## (L2b) -/

/-- **(L2b), of the kind's three runs, with the caller's forms read off the carried record.** Spent
at the lookups on a link's calls: at the smallness test's digits no link calls "planes" or
"join". -/
theorem k3RunsAreWorthAt (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) (lm : ℕ)
    (readers : Readers S) (keys : S → Option (Array Aff)) :
    K3RunIsWorth seat.fork seat.heard form lm (objectsRun seat)
        (fun _ _ g jLK rsK ν _ => (endsOf g.shape lm jLK rsK).rows.map (rowRes ν)) ∧
      K3RunIsWorthAt seat.fork seat.heard form lm (planesRun seat lm readers)
        (fun s _ _ g jLK rsK ν val =>
          [claimLeaves g.shape lm jLK rsK ν fun col => val (bitOf readers s 0 col),
            claimBits g.shape lm jLK rsK ν fun col => val (bitOf readers s 1 col),
            Pin.countK g.shape lm fun col => val (pinOf readers s col)]) ∧
      K3RunIsWorthAt seat.fork seat.heard form lm (joinRun seat keys)
        (fun s _ _ g jLK rsK ν val =>
          [claimJoin g.shape lm jLK rsK ν fun k =>
            val ((keysOf keys s).getD k (Aff.ofConst zeroE))]) :=
  ⟨objects_worth seat form hs lm, planes_worth seat form hs lm readers,
    join_worth seat form hs lm keys⟩

/-- **(L2b), the listed statement to the letter**, for a caller whose readers and keys give the
fixed forms bit, pin, KF wherever they give any. A TOOL FOR A HARNESS: hr asks a form at EVERY
column, also beyond those that the claims read. A caller whose reader refuses there does not meet
it; k3RunsAreWorthAt is the law for such a caller. -/
theorem k3RunsAreWorth (seat : Seat S Cl) (form : Cl → Aff) (hs : SeatFits seat form) (lm : ℕ)
    (readers : Readers S) (keys : S → Option (Array Aff)) (bit : ℕ → ℕ → Aff) (pin : ℕ → Aff)
    (KF : Array Aff)
    (hr : ∀ s r, readers s = some r →
      (∀ e col, r.1 e col = some (bit e col)) ∧ ∀ col, r.2 col = some (pin col))
    (hk : ∀ s KF', keys s = some KF' → KF' = KF) :
    K3RunsAreWorth seat.fork seat.heard form lm bit pin KF (objectsRun seat)
      (planesRun seat lm readers) (joinRun seat keys) := by
  refine ⟨objects_worth seat form hs lm, ?_, ?_⟩
  · intro K _ ρ g jLK rsK F0 F n s s' cl hg hf hI h0 hok hF hrun
    obtain ⟨r, _, _, _, e, _⟩ := planesRun_cut seat lm readers hf hg hrun
    obtain ⟨G, b1, b2, b3, b4, b5, hv⟩ :=
      planes_worth seat form hs lm readers K ρ g jLK rsK F0 F n s s' cl hg hf hI h0 hok hF hrun
    refine ⟨G, b1, b2, b3, b4, b5, fun H hH ν entry => ?_⟩
    have hb : ∀ e' col, bitOf readers s e' col = bit e' col := by
      intro e' col
      unfold bitOf
      rw [e]
      show (r.1 e' col).getD {} = _
      rw [(hr s r e).1 e' col]
      rfl
    have hp : ∀ col, pinOf readers s col = pin col := by
      intro col
      unfold pinOf
      rw [e]
      show (r.2 col).getD {} = _
      rw [(hr s r e).2 col]
      rfl
    rw [hv H hH ν entry]
    simp only [hb, hp]
  · intro K _ ρ g jLK rsK F0 F n s s' cl hg hf hI h0 hok hF hrun
    obtain ⟨KF', e, _⟩ := joinRun_cut seat keys hf hg hrun
    obtain ⟨G, b1, b2, b3, b4, b5, hv⟩ :=
      join_worth seat form hs lm keys K ρ g jLK rsK F0 F n s s' cl hg hf hI h0 hok hF hrun
    refine ⟨G, b1, b2, b3, b4, b5, fun H hH ν entry => ?_⟩
    have ek : keysOf keys s = KF := by
      unfold keysOf
      rw [e]
      exact hk s KF' e
    rw [hv H hH ν entry]
    beta_reduce
    rw [ek]

/-! ## The member that says yes to all -/

/-- A run that says yes to all and hands out no claim fails the law of "planes" wherever the law's
premises can be met at all. -/
theorem yesToAll_fails (fork : S → Option Fork) (heard : S → Option Heard) (form : Cl → Aff)
    (lm : ℕ) (bit : ℕ → ℕ → Aff) (pin : ℕ → Aff)
    (h : K3RunIsWorth fork heard form lm (fun _ s => .ok ([], s))
      (fun _ _ g jLK rsK ν val =>
        [claimLeaves g.shape lm jLK rsK ν fun col => val (bit 0 col),
          claimBits g.shape lm jLK rsK ν fun col => val (bit 1 col),
          Pin.countK g.shape lm fun col => val (pin col)]))
    {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (g : Heard) (jLK : ℕ) (rsK : Rounds K)
    (F0 F : Fork) (s : S) (hg : heard s = some g) (hf : fork s = some F)
    (hI : HeardIs ρ g F0 (endsOf g.shape lm jLK rsK)) (h0 : _root_.Fo.Later F0 F)
    (hok : FoNums.ok g.shape = true) (hF : Sized F) : False := by
  obtain ⟨G, _, _, _, _, _, hv⟩ := h K ρ g jLK rsK F0 F 0 s s [] hg hf hI h0 hok hF rfl
  have := congrArg List.length (hv G (_root_.Fo.Later.refl G) (fun _ => 0) fun _ _ _ => 0)
  simp at this

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3RunsAreWorthAt
#print axioms VerifiableInference.OnPublicFiles.k3RunsAreWorth
#print axioms VerifiableInference.OnPublicFiles.join_size
#print axioms VerifiableInference.OnPublicFiles.yesToAll_fails
