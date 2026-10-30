-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3LeftRuleStatement.lean: the lookup on a link's CALLS, at any closed
caller: STATEMENTS, NOT PROVED HERE, at the level of the rule of composition: what a yes leaves
(Johnson/Top/H/K3LeftStatement.lean: K3Left) AS A PROMISE of the block's piece, with the proved
block's out-statement BY NAME; and that the promise and the relation behind the block ride over
later pieces. Definitions of type Prop.

Main names:
  `GoodInPromise`: a piece that has GoodIn, and at every yes leaves a statement with Q, has GoodIn
    with the promise "on' and Q". So a promise can grow WITHOUT A TURN of a theorem that lies.
  `K3YesNamesOut`: ONE THEOREM AT A YES OF THE BLOCK, general in the caller r: at a piece that holds
    "below b", b any block whose decide says yes only where K3.block's does at the calls' seat and
    the place x: where the piece says yes at a transcript τ, from a statement whose ledger has its
    sizes: there are F, F', g: the ledgers in front and behind and what was heard; F's next free
    slot is the place's first; K3Left at the transcript's own rounds; AND THE PROVED BLOCK PUTS OUT,
    at that transcript's image, lookOutE r.c.h x.lm x.F.next (placeOf mk pl) (st a) (the end values
    of these rounds).
  `K3CallsKeepLeft`: so the piece keeps THE SHARP PROMISE K3LeftAt, at any letter Q that holds of
    the ledger in front.
  `K3LeftOnStays`: K3LeftOn stands at every later record at which what was heard stays and the
    ledger is later and has its sizes.
  `CBehindBack`: THE RELATION BEHIND THE BLOCK GOES BACK over any such step, from a witness w to a
    witness w' (what the later piece's extractor makes of w) that has the same reading wt, where
    the caller's state stays and the pins go back from w to w': this is the premise that the
    rule's GoodInBeside (Johnson/Desc/Sound/GoodIn.lean) asks of a carried claim: so CBehind can
    ride beside every later piece, down to the runs of claims. WHO PAYS ITS PREMISES AT EACH LATER
    PIECE (what was heard stays; both ledgers are there; the later one is later; the state stays;
    the pins go back; the extractor leaves wt) is not said here: it is owed with that piece's laws.

Limits. NOTHING IS PROVED HERE. Ties: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LeftStatement
import Johnson.Desc.First.Look.K3GoodInCaller

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- **A promise can grow.** NOT PROVED HERE. -/
def GoodInPromise : Prop :=
  ∀ (S Cl W : Type) (Fr : Frame) (p : Piece (ckP .two) Fr S Cl W)
    (on on' Q : S × Fr.E.Str → Prop) (R R' : S × Fr.E.Str → W → Prop),
    p.GoodIn on on' R R' → (∀ a τ b, on a → p.ior.red.out a τ = some b → Q b) →
    p.GoodIn on (fun b => on' b ∧ Q b) R R'

/-- **ONE THEOREM AT A YES OF THE BLOCK, general in the caller.** NOT PROVED HERE. -/
def K3YesNamesOut : Prop :=
  ∀ (Cl W : Type) (Fr : Frame) (r : LookupCRCaller) (set : Params.Setting)
    (x : Desc.First.Look.Place) (mk : ℕ → r.c.J₀) (pl : ℕ → ℕ → r.c.J₀)
    (st : Desc.First.S × Fr.E.Str → r.c.St₀) (y₀ : r.c.Ex.Str)
    (sm : Desc.First.S × Fr.E.Str → r.c.Sg.Smp) (wd : Desc.First.S × Fr.E.Str → r.c.Sg.ext.Str)
    (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (b : Desc.Block Desc.First.S Cl),
    (∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
        (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s') →
    ∀ (p : Piece (ckP .two) Fr Desc.First.S Cl W), p.b = below b → p.back = [] →
    (Desc.First.Look.P.ofPlace set false x).shape = some r.c.h →
    (∀ t, r.c.L.mkS t = mk (x.F.next + t)) →
    (∀ t k j, k < r.c.h.NC →
      r.c.L.bc t k j =
        pl (FoNums.cellRC r.c.h x.lm (t, k, j)).1 (FoNums.cellRC r.c.h x.lm (t, k, j)).2) →
    ∀ (hM : List.Forall₂ MeetsT p.ds (specF r.c.h)), (∀ d ∈ p.ds, NoAns d.items) →
    ∀ (a : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) p.ds)) (a' : Desc.First.S × Fr.E.Str),
      (∃ Fk, (Desc.K3.seatCalls claim).fork a.1 = some Fk ∧ OnBytes.PscRun.Sized Fk) →
      p.ior.red.out a τ = some a' →
      ∃ (F F' : Fork) (g : Forest.Heard), (Desc.K3.seatCalls claim).fork a.1 = some F ∧
        F.next = x.F.next ∧ (Desc.K3.seatCalls claim).fork a'.1 = some F' ∧
        (Desc.K3.seatCalls claim).heard a'.1 = some g ∧
        K3Left Reading.gl r.c.h x.lm F F' g (viewRounds p.ds τ) ∧
        ((kLookupCRN [r]).toKind.block r).R.red.out (cRd r st y₀ sm wd a)
            ((mapsT p.ds _ (specF r.c.h) (rkFor r.c.h r.c.L r.c.Ex).R hM.length_eq).view τ) =
          some ((lookOutE r.c.h x.lm x.F.next (placeOf mk pl) (st a)
            (endsOf r.c.h x.lm x.F.next (viewRounds p.ds τ)), sm a), (y₀, wd a))

/-- **So the piece keeps the promise.** NOT PROVED HERE. -/
def K3CallsKeepLeft : Prop :=
  ∀ (Cl W : Type) (Fr : Frame) (h : Forest.Shape) (set : Params.Setting)
    (x : Desc.First.Look.Place) (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (b : Desc.Block Desc.First.S Cl),
    (∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
        (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s') →
    ∀ (p : Piece (ckP .two) Fr Desc.First.S Cl W), p.b = below b → p.back = [] →
    (Desc.First.Look.P.ofPlace set false x).shape = some h →
    ∀ (Q : Fork → Prop) (a : Desc.First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) p.ds))
      (a' : Desc.First.S × Fr.E.Str),
      (∃ Fk, (Desc.K3.seatCalls claim).fork a.1 = some Fk ∧ OnBytes.PscRun.Sized Fk ∧ Q Fk) →
      p.ior.red.out a τ = some a' →
      K3LeftAt (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard h x.lm x.F.next Q
        a'.1

/-- **The promise stands at every later record.** NOT PROVED HERE. -/
def K3LeftOnStays : Prop :=
  ∀ (S : Type) (fork : S → Option Fork) (heard : S → Option Forest.Heard) (h : Forest.Shape)
    (lm first : ℕ) (Q : Fork → Prop) (s t : S) (Fs Ft : Fork), heard t = heard s →
    fork s = some Fs → fork t = some Ft → _root_.Fo.Later Fs Ft → OnBytes.PscRun.Sized Ft →
    K3LeftOn fork heard h lm first Q s → K3LeftOn fork heard h lm first Q t

/-- **The relation behind the block goes back over a later step.** NOT PROVED HERE. -/
def CBehindBack : Prop :=
  ∀ (S W : Type) (Fr : Frame) (r : LookupCRCaller) (lm first : ℕ) (mk : ℕ → r.c.J₀)
    (pl : ℕ → ℕ → r.c.J₀) (st : S × Fr.E.Str → r.c.St₀) (wt : W → r.c.Sg.Wit × r.c.Wp)
    (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (Pin : S × Fr.E.Str → W → Prop) (a b : S × Fr.E.Str) (w w' : W) (Fa Fb : Fork),
    heard b.1 = heard a.1 → fork a.1 = some Fa → fork b.1 = some Fb → _root_.Fo.Later Fa Fb →
    st b = st a → wt w' = wt w → (Pin b w → Pin a w') →
    CBehind r lm first mk pl st wt fork heard Pin b w →
    CBehind r lm first mk pl st wt fork heard Pin a w'

end VerifiableInference.OnPublicFiles
