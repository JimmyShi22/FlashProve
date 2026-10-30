-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3LawKind.lean: the kind «lookup» (K3): the laws that are owed of the text that
runs, STATED OF A KIND's FIELDS AS LETTERS, not of any text's lines. Four definitions of type Prop
and one test with code; nothing is proved.

A kind's block (Johnson/Desc/Block.lean) has a field decide, from the carried record, the block's
rounds as a view shows them and the columns that it is owed to the next record or a refusal, and
named runs of claims, each from the number of claims gathered so far and the record to claims and
the record behind, or a refusal. Here decide and the three runs are letters of these types, AS
Block.lean HAS THEM (by reading),
to the letter: decide : S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Except String S;
a run : Nat → S → Except String (List Cl × S).
So are the readers of the carried record (fork: the open sub-proof's
ledger; heard: what the lookup heard) and the reader of a claim (form). The file does not import
Block.lean.

Main names:

  `K3DecideHears`: decide's yes leaves a record whose «heard» and ledger meet the record of end
    values (`endsOf`) at the very rounds that decide was handed: the three parts of the library's
    dictionary (`ShapeOf`, `PadLeft`, `HeardIs`); and these rounds have the sizes that the shape's
    own plan of rounds states (`planF`).
  `K3CallsShareThePoint`: decide's yes leaves a record in which every call's key point ends in the
    whole of zx, word for word: the lookup's own sentence as a host.
  `K3RunsAreWorth`: under that dictionary the forms of the three runs are worth the members of the
    library's list `claimsOf`, run by run: the sumchecks' rows; the planes' three; the claim on
    the key vectors. The order in which a link lays the runs is the link's.

OF WHICH TEXT THEY SPEAK. Of none: any decide and any runs of these types can be put for the
letters. THE INSTANCE of decide: lookRun behind a seat in the carried record (it gives an
Option: at these types it stands under a name for its refusal); of it the same law is stated as
LookHears and LookHearsSizes (Johnson/Top/H/LookHearsLaw.lean [not in this library]).

For the verifier program's own routines the
second law is proved in the library: rows_claim, planes_claim, claims_port
(OnBytes/Tie/Pv/Lookup/Forest/FoClaimsMeet.lean).

Limits. Statements alone: that a given text's decide and runs meet them is shown elsewhere, or not
at all. Each has the form "a yes gives …": a decide or a run that refuses everything meets it
emptily. `K3DecideHears` gives the dictionary's three parts under `Sized F` alone. They are ties
between a text and the library's records: they have no error term.
No soundness is claimed. Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoRds
import OnBytes.Tie.Pv.Lookup.Forest.FoClaimsMeet
import OnBytes.Maker.OkView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo
open Cb Cb.Fo Cb.Fo.PlaneClaims

/-- **Every word of a field's element in these rounds is below the prime**: in the items that hold
elements (the library's okGot, OnBytes/Maker/OkView.lean) and in the elements drawn (okE). It is
what the fold asks of a whole view in front of all kinds (viewWordsBelowPrime, Johnson/Desc/Block.lean), at a
stretch's rounds. An element of E is three machine words with derived equality, and the field's
operations reduce first: so a law that ranges over all rounds carries this as a named premise. -/
def okRoundsE (rs : List Fmt.RoundView) : Bool :=
  rs.all fun r => r.vals.all OnBytes.Maker.okGot && r.drawn.elems.all fun x => okE (E.ofTriple x)

/-- **(L2a), of a kind's field decide.** calls, pub, lid: the place's public parameters. lm: free,
as in the library's HCout2. The rounds' words are below the prime (okRoundsE). A theorem in
Johnson/Top/H/K3DecideHearsAt.lean says it of `K3.block`'s decide, at every seat that meets
`SeatKeeps` and `SeatReads` (`k3DecideHears`), and with no premise at the two seats that run
(`k3DecideHears_calls`, `k3DecideHears_digits`). -/
def K3DecideHears {S : Type} (fork : S → Option Fork) (heard : S → Option Heard)
    (calls : Array Call) (pub : Array Nat) (lid : ℕ)
    (decide : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S) : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (lm : ℕ) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64))),
    okRoundsE rs = true → decide s rs cols = .ok s' →
    ∃ F F' g, fork s = some F ∧ fork s' = some F' ∧ heard s' = some g ∧
      rs.map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF g.shape ∧
      (Sized F →
        ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
          HeardIs ρ g F' (endsOf g.shape lm F.next (rs.map (rdRV ρ))))

/-- **(H'), the host's own sentence, of a kind's field decide: ALL CALLS' KEY POINTS END IN THE
WHOLE OF zx, WORD FOR WORD.** That zx and zy are what was drawn is not said here: K3DecideHears says
it. calls, pub, lid: the place's public parameters. Where decide says yes, in what it leaves: the
public tests have passed (ShapeOf); zx has dT coordinates and zy has rK; there is a key point for
each call; and call c's key point is the last iota_c coordinates of zy, then ALL OF zx, AS ARRAYS OF
MACHINE WORDS, not only as field elements. That is what a guest borrows: a test of another kind that
every call's key point ends in the last la coordinates of zx follows from it, WITH THE GUEST's la ≤
dT, which the guest's own layout pays. The rounds' words are below the prime (okRoundsE). At the
readings, and only under Sized F, the equation follows from K3DecideHears: HeardIs reads zx, zy and
zk as the record of end values has them, and there zk_c is made of zy's and zx's own lists. NEW
HERE: the equality of the words. The equation and the number of key points hold by make
(OnBytes/K/Kc/FlatHear.lean:142). zy's size holds by the levels' make alone (:125 with
OnBytes/K/Kc/Flat.lean:274-281 and OnBytes/Model/Psc.lean:242-244): no test that runs asks it. zx's
is also held by the test on the key points' sizes (:143-144) together with :124-125. FOR THE decide
OF ANOTHER TEXT BOTH SIZES ARE A TRUE DEBT. NOT PROVED. -/
def K3CallsShareThePoint {S : Type} (heard : S → Option Heard)
    (calls : Array Call) (pub : Array Nat) (lid : ℕ)
    (decide : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S) : Prop :=
  ∀ (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64))),
    okRoundsE rs = true → decide s rs cols = .ok s' →
    ∃ g, heard s' = some g ∧ ShapeOf calls pub lid g.shape ∧
      g.zx.size = g.shape.dT ∧ g.zy.size = g.shape.rK ∧ g.zk.size = g.shape.NC ∧
      ∀ c, c < g.shape.NC →
        g.shape.iota.getD c 0 ≤ g.shape.rK ∧
          g.zk.getD c #[] =
            g.zy.extract (g.shape.rK - g.shape.iota.getD c 0) g.zy.size ++ g.zx

/-- One run of claims is worth a list of values. want: the list, from the record of end values'
arguments, a reading ν of the places and the value val of every form. The run is taken from any
later record at which the lookup's «heard» still stands; behind it the ledger is a later one, with
the same next free slot. -/
def K3RunIsWorth {S Cl : Type} (fork : S → Option Fork) (heard : S → Option Heard)
    (form : Cl → Aff) (lm : ℕ) (run : ℕ → S → Except String (List Cl × S))
    (want : (K : Type) → [CommRing K] → Heard → ℕ → Rounds K → (_root_.Fo.Pl → K) → (Aff → K) →
      List K) : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (g : Heard) (jLK : ℕ)
    (rsK : Rounds K) (F0 F : Fork) (n : ℕ) (s s' : S) (cl : List Cl),
    heard s = some g → fork s = some F →
    HeardIs ρ g F0 (endsOf g.shape lm jLK rsK) → Later F0 F → FoNums.ok g.shape = true →
    Sized F → run n s = .ok (cl, s') →
    ∃ G, fork s' = some G ∧ heard s' = some g ∧ Later F G ∧ Sized G ∧ G.next = F.next ∧
      ∀ H, Later G H → ∀ (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K),
        cl.map (fun c => (form c).value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
          want K g jLK rsK ν fun a => a.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)

/-- **(L2b), of a kind's named runs of claims.** form: what a claim says is 0. bit, pin, KF: the
host's forms: on the planes' columns (at the leaves' point: 0; at the bits' point: 1), for the
counts, for the calls' key vectors (as many as there are calls). The three runs are worth the
members of the library's list claimsOf: the sumchecks' rows; the planes' three; the claim on the
key vectors. A theorem in Johnson/Top/H/K3RunsLaw.lean (`k3RunsAreWorth`) says it of the kind's
own three runs ("objects" as it stands in `K3.block`; `planesRun` and `joinRun`,
Johnson/Desc/First/Look/K3Runs.lean), under `SeatFits seat form`, for a caller whose readers and
keys give the fixed forms bit, pin, KF wherever they give any; a caller whose forms hang on the
carried record is served by `k3RunsAreWorthAt` there. -/
def K3RunsAreWorth {S Cl : Type} (fork : S → Option Fork) (heard : S → Option Heard)
    (form : Cl → Aff) (lm : ℕ) (bit : ℕ → ℕ → Aff) (pin : ℕ → Aff) (KF : Array Aff)
    (objects planes join : ℕ → S → Except String (List Cl × S)) : Prop :=
  K3RunIsWorth fork heard form lm objects
      (fun _ _ g jLK rsK ν _ => (endsOf g.shape lm jLK rsK).rows.map (rowRes ν)) ∧
    K3RunIsWorth fork heard form lm planes
      (fun _ _ g jLK rsK ν val =>
        [claimLeaves g.shape lm jLK rsK ν fun col => val (bit 0 col),
          claimBits g.shape lm jLK rsK ν fun col => val (bit 1 col),
          Pin.countK g.shape lm fun col => val (pin col)]) ∧
    K3RunIsWorth fork heard form lm join
      (fun _ _ g jLK rsK ν val =>
        [claimJoin g.shape lm jLK rsK ν fun k => val (KF.getD k (Aff.ofConst zeroE))])

end VerifiableInference.OnPublicFiles
