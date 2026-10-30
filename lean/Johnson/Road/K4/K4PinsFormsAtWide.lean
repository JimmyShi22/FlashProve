-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsFormsAtWide.lean: THE FIELD forms THAT THE ASSEMBLY OF K4's LAW LEAVES AT A
LATER GROUP (`K4LaterAt`, Johnson/Road/K4/K04LawOf.lean: behind an accepting run, inside the promise
behind, the item on K4's own forms gives the reference value's sentence on them), AT THE WIDER
MEANING AND THE DATA OFF ITS OWN PARAMETERS. A JOINING OF FOUR THEOREMS OF K4's
FILES, ALL CALLED: `forms_pins` (Johnson/Road/K4/FormsAtPins.lean) at the pinned readers `pinAt …` ·
its premise on the stated functions: `hSt_built` (NamesOfBuilt.lean) · its premise asks:
`asks_of_means` (Riders/AsksAtMeans.lean) · its premise hns: `hns_of_front` (FormsPinsNs.lean). No
draw, no count.

  **`forms_wide`**: the field, at a place xL with the segment's number as its link and the plan's
    number of slots, and all of the value's numbers, from: `K4Means` at the wider meaning · the
    table's two lines at K4's place (H : `AtK4` · Kf : `K4Front` at "the ledger has the plan's
    number of slots") · two lines on the term's readers of the runs (hRd, hruns) · the term's number
    of slots at the segment is there · SIX TESTS: `frontB` · `openAllB` · `readsArrayP` ·
    `maskPlanB` · `arraysPlanB` · "the place's number of slots is at most the mask row's length" ·
      TWO CONDITIONS ON PUBLIC LETTERS: `SitsIn`, `Covers` · ONE NAMED EQUATION (𝔇.uL = `uLAt X
      (namesOf 𝔇.built)`) · `tlAt X m` is the plan's · AND THREE BINDERS ON RUNS AND STATES: left
      (inside the promise in front the lookup's ledger is left) · four (four facts behind an
      accepting run, at every sub-protocol that narrows the lot's) · st (the link's states).

OBJECT: `k4DataWide 𝔇 E Mg₀`, `mgWide 𝔇 E Mg₀`. USER: `laterAt_whole`
(Johnson/Road/K4/K4PinsLaterWhole.lean). LETTERS: as named.

Limits. K04_law IS NOT PROVED BY THIS. left, four AND st ARE NOT CONCLUDED; Kf is concluded
elsewhere from `K4Means` and tests. IT SPEAKS AT THE WIDER MEANING: it counts only when the bridge
to the meaning that counts is paid. NO MEMBER IS SHOWN.
-/
import Johnson.Road.K4.K04LawOf
import Johnson.Road.K4.K4PinsAtWide
import Johnson.Road.K4.FormsAtPins
import Johnson.Road.K4.NamesOfBuilt
import Johnson.Road.K4.FormsPinsNs
import Johnson.Road.K4.Riders.AsksAtMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Pub Own)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Desc.First.K4.Total (KeptAsks frontB)
open OnBytes.Road.K4.InT (InTAsks StatesAt oneRowB readsThereB)
open VerifiableInference.Desc.First.FillBare (lookLeftB)
open OnBytes.Road.K4.Rec (recPlanOf readsArrayP maskPlanB arraysPlanB maskEllP openAllB)
open VerifiableInference.OnPublicFiles (LeftQ)
open _root_.Run (ckP)
open VerifiableInference.Desc (Wit Claim Link K9.LinkHoles K9.statesOfLink K9.readersOfLink
  K9.segAt? K9.maskSeat)
open VerifiableInference.Desc.First (S ModelPart Meaning)
open VerifiableInference.Desc.First.Look (Place sigListCalls tlAt pubAt stepOf Stored.entries)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)
open Inst.Model (Scl)
open Inst.Model.Layout (kRef hRef)

variable [scl : Scl] {Fr : Frame} {Xi Tok : Type} {nR : ℕ} {X : Public}
  (𝔇 : MgData Xi ProofFile.InstPub Tok hRef (2 ^ kRef) nR X) (E : WideData ProofFile.InstPub)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT))

/-- the data -/
local notation "𝐃" => k4DataWide 𝔇 E Mg₀
/-- the meaning -/
local notation "𝐌" => mgWide 𝔇 E Mg₀

/-- **The field forms at the wider meaning.** -/
theorem forms_wide (z : ProofFile.InstPub) (links : List ModelPart)
    (ps : List VerifiableInference.Desc.Place) (k m : ℕ) (x : Bool × Par)
    (q : Piece (ckP .two) Fr (ProofFile.InstPub × S) ProofFile.Cl (Wit (CellsK hRef (2 ^ kRef)) Tok MsgT))
    (hg : (parOf x).g < 12) (xL : Place) (posI : ℕ → Bool × ℕ × ℕ) (nM nRr nC nx v7 : ℕ)
    (Em : K4Means (𝐌) (𝐃)) {Hh : K9.LinkHoles} {l : Link S Claim}
    (hRd : (𝐃).Rd m = K9.readersOfLink Hh l)
    (hruns : (𝐃).runs m 3 "own" = [(2, "front"), (2, "back")])
    {pl : VerifiableInference.Desc.Place} (H : AtK4 links ps k m pl) {lm : ℕ}
    (Kf : K4Front (𝐌) z links ps m (parOf x).P.y.fo lm 0 (LeftQ (parOf x).hp.ns)) {ns : ℕ}
    (hnsD : (𝐃).nsOf m = some ns)
    (hBf : frontB (!(parOf x).k3Runs) (parOf x).P (parOf x).hp (parOf x).g (parOf x).P.y.fo =
      true)
    (left : ∀ a : S × Fr.E.Str, onQ (𝐃).N (𝐌) links ps (fun s => (z, s)) k a →
      a.1.failed = none → lookLeftB a.1 = true)
    (four : ∀ B', SeatOf (ProofFile.k4Block x) B' → ∀ a τ fo o G',
      onQ (𝐃).N (𝐌) links ps (fun s => (z, s)) k a → a.1.failed = none →
      Yes seatS (parOf x) (twinOf q B') a τ fo o G' →
      (∀ o', (behindOf seatS (twinOf q B') a τ o G').1.own? = some o' →
        (parOf x).hp.nU.getD 2 0 ≤ o'.v.K3) ∧
      (∀ A, K9.segAt? (behindOf seatS (twinOf q B') a τ o G').1 = some A →
        (K9.maskSeat ((𝐃).N.sent m 0) A).isSome = true) ∧
      (∀ G o', (behindOf seatS (twinOf q B') a τ o G').1.fork? = some G →
        (behindOf seatS (twinOf q B') a τ o G').1.own? = some o' → oneRowB G o'.v.iU3 = true) ∧
      ∀ A o', K9.segAt? (behindOf seatS (twinOf q B') a τ o G').1 = some A →
        (behindOf seatS (twinOf q B') a τ o G').1.own? = some o' →
        readsThereB A o'.v.iU3 ((parOf x).hp.nU.getD 2 0) = true)
    (st : ∀ s : S, StatesAt (K9.statesOfLink l) 2 (parOf x) "front" s ∧
      StatesAt (K9.statesOfLink l) 2 (parOf x) "back" s)
    (hO : openAllB (𝐃).moreL links ps k m = true)
    (hArr : readsArrayP (parOf x).hp (𝐃).D3.shape (𝐃).D3.layout ((𝐃).D3.arrayOf.getD m #[]) m
      ((𝐃).sd.trees m) = true)
    (hMask : maskPlanB (pinAt (𝐃) xL posI Stored.entries) ((𝐃).N.sent m 0)
      (recPlanOf (𝐃) (𝐃).sd) ((𝐃).N.msgsAt ps[k]?) m = true)
    (hCells : arraysPlanB (pinAt (𝐃) xL posI Stored.entries) (parOf x).hp.tl ((𝐃).N.sent m 0)
      (recPlanOf (𝐃) (𝐃).sd) ((𝐃).N.msgsAt ps[k]?) m = true)
    (hell : xL.ns ≤ maskEllP (pinAt (𝐃) xL posI Stored.entries))
    (hsits : SitsIn (sigListCalls (sentOf (𝐃)) (𝐃).L3.rad xL.link)
      (fun j => (𝐃).L3.seat xL.link false j.1) (𝐃).ms (𝐃).N m)
    (hcov : Covers (parOf x).hp.tl nM nRr nC)
    (hl : xL.link = m) (hs : xL.ns = (parOf x).hp.ns) (huL : 𝔇.uL = uLAt X (namesOf 𝔇.built))
    (htl : tlAt X m = some (parOf x).hp.tl) :
    ∀ B', SeatOf (ProofFile.k4Block x) B' → ∀ b w,
      ((qkAt (𝐃) (parOf x) m xL posI Stored.entries nM nRr nC nx v7 hg).lettersOf (Fr := Fr)
        (partOf (sentOf (𝐃)).codes (𝐃).arr (𝐃).ms (𝐃).N m) (parOf x) 0 (parOf x).P.y.fo
        (LeftQ (parOf x).hp.ns) (tableOn0 (𝐃).N (𝐌) z links ps k)
        (keptFrom (tableOn0 (𝐃).N (𝐌) z links ps k) (parOf x) (twinOf q B'))
        (tableCtx0 (𝐃).N (𝐌) z m)
        (decOf (sentOf (𝐃)).codes (𝐃).G (𝐃).smp (𝐃).ms (𝐃).decT (𝐃).N z m)).on' b →
      onQ (𝐃).N (𝐌) links ps (fun s => (z, s)) (k + 1) b → b.1.failed = none →
      meansQ (Fr := Fr) (𝐃).N (𝐌) (fun s => (z, s)) (.formsT m 3 "own") b w →
      FormsT seatS ((qkAt (𝐃) (parOf x) m xL posI Stored.entries nM nRr nC nx v7 hg).semOf
        (partOf (sentOf (𝐃)).codes (𝐃).arr (𝐃).ms (𝐃).N m) (parOf x).hp.tl)
        (frontRun (parOf x)) formsBack b.1 w := by
  intro B' hB b w hon
  have asks := Riders.asks_of_means (q := twinOf q B') (par := parOf x) Em H Kf rfl hnsD hBf left
    (four B' hB) st
  exact forms_pins (pinAt (𝐃) xL posI Stored.entries) xL.ns (pubAt X (m / stepOf X)).y nM nRr nC
    (Forest.elems X.layers.y.fo) (parOf x).hp.ns nx v7 hg Em hRd hruns rfl rfl asks hO hArr hMask
    hCells hell hsits hcov (hns_of_front H Kf (Nat.le_of_eq hs.symm))
    (hSt_built 𝔇 E Mg₀ (pinAt (𝐃) xL posI Stored.entries) Em huL rfl hl hO
      (fun a τ fo o G' ha hu Y => by
        obtain ⟨_, _, As, _⟩ := asks a τ fo o G' ha hu Y
        exact As.sized)
      htl hCells) b w hon

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.forms_wide
