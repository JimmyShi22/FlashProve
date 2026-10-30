-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Plain/K04Plain.lean: K04_law, THE LAW OF THE LAYERS' OWN ROUNDS (the kind K4), STATED
IN THE PLAIN FORM: written APART from the first road: from the words of the
table of joints' row at K4's place and from K4's own text alone (Johnson/Desc/First/K4/Block.lean;
OnBytes/Desc/First/K4/: Engine, Rounds, Hear, Claims, Plain, Steps).

THE TABLE's ROW (a layers' segment m, piece 3): closes: constr m idn · worth m 2 "planes" | "keys" |
"rider"; opens: formsT m 3 "own" · formsT m 2 "planes" | "join" · wo m; reads and leaves open: pin m
0 · pinW · constr m small · pinI; lays nothing.
SO THE LAW IS AT ONE WORLD (`KeepsW`, Johnson/Desc/Plain/World.lean): but for the piece's errors, at
every yes of the block bk that rides at K4's place: the promise behind is kept, and FOR EVERY WORLD
w: if what the row opens holds of (the statement behind, w), what it closes holds of (the statement
in front, w).

WHAT IS A NAMED TERM HERE, AND WHAT A LETTER.
  NAMED: `FormsT`: what "every form behind a run has the value 0, the reads read as true" SAYS, over
    K4's own runs (`formsFrontNoRows`, `formsBack`: OnBytes/Desc/First/K4/Plain.lean; group 1, the
    lookup's own, is left out at either value of `k3Runs`) and the library's own value of a form
    (`Aff.value`, `Fork.worldOf`, `Reading.gl`: OnBytes/Model/HideLaws.lean): the hidden value under
    slot j is vp[j] - mf[j] * mask[j].
  LETTERS, each left open here: `Sem.mask` (the world's mask row) · `Sem.entryT` (THE TRUE
    VALUE of entry i of virtual row r of array t: for the reads: the stated function of the world's
    cells at the points that were heard: what the item "tie" says of the committed reads) ·
    `Letters`: ctx (the three pins) · idn · the three "worth" · wo · the two promises.
FIVE CHOICES IN `FormsT`, EACH MADE AGAINST AN ATTACK.
  (1) "THERE IS a list that the run returns, and each of its forms is 0", NOT "for every list that
      the run returns": where the run would refuse, the second is true for nothing: what the row
      opens would hold for nothing, and the law would be false (`formsT_refused`).
  (2) THE VALUE IS READ AT THE LEDGER BEHIND THE RUN (F'), not at the border's: a run lays the
      hiding coefficients of a sumcheck under their slots where its claim is made: the forms name
      slots that the border's ledger does not hold yet.
  (3) THE READS ARE READ AS TRUE (`entryT`), not as committed: they are committed behind the
      stretch. A masked sumcheck's count wants its start form's value fixed before its first draw.
      BY READING K4's TEXT: only ONE of its seven sumchecks has a start form that can name a read
      (the batched one: `joinStart`: the only routine of HEAR that is handed the forms'
      environment), and every table that it names stands at the LOOKUP's two points ("Z", "zt"),
      heard in front of K4's whole stretch (read whole for this: OnBytes/Model/LayerForms.lean from
      `ewOf` to `joinPart`: `line` and its helpers pass no other point's name; of `joinStart`'s
      other terms KT is a form in slots alone, and cEnd is the lookup's own form, made in front of
      the stretch). So at true reads that value is fixed in time. BY READING; NO LEMMA SAYS IT.
  (4) EVERY SLOT AND ENTRY THAT A FORM NAMES IS THERE AT THE LEDGER (`thereAt`: a public Bool off
      the ledger's own marks): else a form could be worth 0 by silent zeros. (5) THE SECOND RUN
      STARTS FROM THE LEDGER THAT THE FIRST LEAVES, as in the file: said side by side from one
      ledger, the item that K4 delivers need not be the item that the adding spends. (By reading: no
      form of "back" names a slot that "front" lays: so (5) turns no value; it is said so that
      nobody has to know that.)
  `K04Law`: THE STATEMENT. `K04LawAt`: the same with the world's pinned part m OUTSIDE the game (the
    form in which the library's typed chains have their knowledge soundness).
  `k04LawAt_of_part` (proved): the congruence that `K04LawAt` wants of `part`, said: the part holds
    all that the two sides read of w.
  `HearsAs`, `hearsAs_block`, `hearsAs_of_yes` (proved): what a yes of the block at K4's place
    gives; K4's own block at its own seat meets it; it passes to every block whose yes is a yes of
    such a block with the same record behind, at whatever type of claims.
  `k04_of_at` (proved): `K04LawAt` and A PIN (what the row opens fixes the part of w as a function
    of the statement in front) give `K04Law`, at the same errors.
WHAT ONE MAY TRY, AND WHAT IS FOUND. Yes to all: such a bk does not meet `HearsAs`: the
law holds of it for nothing: what shuts it out is the member at the term that rides. No to all:
meets it for nothing. on := false; errors := all challenges: empty, as every `Leads`. Words not
below the prime: K4's "coin-zero" passes (p, 0, 0), whose inverse is 0: SO THE PIECE MUST HOLD
`below bk` (hb), bk the block that rides at K4's place, under `HearsAs`. "back" runs, in the file,
from a ledger that another kind's run (the smallness test's) has turned in between: here it is said
at the border's own ledger: A FRAME LAW OF THE LEDGER's IS OWED BY WHOEVER MOVES IT. N.B. the three
items formsT "own" | "planes" | "join" are said here TOGETHER, as the two runs' whole lists. ctx:
pin m 0 · pinW · constr m small · pinI: a letter.
Limits. A STATEMENT WITH LETTERS: not closed. L : Seat S, par, THE BLOCK bk, THE CLAIMS' TYPE Cl AND
ALL OF THE PIECE pc BUT ITS BLOCK ARE FREE: the seat's two laws and the block's test on the plan are
asked nowhere here (whoever proves toward it has both as premises and would lay them in `on`); a run
that returns the empty list meets `AllZero` for nothing. No count is named: the errors are the
piece's. Nothing says that the letters can be met together.

-/
import Johnson.Desc.Plain.Pinned
import Johnson.Desc.Sound.ChainRule
import Johnson.Desc.Sound.FoldHeardProofs
import Johnson.Desc.First.K4.Block
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Plain.K04
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4 (Seat Par block formsFrontNoRows formsBack hearAt hearFl fitsAll rounds
    entries
  rowsTabled)
open OnBytes.K.Kc (paired)
open VerifiableInference.Desc (bindOk)
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc.Sound

abbrev GE : Type := Cb.Gl.E

/-- What the law reads of a world. -/
structure Sem (Wt : Type) where
  /-- the sub-proof's mask row, entry by entry -/
  mask : Wt → ℕ → GE
  /-- THE TRUE VALUE of entry i of virtual row r of array t, at what was heard -/
  entryT : Own → Wt → ℕ → ℕ → ℕ → GE

variable {S Wt Cl : Type} (L : Seat S) (Sm : Sem Wt)

/-- **A PUBLIC BOOL: every slot and every entry that the form names is there at the ledger**: under
each slot a hidden value has been put (the ledger's own mark `gotF`); each entry is one that the
arrays have: THE LIBRARY's PROGRAM's OWN TEST `Fork.hasEnt` (OnBytes/Model/Hide.lean: the array, the
virtual row, the index inside the columns that the row holds): what `pushEnt` asks when the claim is
ADDED: so the item that K4 delivers names just what the adding can take. WITHOUT IT A FORM COULD BE
"WORTH 0" BY SILENT ZEROS: `Fork.worldOf` reads 0 at a slot that is not filled, without a word. -/
def thereAt (F' : Fork) (f : Aff) : Bool :=
  (f.slots.all fun x => F'.gotF.getD x.1 false) && f.ents.all (Fork.hasEnt F'.trees)

/-- **The same for the two runs, WITHOUT A WORLD: computable: for a promise**: the two runs return,
and every form of theirs is there at its ledger. -/
def runsThere (run₁ run₂ : Own → Fork → Option (Array Aff × Fork)) (o : Own) (F₀ : Fork) : Bool :=
  match run₁ o F₀ with
  | none => false
  | some (fs₁, F₁) =>
    match run₂ o F₁ with
    | none => false
    | some (fs₂, F₂) => fs₁.all (thereAt F₁) && fs₂.all (thereAt F₂)

/-- The forms of one list: each is there at the ledger, and has the value 0, the reads read as true.
-/
def AllZero (o : Own) (fs : Array Aff) (F' : Fork) (w : Wt) : Prop :=
  ∀ f ∈ fs.toList, thereAt F' f = true ∧
    Aff.value Reading.gl (F'.worldOf Reading.gl (Sm.mask w) (Sm.entryT o w)) f = 0

/-- **Every form behind the two runs has the value 0, the reads read as true.** THE SECOND RUN
STARTS FROM THE LEDGER THAT THE FIRST LEAVES, as in the file. -/
def FormsT (run₁ run₂ : Own → Fork → Option (Array Aff × Fork)) (s : S) (w : Wt) : Prop :=
  ∃ o fs₁ F₁ fs₂ F₂, L.own s = some o ∧ run₁ o (L.fork s) = some (fs₁, F₁) ∧
    run₂ o F₁ = some (fs₂, F₂) ∧ AllZero Sm o fs₁ F₁ w ∧ AllZero Sm o fs₂ F₂ w

/-- Where the first run refuses, the item is FALSE, not free. -/
theorem formsT_refused (run₁ run₂ : Own → Fork → Option (Array Aff × Fork)) (s : S) (w : Wt)
    (h : ∀ o, L.own s = some o → run₁ o (L.fork s) = none) : ¬ FormsT L Sm run₁ run₂ s w := by
  rintro ⟨o, fs₁, F₁, fs₂, F₂, ho, hr, -⟩
  rw [h o ho] at hr
  cases hr

/-- K4's first run at a place, WITHOUT THE LOOKUP's OWN CLAIMS (the format's group 1, "objects"):
K4's row neither opens nor reads these, whoever states them (`Par.k3Runs`): with them the row would
not join. -/
def frontRun (par : Par) : Own → Fork → Option (Array Aff × Fork) :=
  formsFrontNoRows par.P par.g

/-- **WHAT A YES OF THE BLOCK AT K4's PLACE GIVES**: what a yes of K4's own block at the seat L
gives: nothing is owed in front; the table of rounds fits; the strict reading; what the lookup
returned is there; the hearing goes on, uses the stretch up, and the record behind is the record in
front with the ledger, what was heard and "nothing owed" laid by L. WHY A PREMISE AND NOT "bk =
block L par": at the first chain's own record K4's block rides LIFTED from its part
(`Block.liftPart`), and no seat at that record makes the two blocks one function: they refuse under
other names. -/
def HearsAs (par : Par) (bk : Block S Cl) : Prop :=
  ∀ s rs cols s', bk.decide s rs cols = .ok s' →
    (L.owed s).isNone = true ∧
    fitsAll (rounds par.P par.hp par.g) (entries par.P par.hp par.g) rs = true ∧
    OnBytes.Desc.First.Kit.plainStretchWith rowsTabled (entries par.P par.hp par.g) rs = true ∧
    ∃ fo o G, L.look s = some fo ∧
      hearFl { par.P with tokv := L.tokv s } par.hp par.g fo (L.fork s)
        (paired rs (entries par.P par.hp par.g)) = some (o, G, []) ∧
      s' = L.setOwed (L.setOwn (L.setFork s G) o) none

/-- **It passes to every block whose yes is a yes of bk with the same record behind**, at whatever
type of claims: so to bk laid bare, under another name, or with a further test behind its decision.
-/
theorem hearsAs_of_yes {Cl' : Type} (par : Par) (bk : Block S Cl) (bk' : Block S Cl')
    (hy : ∀ s rs cols s', bk'.decide s rs cols = .ok s' → bk.decide s rs cols = .ok s')
    (h : HearsAs L par bk) : HearsAs L par bk' :=
  fun s rs cols s' hd => h s rs cols s' (hy s rs cols s' hd)

/-- **It is met by K4's own block at its own seat.** -/
theorem hearsAs_block (par : Par) : HearsAs L par (block L par) := by
  intro s rs cols s' hd
  have needOk : ∀ {n : String} {b : Bool} {u : Unit},
      VerifiableInference.Desc.need n b = .ok u → b = true := by
    intro n b u h
    cases b with
    | true => rfl
    | false => exact nomatch h
  have namedOk : ∀ {n : String} {x : Option Forest.Heard} {y : Forest.Heard},
      VerifiableInference.Desc.named n x = .ok y → x = some y := by
    intro n x y h
    cases x with
    | none => exact nomatch h
    | some z => exact congrArg some (Except.ok.inj h)
  have hd' : hearAt L par s rs = .ok s' := hd
  unfold hearAt at hd'
  obtain ⟨_, h1, hd'⟩ := bindOk hd'
  obtain ⟨_, h2, hd'⟩ := bindOk hd'
  obtain ⟨_, h3, hd'⟩ := bindOk hd'
  obtain ⟨fo, h4, hd'⟩ := bindOk hd'
  split at hd'
  · rename_i o G he
    exact ⟨needOk h1, needOk h2, needOk h3, fo, o, G, namedOk h4, he, (Except.ok.inj hd').symm⟩
  · exact nomatch hd'
  · exact nomatch hd'

/-- The letters of the row that are filled elsewhere. -/
structure Letters (S Wt : Type) (F : Frame) where
  /-- the promises in front and behind -/
  on : S × F.E.Str → Prop
  on' : S × F.E.Str → Prop
  /-- pin m 0 · pinW · constr m small · pinI -/
  ctx : S × F.E.Str → Wt → Prop
  /-- constr m idn: the layers' identities hold of the world's cells and weights -/
  idn : S × F.E.Str → Wt → Prop
  /-- worth m 2 "planes" | "keys" | "rider": at the points that the lookup has heard -/
  worthPlanes : S × F.E.Str → Wt → Prop
  worthKeys : S × F.E.Str → Wt → Prop
  worthRider : S × F.E.Str → Wt → Prop
  /-- wo m: what the own rounds leave for the row on the weights -/
  wo : S × F.E.Str → Wt → Prop

variable {F : Frame} (Lt : Letters S Wt F)

/-- What the row closes, with what it reads. -/
def Front (a : S × F.E.Str) (w : Wt) : Prop :=
  Lt.ctx a w ∧ Lt.idn a w ∧ Lt.worthPlanes a w ∧ Lt.worthKeys a w ∧ Lt.worthRider a w

/-- What the row opens, with what it reads. -/
def Behind (par : Par) (b : S × F.E.Str) (w : Wt) : Prop :=
  Lt.ctx b w ∧ FormsT L Sm (frontRun par) formsBack b.1 w ∧ Lt.wo b w

/-- **K04_law, IN THE PLAIN FORM.** pc: the piece at K4's place. bk: THE BLOCK THAT RIDES THERE, A
LETTER: the piece holds it with the test "every word is below the prime" in front; of bk the law
reads only WHAT ITS YES GIVES (`HearsAs`). Cl, THE TYPE OF A CLAIM, IS A LETTER TOO: a seat may lay
K4's block bare, at another type of claims than K4's own forms. -/
def K04Law (par : Par) (bk : Block S Cl) (pc : Piece (ckP .two) F S Cl Wt) : Prop :=
  pc.b = below bk → HearsAs L par bk →
    pc.ior.red.KeepsW Lt.on Lt.on' (Front Lt) (Behind L Sm Lt par) pc.err

/-- The same with the world's pinned part OUTSIDE the game. -/
def K04LawAt {Mm : Type} (part : Wt → Mm) (par : Par) (bk : Block S Cl)
    (pc : Piece (ckP .two) F S Cl Wt) : Prop :=
  pc.b = below bk → HearsAs L par bk →
    ∀ m : Mm, pc.ior.red.Leads Lt.on
      (fun a b => Lt.on' b ∧ ∀ w, part w = m → Behind L Sm Lt par b w → Front Lt a w) pc.err

/-- **From the world outside the game to K04_law, by a pin**: at the same errors. -/
theorem k04_of_at {Mm : Type} (part : Wt → Mm) (mOf : S × F.E.Str → Mm) (par : Par)
    (bk : Block S Cl) (pc : Piece (ckP .two) F S Cl Wt) (h : K04LawAt L Sm Lt part par bk pc)
    (pin : ∀ a τ b w, Lt.on a → pc.ior.red.out a τ = some b → Lt.ctx b w → part w = mOf a) :
    K04Law L Sm Lt par bk pc := fun hb hh =>
  Reduction.keepsW_of_pinned part mOf (h hb hh) fun a τ b w ha hout hw => pin a τ b w ha hout hw.1

/-- **From a law on the part alone to `K04LawAt`: THE CONGRUENCE THAT IT WANTS, SAID**: what the row
opens gives BM OF THE PART of w, and FM of the part of w gives what the row closes: so the part
holds all that the two sides read of w. Then a law "for every m: BM b m gives FM a m" (the form in
which a typed chain has its knowledge soundness) is `K04LawAt`, at the same errors. -/
theorem k04LawAt_of_part {Mm : Type} (part : Wt → Mm) (par : Par) (bk : Block S Cl)
    (pc : Piece (ckP .two) F S Cl Wt) (BM FM : S × F.E.Str → Mm → Prop)
    (hB : ∀ b w, Behind L Sm Lt par b w → BM b (part w))
    (hF : ∀ a w, FM a (part w) → Front Lt a w)
    (h : pc.b = below bk → HearsAs L par bk →
      ∀ m : Mm, pc.ior.red.Leads Lt.on (fun a b => Lt.on' b ∧ (BM b m → FM a m)) pc.err) :
    K04LawAt L Sm Lt part par bk pc := fun hb hh m a ha =>
  _root_.Iop.Doomed.mono _ _ (fun _ hτ b hout =>
    ⟨(hτ b hout).1, fun w hw hBw => hF a w (hw ▸ (hτ b hout).2 (hw ▸ hB b w hBw))⟩) (h hb hh m a ha)

end VerifiableInference.Desc.Plain.K04

#print axioms VerifiableInference.Desc.Plain.K04.hearsAs_of_yes
#print axioms VerifiableInference.Desc.Plain.K04.hearsAs_block
#print axioms VerifiableInference.Desc.Plain.K04.k04LawAt_of_part
#print axioms VerifiableInference.Desc.Plain.K04.formsT_refused
#print axioms VerifiableInference.Desc.Plain.K04.k04_of_at
