-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngCalls.lean: the range reduction with one lookup argument for each call (definitions).

Hidden: the index (the committed matrix W). To be shown: every looked-up value (key in Lean names)
of every call of a lookup plan is in its table (`Plan.KeysAll`, Blocks/RngPlan.lean). A plan is a
list of calls. The keys of call f are affine functions of the columns of W (an offset plus a public
matrix times the column), and its table is {0, .., 2^(d f) - 1}. For a valid plan this says that W
is valid. The reduction ends in one linear claim on (η, η⁰, bit, RA) and in one index claim on W;
Blocks/RngCallsFront.lean gives its tracking data (words of this library: lean/GLOSSARY.md).

The protocol (the lookup argument and its steps: Blocks/LookupStage.lean):
  1, 2   the prover sends the pad vectors η (the pads of all masked scalars of the calls and of step
         10) and η⁰ (one pad for each call);
  3      it sends the vector `bit` over F, the bits of the multiplicities of all calls;
  4      the list of deferred claims starts empty;
  5, 6   for each call f in turn: steps 1 to 4 of its lookup argument, with its own challenge α_f
         (`Lk.st14`); then, for each call in turn, the point of its degree check (`Lk.st5`);
  7      in one message, for each call the masked scalar s_f = t_f + η⁰_f, where t_f = ⟨G_f(z_f) ⊗
         eq(ψ(z_f), ·), W⟩ is the hidden part of the end value of the call's key side (the product
         trees over its keys; the end value is the public part minus t_f);
  7a, 8  it sends the vector RA, the arrays of the root tests of all calls; then, for each call in
         turn, its root test on its arrays in RA (`Lk.st6r`, Blocks/LookupRA.lean);
  9, 10  four claims LIN for each call are added to the list, and the closing block
         (Blocks/ClosingStage.lean) turns all deferred claims of all calls into one linear claim;
  11     it sends the pad vector η¹ and the verifier one coefficient for each call; the merge of the
         index claims (Blocks/MergeStage.lean), a masked sumcheck over the column variables,
         combines the claims t_f = s_f - η⁰_f of all calls into one.

Main names: `Par` (the parameters), `Par.OK` (what is asked of them), `Par.core` (the protocol),
`Par.stage` (the protocol with errors and simulator, Blocks/Stage.lean), `Par.c0` and `Par.cEnd`
(the relations before and after), `Spec.props_stage` (the statement; proof:
Blocks/RngCallsProps.lean).

This file follows the implementation (its one-time range file): one lookup argument for each call,
each table with its own size, the three passes over the calls (steps 5, 6 and 8) in the order above,
`bit` over F and RA as committed vectors with the implementation's placement of entries, and padding
keys not counted in the multiplicities. The order of the rounds in the last layer over the keys and
the coordinates of its end point at which the verifier rejects 0 are parameters (`ordK`, `zf`), so
that an instance can take the implementation's.

This file's model is not the released programs' (lean/LIMITS.md, L1); how the released programs do
it: docs/format/FORMAT.md.
In this model:
 * The deferred claims are turned into one linear claim. The reduction ends in that claim and
   contains no sub-protocol that proves it.
 * Consecutive verifier messages are separate rounds. The key side and the table side of a call come
   one after the other.
 * Which row of W is in which call is a matter of the plan, so of the instance.
The implementation's verifier also rejects a round challenge 1, a coefficient 0 on a pad entry and a
leading coefficient 0, and its committer stops at every sampled 0 (α_f and the merge's coefficients
among them); this verifier rejects a sampled 0 only at the flagged coordinates: those by which a
later step divides, and those that `zf` selects; whether it holds of the released programs is not
known. The list of differences is complete only as far as the comparison of the one-time test's own
steps goes.

Notation: the fields of a plan (`Plan`, Blocks/RngPlan.lean), natural numbers unless a type is
given: `h`, `k`: the matrix W has h rows and 2^k columns; `nc`: number of calls; `D`, `B`: the key
hypercube has D coordinates, the last B of which are the class; `lp`: a multiplicity has 2^lp bits;
`d : ℕ → ℕ`, `off : ℕ → ℕ → F`, `Γ : ℕ → ℕ → ℕ → F`: call f has the table {0, .., 2^(d f) - 1},
offsets off f and the matrix Γ f. z_f: the end point of the key side of call f; G_f, ψ: g and ψ of
the index claim of call f, from the end point z_f (`Par.gpsi`; `Plan.gAll`, `Plan.psi`,
Blocks/RngForest.lean). `NT`, `Pm`, `gT` (`LkPar`, Blocks/LookupRel.lean): the keys come in NT
batches (trees); the number of the highest plane, `2 ^ lp - 1`; the number of variables of the
leaves of the table side.
Limits: the properties are not proved here but in Blocks/RngCallsProps.lean.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Blocks.RngCallsPlan
import Blocks.RngForms
import Blocks.LookupStage
import Blocks.LookupFacts
import Blocks.ClosingStage
import Blocks.MergeStage
import Blocks.HLed
import Blocks.StageMap
import Blocks.StageRep
import Blocks.LookupRA
import Blocks.LookupPush
import Blocks.TablePlace
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks.RngC

open Iop Prob Finset Alg
open Blocks.Rng (Plan pre pick)
open scoped ENNReal

abbrev Mat (F : Type) : Type := ℕ → ℕ → F

/-- The parameters: a plan; the codes and numbers of positions of the pad vector η, of the pad
vector η⁰ of the masked scalars s_f, of bit (cut into rowsB rows), of the vector RA of the arrays of
the root tests (rowsA rows), and of the pad vector η¹ of the merge of the index claims; two choices
in the key side of a call. -/
structure Par (F : Type) where
  plan : Plan F
  Cη : Code.Enc F
  qη : ℕ
  C0 : Code.Enc F
  q0 : ℕ
  Cb : Code.Enc F
  rowsB : ℕ
  /-- bit is a table of 2^lgR rows, cut into code rows by tB (Blocks/TablePlace.lean) -/
  lgR : ℕ
  tB : TPl
  mrowB : ℕ
  qb : ℕ
  CA : Code.Enc F
  rowsA : ℕ
  mrowA : ℕ
  qA : ℕ
  C1 : Code.Enc F
  q1 : ℕ
  /-- the number of covered row places of call f: the keys at the row places from cov f on are
  padding (public; the verifier puts the factor of the padding keys into the root equation) -/
  cov : ℕ → ℕ
  /-- the order in which the rounds of the last layer of the key side of every call bind its
  variables, and the coordinates of its end point at which the verifier rejects 0
  (Blocks/LookupRel.lean: LkPar.ordK, LkPar.zf) -/
  ordK : List ℕ
  /-- Any zf is sound here (`Par.OK` asks nothing of it; soundness: `Spec.props_stage`, under its
  hypotheses): nothing after a call divides by a coordinate of its end point, and the end claim is
  recovered without its premise (END and its premise: the head of Blocks/LookupBlock.lean) from the
  deferred LIN and the index claim. -/
  zf : ℕ → Bool
  [neη : Nonempty (Fin Cη.n)]
  [ne0 : Nonempty (Fin C0.n)]
  [neb : Nonempty (Fin Cb.n)]
  [neA : Nonempty (Fin CA.n)]
  [ne1 : Nonempty (Fin C1.n)]

attribute [instance] Par.neη Par.ne0 Par.neb Par.neA Par.ne1

/-- The explicit part while the calls run: the one list of deferred claims; for each call the
explicit part of its lookup argument (whose own field "led" is not read: the list is the common
one); the masked scalars s_f. -/
structure XL (N E : Type) where
  led : Ledger N E
  c : ℕ → LkX N E
  s : ℕ → E

/-- The honest prover's state while the calls run: the matrix; its copy of the list of deferred
claims; for each call the state of its lookup argument (whose own field "hl" is not read). -/
structure IL (F E : Type) where
  W : Mat F
  hl : HLed E
  a : ℕ → LkA E

namespace XL
variable {N E : Type}
/-- what the lookup argument of call f sees -/
def get (x : XL N E) (f : ℕ) : LkX N E := { x.c f with led := x.led }
/-- what it leaves -/
def put (x : XL N E) (f : ℕ) (xo : LkX N E) : XL N E := ⟨xo.led, Function.update x.c f xo, x.s⟩
/-- all forms carried along a map of entries -/
def push {N' : Type} [Fintype N] [DecidableEq N'] [CommRing E] (σ : N → N') (x : XL N E) :
    XL N' E :=
  ⟨x.led.push σ, fun f => (x.c f).push σ, x.s⟩
end XL

namespace IL
variable {F E : Type}
def get (s : IL F E) (f : ℕ) : LkA E := { s.a f with hl := s.hl }
def put (s : IL F E) (f : ℕ) (so : LkA E) : IL F E := ⟨s.W, so.hl, Function.update s.a f so⟩
end IL

namespace Par

variable {F : Type} [Field F] (G : Par F) (E : Type) [Field E] [NeZero (2 : E)] [Fintype E]
  [DecidableEq E] [Algebra F E]

/-! ## Pads, vectors, entries -/

/-- the pads of η and η⁰: first those of η -/
abbrev P0 : Type := Fin (G.Cη.msg + G.C0.msg)
/-- all pads: also those of η¹ -/
abbrev Pd : Type := G.P0 ⊕ Fin G.C1.msg

def iη : Fin G.Cη.msg → G.P0 := Fin.castAdd G.C0.msg
def i0 : Fin G.C0.msg → G.P0 := Fin.natAdd G.Cη.msg

/-- the round in which bit is sent: one vector over F -/
abbrev rBit : Round :=
  vRoundK E F Unit (fun _ => true) (fun _ => G.rowsB) (fun _ => G.Cb.msg) Empty Unit

/-- bit is a tested vector under the code Cb -/
def eBit : REnc F E (G.rBit E) :=
  REnc.ofVK E Unit (fun _ => true) (fun _ => G.Cb) (fun _ => G.rowsB) (fun _ => G.mrowB)
    (fun _ => Role.tested) (fun _ => G.qb) Empty Unit

abbrev s0 : Sorts := ⟨Unit, Mat F, Mat F⟩
abbrev s1 : Sorts := ⟨Unit, Mat F × (Fin G.Cη.msg → E), Mat F⟩
abbrev s2 : Sorts := ⟨Unit, (Mat F × (Fin G.Cη.msg → E)) × (Fin G.C0.msg → E), Mat F⟩

/-- the implicit part from step 3 until RA is sent: the matrix, η, η⁰, bit -/
abbrev Y1 : Type := ((Mat F × (Fin G.Cη.msg → E)) × (Fin G.C0.msg → E)) × (G.rBit E).Orc
abbrev s3 : Sorts := ⟨Unit, G.Y1 E, Mat F⟩

def rd0 : Reads F E (s0 (F := F)) := Reads.start F E Unit (Mat F)
def rd1 : Reads F E (G.s1 E) := Stage.readsPads G.Cη.msg (rd0 E)
def rd2 : Reads F E (G.s2 E) := Stage.readsPads G.C0.msg (G.rd1 E)
def rd3 : Reads F E (G.s3 E) := Stage.readsName (G.eBit E) (G.rd2 E)

/-- the entries of η, η⁰ and bit -/
abbrev N1 : Type :=
  ((Empty ⊕ Fin G.Cη.msg) ⊕ Fin G.C0.msg) ⊕ (Σ _ : Unit, Fin G.rowsB × Fin G.Cb.msg)

def proj1 (y : G.Y1 E) : G.N1 → E := (G.rd3 E).rd y

/-- the entry at which a pad is -/
def place1 (p : G.P0) : G.N1 :=
  Fin.addCases (fun j => .inl (.inl (.inr j))) (fun j => .inl (.inr j)) p

/-- the form that reads entry number x of bit (as one sequence) -/
def ent1 (x : ℕ) : Form G.N1 E :=
  if h : x / G.Cb.msg < G.rowsB ∧ 0 < G.Cb.msg then
    Form.ent (.inr ⟨(), ⟨x / G.Cb.msg, h.1⟩, ⟨x % G.Cb.msg, Nat.mod_lt _ h.2⟩⟩)
  else 0

/-- the round in which RA is sent: one vector over E -/
abbrev rRA : Round := vRound E Unit (fun _ => G.rowsA) (fun _ => G.CA.msg) Empty Unit

/-- RA is a tested vector under the code CA -/
def eRA : REnc F E (G.rRA E) :=
  REnc.ofV E Unit (fun _ => G.CA) (fun _ => G.rowsA) (fun _ => G.mrowA) (fun _ => Role.tested)
    (fun _ => G.qA) Empty Unit

/-- The implicit part from RA on: the matrix, η, η⁰, bit, RA. -/
abbrev Y : Type := G.Y1 E × (G.rRA E).Orc

/-- the entries of η, η⁰, bit and RA -/
abbrev N : Type := G.N1 ⊕ (Σ _ : Unit, Fin G.rowsA × Fin G.CA.msg)

def proj (y : G.Y E) : G.N → E := Sum.elim (G.proj1 E y.1) fun q => y.2 q.1 q.2.1 q.2.2

def place (p : G.P0) : G.N := Sum.inl (G.place1 p)

/-- the form that reads entry number x of RA (as one sequence) -/
def entA (x : ℕ) : Form G.N E :=
  if h : x / G.CA.msg < G.rowsA ∧ 0 < G.CA.msg then
    Form.ent (.inr ⟨(), ⟨x / G.CA.msg, h.1⟩, ⟨x % G.CA.msg, Nat.mod_lt _ h.2⟩⟩)
  else 0

/-- RA as one sequence -/
def flatRA (b : (G.rRA E).Orc) (x : ℕ) : E :=
  nat (fun i => nat (fun j => b () i j) (x % G.CA.msg)) (x / G.CA.msg)

/-- bit as one sequence, read in E -/
def flatBit (b : (G.rBit E).Orc) (x : ℕ) : E :=
  nat (fun i => nat (fun j => (b () i j).toE) (x % G.Cb.msg)) (x / G.Cb.msg)

/-! ## One call -/

/-- call f as a plan -/
abbrev pl1 (f : ℕ) : Plan F := G.plan.one f

/-- the number of padding keys in each batch of call f -/
def phi (f : ℕ) : ℕ := (2 ^ (G.plan.D - G.plan.k) - G.cov f) * 2 ^ (G.plan.k - G.plan.B)

/-- The parameters of the lookup argument of call f: 2^B batches of 2^(D - B) keys, of which phi f
are padding keys (the value 0, row 0 of the table) and are not counted in the multiplicities; a
table of 2^(d f) entries. -/
abbrev par (f : ℕ) : LkPar E :=
  { (G.pl1 f).lk E 0 (G.plan.d f) with φ := fun _ => G.phi f, ordK := G.ordK, zf := G.zf }

/-- is key number i of the batch θ of call f a padding key? -/
def padT (f θ i : ℕ) : Bool :=
  decide (G.cov f ≤ (i * 2 ^ G.plan.B + θ % 2 ^ G.plan.B) / 2 ^ G.plan.k)

/-- the number of multiplicity bits of call f -/
def wBit (f : ℕ) : ℕ := 2 ^ (G.par E f).gT

/-- bit is a table of 2^lgR rows, of which call f owns kB f columns, after those of the calls before
it -/
def kB (f : ℕ) : ℕ := 2 ^ ((G.par E f).gT - G.lgR)

/-- Where multiplicity bit number u of call f is in bit, as one number (code row · length +
coordinate): it is cell (r, x) of the columns of the call with u = r · kB f + x, and the table is
cut into code rows by tB. -/
def plcB (f u : ℕ) : ℕ := G.tB.line (u / G.kB E f) (pre (G.kB E) f + u % G.kB E f)

/-- the form that reads multiplicity bit number x of call f in bit; before RA is sent, and after -/
def entC1 (f x : ℕ) : Form G.N1 E := G.ent1 E (G.plcB E f x)
def entC (f x : ℕ) : Form G.N E := Form.push Sum.inl (G.entC1 E f x)

/-- the number of entries of call f in RA: U_π[θ] and V_π[θ] -/
def wRA (f : ℕ) : ℕ := 2 * ((G.par E f).Pm * (G.par E f).NT)

/-- where V_π[θ] and U_π[θ] are in the part of RA that belongs to a call: for π = Pm - 1 down to 0
the NT entries of V_π, then the NT entries of U_π -/
def iV (f π θ : ℕ) : ℕ := ((G.par E f).Pm - 1 - π) * (2 * (G.par E f).NT) + θ
def iU (f π θ : ℕ) : ℕ := ((G.par E f).Pm - 1 - π) * (2 * (G.par E f).NT) + ((G.par E f).NT + θ)

/-- the forms that read U_π[θ] and V_π[θ] of call f in RA -/
def ru (f π θ : ℕ) : Form G.N E := G.entA E (pre (G.wRA E) f + G.iU E f π θ)
def rv (f π θ : ℕ) : Form G.N E := G.entA E (pre (G.wRA E) f + G.iV E f π θ)

/-- The lookup argument of call f, before RA is sent. Its pads are taken from pl f. -/
def lk1 (pl : ℕ → Lk E PUnit G.P0 PUnit) (f : ℕ) : Lk E (G.Y1 E) G.P0 G.N1 where
  par := G.par E f
  proj := G.proj1 E
  place := G.place1
  pZ := (pl f).pZ
  pY := (pl f).pY
  pK := (pl f).pK
  pKv := (pl f).pKv
  pT := (pl f).pT
  pTv := (pl f).pTv
  pL := (pl f).pL
  pLv := (pl f).pLv
  pB := (pl f).pB
  pBv := (pl f).pBv
  pU := (pl f).pU
  pV := (pl f).pV
  pR := (pl f).pR

/-- `lk1` after RA is sent -/
abbrev lk (pl : ℕ → Lk E PUnit G.P0 PUnit) (f : ℕ) : Lk E (G.Y E) G.P0 G.N :=
  (G.lk1 E pl f).up Sum.inl (G.proj E)

/-- The true objects of the lookup argument of call f: the keys of the call, and its part of the
sent bits. -/
def lkT1 (f : ℕ) : Lk.Vecs E (G.Y1 E) where
  key := fun y => (G.pl1 f).keyT y.1.1.1
  B := fun y => (G.par E f).bOf (G.entC1 E f) (G.proj1 E y)

def lkT (f : ℕ) : Lk.Vecs E (G.Y E) where
  key := fun y => (G.pl1 f).keyT y.1.1.1.1
  B := fun y => (G.par E f).bOf (G.entC E f) (G.proj E y)

/-- the public part of the end value of the key side of call f, at the challenge α and the end point
z -/
def cst (f : ℕ) (al : E) (z : ℕ → E) : E := al * (G.pl1 f).pubN 0 z - (G.pl1 f).offAll 0 z

/-- The hidden part of the end value of the key side of call f: t_f = ⟨G_f(z) ⊗
eq(ψ(z), ·), W⟩; the end value is the public part minus t_f. It is sent masked, as s_f. -/
def tval (f : ℕ) (W : Mat F) (z : ℕ → E) : E :=
  ∑ y ∈ range G.plan.h, ∑ c ∈ range (2 ^ G.plan.k),
    (G.pl1 f).gAll 0 z y * eqN G.plan.k 0 ((G.pl1 f).psi 0 z) c * algebraMap F E (W y c)

/-! ## The honest vector bit -/

section Honest

variable [DecidableEq F]

/-- bit π of the number of keys of the batch θ of call f that are no padding keys and equal t -/
def bitN (f : ℕ) (W : Mat F) (t θ π : ℕ) : Bool :=
  ((G.par E f).trueMult (G.padT f) ((G.pl1 f).rowT W) θ t).testBit π

/-- multiplicity bit number u = (i|θ|π) of call f, over F: bit π of the number of keys of the batch
θ of the call that are no padding keys and equal i -/
def bitU (W : Mat F) (f u : ℕ) : F :=
  if G.bitN E f W ((G.par E f).iOf u) ((G.par E f).thOf u) ((G.par E f).piOf u) then 1 else 0

/-- the honest bit, as one sequence, over F: at the index x is the cell (row, column) of the table
that tB puts there; the column belongs to a call f, as its column number xc; the cell is
multiplicity bit number row · kB f + xc of that call -/
def bitFlat (W : Mat F) (x : ℕ) : F :=
  pick (G.kB E) G.plan.nc (fun f xc => G.bitU E W f (G.tB.rowOf x * G.kB E f + xc)) (G.tB.colOf x)

/-- the honest message of step 3 -/
def msgBit (W : Mat F) : (G.rBit E).Orc := fun _ i j => G.bitFlat E W (i.val * G.Cb.msg + j.val)

/-- the first state of the honest prover of the lookup argument of call f -/
def initA (W : Mat F) (f : ℕ) : LkA E :=
  ⟨(G.pl1 f).keyT W,
    fun i θ π => G.flatBit E (G.msgBit E W) (G.plcB E f ((G.par E f).bIdx i θ π)), ⟨0, [], []⟩, 0,
    fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- entry number u of the part of call f in the honest RA, from the state a of its lookup
argument: block number u / (2 NT) holds V_π and then U_π for π = Pm - 1 - u / (2 NT) -/
def raVal (f : ℕ) (a : LkA E) (u : ℕ) : E :=
  if u % (2 * (G.par E f).NT) < (G.par E f).NT then
    (G.par E f).hV ((G.par E f).Yt a.B a.al)
      ((G.par E f).Pm - 1 - u / (2 * (G.par E f).NT)) (u % (2 * (G.par E f).NT))
  else
    (G.par E f).hU ((G.par E f).Yt a.B a.al) ((G.par E f).Pm - 1 - u / (2 * (G.par E f).NT))
      (u % (2 * (G.par E f).NT) - (G.par E f).NT)

/-- the honest RA, as one sequence, call after call -/
def raFlat (s : IL F E) (x : ℕ) : E :=
  pick (G.wRA E) G.plan.nc (fun f u => G.raVal E f (s.a f) u) x

/-- the honest message RA -/
def msgRA (s : IL F E) : (G.rRA E).Orc := fun _ i j =>
  G.raFlat E s (i.val * G.CA.msg + j.val)

end Honest

/-! ## The statement types and the numbers of deferred claims -/

/-- the statement types while the calls run: before RA is sent; when it has been sent; after the
forms have been carried over -/
abbrev sL1 : Sorts := ⟨XL G.N1 E, G.Y1 E, IL F E⟩
abbrev sLa : Sorts := ⟨XL G.N1 E, G.Y E, IL F E⟩
abbrev sL : Sorts := ⟨XL G.N E, G.Y E, IL F E⟩

/-- what steps 1 to 4, and the root test, of call f add to the honest prover's copy of the list:
LIN, opened forms, REL -/
def add14 (f : ℕ) : ℕ × ℕ × ℕ :=
  (2, 2 * ((G.par E f).D + (G.par E f).r + 2), (G.par E f).D + (G.par E f).r + 2)
def add6 (f : ℕ) : ℕ × ℕ × ℕ := (1, 3 * (G.par E f).Pm, 1)

/-- sums of such triples over the calls below k -/
def acc (A : ℕ → ℕ × ℕ × ℕ) (k : ℕ) : ℕ × ℕ × ℕ :=
  (∑ f ∈ range k, (A f).1, ∑ f ∈ range k, (A f).2.1, ∑ f ∈ range k, (A f).2.2)

/-- the numbers of deferred LIN, opened forms and REL at the closing block -/
def nL : ℕ := (acc (G.add14 E) G.plan.nc).1 + (acc (G.add6 E) G.plan.nc).1 + 4 * G.plan.nc
def nO : ℕ := (acc (G.add14 E) G.plan.nc).2.1 + (acc (G.add6 E) G.plan.nc).2.1
def nR : ℕ := (acc (G.add14 E) G.plan.nc).2.2 + (acc (G.add6 E) G.plan.nc).2.2

/-- what is kept for the merge of the index claims: the end points z_f, and the scalars s_f -/
abbrev Keep : Type := (ℕ → ℕ → E) × (ℕ → E)
/-- what the honest prover keeps for the merge: the matrix and the end points -/
abbrev KeepH : Type := Mat F × (ℕ → ℕ → E)

abbrev s5 : Sorts :=
  ⟨Ledger G.N E × Keep E, G.Y E, Closing.HClose E (Fin (G.nR E)) (G.nO E) × KeepH (F := F) E⟩
abbrev s6 : Sorts :=
  ⟨Form G.N E × Keep E, G.Y E, Closing.HClose E (Fin (G.nR E)) (G.nO E) × KeepH (F := F) E⟩

/-! ## The end: the merge of the index claims -/

abbrev Nend : Type := G.N ⊕ Fin G.C1.msg
abbrev Yend : Type := G.Y E × (Fin G.C1.msg → E)
def rdEnd (y : G.Yend E) : G.Nend → E := Sum.elim (G.proj E y.1) y.2
def placeEnd : G.Pd → G.Nend := Sum.map G.place id

/-- The setting of the merge. idxM holds the two pads of each of its rounds. -/
def mg (idxM : Fin G.plan.k → Fin 2 → G.Pd) :
    MG E (G.Yend E) G.Pd (Fin G.plan.h) (Fin G.plan.k) where
  forms := Forms.ofForm (G.rdEnd E) G.placeEnd
  mat := fun y q c => algebraMap F E (y.1.1.1.1.1 q.val (num c))
  idx := idxM

/-- all column variables, in their order -/
def vars : List (Fin G.plan.k) := List.finRange G.plan.k

/-- All pads: for each call the thirteen maps of its lookup argument (of the structure lk f only
these are read); the pads of the closing block; the pad of each scalar s_f; the two pads of each
round of the merge. -/
structure Places where
  lk : ℕ → Lk E PUnit G.P0 PUnit
  cl : Closing.Places G.P0 (Fin (G.nR E)) (G.nO E)
  cr : ℕ → G.P0
  mg : Fin G.plan.k → Fin 2 → G.Pd

/-! ## The protocol -/

section Protocol

variable [DecidableEq F] (pl : G.Places E)

/-- the lookup argument of call f with its pads: before RA is sent, and after -/
abbrev L1 (f : ℕ) : Lk E (G.Y1 E) G.P0 G.N1 := G.lk1 E pl.lk f
abbrev L (f : ℕ) : Lk E (G.Y E) G.P0 G.N := G.lk E pl.lk f

/-- the entries of the pads of the closing block -/
def plN : Closing.Places G.N (Fin (G.nR E)) (G.nO E) :=
  ⟨fun k => G.place (pl.cl.aux k), fun o => G.place (pl.cl.opn o)⟩

def co1 : Core G.P0 E (s0 (F := F)) (G.s1 E) := Core.pads (s0 (F := F)) G.iη
def co2 : Core G.P0 E (G.s1 E) (G.s2 E) := Core.pads (G.s1 E) G.i0
def co3 : Core G.P0 E (G.s2 E) (G.s3 E) :=
  Core.nameVec (G.s2 E) (G.rBit E) (fun e => e.elim) (G.msgBit E)
def co4 : Core G.P0 E (G.s3 E) (G.sL1 E) :=
  Core.pure (fun _ => some ⟨Ledger.empty, fun _ => LkX.init Ledger.empty 0, fun _ => 0⟩)
    id fun W => ⟨W, ⟨0, [], []⟩, G.initA E W⟩

/-- steps 1 to 4 of the lookup argument of call f, on the common list -/
def co14 (f : ℕ) : Core G.P0 E (G.sL1 E) (G.sL1 E) :=
  (G.L1 E pl f).co14.on (a' := G.sL1 E) (b' := G.sL1 E) (fun x => x.led) (fun x xo => x.put f xo) id
    (fun y _ => y) (fun s => s.get f) fun s so => s.put f so

/-- the point of the degree check of call f -/
def co5 (f : ℕ) : Core G.P0 E (G.sL1 E) (G.sL1 E) :=
  (G.L1 E pl f).co5.on (a' := G.sL1 E) (b' := G.sL1 E) (fun x => x.get f) (fun x xo => x.put f xo)
    id (fun y _ => y) (fun s => s.get f) fun s so => s.put f so

/-- the root test of call f, on its arrays in RA -/
def co6 (f : ℕ) : Core G.P0 E (G.sL E) (G.sL E) :=
  ((G.L E pl f).co6r (G.ru E f) (G.rv E f)).on (a' := G.sL E) (b' := G.sL E) (fun x => x.get f)
    (fun x xo => x.put f xo) id (fun y _ => y) (fun s => s.get f) fun s so => s.put f so

/-- the honest values t_f -/
def valS (s : IL F E) (f : Fin G.plan.nc) : E := G.tval E f s.W (s.a f).z

/-- The masked scalars s_f, in one message. -/
def coSc : Core G.P0 E (G.sL1 E) (G.sL1 E) :=
  (Core.nameScalars (E := E) (G.sL1 E) (fun f : Fin G.plan.nc => pl.cr f) (G.valS E)).seq
    (Core.pure (b := G.sL1 E) (fun o => some { o.1 with s := nat o.2 }) id id)

/-- The vector RA: the arrays of the root tests of all calls. -/
def coRA : Core G.P0 E (G.sL1 E) (G.sLa E) :=
  Core.nameVec (G.sL1 E) (G.rRA E) (fun e => e.elim) (G.msgRA E)

/-- the forms of the list and of all calls are carried to the entries with RA -/
def coUp : Core G.P0 E (G.sLa E) (G.sL E) := Core.pure (fun x => some (x.push Sum.inl)) id id

/-- the form s_f - η⁰_f of call f: the scalar minus its pad; before RA is sent, and
after -/
def crForm1 (s : ℕ → E) (f : ℕ) : Form G.N1 E := Form.masked (s f) (G.place1 (pl.cr f))
def crForm (s : ℕ → E) (f : ℕ) : Form G.N E := Form.masked (s f) (G.place (pl.cr f))

/-- The four LIN of call f: the end form of its key side is the public part minus
(s_f - η⁰_f); its two claims on ~bit; its degree claim. -/
def lins1 (x : XL G.N E) (f : ℕ) : List (Form G.N E) :=
  [G.crForm E pl x.s f - (Form.const (G.cst E f (x.c f).al (x.c f).z) - (x.c f).Cend),
    (x.c f).v4 - (G.par E f).bForm (G.entC E f) (x.c f).p4,
    (x.c f).v5 - (G.par E f).bForm (G.entC E f) (x.c f).p5,
    (G.par E f).degForm (G.entC E f) (x.c f).p6]

def lins (x : XL G.N E) : List (Form G.N E) := (List.range G.plan.nc).flatMap (G.lins1 E pl x)

def co7 : Core G.P0 E (G.sL E) (G.s5 E) :=
  Core.pure (fun x => some (x.led.addLins (G.lins E pl x), (fun f => (x.c f).z, x.s))) id
    fun s => (s.hl.toClose (G.nR E) (G.nO E), (s.W, fun f => (s.a f).z))

def co8 : Core G.P0 E (G.s5 E) (G.s6 E) :=
  (Closing.core (E := E) (G.nL E) (G.plN E pl) pl.cl).on (a' := G.s5 E)
    (b' := G.s6 E) (fun x => x.1) (fun x g => (g, x.2)) (G.proj E) (fun y _ => y)
    (fun s => s.1) fun s so => (so, s.2)

/-- Steps 1 to 10, over the pads of η and η⁰. -/
def coA : Core G.P0 E (s0 (F := F)) (G.s6 E) :=
  (G.co1 E).seq
    ((G.co2 E).seq
      ((G.co3 E).seq
        ((G.co4 E).seq
          ((Core.rep (G.co14 E pl) G.plan.nc 0).seq
            ((Core.rep (G.co5 E pl) G.plan.nc 0).seq
              ((G.coSc E pl).seq
                ((G.coRA E).seq
                  ((G.coUp E).seq
                    ((Core.rep (G.co6 E pl) G.plan.nc 0).seq
                      ((G.co7 E pl).seq (G.co8 E pl)))))))))))

/-- the setting of the merge with its pads -/
abbrev M : MG E (G.Yend E) G.Pd (Fin G.plan.h) (Fin G.plan.k) := G.mg E pl.mg

/-- g and ψ of the index claim of call f, from the end point z_f -/
def gpsi (z : ℕ → ℕ → E) (f : ℕ) : (Fin G.plan.h → E) × (Fin G.plan.k → E) :=
  (fun q => (G.pl1 f).gAll 0 (z f) q.val, fun t => (G.pl1 f).psi 0 (z f) t.val)

/-- The index claim of call f: ⟨G_f(z_f) ⊗ eq(ψ(z_f), ·), W⟩ = s_f - η⁰_f. -/
def idxOf (x : Keep E) (f : ℕ) : (G.M E pl).Idx :=
  ⟨(G.gpsi E x.1 f).1, (G.gpsi E x.1 f).2, Form.push Sum.inl (G.crForm E pl x.2 f)⟩

abbrev sEnd : Sorts :=
  ⟨Form G.Nend E × (G.M E pl).Idx, G.Yend E, MG.St2 E (Fin G.plan.h) (Fin G.plan.k)⟩

/-- Step 11: η¹ and the merge. -/
def coM : Core G.Pd E (G.s6 E) (G.sEnd E pl) :=
  ((G.M E pl).coPadsMerge (Fin G.plan.nc) Sum.inr G.vars).on (a' := G.s6 E) (b' := G.sEnd E pl)
    (fun x j => G.idxOf E pl x.2 j) (fun x a => (Form.push Sum.inl x.1, a)) id
    (fun y yo => (y, yo.2))
    (fun s => (fun j => G.gpsi E s.2.2 j, fun q c => algebraMap F E (s.2.1 q.val (num c))))
    fun _ so => so

/-- The range reduction by calls, as one protocol. -/
def core : Core G.Pd E (s0 (F := F)) (G.sEnd E pl) :=
  ((G.coA E pl).mapP Sum.inl).seq (G.coM E pl)

end Protocol

/-! ## The stages -/

section Stages

variable [DecidableEq F] (pl : G.Places E)

def st1 : Stage G.P0 E (s0 (F := F)) (G.s1 E) := Stage.pads (s0 (F := F)) G.iη
def st2 : Stage G.P0 E (G.s1 E) (G.s2 E) := Stage.pads (G.s1 E) G.i0
def st3 : Stage G.P0 E (G.s2 E) (G.s3 E) :=
  Stage.nameVec (G.s2 E) (G.rBit E) (fun e => e.elim) (G.msgBit E)
def st4 : Stage G.P0 E (G.s3 E) (G.sL1 E) :=
  Stage.pure (fun _ => some ⟨Ledger.empty, fun _ => LkX.init Ledger.empty 0, fun _ => 0⟩)
    id fun W => ⟨W, ⟨0, [], []⟩, G.initA E W⟩
def st14 (f : ℕ) : Stage G.P0 E (G.sL1 E) (G.sL1 E) :=
  (G.L1 E pl f).st14.on (a' := G.sL1 E) (b' := G.sL1 E) (fun x => x.led) (fun x xo => x.put f xo) id
    (fun y _ => y) (fun s => s.get f) fun s so => s.put f so
def st5 (f : ℕ) : Stage G.P0 E (G.sL1 E) (G.sL1 E) :=
  (G.L1 E pl f).st5.on (a' := G.sL1 E) (b' := G.sL1 E) (fun x => x.get f) (fun x xo => x.put f xo)
    id (fun y _ => y) (fun s => s.get f) fun s so => s.put f so
def st6 (f : ℕ) : Stage G.P0 E (G.sL E) (G.sL E) :=
  ((G.L E pl f).st6r (G.ru E f) (G.rv E f)).on (a' := G.sL E) (b' := G.sL E) (fun x => x.get f)
    (fun x xo => x.put f xo) id (fun y _ => y) (fun s => s.get f) fun s so => s.put f so
def stSc : Stage G.P0 E (G.sL1 E) (G.sL1 E) :=
  (Stage.nameScalars (E := E) (G.sL1 E) (fun f : Fin G.plan.nc => pl.cr f) (G.valS E)).seq
    (Stage.pure (b := G.sL1 E) (fun o => some { o.1 with s := nat o.2 }) id id)
def stRA : Stage G.P0 E (G.sL1 E) (G.sLa E) :=
  Stage.nameVec (G.sL1 E) (G.rRA E) (fun e => e.elim) (G.msgRA E)
def stUp : Stage G.P0 E (G.sLa E) (G.sL E) :=
  Stage.pure (fun x => some (x.push Sum.inl)) id id
def st7 : Stage G.P0 E (G.sL E) (G.s5 E) :=
  Stage.pure (fun x => some (x.led.addLins (G.lins E pl x), (fun f => (x.c f).z, x.s))) id
    fun s => (s.hl.toClose (G.nR E) (G.nO E), (s.W, fun f => (s.a f).z))
def st8 : Stage G.P0 E (G.s5 E) (G.s6 E) :=
  (Closing.stage (E := E) (G.nL E) (G.plN E pl) pl.cl).on (a' := G.s5 E)
    (b' := G.s6 E) (fun x => x.1) (fun x g => (g, x.2)) (G.proj E) (fun y _ => y)
    (fun s => s.1) fun s so => (so, s.2)

def stA : Stage G.P0 E (s0 (F := F)) (G.s6 E) :=
  (G.st1 E).seq
    ((G.st2 E).seq
      ((G.st3 E).seq
        ((G.st4 E).seq
          ((Stage.rep (G.st14 E pl) G.plan.nc 0).seq
            ((Stage.rep (G.st5 E pl) G.plan.nc 0).seq
              ((G.stSc E pl).seq
                ((G.stRA E).seq
                  ((G.stUp E).seq
                    ((Stage.rep (G.st6 E pl) G.plan.nc 0).seq
                      ((G.st7 E pl).seq (G.st8 E pl)))))))))))

def stM : Stage G.Pd E (G.s6 E) (G.sEnd E pl) :=
  ((G.M E pl).stPadsMerge (Fin G.plan.nc) Sum.inr G.vars).on (a' := G.s6 E) (b' := G.sEnd E pl)
    (fun x j => G.idxOf E pl x.2 j) (fun x a => (Form.push Sum.inl x.1, a)) id
    (fun y yo => (y, yo.2))
    (fun s => (fun j => G.gpsi E s.2.2 j, fun q c => algebraMap F E (s.2.1 q.val (num c))))
    fun _ so => so

/-- The range reduction by calls, as one stage. -/
def stage : Stage G.Pd E (s0 (F := F)) (G.sEnd E pl) :=
  ((G.stA E pl).mapP Sum.inl).seq (G.stM E pl)

theorem toCore_stA : (G.stA E pl).toCore = G.coA E pl := rfl
theorem toCore_stM : (G.stM E pl).toCore = G.coM E pl := rfl
/-- For 2 ≠ 0 in E, the protocol of `stage` is `core`. -/
theorem toCore_stage : (G.stage E pl).toCore = G.core E pl := rfl

end Stages

/-! ## The relations between the stages -/

section Cuts

variable [DecidableEq F] (pl : G.Places E)

/-- the relation of soundness of call f in phase j: 0 before its lookup argument, 1 after steps 1
to 4, 2 after the point of the degree check, 3 after the root test -/
def RAt (j f : ℕ) : LkX G.N1 E → G.Y1 E → Prop :=
  match j with
  | 0 => fun x y => (G.L1 E pl f).R0 (G.lkT1 E f) x.led y
  | 1 => (G.L1 E pl f).R7 (G.lkT1 E f)
  | 2 => (G.L1 E pl f).R8 (G.lkT1 E f)
  | _ => (G.L1 E pl f).R10 (G.lkT1 E f)

/-- the relation of the honest run of call f in phase j -/
def HAt (j f : ℕ) : LkA E → (G.P0 → E) → LkX G.N1 E → G.Y1 E → Prop :=
  match j with
  | 0 => fun a π x y => (G.L1 E pl f).Lnk0 (G.lkT1 E f) (G.L1 E pl f).allPads a π x.led y
  | 1 => (G.L1 E pl f).H7 (G.lkT1 E f) (G.L1 E pl f).allPads
  | 2 => (G.L1 E pl f).H8 (G.lkT1 E f) (G.L1 E pl f).allPads
  | _ => (G.L1 E pl f).H10 (G.lkT1 E f) (G.L1 E pl f).allPads

/-- `RAt` after RA is sent: phase 2 before the root test of the call, 3 after it. For the honest
prover (`HAtR`) RA holds the honest arrays of a call whose root test is still to come. -/
def RAtR (j f : ℕ) : LkX G.N E → G.Y E → Prop :=
  match j with
  | 2 => (G.L E pl f).R8 (G.lkT E f)
  | _ => (G.L E pl f).R10 (G.lkT E f)

def HAtR (j f : ℕ) : LkA E → (G.P0 → E) → LkX G.N E → G.Y E → Prop :=
  match j with
  | 2 =>
    fun a π x y =>
      (G.L E pl f).H8 (G.lkT E f) (G.L E pl f).allPads a π x y ∧
      (G.L E pl f).RAh (G.lkT E f) (G.ru E f) (G.rv E f) x y
  | _ => (G.L E pl f).H10 (G.lkT E f) (G.L E pl f).allPads

/-- in pass j, before its step k: the calls below k are in phase j + 1, the others in phase j -/
def ph (j k f : ℕ) : ℕ := if f < k then j + 1 else j

/-- The masked scalar of call f is the true one: s_f - η⁰_f = t_f at the end point z. -/
def CrOK1 (s : ℕ → E) (z : ℕ → E) (y : G.Y1 E) (f : ℕ) : Prop :=
  Form.val (G.proj1 E y) (G.crForm1 E pl s f) = G.tval E f y.1.1.1 z
def CrOK (s : ℕ → E) (z : ℕ → E) (y : G.Y E) (f : ℕ) : Prop :=
  Form.val (G.proj E y) (G.crForm E pl s f) = G.tval E f y.1.1.1.1 z

/-- how long the honest prover's copy of the list is in pass j before its step k -/
def lenAt (j k : ℕ) : ℕ × ℕ × ℕ :=
  match j with
  | 0 => acc (G.add14 E) k
  | 1 => acc (G.add14 E) G.plan.nc
  | _ =>
    ((acc (G.add14 E) G.plan.nc).1 + (acc (G.add6 E) k).1,
      (acc (G.add14 E) G.plan.nc).2.1 + (acc (G.add6 E) k).2.1,
      (acc (G.add14 E) G.plan.nc).2.2 + (acc (G.add6 E) k).2.2)

/-- The relations in pass j (0: steps 1 to 4; 1: degree points; and (2, 0): before RA) before its
step k. sc says whether the scalars s_f have been sent. -/
def cutL (j k : ℕ) (sc : Bool) : Cut G.P0 E (G.sL1 E) where
  R := fun x y =>
    x.led.True (G.proj1 E y) ∧
    (∀ f, f < G.plan.nc → G.RAt E pl (ph j k f) f (x.get f) y) ∧
    (sc = true → ∀ f, f < G.plan.nc → G.CrOK1 E pl x.s (x.c f).z y f)
  Hn := fun s π x y =>
    (s.W = y.1.1.1 ∧
      (∀ p, G.proj1 E y (G.place1 p) = π p) ∧
      s.hl.Good x.led (G.proj1 E y) ∧
      s.hl.len = G.lenAt E j k) ∧
    (∀ f, f < G.plan.nc → G.HAt E pl (ph j k f) f (s.get f) π (x.get f) y) ∧
    (sc = true → ∀ f, f < G.plan.nc → G.CrOK1 E pl x.s (x.c f).z y f)
  V := fun _ => True

/-- after RA has been sent: soundness asks nothing of RA; the honest RA is msgRA -/
def cutA : Cut G.P0 E (G.sLa E) :=
  ⟨fun x yo => (G.cutL E pl 2 0 true).R x yo.1 ∧ () = (),
    fun s π x yo => (G.cutL E pl 2 0 true).Hn s π x yo.1 ∧ yo.2 = G.msgRA E s,
    fun _ => True⟩

/-- The relations in the pass of the root tests before its step k. -/
def cutR (k : ℕ) : Cut G.P0 E (G.sL E) where
  R := fun x y =>
    x.led.True (G.proj E y) ∧
    (∀ f, f < G.plan.nc → G.RAtR E pl (ph 2 k f) f (x.get f) y) ∧
    ∀ f, f < G.plan.nc → G.CrOK E pl x.s (x.c f).z y f
  Hn := fun s π x y =>
    (s.W = y.1.1.1.1 ∧ (∀ p, G.proj E y (G.place p) = π p) ∧
      s.hl.Good x.led (G.proj E y) ∧ s.hl.len = G.lenAt E 2 k) ∧
    (∀ f, f < G.plan.nc → G.HAtR E pl (ph 2 k f) f (s.get f) π (x.get f) y) ∧
    ∀ f, f < G.plan.nc → G.CrOK E pl x.s (x.c f).z y f
  V := fun _ => True

/-- before the protocol: every key of every call is in its table -/
def c0 : Cut G.P0 E (s0 (F := F)) :=
  ⟨fun _ W => G.plan.KeysAll W, fun s _ _ W => s = W ∧ G.plan.KeysAll W, fun _ => True⟩
def c1 : Cut G.P0 E (G.s1 E) := Stage.cutPads G.iη (G.c0 E)
def c2 : Cut G.P0 E (G.s2 E) := Stage.cutPads G.i0 (G.c1 E)
/-- (The clause "() = ()" is what the library's theorem on a named vector leaves when nothing is
said of the vector: soundness asks nothing of bit here.) -/
def c3 : Cut G.P0 E (G.s3 E) :=
  ⟨fun x yo => (G.c2 E).R x yo.1 ∧ () = (),
    fun s π x yo => (G.c2 E).Hn s π x yo.1 ∧ yo.2 = G.msgBit E s,
    fun _ => True⟩

/-- what is said of the scalars s_f after the calls -/
def KeepOK (x : Keep E) (y : G.Y E) : Prop := ∀ f, f < G.plan.nc → G.CrOK E pl x.2 (x.1 f) y f

/-- the honest prover has kept the matrix and the end points -/
def KeepH_OK (s : KeepH (F := F) E) (x : Keep E) (y : G.Y E) : Prop :=
  s.1 = y.1.1.1.1 ∧ ∀ f, f < G.plan.nc → s.2 f = x.1 f

def c5 : Cut G.P0 E (G.s5 E) :=
  ⟨fun x y => x.1.True (G.proj E y) ∧ G.KeepOK E pl x.2 y,
    fun s π x y =>
      Closing.HonLedger (G.nL E) (G.plN E pl) pl.cl s.1 π x.1 (G.proj E y) ∧
      G.KeepOK E pl x.2 y ∧
      G.KeepH_OK E s.2 x.2 y,
    fun _ => True⟩

/-- after step 10: the linear claim is true, and the scalars s_f are the true ones -/
def c6 : Cut G.P0 E (G.s6 E) :=
  ⟨fun x y => Form.val (G.proj E y) x.1 = 0 ∧ G.KeepOK E pl x.2 y,
    fun s _ x y => Form.val (G.proj E y) x.1 = 0 ∧ G.KeepOK E pl x.2 y ∧ G.KeepH_OK E s.2 x.2 y,
    fun _ => True⟩

/-- After the protocol: the linear claim and the one index claim are true. -/
def cEnd : Cut G.Pd E (G.sEnd E pl) where
  R := fun x y => Form.val (G.rdEnd E y) x.1 = 0 ∧ x.2.Holds y
  Hn := fun b π x y => Form.val (G.rdEnd E y) x.1 = 0 ∧ (G.M E pl).HoI (Set.range Sum.inr) b π x.2 y
  V := fun _ => True

/-- The pads that call f uses: all groups of its lookup argument but that of the arrays U, V of the
root test (rank 5 in Blocks/LookupStage.lean). These arrays are in RA and are not masked; the
library's structure of a lookup argument still names pads for them (pU, pV), which no step of this
reduction reads. -/
def used (f : ℕ) : Set G.P0 := (G.L1 E pl f).UG (· ≠ 5)

/-- What the parameters have to satisfy; p is the characteristic, WFp the predicate on matrices for
which the plan is valid. -/
structure OK (p : ℕ) (WFp : Mat F → Prop) : Prop where
  valid : G.plan.Valid p WFp
  char : ∀ f, f < G.plan.nc → 2 ^ (G.plan.d f + 2 ^ G.plan.lp) < p
  /-- the order of the rounds of the last layer over the keys names each of its variables once -/
  ord : G.ordK.Perm (PL.vars (G.plan.D - G.plan.B - 1 + (0 + G.plan.B)))
  /-- the class of a key is a part of its column; the row places from cov f on hold padding keys -/
  Bk : G.plan.B ≤ G.plan.k
  covLe : ∀ f, f < G.plan.nc → G.cov f ≤ 2 ^ (G.plan.D - G.plan.k)
  covPad : ∀ f,
    f < G.plan.nc → ∀ i', G.cov f ≤ i' → i' < 2 ^ (G.plan.D - G.plan.k) → G.plan.IsPad f i'
  /-- bit has room for the bits of all multiplicities of all calls: the bits of a call fill its
  columns; a code row of bit has the data coordinates of tB; the columns of all calls fit into the
  blocks of a table row; the code rows are those of the table -/
  lgRle : ∀ f, f < G.plan.nc → G.lgR ≤ (G.par E f).gT
  tBmsg : G.Cb.msg = G.tB.msg
  tBpos : 0 < G.tB.K2
  tBx : G.tB.x ≤ G.lgR
  room : pre (G.kB E) G.plan.nc ≤ G.tB.hB * G.tB.K2
  rowsBeq : G.rowsB = 2 ^ (G.lgR - G.tB.x) * G.tB.hB
  /-- RA has room for the arrays of the root tests of all calls -/
  roomA : pre (G.wRA E) G.plan.nc ≤ G.rowsA * G.CA.msg
  /-- every pad is used for one masked scalar only: in a call, .. -/
  pads : ∀ f, f < G.plan.nc → (G.L1 E pl f).PadsOK
  /-- .. in different calls, .. -/
  apart : ∀ f g, f < G.plan.nc → g < G.plan.nc → f ≠ g → Disjoint (G.used E pl f) (G.used E pl g)
  /-- .. in the closing block, .. -/
  auxInj : Function.Injective pl.cl.aux
  opnInj : Function.Injective pl.cl.opn
  auxOpn : Disjoint (Set.range pl.cl.opn) (Set.range pl.cl.aux)
  apartCl : ∀ f,
    f < G.plan.nc → Disjoint (G.used E pl f) (Set.range pl.cl.aux ∪ Set.range pl.cl.opn)
  /-- .. for the scalars s_f. -/
  crInj : Function.Injective fun f : Fin G.plan.nc => pl.cr f
  /-- Which pad vector holds which pad: η those of the calls and of the closing block, η⁰ those of
  the scalars s_f and no other. So the forms of the index claims have coefficients on η⁰ only, and
  that of the merged claim on η⁰ and η¹ only. (No theorem of this library proves this, for the index
  claims or for the merged claim, nor that the linear claim has no coefficient on η¹. The library's
  notion of an index claim allows a form on all exposed entries (those that forms may read), and no
  property of the reduction needs more. A later step that proves the index claim in a separate run,
  which reads η⁰ and η¹ and not η, bit or RA (as the programs' member does), needs to know where the
  form has coefficients.) -/
  lkIn : ∀ f, f < G.plan.nc → G.used E pl f ⊆ Set.range G.iη
  clIn : Set.range pl.cl.aux ∪ Set.range pl.cl.opn ⊆ Set.range G.iη
  crIn : ∀ f, f < G.plan.nc → pl.cr f ∈ Set.range G.i0
  /-- The pads of the merge are pads of η¹, each used once. -/
  mgIn : ((G.M E pl).sc (Fin G.plan.nc)).padsOf G.vars ⊆ Set.range Sum.inr
  mgOnce : ((G.M E pl).sc (Fin G.plan.nc)).PlacesOnce

end Cuts

/-! ## The claims at the end -/

section Front

variable [DecidableEq F] (pl : G.Places E)

/-- The claims in which the reduction ends: one linear claim, and one index claim; the form of the
index claim is v - ⟨c, entries⟩. -/
def out (x : (G.sEnd E pl).X) : OutClaims G.Nend E 1 :=
  ⟨fun _ => x.1, nat x.2.g, nat x.2.ψ,
    fun m => -(x.2.f : Form G.Nend E) (some m), (x.2.f : Form G.Nend E) none⟩

end Front

end Par

/-! ## The statements -/

namespace Spec

variable {F : Type} [Field F] [DecidableEq F] (G : Par F) (E : Type) [Field E] [NeZero (2 : E)]
  [Fintype E] [DecidableEq E] [Algebra F E] (pl : G.Places E)

/-- Under `Par.OK`, at the characteristic p of E, and 2 ≠ 0 in E: `Stage.Props` of the range
reduction by calls, among them soundness round by round, completeness, masked form (`Hon.Masked`,
Blocks/BlockHon.lean) and the bounds for the withheld sets (`Hon.withheld`, Blocks/BlockHon.lean),
from "every key of every call is in its table" to "the linear claim and the index claim are true".
-/
def props_stage : Prop :=
  ∀ (p : ℕ) [CharP E p] (WFp : Mat F → Prop),
    G.OK E pl p WFp → (G.stage E pl).Props ((G.c0 E).mapP Sum.inl) (G.cEnd E pl)

end Spec

end Blocks.RngC
