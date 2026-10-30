-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRead.lean: the step "read": claims on virtual cells are closed by sending partial
evaluations, as an interactive oracle reduction over oracle messages with samples.

This file is about one step of a protocol on integer matrices that are sent in packed form, several
rows in one: the prover sends partial evaluations of the unpacked matrix, and claims on the unpacked
matrix become linear claims on what was sent.
Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in Cb/Ld/LdReadProofs.lean.
It builds on Cb/Ld/LdRng.lean (parameters, the predicate's joint `rngJ`), Cb/Ld/LdRngAlg.lean
(packing, the predicate `Rng`, the virtual matrix of cells) and Cb/Ld/LdSigSum.lean (the sending).
The virtual matrix `cells P b ϱ mpk` is an integer matrix with entries below b in absolute value
whose packing is mpk, if there is one, and 0 else.

Why: with P > 1 rows of cells packed into one row, a cell is not a linear function of the entry that
is sent. Keys and summands of the protocol are built over the virtual matrix of cells,
cells (2 D) ϱ (pk m): a function of the messages, sent by nobody (Cb/Ld/LdRngAlg.lean). Lookups,
zerochecks and sumchecks run on such maps unchanged, and end in claims on values of cell maps (maps
that are affine in the cells, see `Spec.ldRead_cellmap` below) at points. No row on the packed
entries says such a claim.

The step: when the points of all these claims are known, the prover sends one more oracle message
(in a family N) with the reads: for each weight vector that the claims need, the vector
(weights)ᵀ · (cells), one entry for each column. From then on each claim is a linear row on the
reads, and the predicate of the range check, which follows, ties the reads to the cells.

The claims (`ReadCl`). Claim j, in the state st:
    k0 st j + ∑_{k, c} cw st j k c · (read k at the column c) + ∑_n ms st j n · (entry n) = v st j,
    v public.
  cl.OnReads st mrd e    all claims, with the reads taken from a matrix mrd: rows, linear in mrd and
    in the entries e (masks).
  `Spec.ldRead_cellmap`: this is the claim on the value of a cell map at a point: for a map
    F(b, c) = c_F + ∑_ι c_ι · Y((b, ι), c), affine in the cells, and weights φ on b, ψ on c that sum
    to 1 each (equality weights at the two parts of a point),
      ∑_{b, c} φ(b) ψ(c) F(b, c)
        = c_F + ∑_ι c_ι ∑_c ψ(c) · (the read with the weights φ laid on the rows (·, ι), at c).

From `S.over (readIn p c cl A₀)`: the packed matrix pk m is the packing of cells (honest: below B,
the core's matrix; relaxed: below 2 D, some matrix), and the claims hold of the virtual cells,
beside any base joint A₀. Where the first conjunct comes from: the sending of an oracle message that
holds packed cells adds exactly it (it is the predicate without reads, `Packed`); for an oracle
message of an earlier part of a protocol whose cells are read again it is carried along.
To (S.sum N).over (rngIn p (c.withReads ..) (S.grow N (readRows ..) ..)): the input joint of the
range check (Cb/Ld/LdRng.lean) for the two components (pk of the old messages, the reads in the new
messages), beside: the claims as rows on the reads, and A₀.
Two rounds, those of the sending; one verifier message is not empty (the seed). No challenge of its
own, no error of its own: the errors and budget are the sending's; the hypotheses are the sending's
plus `p.OK` and `Uniq` (below). The extractor forgets what was sent. Complete without error.

What is asked beside the sending's hypotheses: `p.OK` (Cb/Ld/LdRng.lean) and
`Uniq (2 D) ϱ P (characteristic)`: 2 (2 D) - 2 < ϱ and (2 (2 D) - 2) ∑_{l < P} ϱ^l < characteristic.
Where they enter. Backwards: the integer matrix that the relaxed predicate names is the virtual
matrix, so rows on the reads are claims on the virtual cells (`Spec.ldRead_iff`).
Forwards: the virtual matrix is the honest one.
`Spec.ldRead_step` and `Spec.ldRead_goodT` state knowledge soundness at the joint's condition only
(over a signature: the samples do not collide, and the condition of A₀ holds).
Then the range check (`Spec.ldRead_rng`, under the hypotheses of its statement): five rounds, three
verifier messages that are not empty; the range check's verifier message Θ (`p.Chal`) comes after
the answers of the sample of the reads: the reduction is `(ldRead ..).seq (ldRng ..)`.
The rows as linear forms (`readRow`, `Spec.ldRead_rows`): with the reads at places of a vector of
entries; public target v - k0.
P = 1. No read is needed: a cell is an entry, and a claim on a cell map is a row on the packed
matrix itself. The range check is then used alone, with Rd empty (Cb/Ld/LdRngAlg.lean:
`rngPk_plain`).

Main names: `CellRd`, `ReadCl` (data); `readIn` (the input joint at the base); `ldRead` (the step);
`Spec.ldRead_iff`, `Spec.ldRead_step`: see their docstrings.

What the sending's hypotheses ask; each stands in `Spec.ldRead_goodT` as a premise (there C is
`(N.om a).C`, o is `N.om a`, D is `Dn`; the last row's `N.Hides bud` is `Dn.Nn.Hides (N.budT t)`):
  The laws of a code read under a transformation (`C.Laws`, that is `LdCode.Laws`) ask: the encoder
    `C.enc`, as a map of the pair (message, randomness), and the transformation `C.T`, from native
    words to long words, are linear over E; the encoder sends only the zero message with zero
    randomness to zero; and, for every long position x, any two native words that agree at the
    native positions `C.src x` have the same long symbol at x.
  `Sd.Fair` (`Sig.Seeds.Fair`) asks of the joint seeds of a family: for each member a and each seed
    ρ of that member's sample map `(N.om a).Z`, at most `Sd.mult a` joint seeds s have
    `Sd.sd a s = ρ`.
  The list of a word f as sent (`o.InList f`) consists of the messages m for which, for some
    randomness r, the long words `o.C.T (o.upW f)` and `o.C.T (o.C.enc m r)` differ at no more than
    `o.e` long positions; `o.ListLE L` (`OMsg.ListLE`) asks that, for every word f as sent, that
    list has at most L members.
  `o.Evades` (`OMsg.Evades`) asks: for every word f as sent and any two different messages m and m'
    of the list `o.InList f`, the seeds ρ of the sample map `o.Z` at which m and m' have the same
    answers (`o.Z.val ρ m = o.Z.val ρ m'`) number at most `o.Z.err`.
  The laws of a sender (`D.Laws back`, that is `Sig.Sender.Laws`; for one oracle message
    `OMsg.Sender.Laws`) ask two things: for every m and r, the word `D.Nn.enc m r` (for one oracle
    message, `D.N.enc m r`), read as a native word through `upW`, is the code's encoding of
    `D.upM m` with randomness `D.upR r`, for a family at each member a
    (`(N.om a).upW (D.Nn.enc m r a) = (N.om a).C.enc (D.upM m a) (D.upR r a)`); and `back` returns w
    from `D.upM (D.put w k)` and `D.rest w`, for every witness w and every k in `D.Mk`.
  `D.Blind Sd` (`Sig.Sender.Blind`) asks that, for every joint seed s and all witnesses w and w',
    the distribution of `D.ans Sd s w k` over uniform k in `D.Mk` equal that of `D.ans Sd s w' k`;
    `D.ans Sd s w k` gives the family, over the members a, of the answers
    `(N.om a).Z.val (Sd.sd a s)` of `D.upM (D.put w k) a`, and the distribution is of that whole
    family. For one oracle message o, `D.Blind` (`OMsg.Sender.Blind`) asks the same with a seed ρ of
    `o.Z` in place of s: that, for every ρ and all w and w', the distribution of `D.ans ρ w k` over
    uniform k in `D.Mk` equal that of `D.ans ρ w' k`, where `D.ans ρ w k` is
    `o.Z.val ρ (D.upM (D.put w k))`.
  `N.Hides bud` (`Enc.Hides`) asks that, for every set S of positions with `bud S` and all messages
    m and m', the distribution of `N.shows S m r` over uniform r in `N.Rnd` equal that of
    `N.shows S m' r`; `N.shows S m r` gives the symbols of `N.enc m r` at the positions of S.

Notation: `p`: the parameters of a range check with packing (`RngPar`, Cb/Ld/LdRng.lean); `p.Rp`:
packed rows; `p.Rd`: reads; `p.C`: columns; P = `p.P`: how many rows of cells are packed into one;
ϱ = `p.rdx`: the radix; B = `p.B`: the honest bound; D = `p.D`: the half-width of the window;
`p.Row`: the rows of cells; `p.Cells`: matrices of cells; pk: a matrix on the packed rows and the
columns, read off the messages (`CellRd.pk`); S, N: signatures (`Sig`, Cb/Ld/LdSig.lean).

Limits: declared differences to a write-up of ours (lean/CREDITS.md).
  (a) A claim may use any linear form on the reads; the write-up's is a few reads under
      equality weights on the columns.
  (b) Several matrices of cells are one matrix here; a weight vector that lives on the rows of one
      of them is a case.
  (c) The honest relation names the integer matrix through the core of the witness.
  (d) The reads are sent in a family N, which may hold more.
This file does not say in which group the reads and the masks of the claims lie. A claim whose mask
lies in another group needs a splitting. That a later part of a protocol that reads cells of an
earlier oracle message sends its own reads, and runs its own range check on them, is a use of the
two blocks: pk may read any oracle messages of S. This file says nothing on sizes or running times.
Zero knowledge is the sending's: that the reads are hidden is its hypothesis on the sender (exactly:
`D.Blind Sd` and `D.Nn.Hides (N.budT t)` in `Spec.ldSendSig_goodT`, Cb/Ld/LdSigSum.lean).
Partial evaluations are the field's technique; the step follows this protocol's technical report,
which follows the paper that this protocol builds on and advice (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdRng
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Rng Cb.RngPk

/-! ## 1. Cells and claims -/

/-- How the cells are read: the weights of the reads off the explicit part; the packed matrix and
the entries that mask forms may read off the messages; the integer matrix off the core. -/
structure CellRd (p : RngPar) (E St M Kc J : Type) where
  W   : St → p.Rd → p.Row → E
  pk  : M → p.Rp → p.C → E
  yz  : Kc → p.Cells
  ent : M → J → E

/-- The claims: constants, coefficients on the entries of the reads, mask forms, public targets; all
are functions of the state. -/
structure ReadCl (p : RngPar) (E St J : Type) where
  Jc : Type
  k0 : St → Jc → E
  cw : St → Jc → p.Rd → p.C → E
  ms : St → Jc → J → E
  v  : St → Jc → E

/-- the reads -/
abbrev RngPar.Rds (p : RngPar) (E : Type) : Type := p.Rd → p.C → E

section
variable {E St M Kc Wp J : Type} [CommRing E] [Fintype J] {E₀ : ExtSpec} {p : RngPar}

/-- the reads of a matrix of cells -/
def readsOf (W : p.Rd → p.Row → E) (Y : p.Cells) : p.Rds E := fun k c =>
  ∑ r, W k r * ((Y r c : ℤ) : E)

/-- The claims as rows on the reads. -/
def ReadCl.OnReads (cl : ReadCl p E St J) (st : St) (mrd : p.Rds E) (e : J → E) : Prop :=
  ∀ j, cl.k0 st j + ∑ k, ∑ c, cl.cw st j k c * mrd k c + ∑ n, cl.ms st j n * e n = cl.v st j

/-- The claims on a matrix of cells. -/
def ReadCl.OnCells (cl : ReadCl p E St J) (W : St → p.Rd → p.Row → E) (st : St)
    (Y : p.Cells) (e : J → E) : Prop :=
  cl.OnReads st (readsOf (W st) Y) e

variable (p) (c : CellRd p E St M Kc J) (cl : ReadCl p E St J) (A₀ : IOR.Rels Kc St E₀ (M × Wp))

/-- The input joint, at the base: packing, and the claims on the virtual cells. -/
def readIn : IOR.Rels Kc St E₀ (M × Wp) where
  rel  := fun st y w =>
    PackBy p.B p.rdx (c.yz (A₀.core w)) (c.pk w.1) ∧
    cl.OnCells c.W st (cells p.P (2 * p.D) p.rdx (c.pk w.1)) (c.ent w.1) ∧
    A₀.rel st y w
  relR := fun a w =>
    Packed p.P (2 * p.D) p.rdx (c.pk w.1) ∧
    cl.OnCells c.W a.1 (cells p.P (2 * p.D) p.rdx (c.pk w.1)) (c.ent w.1) ∧
    A₀.relR a w
  on   := A₀.on
  core := A₀.core

/-- The claims as rows on reads that are a further part of the witness, beside A₀. -/
def readRows : IOR.Rels Kc St E₀ (M × (Wp × p.Rds E)) where
  rel  := fun st y w => cl.OnReads st w.2.2 (c.ent w.1) ∧ A₀.rel st y (w.1, w.2.1)
  relR := fun a w => cl.OnReads a.1 w.2.2 (c.ent w.1) ∧ A₀.relR a (w.1, w.2.1)
  on   := A₀.on
  core := fun w => A₀.core (w.1, w.2.1)

/-- The joint between the step without rounds and the sending: the predicate with reads, the reads
being a further part of the witness. -/
def readMid : IOR.Rels Kc St E₀ (M × (Wp × p.Rds E)) :=
  rngJ p c.W c.yz (fun w => c.pk w.1) (fun w => w.2.2) (readRows p c cl A₀)

end

/-! ## 2. The step -/

section
variable {E St Kc Wp J : Type} [Field E] [Fintype J] {E₀ : ExtSpec} (p : RngPar) (S N : Sig E)
  (c : CellRd p E St S.Msg Kc J) (cl : ReadCl p E St J) (A₀ : IOR.Rels Kc St E₀ (S.Msg × Wp))

/-- the reads are read off the new messages -/
def readBk (get : N.Msg → p.Rds E) : N.Msg → Wp → Wp × p.Rds E := fun m wp => (wp, get m)

/-- How the range check that follows reads: the packed matrix off the old messages, the reads off
the new ones. -/
def CellRd.withReads (get : N.Msg → p.Rds E) : RngRd p E St (S.sum N).Msg Kc :=
  ⟨c.W, fun m => c.pk (S.left N (T := OMsg.Msg) m),
    fun m => get (S.right N (T := OMsg.Msg) m), c.yz⟩

/-- what the honest prover does before it sends: it computes the reads of the core's matrix -/
def readM (a : (St × S.Smp) × (S.Wit × Wp)) : (St × S.Smp) × (S.Wit × (Wp × p.Rds E)) :=
  (a.1, (a.2.1, (a.2.2, readsOf (c.W a.1.1) (c.yz (A₀.core (S.msgs a.2.1, a.2.2))))))

variable (Sd : N.Seeds)

/-- The step "read": the sending of the family that holds the reads. -/
abbrev ldRead (St : Type) (E₀ : ExtSpec) :
    IOR (St × S.Smp) (E₀.prod S.ext) (St × (S.sum N).Smp) (E₀.prod (S.sum N).ext) :=
  (ldSendSig S N Sd St E₀).pre (fun x => some x) (ExtMap.id (E₀.prod S.ext))

abbrev ldReadH (Dn : N.Sender (S.Wit × (Wp × p.Rds E)) (S.Wit × Wp)) :
    (ldRead S N Sd St E₀).Honest (S.Wit × Wp) ((S.sum N).Wit × Wp) :=
  (ldSendSigHon Sd St E₀ Dn).pre (fun x => some x) (ExtMap.id (E₀.prod S.ext)) (readM p S c A₀)

abbrev ldReadN (St : Type) (E₀ : ExtSpec) (Kc : Type) (L t : N.O → ℕ) :
    IOR.Nums Kc (ldRead S N Sd St E₀) :=
  (ldSendSigNums S N Sd St E₀ Kc L t).pre (fun x => some x) (ExtMap.id (E₀.prod S.ext))

end

/-! ## 3. The rows as linear forms -/

/-- The row of a claim, with the reads at the places `at'` of the vector of entries. -/
def readRow {E St J : Type} [Field E] [DecidableEq J] {p : RngPar} (cl : ReadCl p E St J)
    (at' : p.Rd → p.C → J) (j : cl.Jc) : Slf E St J :=
  fun st n =>
    placed (fun x : p.Rd × p.C => at' x.1 x.2) (fun x => cl.cw st j x.1 x.2) n + cl.ms st j n

/-! ## The statements -/

namespace Spec
open IOR

/-- Under the hypotheses below, a claim on the value of a cell map at a point is a claim of the kind
treated here. -/
def ldRead_cellmap : Prop :=
  ∀ (E Bq I Rw C : Type) [CommRing E] [Fintype Bq] [Fintype I] [Fintype Rw]
      [DecidableEq Rw] [Fintype C] (rowOf : Bq × I → Rw) (φ : Bq → E) (ψ : C → E) (cF : E)
      (cι : I → E) (Y : Rw → C → E),
    ∑ b, φ b = 1 → ∑ c, ψ c = 1 →
    ∑ b, ∑ c, φ b * ψ c * (cF + ∑ ι, cι ι * Y (rowOf (b, ι)) c) =
      cF + ∑ ι, cι ι * ∑ c, ψ c * ∑ r, placed (fun b => rowOf (b, ι)) φ r * Y r c

/-- States, under `Uniq b p.rdx p.P pp` with pp the characteristic of E: under the predicate with
reads (`Rng`), a claim on the virtual cells is a row on the reads. -/
def ldRead_iff : Prop :=
  ∀ (E St J : Type) [CommRing E] [Fintype J] (pp : ℕ) [CharP E pp] (p : RngPar) (b : ℤ)
      (W : St → p.Rd → p.Row → E) (cl : ReadCl p E St J) (st : St) (mpk : p.Rp → p.C → E)
      (mrd : p.Rds E) (e : J → E),
    Uniq b p.rdx p.P pp → Rng b p.rdx (W st) mpk mrd →
    (cl.OnCells W st (cells p.P b p.rdx mpk) e ↔ cl.OnReads st mrd e)

/-- States, under `p.OK` and `Uniq (2 * p.D) p.rdx p.P pp` with pp the characteristic of E, that
`readM` is a step without rounds (`StepT`), without error, from `S.over (readIn ..)` to
`S.over (readMid ..)`. The reads become a further part of the witness. -/
def ldRead_step : Prop :=
  ∀ (E St Kc Wp J : Type) [Field E] [Fintype J] (pp : ℕ) [CharP E pp]
      (E₀ : ExtSpec) (p : RngPar) (S : Sig E) (c : CellRd p E St S.Msg Kc J)
      (cl : ReadCl p E St J) (A₀ : Rels Kc St E₀ (S.Msg × Wp)),
    p.OK → Uniq (2 * p.D) p.rdx p.P pp →
    StepT (fun x => some x) (ExtMap.id (E₀.prod S.ext)) (readM p S c A₀) (fun _ w => (w.1, w.2.1))
      (S.over (readIn p c cl A₀)) (S.over (readMid p c cl A₀))

/-- After the sending the joint is the input joint of the range check. -/
def ldRead_joint : Prop :=
  ∀ (E St Kc Wp J : Type) [Field E] [Fintype J] (E₀ : ExtSpec) (p : RngPar) (S N : Sig E)
      (c : CellRd p E St S.Msg Kc J) (cl : ReadCl p E St J)
      (A₀ : Rels Kc St E₀ (S.Msg × Wp)) (get : N.Msg → p.Rds E),
    S.grow N (readMid p c cl A₀) (readBk p N get) =
      rngIn p (c.withReads p S N get) (S.grow N (readRows p c cl A₀) (readBk p N get))

/-- The step "read". -/
def ldRead_goodT : Prop :=
  ∀ (E St Kc Wp J : Type) [Field E] [Fintype J] (pp : ℕ) [CharP E pp] (E₀ : ExtSpec) (p : RngPar)
      (S N : Sig E) (c : CellRd p E St S.Msg Kc J) (cl : ReadCl p E St J)
      (A₀ : Rels Kc St E₀ (S.Msg × Wp)) (get : N.Msg → p.Rds E) (Sd : N.Seeds)
      (Dn : N.Sender (S.Wit × (Wp × p.Rds E)) (S.Wit × Wp)) (L t : N.O → ℕ),
    p.OK → Uniq (2 * p.D) p.rdx p.P pp → (∀ a, (N.om a).C.Laws) → Sd.Fair →
    (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) →
    Dn.Laws (S.backN N (readBk p N get)) → Dn.Blind Sd → Dn.Nn.Hides (N.budT t) →
    GoodT (ldRead S N Sd St E₀) (ldReadH p S N c A₀ Sd Dn) (S.over (readIn p c cl A₀)).cf
      ((S.sum N).over
        (rngIn p (c.withReads p S N get) (S.grow N (readRows p c cl A₀) (readBk p N get)))).cf
      (fun _ _ w => (S.left N (T := OMsg.Wit) w.1, w.2)) (ldReadN S N Sd St E₀ Kc L t)

/-- Two rounds. -/
def ldRead_rounds : Prop :=
  ∀ (E St : Type) [Field E] (E₀ : ExtSpec) (S N : Sig E) (Sd : N.Seeds),
    (ldRead S N Sd St E₀).shape.length = 2

/-- Read, then the range check: from packing and claims on virtual cells to digits in their tables,
the range check's rows and the claims as rows on the reads. -/
def ldRead_rng : Prop :=
  ∀ (E St Kc Wp J : Type) [Field E] [Fintype J] (pp : ℕ) [CharP E pp] (E₀ : ExtSpec) (p : RngPar)
      (S N N' : Sig E) (c : CellRd p E St S.Msg Kc J) (cl : ReadCl p E St J)
      (A₀ : Rels Kc St E₀ (S.Msg × Wp)) (get : N.Msg → p.Rds E) (Sd : N.Seeds)
      (Dn : N.Sender (S.Wit × (Wp × p.Rds E)) (S.Wit × Wp)) (L t : N.O → ℕ)
      (get' : N'.Msg → p.Dg E) (Sd' : N'.Seeds)
      (Dn' : N'.Sender ((S.sum N).Wit × (Wp × p.Dg E)) ((S.sum N).Wit × Wp)) (L' t' : N'.O → ℕ),
    p.OK → Uniq (2 * p.D) p.rdx p.P pp → (∀ a, (N.om a).C.Laws) → Sd.Fair →
    (∀ a, (N.om a).ListLE (L a)) → (∀ a, (N.om a).Evades) → Dn.Laws (S.backN N (readBk p N get)) →
    Dn.Blind Sd → Dn.Nn.Hides (N.budT t) → (∀ a, (N'.om a).C.Laws) → Sd'.Fair →
    (∀ a, (N'.om a).ListLE (L' a)) → (∀ a, (N'.om a).Evades) →
    Dn'.Laws ((S.sum N).backN N' (rngBk p N' get')) → Dn'.Blind Sd' → Dn'.Nn.Hides (N'.budT t') →
    GoodT ((ldRead S N Sd St E₀).seq (ldRng p (S.sum N) N' Sd' St E₀))
      ((ldReadH p S N c A₀ Sd Dn).seq
        (ldRngH p (S.sum N) N' (c.withReads p S N get)
          (S.grow N (readRows p c cl A₀) (readBk p N get)) Sd' Dn'))
      (S.over (readIn p c cl A₀)).cf
      (((S.sum N).sum N').over
        ((S.sum N).grow N'
          (rngOut p (c.withReads p S N get) (S.grow N (readRows p c cl A₀) (readBk p N get)))
          (rngBk p N' get'))).cf
      (fun _ _ w => (S.left N (T := OMsg.Wit) ((S.sum N).left N' (T := OMsg.Wit) w.1), w.2))
      ((ldReadN S N Sd St E₀ Kc L t).seq (ldRngN p (S.sum N) N' (c.withReads p S N get) Sd' L' t'))

/-- The claims on the reads are linear forms with public targets. -/
def ldRead_rows : Prop :=
  ∀ (E St J : Type) [Field E] [Fintype J] [DecidableEq J] (p : RngPar) (cl : ReadCl p E St J)
      (at' : p.Rd → p.C → J) (st : St) (v : J → E),
    cl.OnReads st (fun k c => v (at' k c)) v ↔
    Slf.All (readRow cl at') (fun j => cl.v st j - cl.k0 st j, fun _ => st) v

end Spec
end Cb
