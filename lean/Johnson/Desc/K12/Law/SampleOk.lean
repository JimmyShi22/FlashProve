-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SampleOk.lean: do the premises of `says_sample_t` and `answers_of_says_t` meet
a real record? A test that can run at a place and the record behind the batching. Definitions with
code alone; no theorem; no Mathlib beneath it.

The two theorems are in Johnson/Desc/K12/Law/SampleAt.lean. At each member of the group under test
the question is: is the record's sample row "{ Send.form codes shape o seed 0 with target := the
answer }" at a seed of the cube's own length with a factor other than 0? What the yes of `sampleL`
gives is a theorem in Johnson/Desc/K12/Law/SampleLaw.lean (`sample_of_L`).
The record keeps the rows, not the seeds. `seedOfRow` reads a seed back off the row's own terms.
Where the shape has one table, the row's one structured term is Tensor.eq (z.take bits) 1, whose
pairs are (1 − x, x): so the point is the pairs' second halves; the first single entry stands on the
pad's first place with the coefficient β · θ^0 − (the term's entry there): so β is that coefficient
and the term's entry, added. Where the shape has both tables the cube has one bit more than the
longer table: the row has two terms, main then mask; the longer table's term holds all coordinates
but the last in its pairs, and its scalar is that of `Send.front` with an empty product: 1 − top on
the main table, top on the mask table: so the last coordinate comes out of that one scalar, without
a quotient; the pad stands on the mask table. The test is then not "the seed was drawn so" but:
`Send.form` at the seed read back gives the record's row again, field by field, the target apart.
Main names:
  `rowSame a b`: kind; terms (oracle, part, the tensor's five fields); single entries; no runs and
    no forms in either. The target is not compared.
  `sampleL K m x`: twelve clauses: smp.sampled; smp.one (one sample row); smp.answers (the shape has
    one answer); smp.kind; smp.seed (a seed can be read back); smp.form (`Send.form` at it gives the
    row again); smp.len (the point has as many coordinates as the message's own cube has bits);
    smp.beta (the factor is not 0); smp.canon (its three words are below the field's size, so that
    "not 0" as words is "not 0" in the field); smp.case (what the library's `MeetsAt` asks: `CaseE ∨
    CaseF`); smp.powM, smp.powZ (the message length of each code of which the shape has rows is a
    power of two).
  `sampleLines tag p t`: a line a member: the numbers (the point's length, the cube's bits, whether
    the record's target is 0), each clause; a last line; and controls, each due false: the point's
    first coordinate and 1 added; its last coordinate and 1 added (with both tables that is the
    coordinate which `Send.front` alone reads); the factor and 1 added; another message's number.
Limits: no soundness is claimed, and nothing is said on hiding.

-/
import Johnson.Desc.K12.Law.SiteOk

set_option autoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (Seat1 Plain)

def tensorSame (a b : Tensor) : Bool :=
  decide (a.scalar = b.scalar) && decide (a.pairs = b.pairs) && decide (a.denseVars = b.denseVars)
      &&
    decide (a.values.toList = b.values.toList) && decide (a.first = b.first)

def rowSame (a b : Row) : Bool :=
  decide (a.kind = b.kind) && a.terms.size == b.terms.size &&
    ((a.terms.toList.zip b.terms.toList).all fun x =>
      x.1.oracle == x.2.oracle && decide (x.1.part = x.2.part) && tensorSame x.1.v x.2.v) &&
    a.units.size == b.units.size &&
    ((a.units.toList.zip b.units.toList).all fun x =>
      x.1.oracle == x.2.oracle && decide (x.1.part = x.2.part) && x.1.index == x.2.index &&
        decide (x.1.coeff = x.2.coeff)) &&
    a.runs.size == 0 && b.runs.size == 0 && a.forms.size == 0 && b.forms.size == 0

def seedOfRow (K : Codes) (sh : OracleShape) (r : Row) : Option SampleSeed :=
  let c := Send.cube K sh
  if c.hasMain && c.hasMask then
    match r.terms[0]?, r.terms[1]?, r.units[0]? with
    | some tM, some tZ, some u =>
      let low := if c.maskBits ≤ c.mainBits then tM.v.pairs.map (·.2) else tZ.v.pairs.map (·.2)
      let top := if c.maskBits ≤ c.mainBits then subE oneE tM.v.scalar else tZ.v.scalar
      some ⟨low ++ [top], addE u.coeff (tZ.v.entry u.index)⟩
    | _, _, _ => none
  else
    match r.terms[0]?, r.units[0]? with
    | some t, some u => some ⟨t.v.pairs.map (·.2), addE u.coeff (t.v.entry u.index)⟩
    | _, _ => none

def formIs (K : Codes) (sh : OracleShape) (o : Nat) (seed : SampleSeed) (r : Row) : Bool :=
  match Send.form K sh o seed 0 with
  | some row => rowSame row r
  | none => false

def sampleL (K : Codes) (m : Seat1) (x : OnBytes.Oracle) : Clauses :=
  let r := x.sampleRows.getD 0 default
  let c := Send.cube K m.sh
  let sd := seedOfRow K m.sh r
  [("smp.sampled", x.sampled), ("smp.one", x.sampleRows.size == 1), ("smp.answers", m.sh.answers ==
      1),
   ("smp.kind", decide (r.kind = .sample)),
   ("smp.seed", sd.isSome),
   ("smp.form", match sd with | some s => formIs K m.sh m.id s r | none => false),
   ("smp.len", match sd with | some s => s.z.length == c.bits | none => false),
   ("smp.beta", match sd with | some s => !isZeroE s.beta | none => false),
   ("smp.canon", match sd with | some s => okE s.beta | none => false),
   ("smp.case", decide ((0 < m.sh.maskRows ∨ m.sh.mainDeg = 3) ∨ (m.sh.maskRows = 0 ∧ m.sh.mainDeg
       = 1))),
   ("smp.powM", m.sh.mainRows == 0 || 2 ^ ceilLog2 (mainB K m.sh).ell == (mainB K m.sh).ell),
   ("smp.powZ", m.sh.maskRows == 0 || 2 ^ ceilLog2 (maskB K m.sh).ell == (maskB K m.sh).ell)]

def sampleAll (p : P12) (t : T12) : Clauses :=
  match plainAt p t with
  | some (_, D) => D.mems.zipIdx.flatMap fun y =>
      match D.st.oracles[y.1.id]? with
      | some x => tagM y.2 (sampleL D.st.codes y.1 x)
      | none => [(toString y.2 ++ ":the statement has not the message", false)]
  | none => [("no stage, no claim, or the plain data cannot be made", false)]

def sampleOk (p : P12) (t : T12) : Bool := ok (sampleAll p t)

def sampleNo (p : P12) (t : T12) : List String := ((sampleAll p t).filter (!·.2)).map (·.1)

def smpLine (tagS : String) (K : Codes) (m : Seat1) (x : OnBytes.Oracle) : String :=
  let r := x.sampleRows.getD 0 default
  let c := Send.cube K m.sh
  let sd := seedOfRow K m.sh r
  let ctl : String := match sd with
    | some s =>
      let z1 := match s.z with | [] => [] | a :: l => addE a oneE :: l
      s!"CONTROLS, EACH DUE false: the point's first coordinate and 1 added \
          {formIs K m.sh m.id ⟨z1, s.beta⟩ r} · its last coordinate and 1 added \
          {formIs K m.sh m.id ⟨s.z.dropLast ++ [addE (s.z.getLastD zeroE) oneE], s.beta⟩ r} · the \
          factor and 1 added {formIs K m.sh m.id ⟨s.z, addE s.beta oneE⟩ r} · another message's \
          number {formIs K m.sh (m.id + 1) s r}"
    | none => "no control: no seed"
  s!"{tagS}\tmessage {m.id} · rows {m.sh.mainRows} | {m.sh.maskRows} · sample rows \
      {x.sampleRows.size} · terms {r.terms.size} · single entries {r.units.size} · runs \
      {r.runs.size} · forms {r.forms.size}\ttables \
      {if c.hasMain && c.hasMask then "BOTH" else "one"} (main bits {c.mainBits} · mask bits \
      {c.maskBits})\tthe point read back has {(sd.map (·.z.length)).getD 0} coordinates · the \
      message's own cube has {c.bits} bits\tIS THE RECORD's TARGET 0? {isZeroE r.target}\tsample \
      {ok (sampleL K m x)} · refusing {((sampleL K m x).filter (!·.2)).map (·.1)}\t{ctl}"

def sampleLines (tagS : String) (p : P12) (t : T12) : List String :=
  match plainAt p t with
  | some (_, D) =>
    (D.mems.zipIdx.map fun y =>
      match D.st.oracles[y.1.id]? with
      | some x => smpLine (tagS ++ ".SMP." ++ toString y.2) D.st.codes y.1 x
      | none => s!"{tagS}.SMP.{y.2}\tthe statement has not the message {y.1.id}") ++
    [s!"{tagS}.SMP.all\tsampleOk {sampleOk p t}\tmembers {D.mems.length}\trefusing: {sampleNo p t}"]
  | none =>
      [s!"{tagS}.SMP.all\tsampleOk false\tno stage, no claim, or the plain data cannot be made"]

end H2K.Pin
