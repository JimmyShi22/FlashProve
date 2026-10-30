-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/ServesAtRef.lean

"Serves" (Johnson/HonestTrace/Serves.lean) at the reference sizes: what the library's theorems say
of it there.

The definition of "Serves" is general in the sizes. Every theorem of this file that ties it to a
relation of the library is at the reference sizes "ppref" (1,024 positions, 48 layers), the lookup
tables "tbRef" and the weights that an index "Cm.Idx" holds. Nearly every proof is one call of a
theorem that stands elsewhere: the file's use is that whoever works with "Serves" or "traceRef" may
quote these theorems.

Main definition and theorems:
* "serves_iff_isTrueUnder": "Serves" is "Policy.IsTrueUnder", true under the policy. By definition.
* "modelR_of_serves": "Serves" gives "ModelR" at the weights that the layout reads from the index's
  matrix.
* "serves_tfae": at a prime p ≥ 2^61 - 1, a lawful table of scales and a policy with C, θ < 2^40 and
  cap < 2^16, four things say the same of an index and a request: the weights serve it; the
  library's honest cells "Cm.trace" meet the library's relation with the cost ledger modulo p
  ("Policy.LedgerRel.Ryes"); some cells meet it; some cells meet its relaxation ("Rno").
* "traceRef": "traceOf" at "Cm.trace": the library's honest cells where the weights serve the
  request, "none" elsewhere.
* "traceRef_ryes", "traceRef_below": at a lawful table and a policy with these bounds, a value of
  "traceRef" meets "Ryes" modulo every prime p ≥ 2^61 - 1, and its cells that a segment reads are
  below 129 in absolute value.
* "ordsL_of_traceRef": under the premises of "ordsL_of_true" (Johnson/Road/Lane5TopLTrue.lean) but
  for its last, the matrices of a value of "traceRef" meet the bundle "OrdsL".
* "serves_iff_meetsPolicy": at a lawful table whose settings are valid, for a request built from a
  prompt, output tokens and a padding, "Serves" says that the program runs on the window and the
  output meets the policy.
* Guards. "serves_met": at every lawful table and under every policy the all-zero weights serve one
  request, which has no counted position. "serves_met_counted": at every lawful table and under a
  policy with 257 ≤ θ and 257 ≤ C they serve every request that has its form, with y = 0 if e =
  1,024. "not_serves_of_low_theta": under a policy with θ < 2^8 ≤ C no index's weights serve a
  request with a counted position. "not_serves_at_haltW": at the reference table of scales some
  well-formed weights serve no request, since a range condition fails. (Through the form:
  "not_serves_of_le", in Serves.lean.)

Limits. At other sizes nothing here says that cells which meet a relation exist wherever "Serves"
holds. "serves_tfae" is on the library's own keys and tables, a relation on integers and residues,
and names no list of a verifier. The library's model has no cell for a lookup's counts: in the
matrices of "ordsL_of_traceRef" the matrix b of a group of layers, the matrix bA of attention and,
by a reading of "Hd.zOf", the head's matrix bH are 0, which no honest prover of the protocol would
commit to. By a reading of its text "OrdsL" does not read b and bA. The places of attention's cells
in these matrices are written by a reading of the verifier's texts; no theorem ties them to these
texts (Johnson/Road/Lane5AttDef.lean). Three of the four guards are at synthetic weights (the
all-zero weights; "haltW"); "not_serves_of_low_theta" speaks of every index. This file exhibits
served requests at all weights 0 alone ("serves_met", "serves_met_counted");
Policy/Rel/PosGuards.lean has some more, at the reference table of scales and synthetic weights
whose 48 layers are all zero ("real_gap", "step_gap"), and Johnson/Road/Lane5TrueLayerAt.lean one at
synthetic weights in which of the layers' matrices only W_v and W_o of layer 0 are not 0, at a
request with no counted position ("true_layer_ref"). Whether the public premises of
"ordsL_of_traceRef" hold of a parameter file hangs on what the Lean verifier's functions return for
it; that its "publicOf" returns at the stored full-size files is checked in this library by an
evaluation ("#guard", Johnson/Goal/Meaning/ScopeRun.lean), which is no theorem.

Not claimed: that a verifier accepts a proof made of these cells (completeness of the protocol);
that a prover's committed cells are these; that the public premises of "ordsL_of_traceRef" hold of
any parameter file.

-/
import Mathlib.Tactic.TFAE
import Cm.RelTrueExp
import Cm.Rel2Guards
import Policy.Rel.LedgerRelLaws
import Policy.Rel.TrueGuards
import Policy.Front.TrueUnderConverse
import Johnson.Road.Lane5TopLTrue
import Johnson.HonestTrace.Serves

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model

/-! ## The library's relations -/

section Ref
open Inst.Model.All
open Inst.Model.Layout (kRef)

/-- At the reference sizes, the tables "tbRef" and the weights that an index holds, for every table
of scales and every policy: "Serves" is "true under the policy" (Policy/Rel/True.lean). It holds by
definition: both sides unfold to one text. -/
theorem serves_iff_isTrueUnder (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) :
    Serves ppref s.kap s.nf (fun _ => tbRef) pol i.index.val x ↔ Policy.IsTrueUnder s pol i x :=
  Iff.rfl

/-- At the reference sizes, where the weights that an index holds serve a request, "ModelR" holds
(the program runs and the policy's clauses hold: "Serves" without the request's form) in the words
in which the theorems on honest cells ask it: at the weights that the layout reads from the index's
matrix, and the tables "tbsOf". -/
theorem modelR_of_serves {s : Cm.Scales} {pol : AcceptancePolicy} (i : Cm.Idx) {x : Instance ppref}
    (h : Serves ppref s.kap s.nf (fun _ => tbRef) pol i.index.val x) :
    ModelR ppref s.kap s.nf (tbsOf fun _ => tbRef) pol (Layout.weightsOf ppref kRef i.mat) x :=
  ⟨h.1, h.2.2⟩

/-- Where the library's relation with the cost ledger has a witness, at the reference sizes. At a
prime p ≥ 2^61 - 1, a lawful table of scales and a policy with C, θ < 2^40 and cap < 2^16, these
four say the same of an index and a request:
* the weights that the index holds serve the request;
* the library's honest cells "Cm.trace" meet "Policy.LedgerRel.Ryes": r < e; every cell that a
  segment reads is below 129 in absolute value; modulo p every key is in its table, every identity
  is 0, the cost ledger's four clauses hold, and y = 0 if e < 1,024;
* some cells meet "Ryes";
* some cells meet "Rno", the same with the bound 2^18.

So, under these premises and for that relation, a key outside its table is no further reason to have
no trace. The keys and tables are the library's own terms. No list of a verifier is named. -/
theorem serves_tfae (p : ℕ) (hp : p.Prime) (hB : 2 ^ 61 - 1 ≤ p) {s : Cm.Scales} (hs : s.Lawful)
    {pol : AcceptancePolicy} (hpol : Policy.PolCond pol) (i : Cm.Idx) (x : Instance ppref) :
    List.TFAE
      [Serves ppref s.kap s.nf (fun _ => tbRef) pol i.index.val x,
       Policy.LedgerRel.Ryes p (Policy.ppOf s pol) i x (Cm.trace (Policy.ppOf s pol) i x),
       ∃ T : Trace, Policy.LedgerRel.Ryes p (Policy.ppOf s pol) i x T,
       ∃ T : Trace, Policy.LedgerRel.Rno p (Policy.ppOf s pol) i x T] := by
  have hT := Policy.tableOK_ppOf hs hpol
  tfae_have 1 → 2 := fun h => (Policy.ledger_trace_iff p hp hB _ hT i x).2 h
  tfae_have 2 → 3 := fun h => ⟨_, h⟩
  tfae_have 3 → 4 := fun ⟨T, h⟩ => ⟨T, Policy.ledger_sub p _ i x T h⟩
  tfae_have 4 → 1 := fun ⟨T, h⟩ => Policy.ledger_forces p hp hB _ hT i x T h
  tfae_finish

/-- The library's honest cells where the weights serve the request, at the reference sizes, a table
of scales and a policy: "traceOf" with an index as what all requests share, the weights that the
index holds, and the cells "Cm.trace". The table and the policy are asked nothing: at a table that
is not lawful or a policy outside its bounds it can have a value of which no theorem of this file
speaks. -/
def traceRef (s : Cm.Scales) (pol : AcceptancePolicy) : Cm.Idx → Instance ppref → Option Trace :=
  traceOf ppref s.kap s.nf (fun _ => tbRef) pol (fun i => i.index.val)
    (Cm.trace (Policy.ppOf s pol))

/-- "traceRef" has the value T exactly if the weights that the index holds serve the request and T
is "Cm.trace" there. -/
theorem traceRef_eq_some_iff (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref)
    (T : Trace) :
    traceRef s pol i x = some T ↔
      Serves ppref s.kap s.nf (fun _ => tbRef) pol i.index.val x ∧
        Cm.trace (Policy.ppOf s pol) i x = T :=
  traceOf_eq_some_iff _ _ i x T

/-- At a prime p ≥ 2^61 - 1, a lawful table of scales and a policy with C, θ < 2^40 and cap < 2^16:
a value of "traceRef" meets the library's relation with the cost ledger modulo p,
"Policy.LedgerRel.Ryes". -/
theorem traceRef_ryes (p : ℕ) (hp : p.Prime) (hB : 2 ^ 61 - 1 ≤ p) {s : Cm.Scales}
    (hs : s.Lawful) {pol : AcceptancePolicy} (hpol : Policy.PolCond pol) {i : Cm.Idx} {x : Instance ppref}
    {T : Trace} (h : traceRef s pol i x = some T) :
    Policy.LedgerRel.Ryes p (Policy.ppOf s pol) i x T := by
  obtain ⟨hS, rfl⟩ := (traceRef_eq_some_iff s pol i x T).1 h
  exact (Policy.ledger_trace_iff p hp hB _ (Policy.tableOK_ppOf hs hpol) i x).2 hS

/-- At a lawful table of scales and a policy with C, θ < 2^40 and cap < 2^16: in a value of
"traceRef" every cell that a segment reads is below 129 in absolute value. -/
theorem traceRef_below {s : Cm.Scales} (hs : s.Lawful) {pol : AcceptancePolicy} (hpol : Policy.PolCond pol)
    {i : Cm.Idx} {x : Instance ppref} {T : Trace} (h : traceRef s pol i x = some T) :
    Cm.Below 129 T :=
  (traceRef_ryes Code.pGold Code.pGold_prime Policy.ledger_gl_big hs hpol h).2.1

end Ref

/-! ## The matrices, numbered as Johnson/Road/ numbers a sub-proof's arrays -/

section Road
open OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Layer (Lay)

variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  {hH : Model.Head.Shape} {tau : Array F} {L : Model.Head.HL} {sc : Model.Layer.Scales}
  {nf : NormPar} {pol : AcceptancePolicy} {SA : ℕ → Attention.Shape}

/-- "ordsL_of_true" (Johnson/Road/Lane5TopLTrue.lean), said of a value of "traceRef". The premises
are that theorem's to the letter, but for the last: twelve on the public shapes, layouts, scales and
tables; the table of scales made of them is lawful; the policy has C, θ < 2^40 and cap < 2^16. Then
for every index and request at which "traceRef" at that table and policy has a value T, the matrices
of T, numbered as the files of Johnson/Road/ number the arrays of a sub-proof ("Hd.zOf", "zsOf"),
meet "OrdsL".
In these matrices the matrix b of a group of layers, the matrix bA of attention and, by a reading of
"Hd.zOf", the head's matrix bH are 0; by a reading of its text "OrdsL" does not read b and bA.
Nothing is said on what a verifier accepts. -/
theorem ordsL_of_traceRef (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hw : ∀ g < 12, 7200 ≤ (SA g).kAs / (SA g).cf.NAs * (SA g).cf.NAs)
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (hs : (scalesOf hL sc nf).Lawful) (hpol : Policy.PolCond pol)
    (i : Cm.Idx) (x : Instance ppref) {T : All.Trace}
    (h : traceRef (scalesOf hL sc nf) pol i x = some T) :
    OrdsL hL sc y hH L nf pol SA i.mat x
      (fun _ => Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main T))
      (fun g => zsOf (SA g) g (Cm.Seg.toMat Cm.Seg.Hd.main T)) := by
  obtain ⟨hS, rfl⟩ := (traceRef_eq_some_iff _ pol i x T).1 h
  exact ordsL_of_true hy S Zd Z2 hp4 h12 hF hLy hSA hw hsh hE hs hpol i x hS

end Road

/-! ## Requests built from tokens -/

section Top
open VerifiableInference

/-- At a lawful table of scales whose settings are the valid settings "settings", for every policy
and index, and a request x built from a prompt, output tokens and a padding: the weights that the
index holds serve x exactly if the integer program runs on x's window of 1,024 tokens (no range
condition fails at any position, the padding's too) and the output meets the policy under the scores
of these weights ("Policy.MeetsPolicy"). This is "Policy.isTrueUnder_iff_meetsPolicy"
(Policy/Front/TrueUnderConverse.lean), said of "Serves". -/
theorem serves_iff_meetsPolicy {scales : Cm.Scales} (lawful : scales.Lawful)
    {settings : IntegerTransformer.Settings} (valid : settingsAreValid settings = true)
    (tie : settingsOf scales = settings) (policy : AcceptancePolicy) (i : Cm.Idx)
    {x : Instance ppref} {prompt output padding : List ℕ}
    (built : requestOfTokens (prompt, output) padding = some x) :
    Serves ppref scales.kap scales.nf (fun _ => tbRef) policy i.index.val x ↔
      RunsK ppref scales.kap scales.nf (fun _ => tbRef) i.index.val x.prompt ∧
        Policy.MeetsPolicy settings policy (weightsOfIndex valid i) prompt output :=
  Policy.isTrueUnder_iff_meetsPolicy lawful valid tie policy i built

end Top

/-! ## Guards: "Serves" holds somewhere, and fails through the policy and a range condition -/

section Guards
open Inst.Model.ScalesSanity Inst.Model.RequestGuards2 Inst.Model.SanityRef

/-- "Serves" is met at every lawful table of scales and under every policy: the all-zero weights
serve the request with all tokens 0, r = 1,023, e = 1,024, y = 0. That request has no counted
position. -/
theorem serves_met {s : Cm.Scales} (hs : s.Lawful) (pol : AcceptancePolicy) :
    Serves ppref s.kap s.nf (fun _ => tbRef) pol (Cm.Idx.ofIndex iZero).index.val
      (xz ⟨1023, by decide⟩ ⟨1024, by decide⟩) :=
  Policy.TrueGuards.some_true hs pol

/-- At every lawful table of scales and under every policy with 257 ≤ θ and 257 ≤ C, the all-zero
weights serve every request that has its form, with y = 0 if e = 1,024, whatever its other tokens:
so also requests with 1,023 counted positions (r = 0, e = 1,024). -/
theorem serves_met_counted {s : Cm.Scales} (hs : s.Lawful) (pol : AcceptancePolicy) (hθ : 257 ≤ pol.theta)
    (hC : 257 ≤ pol.C) (x : Instance ppref) (h3 : Head3 x) (hy : x.e = ppref.T → x.y.val = 0) :
    Serves ppref s.kap s.nf (fun _ => tbRef) pol (Cm.Idx.ofIndex iZero).index.val x :=
  Policy.TrueGuards.zero_all hs pol hθ hC x h3 hy

/-- "Serves" fails through the policy: under a policy with θ < 2^8 ≤ C no index's weights serve a
request with a counted position, at any table of scales. -/
theorem not_serves_of_low_theta (s : Cm.Scales) (pol : AcceptancePolicy) (h1 : pol.theta < 256)
    (h2 : 256 ≤ pol.C) (i : Cm.Idx) (x : Instance ppref) (hN : 0 < x.NB) :
    ¬ Serves ppref s.kap s.nf (fun _ => tbRef) pol i.index.val x :=
  Policy.TrueGuards.none_true s pol h1 h2 i x hN

/-- "Serves" fails through a range condition: at the reference table of scales the synthetic weights
"haltW" (Inst/Model/SanityRef.lean), which are well formed, serve no request under any policy. A
wide query entry of layer 0 is 36,631 at position 0, whatever the tokens. -/
theorem not_serves_at_haltW (pol : AcceptancePolicy) (x : Instance ppref) :
    ¬ Serves ppref Cm.sRef.kap Cm.sRef.nf (fun _ => tbRef) pol
      (Cm.Idx.ofIndex ⟨haltW, haltW_wf⟩).index.val x := by
  rintro ⟨hr, -, -⟩
  rw [Cm.index_ofIndex] at hr
  change RunsK ppref ppRef.kap ppRef.nf (fun _ => tbRef) haltW x.prompt at hr
  rw [Cm.kap_pp] at hr
  unfold RunsK at hr
  rw [Inst.Model.XK_const] at hr
  have h := ((hr.1 0 (by decide)).1 0 (by decide)).2.1 0 (by decide)
  have e : Att.qkw ppref tbRef (haltW.layer 0) 0 (X ppref tbRef haltW x.prompt (2 * 0)) 0 0 =
      36631 :=
    qkw_haltW x.prompt
  have h2 : Att.qkw ppref tbRef (haltW.layer 0) 0 (X ppref tbRef haltW x.prompt (2 * 0)) 0 0 <
      2 ^ 15 := h.2
  rw [e] at h2
  exact absurd h2 (by norm_num)

end Guards

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.serves_iff_isTrueUnder
#print axioms OnBytes.HonestTrace.modelR_of_serves
#print axioms OnBytes.HonestTrace.serves_tfae
#print axioms OnBytes.HonestTrace.traceRef
#print axioms OnBytes.HonestTrace.traceRef_eq_some_iff
#print axioms OnBytes.HonestTrace.traceRef_ryes
#print axioms OnBytes.HonestTrace.traceRef_below
#print axioms OnBytes.HonestTrace.ordsL_of_traceRef
#print axioms OnBytes.HonestTrace.serves_iff_meetsPolicy
#print axioms OnBytes.HonestTrace.serves_met
#print axioms OnBytes.HonestTrace.serves_met_counted
#print axioms OnBytes.HonestTrace.not_serves_of_low_theta
#print axioms OnBytes.HonestTrace.not_serves_at_haltW
