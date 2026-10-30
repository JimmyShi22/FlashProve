-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegNoReply.lean: the coefficient tables of the first 24 segments read the prompt alone:
not the reply, not the range.

Definitions and statements (`Cm.Seg.TS.Spec.no_reply` and two more); the proofs are in
Cm/TargetSegNoReplyProofs.lean. `segM s k` (Cm/TargetSegModel.lean) is segment k of the model's 25
at the table s of scales.

Why: by type the coefficient table of a term (Cb/Req/ReqSpec.lean: `Term.coef : X → ℕ → E`) reads
the whole instance, in every segment. The
reply occurs in the coefficients of the last segment only, and that is used: the reply goes out in a
separate round (paper/paper.pdf, Construction D.9, IOP^req, step 1(a)),
and no earlier message may depend on it. What the parties compute in a segment depends on the
instance through the coefficient tables alone: atoms of the first two kinds do not read the
instance by type; a sum atom reads it through the tables of its own terms. So the property is
stated on the tables, term by term, also under inner sums; that the conditions' truth does not
depend on the reply would be weaker and would not serve.

Main names:
  `sameT ts x x'`: all terms of the list have the same coefficient table at the instances x and x'.
  `sameA a x x'`: an atom: nothing for the first two kinds; for a sum atom: `sameT` of its terms.
  `sameF f x x'`: a family: its terms, and all its numbered atoms.
  `sameS S x x'`: a segment: all its families of identities and of keys.
  `Spec.no_reply`: see its docstring. (Of the two requests x, x' the range (r, e) and the reply y
    may differ.)
  `Spec.no_instance`: the segments 1 to 23 do not read the request at all; of the first 24
    segments, segment 0 alone can read the prompt (in the embedding's identity).
  `Spec.reply_read`: a guard: the property is not empty talk: the last segment does not have it:
    for every s there are two requests with the same prompt and the same range at which
    `sameS (segM s 24)` fails. (A request has four fields: prompt, y, r, e; so the two differ in y
    alone.)

Limits: the other half of what the reply's round needs is owed: in a segment the tables are all
that the verifier reads of the instance; the honest prover's messages depend also on its cells:
that the honest trace's matrices of the segments before the last are the same at two requests with
the same prompt (they are the forward pass on the prompt) is not stated here. Nothing on protocols:
that the messages of a segment's blocks are functions of tables and cells is the builder's matter.
The last segment's tables read range, checked tokens and reply.
Terms: lean/GLOSSARY.md.
-/
import Cm.TargetSegModel

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All

section
variable {X F E : Type}

/-- the terms have the same coefficient tables at x and x' -/
def sameT (ts : List (Term X E)) (x x' : X) : Prop := ∀ t ∈ ts, ∀ b, t.coef x b = t.coef x' b

def sameA (a : Atom X E) (x x' : X) : Prop :=
  match a with
  | .base _ => True
  | .sum _ P => sameT P.terms x x'

def sameF (f : Fam X E) (x x' : X) : Prop := sameT f.terms x x' ∧ ∀ j < f.na, sameA (f.atom j) x x'

/-- all coefficient tables of the segment are the same at x and x' -/
def sameS (S : SegSpec X F E) (x x' : X) : Prop :=
  (∀ f ∈ S.idn, sameF f x x') ∧ ∀ k ∈ S.keys, sameF k.1 x x'

end

namespace Spec

/-- No coefficient table before the last segment reads more of a request than its prompt. -/
def no_reply : Prop :=
  ∀ (s : Scales) (k : ℕ),
    k < 24 → ∀ x x' : Instance ppref, x.prompt = x'.prompt → sameS (segM s k) x x'

/-- The segments 1 to 23 do not read the request. -/
def no_instance : Prop :=
  ∀ (s : Scales) (k : ℕ), 1 ≤ k → k < 24 → ∀ x x' : Instance ppref, sameS (segM s k) x x'

/-- The last segment reads the reply. -/
def reply_read : Prop :=
  ∀ s : Scales, ∃ x x' : Instance ppref,
    x.prompt = x'.prompt ∧ x.rF = x'.rF ∧ x.eF = x'.eF ∧ ¬ sameS (segM s 24) x x'

end Spec

end Cm.Seg.TS
