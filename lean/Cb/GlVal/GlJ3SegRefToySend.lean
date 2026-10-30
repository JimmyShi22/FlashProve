-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
In this library the records through which a count for agreement is claimed (`IsGlJ`, `IsGlS`:
Cb/Gl/GlLdJ.lean; `IsGlCpJ`: Cb/Gl/GlCopy.lean) do not ask a
radius within half the distance, and the fact on agreement, `Gl.AgreeJ`, is stated nowhere as a
separate theorem: it follows, by one application that is written down nowhere, from `Cb.BCHKS46At`
(`Cb.Gl.glAg_ofAt`, Cb/Gl/GlFinalAg.lean), which this library proves in Cb/Bridge (bchks46At), from
files adapted from ArkLib and Mathlib (lean/LIMITS.md,
L15), and applies in second forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file
does not apply that proof.
So read the Lean text, not the words below, to see
what is a hypothesis here: neither "the statement on codes" nor "the fact on agreement" in these
words tells whether it is one.
A theorem with no premise rests on nothing unproved beyond Lean's three axioms (a theorem's premises
are the hypotheses in its statement; how the axioms are checked: lean/CHECKING.md). A theorem that
has the premise Gl.AgreeJ takes it as a hypothesis: this library states it nowhere as a separate
theorem (only its conclusion within half the distance: agreeHalf, Cb/Gl/GlAgreeHalf.lean). A
statement that has the premise Cb.BCHKS46, BCHKS46F or BCHKS46At takes it as a hypothesis; this file
does not prove it. Cb/Bridge/ proves BCHKS46 and BCHKS46At from the files under ThirdParty/,
which are adapted from ArkLib and Mathlib, and BCHKS46F follows from the first by one
line
(Cb.bchks46F_of_wide). Its
source: Theorem 4.6 of the full version (ePrint 2025/2055) of a paper published at STOC 2026; the
theorem is not in the proceedings, which state the plain form (their Theorem 1.5). Of a statement
with any other premise these lines say nothing: it rests on what that premise asks. (More on the
source, of which no full proof was checked for this library: the head of
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToySend.lean: a tool for small example instances: the
first step in which the prover sends oracle messages (a sending). It is the first sending of a
request whose cells are a pair: the data of the oracle messages that are no masks, and a ghost.

Definitions, statement (`Cb.GlJ3.Spec.ldToyFirst`) and proof. A tool for guards against empty
theorems; no parameter of a protocol.
The family has one datum a member (`datSig I`, Cb/GlVal/GlJ3RefKit.lean). The further witness at the
start has the type PI × ((Dn → E) × G) (G: the ghost); c : Dn → E are the data, and `name n` is the
member whose datum is to be c n (the statement's two hypotheses on `name` say so).

Main names:
  `firstD A Y name w0`: the first sending: `LayD.sendD` (Cb/GlVal/GlJ3RefSendD.lean) at the stage
    `LdStage.start E Kc A` (Cb/Req1/LdReqStart.lean), for any relation A on such witnesses and any
    layout Y (`LayD`, Cb/GlVal/GlJ3RefLay.lean).
  `Spec.ldToyFirst` states: if Y has a block (`Y.Bk`), `Y.val w (name n)` is the witness's c n, and
    no `name n` is a place `Y.pl b x`: `(firstD ..).Hyp` (`LdSendD.Hyp`, Cb/Req1/LdSegKit.lean); the
    first and the last component of the further witness are handed on.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `datSig`, `datAt`, Cb/GlVal/GlJ3RefKit.lean, `LayD` with `datum_off`,
Cb/GlVal/GlJ3RefLay.lean, and `sendD` with `sendD_hyp`, Cb/GlVal/GlJ3RefSendD.lean; the relation A,
the layout Y and the names are parameters): the fields are F, the integers modulo 2^64 - 2^32 + 1,
and E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). The toys' code is that of Cb/GlVal/GlToyBase4.lean:
eight points, dimension 4, distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: this file says nothing on freshness of the masks (`sendD_after_ent`, `sendD_after_wide`,
Cb/GlVal/GlJ3RefSendD.lean), nor on the entry step behind the sending. It does not say that the
relation can be met. Pads in the subfield F are not exercised. The bound that the toys write (one
hidden position: `(firstD ..).t`, from `sendD`, Cb/GlVal/GlJ3RefSendD.lean) is kept, though this
code hides 3.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3RefSendD
import Cb.Req1.LdReqStart
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {Kc Xi PI G Dn I : Type}
  {E0 : ExtSpec} [Fintype I] [DecidableEq I] (A : Rels Kc Xi E0 (PI × ((Dn → E) × G)))

/-- what is handed on: the further witness without the data; what is read back: (the first component
handed on, (the data at the names, the last component handed on)) -/
def fRest (w : (Sig.nil E).Wit × (PI × ((Dn → E) × G))) : (Sig.nil E).Wit × (PI × (Unit × G)) :=
  (w.1, (w.2.1, ((), w.2.2.2)))
def fBk (name : Dn → I) (m : (datSig I).Msg) (w' : PI × (Unit × G)) : PI × ((Dn → E) × G) :=
  (w'.1, (fun n => datAt m (name n), w'.2.2))

/-- The first sending. -/
@[reducible] def firstD
    (Y : LayD I ((LdStage.start E Kc A).S.Wit × (LdStage.start E Kc A).Wp)) (name : Dn → I)
    (w0 : (LdStage.start E Kc A).S.Wit × (LdStage.start E Kc A).Wp) :
    LdSendD (LdStage.start E Kc A) :=
  Y.sendD (LdStage.start E Kc A) (PI × (Unit × G)) (fBk name) fRest w0

end

open Iop Prob Hiop Blocks Cb.Ood IOR in
def Spec.ldToyFirst : Prop :=
  ∀ (Kc Xi PI G Dn I : Type) (E0 : ExtSpec) [Fintype I] [DecidableEq I]
      (A : Rels Kc Xi E0 (PI × ((Dn → E) × G)))
      (Y : LayD I ((LdStage.start E Kc A).S.Wit × (LdStage.start E Kc A).Wp)) (name : Dn → I)
      (w0 : (LdStage.start E Kc A).S.Wit × (LdStage.start E Kc A).Wp) (_ : Y.Bk),
    (∀ w n, Y.val w (name n) = w.2.2.1 n) → (∀ n b x, Y.pl b x ≠ name n) →
    (firstD A Y name w0).Hyp ∧
    (∀ w, ((firstD A Y name w0).D.rest w).2.1 = w.2.1) ∧
    ∀ w, ((firstD A Y name w0).D.rest w).2.2.2 = w.2.2.2

open Iop Prob Hiop Blocks Cb.Ood IOR in
theorem ldToyFirst : Spec.ldToyFirst := by
  intro Kc Xi PI G Dn I E0 _ _ A Y name w0 b hv hoff
  refine ⟨Y.sendD_hyp (LdStage.start E Kc A) _ (fBk name) fRest w0 b fun w ms m hm => ?_,
    fun _ => rfl, fun _ => rfl⟩
  show (w.1, (w.2.1, ((fun n => datAt m (name n)), w.2.2.2))) = w
  have e : (fun n => datAt m (name n)) = w.2.2.1 :=
    funext fun n => by rw [hm, Y.datum_off w ms _ (hoff n), hv]
  rw [e]

end Cb.GlJ3
