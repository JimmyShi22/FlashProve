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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3SegRefToyGrpSend.lean: a tool for small example instances: the
first step in which the prover sends oracle messages (a sending), by the library's standard honest
sender. It is the first sending of a request whose cells are a pair: the data of the oracle messages
that are no masks, and a ghost.

Definitions, statement (`Cb.GlJ3.Spec.ldToyFirstG`) and proof. A tool for guards against empty
theorems; no parameter of a protocol.
The family is that of Cb/GlVal/GlJ3SegRefToyGrp.lean (G : `GrpD I O`). The further witness at the
start has the type PI × ((Dn → E) × Gh) (Gh: the ghost); c : Dn → E are the data, and `name n` names
the entry that is to hold c n (it does if `name n` is a datum and `name` is injective: the
statement's hypotheses).

Main names:
  `G.firstG A name h w0`: the first sending: `LdSendD.std` (Cb/Obj/LdObjectSenders.lean) at the
    stage `LdStage.start E Kc A` (Cb/Req1/LdReqStart.lean), with independent seeds and `LJ3` as the
    bound on lists.
  `Spec.ldToyFirstG` states: if every `name n` is a datum (`h`) and `name` is injective:
    `(G.firstG ..).Hyp` (`LdSendD.Hyp`, Cb/Req1/LdSegKit.lean); what is read back off any messages m
    is (.., (fun n => the entry `G.at' (name n)` of m), ..); the first and the last component of the
    further witness are handed on; the sending is a standard one, by definition (`LdSendD.StdAt`,
    Cb/Req1/LdReqStdLay.lean).

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `GrpD` with `ldToyGrp`, Cb/GlVal/GlJ3SegRefToyGrp.lean, and `LJ3`,
Cb/GlVal/GlJ3Base.lean; G, the relation A and the names are parameters): the fields are F, the
integers modulo 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). The toys' code is
that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4, distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness).

Limits: this file says nothing on freshness (`Spec.ldReqStdLay_fresh`, Cb/Req1/LdReqStdLay.lean, has
`StdAt` and `Y.OK` among its premises), nor on the entry step behind the sending. Pads in the
subfield F are not exercised.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyNum
import Cb.GlVal.GlToyLkpNames
import Cb.GlVal.GlJ3Send
import Cb.GlVal.GlToyConfM
import Cb.GlVal.GlJ3PackNames
import Cb.GlVal.GlJ3SegRefToyGrp
import Cb.GlVal.GlJ3SegRefToySend
import Cb.Req1.LdReqStdLay
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl hiding p
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace GrpD
variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq O] (G : GrpD I O)
  {Kc Xi PI Gh Dn : Type} {E0 : ExtSpec} (A : Rels Kc Xi E0 (PI × ((Dn → E) × Gh)))
  (name : Dn → I) (h : ∀ n, ¬ G.fr (name n))

open Classical in
/-- The data: at `name n`: c n, if `name` is injective (in general c n' for a chosen n' with the
same name); at every other name: 0. -/
def valN (w : (Sig.nil E).Wit × (PI × ((Dn → E) × Gh))) (i : I) : E :=
  if e : ∃ n, name n = i then w.2.2.1 e.choose else 0

/-- What is read back: (the first component handed on, (the data entries at the names, the last
component handed on)). -/
def bkN (x : ∀ a, G.Y.Dt a → E) (w' : PI × (Unit × Gh)) : PI × ((Dn → E) × Gh) :=
  (w'.1, (fun n => x (G.mem (name n)) ⟨(⟨name n, rfl⟩ : G.X (G.mem (name n))), h n⟩, w'.2.2))

/-- The first sending. -/
@[reducible] def firstG
    (w0 : (LdStage.start E Kc A).S.Wit × (LdStage.start E Kc A).Wp) :
    LdSendD (LdStage.start E Kc A) :=
  LdSendD.std (LdStage.start E Kc A) G.N (Sig.Seeds.indep G.N) (PI × (Unit × Gh)) (fun _ => LJ3)
    (fun _ => 3) G.Y (G.dat (valN name)) (fun w => (w.1, ((), w.2.2))) (G.bkN name h) w0

end GrpD

open Iop Prob Hiop Blocks Cb.Ood IOR in
def Spec.ldToyFirstG : Prop :=
  ∀ (I O : Type) [Fintype I] [Fintype O] [DecidableEq O] (G : GrpD I O) (Kc Xi PI Gh Dn : Type)
      (E0 : ExtSpec) (A : Rels Kc Xi E0 (PI × ((Dn → E) × Gh))) (name : Dn → I)
      (h : ∀ n, ¬ G.fr (name n)) (w0 : (LdStage.start E Kc A).S.Wit × (LdStage.start E Kc A).Wp),
    Function.Injective name →
    (G.firstG A name h w0).Hyp ∧
    (∀ (m : G.N.Msg) (w' : PI × (Unit × Gh)),
      (G.firstG A name h w0).bk m w' = (w'.1, (fun n => G.N.ents m (G.at' (name n)), w'.2.2))) ∧
    (∀ w, ((G.firstG A name h w0).D.rest w).2.1 = w.2.1) ∧
    (∀ w, ((G.firstG A name h w0).D.rest w).2.2.2 = w.2.2.2) ∧
    (G.firstG A name h w0).StdAt
      E G.Y (G.dat (GrpD.valN name)) (fun w => (w.1, ((), w.2.2))) (G.bkN name h) w0

open Iop Prob Hiop Blocks Cb.Ood IOR in
theorem ldToyFirstG : Spec.ldToyFirstG := by
  intro I O _ _ _ G Kc Xi PI Gh Dn E0 A name h w0 hn
  obtain ⟨-, -, -, e2, -, hY, hL, hl, he, -, -⟩ := ldToyGrp I O G
  refine ⟨ldSendD_std E E Kc (LdStage.start E Kc A) G.N (Sig.Seeds.indep G.N) _ (fun _ => LJ3)
      (fun _ => 3) G.Y _ _ (G.bkN name h) w0 hY (fun w => ?_) hL
      (ldSendFam_fair_indep E G.N).1 hl he,
    fun m w' => ?_, fun _ => rfl, fun _ => rfl, rfl⟩
  · have e : (fun n => GrpD.valN name w (name n)) = w.2.2.1 := funext fun n => by
      have hx : ∃ n', name n' = name n := ⟨n, rfl⟩
      unfold GrpD.valN
      rw [dif_pos hx, hn hx.choose_spec]
    show (w.2.1, ((fun n => GrpD.valN name w (name n)), w.2.2.2)) = w.2
    rw [e]
  · refine Prod.ext rfl (Prod.ext (funext fun n => ?_) rfl)
    show m (G.mem (name n))
        (G.Y.atD (G.mem (name n)) ⟨(⟨name n, rfl⟩ : G.X (G.mem (name n))), h n⟩) =
      G.N.ents m (G.at' (name n))
    rw [e2 (name n) (h n)]
    rfl

end Cb.GlJ3
