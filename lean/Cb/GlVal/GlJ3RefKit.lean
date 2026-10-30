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
Cb/Gen/CodeListRS.lean.) Cb/GlVal/GlJ3RefKit.lean: a small test instance of a sending of several
oracles at once: for any finite set of names, one word of two Reed-Solomon rows for each name, whose
message has two entries, a datum and a pad. Every hypothesis that is asked of such a step
(`LdSendD.Hyp`) is proved for it, under one hypothesis on the extractor.

Definitions, theorems. Building stone for toys; a guard against empty theorems; no parameter of a
protocol.

Conventions of this namespace's toys, said of the toys' own oracle messages and groups, not of what
a statement takes as a parameter (of the names declared in Cb/GlVal/ and Cb/Gl/GlField.lean this
file uses only the field E, `toyS` with its sender's and its own facts and `ld_toy`,
Cb/GlVal/GlJ3Send.lean, `toyLd` and `nu`, Cb/GlVal/GlToySend.lean, and `LJ3`,
Cb/GlVal/GlJ3Base.lean; the stage a and the set I of names are parameters): the fields are F, the
integers modulo p = 2^64 - 2^32 + 1, and E = F[x] / (x^3 - 2) (Cb/Gl/GlField.lean). The toys' code
is that of Cb/GlVal/GlToyBase4.lean: eight points, dimension 4, distance 5, hides 3.
The radius, the bounds on lists, the counts for agreement and the pad's coefficient of these toys
are told in the head of Cb/GlVal/GlJ3Base.lean: read it before quoting.
This is not said of the offline side (configuration, index, lookup tables, weights-formedness). The
names of codes, messages and their facts: Cb/GlVal/GlJ3Send.lean, Cb/GlVal/GlJ3StdNames.lean,
Cb/GlVal/GlJ3PackNames.lean.

Main names:
  `datSend_hyp`: all that a move "send" asks (`LdSendD.Hyp`), under `h`: see its docstring.

Limits: this file says nothing on real parameters: no security.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlJ3Send
import Cb.Ld.LdSendMem
import Cb.Req1.LdSegKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb.GlJ3
open Cb.Gl
open Iop Prob Hiop Blocks Cb.Ood

section
variable (I : Type) [Fintype I] [DecidableEq I]

/-- The family. -/
@[reducible] def datSig : Sig E := { O := I, om := fun _ => toyS }

variable {I}

/-- The datum of a member. -/
def datAt (m : (datSig I).Msg) (i : I) : E := m i (nu.symm (Sum.inl ()))

/-- Messages with given data. -/
def datMsg (v : I → E) : (datSig I).Msg := fun i j => Sum.elim (fun _ => v i) (fun _ => 0) (nu j)

theorem datAt_msg (v : I → E) (i : I) : datAt (datMsg v) i = v i := by
  show Sum.elim (fun _ => v i) (fun _ => (0 : E)) (nu (nu.symm (Sum.inl ()))) = v i
  rw [Equiv.apply_symm_apply]
  rfl

variable {W W' : Type}

/-- The sender of one member. -/
@[reducible] def datMem (val : W → E) (w0 : W) : toyS.Sender W Unit where
  N := (toyLd Bool).Nn
  upM := fun m => m
  upR := fun r => r
  Mk := E
  put := fun w k j => Sum.elim (fun _ => val w) (fun _ => k) (nu j)
  rest := fun _ => ()
  w0 := w0

/-- The sender of the family. -/
@[reducible] def datSnd (val : W → I → E) (rest : W → W') (w0 : W) :
    (datSig I).Sender W W' :=
  Sig.Sender.ofMem (N := datSig I) (fun a => datMem (fun w => val w a) w0) rest w0

theorem datMem_uniform (val : W → E) (w0 : W) : (datMem val w0).Uniform := fun ρ w =>
  toyD_uniform ρ (val w)

theorem datAt_put (val : W → I → E) (rest : W → W') (w0 : W) (w : W)
    (k : (datSnd val rest w0).Mk) (i : I) :
    datAt ((datSnd val rest w0).upM ((datSnd val rest w0).put w k)) i = val w i := by
  show Sum.elim (fun _ => val w i) (fun _ => k i) (nu (nu.symm (Sum.inl ()))) = val w i
  rw [Equiv.apply_symm_apply]
  rfl

end

section
variable {Kc : Type} (a : LdStage E Kc) (I : Type) [Fintype I] [DecidableEq I] (Wp' : Type)
  (bk : (datSig I).Msg → Wp' → a.Wp) (val : a.S.Wit × a.Wp → I → E)
  (rest : a.S.Wit × a.Wp → a.S.Wit × Wp') (w0 : a.S.Wit × a.Wp)

/-- The data of the move. -/
@[reducible] def datSendD : LdSendD a :=
  ⟨datSig I, Sig.Seeds.indep (datSig I), Wp', bk, datSnd val rest w0, fun _ => LJ3, fun _ => 1⟩

/-- All that a move "send" asks (`LdSendD.Hyp`), if, by `h`, `a.S.backN (datSig I) bk` gives w back
from `rest w` and any messages of the family whose data are `val w`. -/
theorem datSend_hyp
    (h : ∀ w (m : (datSig I).Msg),
      (∀ i, datAt m i = val w i) → a.S.backN (datSig I) bk m (rest w) = w) :
    (datSendD a I Wp' bk val rest w0).Hyp := by
  have hT := ld_toy Bool
  exact
  { laws := fun _ => hT.1
    fair := (ldSendFam_fair_indep E (datSig I)).1
    list := fun _ => sig_list_of_code E toyS LJ3 hT.2.2.2.1
    evades := fun _ => toyS_evades
    sender := ldSendMem_laws E (datSig I) _ _ _ rest w0 _ (fun _ _ _ => rfl) fun w k =>
      h w _ fun i => datAt_put val rest w0 w k i
    blind := ldSendMem_blind E (datSig I) _ _ _ rest w0 _ fun i =>
      ldSend_blind_of_uniform E toyS _ Unit _ (datMem_uniform (fun w => val w i) w0)
    hides := ldSendMem_hides E (datSig I) _ _ _ rest w0 _ fun _ => hT.2.2.2.2.2.2.1 }

end
end Cb.GlJ3
