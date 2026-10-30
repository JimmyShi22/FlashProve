-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartLink.lean: the link's part (`PLink`) of an instance of the object with the terms
that the library builds for its sub-protocols (`LdObjT`, Cb/Obj/LdObjectTerms.lean). This part is
built with standard parts.


The object (`LdObj`, Cb/Obj/LdObject.lean) is one record with a configuration and, over it, the
sub-protocols of the proof system, as five terms. Cb/Obj/LdObjectParts.lean cuts the record `LdObjP`
(Cb/Obj/LdObjectPlan.lean), from which an object is made, and its hypotheses into five parts. The
link is the sub-protocol for `ConfigurationWithOutOfDomainSample.Req` (Hiop/RecConf.lean): two encoded indices hold the same
index.
A definition, theorems. Cb/Obj/LdObjectParts.lean asks of the link a record `PLink Cf` and the
bundle `Lk.Hyp` (the sending; the pair of conditions on the two encoded indices fits (`fitsK`); the
two folds' bad points; distinct places; the test needs no more positions than the sent words bear;
the closing).

Main names:
  `D.part L t ε₀ ε₁` (`D : StdLk Cf P`, Cb/Obj/LdObjectLinkStd.lean). `stdLk_part`: its bundle, for
    non-empty `Fin Cf.C₀.n` and P, from the conditions on codes of `Cb.ldOl_std`, the bounds on the
    two folds' bad points (`hF`), distinct places (`hpl`) and tb ≤ t (`ht`). The conditions on codes
    ask `D.M.OK L t` (`hM`); that the member's code (`D.M.Cm`) has distance `D.d` (`hd`) above its
    radius `D.M.e` (`he`) and is transparent (`htr`); that every code at these positions
    (`LdCode E P`) with its laws and distance `D.d` has lists of at most `D.Lc` (`hl`) and of at
    most `D.L2` (`hl2`) at the radius; and that every code at these positions with its laws has at
    most `D.bad` exceptional coefficients at the radius (`hm`).




Notation: `L`, `t`: natural numbers (`LdLkP.Snd`, Cb/Ld/LdLink.lean: the numbers of the sending:
bounds on the lists, numbers of long positions that the encodings bear); `ε₀`, `ε₁`: natural
numbers, in `LdLkP.FoldErr` (Cb/Ld/LdLink.lean):
`∀ f rec, on0 f rec → cnt (P.D.X.Bad f rec P.e₀) ≤ ε₀` and
`∀ f rec, on1 f rec → cnt (P.D.X.Bad f rec P.e₁) ≤ ε₁`.

Limits: this file says nothing on the other four parts.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectParts
import Cb.Obj.LdObjectToy7
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  [Nonempty (Fin Cf.C₀.n)] {P : Type} [Fintype P] [Nonempty P] (D : StdLk Cf P)

/-- The link with standard parts, as a part. -/
@[reducible] def StdLk.part (L t ε₀ ε₁ : ℕ) : PLink Cf where
  K := D.K
  Sl := D.S L t
  ε₀ := ε₀
  ε₁ := ε₁
  Kc := D.Kc
  dK₂ := (fun _ => (fun _ => 0, fun _ => 0), (fun _ _ => 0, fun _ _ => 0))
  dK := (fun _ _ => 0, fun _ _ => 0)

omit [Fintype F] in
theorem stdLk_part {L t ε₀ ε₁ : ℕ} (hF : D.K.P.FoldErr D.K.free D.K.free ε₀ ε₁)
    (hpl : Function.Injective D.pl) (hM : D.M.OK L t) (hd : D.M.Cm.Dist D.d)
    (htr : D.M.Cm.Transparent) (he : D.M.e < D.d)
    (hl : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.M.e D.Lc)
    (hl2 : ∀ C : LdCode E P, C.Laws → C.Dist D.d → C.ListAt D.M.e D.L2)
    (hm : ∀ C : LdCode E P, C.Laws → C.MCAat D.M.e D.bad) (ht : D.tb ≤ t) :
    (D.part L t ε₀ ε₁).Hyp :=
  ⟨stdLk_snd D hM, ⟨fun _ _ _ h => h, fun _ _ h => h⟩, hF, hpl,
    fun _ => ht, stdLk_cl D hM hd htr he hl hl2 hm⟩

end

end Cb
