-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskLift2.lean: the item "masked messages" of the assembled lookup, `LkAsm2`, carried
from the base chain to the forms that callers use.
Callers use the lookup in three forms: with its read-out (`baseA`, `baseN`), over a signature of
oracle messages (`subN`), and with an encoded index (`subIN`).

Definitions, statements (in `Cb.Spec`) and proofs. Glue: no new protocol, and nothing is said here
on whether the chain has the item.

`H.MM D` asks five things: the block sends no oracle; `H.withheld w x` is always empty; the honest
prover's plain parts are `D.msg` at `D.kc w`, `D.pub x` and ρ; `D.Cl` is kept under `D.put`; and
where `D.Cl xp k` holds, `D.msg (D.put M k) xp ρ` over uniform M has the distribution `D.sim xp ρ`.
`GoodM` is `GoodB` (`GoodT` without the clause `exact`) with `H.MM D`, and the clause that every (x,
y, w) in the honest relation meets `D.Cl (D.pub x) (D.kc w)`. Here `MM` is the conclusion of
`Spec.mjLift2_subN` and `Spec.mjLift2_subIN`; `GoodM` stands in no statement of this file. (In the
first two sentences `D : MaskData ..` and `M : D.Mk` are the letters of Ior/Masked.lean; the two
statements have `A.dmN ι S Dc Cc rd` and `A.dmIN ι C S Dc Cc rd` for that `D`.)

The hypothesis of every statement, but for `Spec.mjLift2_clN` and `Spec.mjLift2_clIN`, which take Dc
and Cc without the `Link`: an `MJ` record Dc for the chain before the read-out (`A.chainA` of
Cb/Ld/LdLkpAsm2.lean) with `Dc.Link .. rd rd Sr Sw Cc` (Cb/Ld/LdLkpMaskSp.lean): the chain, started
with the claim Cc, has the item, hands the entries on unchanged and ends with `nxt` (`MJ.Fits`,
Cb/Ld/LdLkpMaskChain.lean); its messages read the entries in Sr only; its own masks lie in Sw.

Main names:
  `A.mjA Dc`, `A.mjN ι Dc`: the `MJ` records after the read-out (a step without rounds): all
    entries; the named entries.
  `Spec.mjLift2_baseA`, `Spec.mjLift2_baseN`: the same `Link` for `A.baseA`, `A.baseN ι`.
  `A.dmN ι S Dc Cc rd`, `Spec.mjLift2_subN`: over a signature: the honest side of `A.subN ι` has the
    item (Ior/Masked.lean: `MM`); of a witness is read what rd reads of (messages, further witness):
    no encoding randomness.
  `A.dmIN ι C S Dc Cc rd`, `Spec.mjLift2_subIN`: with an encoded index: the honest side of
    `A.subIN ι` has the item; of a witness is read what rd reads of (message of the prover encoded
    index, messages).
  `Spec.mjLift2_clN`, `Spec.mjLift2_clIN`: the relation gives the claim: if "every key in the table,
    and Mu" at the entries gives Cc at the reading, then the exact input relation of the lookup
    (over S; with an index) gives the item's claim.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2Pull
import Cb.Ld.LdLkpMaskSp
import Cb.Ld.LdWfIdxProofs

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section
namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E) {N : Type} (ι : N → A.J)

section
variable {Ex : ExtSpec} {M Wp Kc : Type} {msg : M → A.J → E}

/-- The `MJ` records after the read-out. -/
def mjA (Dc : MJ E A.J (A.chainA Ex M Wp Kc msg).R) : MJ E A.J (A.baseA Ex M Wp Kc msg).R :=
  Dc.post (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd
def mjN (Dc : MJ E A.J (A.chainA Ex M Wp Kc msg).R) : MJ E A.J (A.baseN ι Ex M Wp Kc msg).R :=
  Dc.post (fun o => some (A.rdN ι o)) (ExtMap.id Ex) (A.rdN ι)

end

/-- The `MaskData` over a signature. -/
def dmN (S : Sig E) {E₀ : ExtSpec} {Kc Wp : Type} {msg : S.Msg → A.J → E}
    (Dc : MJ E A.J (A.chainA E₀ S.Msg Wp Kc msg).R)
    (Cc : A.St → (A.J → E) → Prop) (rd : S.Msg × Wp → A.J → E) :
    MaskData (A.subN ι S E₀ Kc Wp msg).R (S.Wit × Wp) :=
  ((((A.mjN ι Dc).narrow Cc).data rd).keep S.Smp S.ext).mapW fun w => (S.msgs w.1, w.2)

/-- The `MaskData` with an encoded index. -/
def dmIN (C : ConfigurationWithOutOfDomainSample) (S : Sig E) {msg : C.Msg × S.Msg → A.J → E}
    (Dc : MJ E A.J (A.chainA C.E0 (C.Msg × S.Msg) Unit Unit msg).R) (Cc : A.St → (A.J → E) → Prop)
    (rd : (C.Msg × S.Msg) × Unit → A.J → E) :
    MaskData (A.subIN ι C S msg).R (S.Wit × (C.PIdx × Unit)) :=
  idxMask C S (((A.mjN ι Dc).narrow Cc).data rd)

end LkAsm2
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def mjLift2_baseA : Prop :=
  ∀ (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E)
      (Dc : MJ E A.J (A.chainA Ex M Wp Kc msg).R) (rd : M × Wp → A.J → E)
      (Sr Sw : A.J → Prop) (Cc : A.St → (A.J → E) → Prop),
    Dc.Link (A.chainA Ex M Wp Kc msg).H rd rd Sr Sw Cc →
    (A.mjA Dc).Link (A.baseA Ex M Wp Kc msg).H rd rd Sr Sw Cc

def mjLift2_baseN : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type)
      (msg : M → A.J → E) (Dc : MJ E A.J (A.chainA Ex M Wp Kc msg).R) (rd : M × Wp → A.J → E)
      (Sr Sw : A.J → Prop) (Cc : A.St → (A.J → E) → Prop),
    Dc.Link (A.chainA Ex M Wp Kc msg).H rd rd Sr Sw Cc →
    (A.mjN ι Dc).Link (A.baseN ι Ex M Wp Kc msg).H rd rd Sr Sw Cc

/-- Over a signature. -/
def mjLift2_subN : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
      (msg : S.Msg → A.J → E) (Dc : MJ E A.J (A.chainA E₀ S.Msg Wp Kc msg).R)
      (rd : S.Msg × Wp → A.J → E) (Sr Sw : A.J → Prop) (Cc : A.St → (A.J → E) → Prop),
    Dc.Link (A.chainA E₀ S.Msg Wp Kc msg).H rd rd Sr Sw Cc →
    (A.subN ι S E₀ Kc Wp msg).H.MM (A.dmN ι S Dc Cc rd)

/-- With an encoded index. -/
def mjLift2_subIN : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E)
      (Dc : MJ E A.J (A.chainA C.E0 (C.Msg × S.Msg) Unit Unit msg).R)
      (rd : (C.Msg × S.Msg) × Unit → A.J → E) (Sr Sw : A.J → Prop) (Cc : A.St → (A.J → E) → Prop),
    Dc.Link (A.chainA C.E0 (C.Msg × S.Msg) Unit Unit msg).H rd rd Sr Sw Cc →
    (A.subIN ι C S msg).H.MM (A.dmIN ι C S Dc Cc rd)

/-- Under the hypotheses of its statement, the relation gives the claim, over a signature. -/
def mjLift2_clN : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Mu : A.St → (A.J → E) → Prop) (S : Sig E)
      (E₀ : ExtSpec) (Kc Wp : Type) (R0 : Rels Kc A.St E₀ (S.Msg × Wp))
      (msg : S.Msg → A.J → E) (Dc : MJ E A.J (A.chainA E₀ S.Msg Wp Kc msg).R)
      (rd : S.Msg × Wp → A.J → E) (Cc : A.St → (A.J → E) → Prop),
    (∀ st w, A.lk.inP Mu st (msg w.1) → Cc st (rd w)) →
    ∀ x y w, (S.over (cj R0 msg id (A.lk.inP Mu) A.lk.inR)).rel x y w →
      (A.dmN ι S Dc Cc rd).Cl ((A.dmN ι S Dc Cc rd).pub x) ((A.dmN ι S Dc Cc rd).kc w)

/-- Under the hypotheses of its statement, the relation gives the claim, with an encoded index. -/
def mjLift2_clIN : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Mu : A.St → (A.J → E) → Prop) (C : ConfigurationWithOutOfDomainSample) (S : Sig E)
      (rc : A.St → C.Rec) (R0 : Rels Unit A.St C.E0 ((C.Msg × S.Msg) × Unit))
      (msg : C.Msg × S.Msg → A.J → E)
      (Dc : MJ E A.J (A.chainA C.E0 (C.Msg × S.Msg) Unit Unit msg).R)
      (rd : (C.Msg × S.Msg) × Unit → A.J → E) (Cc : A.St → (A.J → E) → Prop),
    (∀ st w, A.lk.inP Mu st (msg w.1) → Cc st (rd w)) →
    ∀ x y w, (S.over (idxAt C rc (cj R0 msg id (A.lk.inP Mu) A.lk.inR))).rel x y w →
      (A.dmIN ι C S Dc Cc rd).Cl ((A.dmIN ι C S Dc Cc rd).pub x) ((A.dmIN ι C S Dc Cc rd).kc w)

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

theorem mjLift2_baseA : Spec.mjLift2_baseA E := fun A Ex _ _ _ _ _ rd _ _ _ h =>
  mjl_post h (fun o => some (A.rd o)) (ExtMap.id Ex) A.rd (fun o => (A.rd o.1, o.2)) rd
    (fun _ => rfl) fun _ => rfl

theorem mjLift2_baseN : Spec.mjLift2_baseN E := fun A _ ι Ex _ _ _ _ _ rd _ _ _ h =>
  mjl_post h (fun o => some (A.rdN ι o)) (ExtMap.id Ex) (A.rdN ι) (fun o => (A.rdN ι o.1, o.2)) rd
    (fun _ => rfl) fun _ => rfl

theorem mjLift2_subN : Spec.mjLift2_subN E := by
  intro A N ι S E₀ Kc Wp msg Dc rd Sr Sw Cc h
  have h1 := mm_keep _ _ _ _ _ _ _ _ _ S.Smp S.ext
    (mjl_mm (mjLift2_baseN E A N ι E₀ S.Msg Wp Kc msg Dc rd Sr Sw Cc h))
  exact mm_mapW _ _ _ _ _ _ (S.Wit × Wp) _ (S.Wit × Wp) _ _
    (fun w : S.Wit × Wp => (S.msgs w.1, w.2))
    (fun (w : S.Wit × Wp) (o : S.Msg × Wp) => (w.1, o.2)) h1

theorem mjLift2_subIN : Spec.mjLift2_subIN E := fun A N ι C S msg Dc rd Sr Sw Cc h =>
  idxLift_mm E C S _ _ Unit Unit _ _ _
    (mjl_mm (mjLift2_baseN E A N ι C.E0 (C.Msg × S.Msg) Unit Unit msg Dc rd Sr Sw Cc h))

theorem mjLift2_clN : Spec.mjLift2_clN E := fun _ _ _ _ S _ _ _ _ _ _ _ _ hC x _ w h =>
  hC x.1 (S.msgs w.1, w.2) h.2.2.2

theorem mjLift2_clIN : Spec.mjLift2_clIN E := fun _ _ _ _ C S _ _ _ _ _ _ hC x _ w h =>
  hC x.1 (idxIn C (S.msgs w.1, w.2)) h.2.2.2.2

end
end Cb
