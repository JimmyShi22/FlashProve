-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm2Pull.lean: the assembled lookup `LkAsm2` (Cb/Ld/LdLkpAsm2.lean), the rest of the
interface: the wide predicate on multiplicities, the number of rows, what rows and mask form read,
the read-out on named entries, the version with an encoded index, formats.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpAsm2PullProofs.lean.
The lookup is the sub-protocol for the claim that every key is an entry of a table (`Lk.inR`,
Cb/Ld/LdLkp.lean). Its main statements are in Cb/Ld/LdLkpAsm2.lean; this file adds further ones.
`BkA.Good` (Cb/Ld/LdLkpTreeP.lean) is `GoodAt` (Cb/Ld/LdSigLift.lean) with the identity as
extractor: among its fields, completeness in the sense of `Honest.Acc` (Ior/Honest.lean) and, for
each fixed tuple of messages, round-by-round knowledge soundness (`Know`, Ior/Know.lean).
At the base means between joints in which the tuple of messages is a part of the witness (`BkA`,
Cb/Ld/LdLkpTreeP.lean), before the lift over a signature (Cb/Ld/LdSigLift.lean).
This file's statements are those of `LkAsm` (Cb/Ld/LdLkpAsm.lean) in Cb/Ld/LdLkpAsmMore.lean,
Cb/Ld/LdLkpSupp.lean and Cb/Ld/LdLkpAsmPull.lean, word for word, at the data and the chain of
Cb/Ld/LdLkpAsm2.lean, with `H.MuOn` for `H.MuOK`.

Main names:
  `ldLkpAsm2_muValid`: if n + 1 ≤ 2^w, `A.ValidMu` meets `H.MuOn` (Cb/Ld/LdLkpHead2.lean).
  `A.nRows`: the number of rows, one row fewer than `LkAsm` (Cb/Ld/LdLkpAsm.lean).
  `ldLkpAsm2_ok_valid`, `ldLkpAsm2_ok_first`: under `A.H.lkb.Adm p`, p the characteristic of E,
    `A.sub` is `SubR.OK` with `A.ValidMu`, and with the counts by the first-occurrence rule.
  `A.PlacesIn G`: G holds of all places that the data name (`LkAsm2` has no field cE, which `LkAsm`
    has). `ldLkpAsm2_suppRows`, `ldLkpAsm2_suppForm`: under it, all rows and the mask form are 0
    outside G.
  `A.rdN ι`, `A.baseN ι`, `A.subN ι`, `A.baseIN ι`, `A.subIN ι`: the read-out on the entries named
    by ι : N → A.J; at the base; over a signature; on tuples (message of the index, messages), at
    the base and over a signature.
  `ldLkpAsm2N_base`, `ldLkpAsm2N_ok`, `ldLkpAsm2N_idx`: good at the base; `SubR.OK`; with an encoded
    index decoded by the statement. Conditions of all three: ι injective; `A.PlacesIn` of the range
    of ι; `A.H.lkb.Adm p`, p the characteristic of E; `A.H.MuOn Mu`.
  `ldLkpAsm2N_idxStep`, `ldLkpAsm2N_passes`, `ldLkpAsm2N_same`: formats of `A.subIN`: further
    oracles not read, not tied, copied; state and samples handed on; the honest prover ends with the
    witness with which it began.

Limits: this file says nothing on zero knowledge, on places pairwise different, or on errors.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2
import Cb.Ld.LdLkpSupp
import Cb.Ld.LdLkpMult
import Cb.Ld.LdWfIdx

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section
namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E)

/-- The vector is the multiplicities, wide form. -/
def ValidMu : A.St → (A.J → E) → Prop := fun st m =>
  Valid (A.v' + 1) A.d A.w (A.n + 1) (A.key st m) (A.tab st) (A.H.bit m)

/-- The number of rows. -/
def nRows : ℕ := (A.n + 1) + ((A.v' + 1) + ((A.d + 3) + 1))

/-- G holds of all places that the data name. -/
structure PlacesIn (G : A.J → Prop) : Prop where
  bAt : ∀ u j, G (A.bAt u j)
  wS  : ∀ i, G (A.wS i)
  cS  : ∀ b, G (A.cS b)
  wAt : ∀ l i, G (A.wAt l i)
  cAt : ∀ l b, G (A.cAt l b)
  wK  : ∀ l i, G (A.wK l i)
  cK  : ∀ l b, G (A.cK l b)
  wT  : ∀ l i, G (A.wT l i)
  cT  : ∀ l b, G (A.cT l b)
  wE  : ∀ i, G (A.wE i)
  wB  : ∀ i, G (A.wB i)
  cB  : G A.cB

variable {N : Type} (ι : N → A.J)

/-- The read-out on the named entries. -/
def rdN (o : A.XB) : TX A.St E N := ((A.rd o).1, (A.rd o).2.1.pull ι, (A.rd o).2.2.map (Row.pull ι))

/-- the entries named by N -/
def entN (m : A.J → E) : N → E := fun n => m (ι n)

/-- At the base. -/
def baseN (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) : BkA Kc M A.St (TX A.St E N) Ex Wp :=
  (A.chainA Ex M Wp Kc msg).postM (A.rdN ι)

/-- Over a signature. -/
def subN (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) :
    SubR S E₀ Kc A.St N Wp :=
  ⟨(A.baseN ι E₀ S.Msg Wp Kc msg).R.keep S.Smp S.ext,
    S.liftH (A.baseN ι E₀ S.Msg Wp Kc msg).H,
    fun _ _ w => w,
    (A.baseN ι E₀ S.Msg Wp Kc msg).P.keep S.Smp S.ext⟩

/-- On tuples (message of the index, messages). -/
def baseIN (C : ConfigurationWithOutOfDomainSample) (M : Type) (msg : C.Msg × M → A.J → E) :
    BkA Unit M A.St (TX A.St E N) C.E0 (C.PIdx × Unit) :=
  ⟨(A.baseN ι C.E0 (C.Msg × M) Unit Unit msg).R,
    idxH C (A.baseN ι C.E0 (C.Msg × M) Unit Unit msg).H,
    (A.baseN ι C.E0 (C.Msg × M) Unit Unit msg).P⟩

def subIN (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E) :
    Sub S S C.E0 A.St N (C.PIdx × Unit) :=
  ⟨(A.baseIN ι C S.Msg msg).R.keep S.Smp S.ext,
    S.liftH (A.baseIN ι C S.Msg msg).H,
    fun _ _ w => w,
    (A.baseIN ι C S.Msg msg).P.keep S.Smp S.ext⟩

end LkAsm2
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def ldLkpAsm2_muValid : Prop := ∀ A : LkAsm2 E, A.n + 1 ≤ 2 ^ A.w → A.H.MuOn A.ValidMu

def ldLkpAsm2_len : Prop := ∀ (A : LkAsm2 E) (o : A.XB), (A.rd o).2.2.length = A.nRows

def ldLkpAsm2_out_len : Prop :=
  ∀ (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) x y τ xo,
    (A.baseA Ex M Wp Kc msg).R.out x y τ = some xo → xo.2.2.length = A.nRows

def ldLkpAsm2_sub_len : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) x y τ xo,
    (A.sub S E₀ Kc Wp msg).R.out x y τ = some xo → xo.1.2.2.length = A.nRows

def ldLkpAsm2_ok_valid : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
      (R0 : Rels Kc A.St E₀ (S.Msg × Wp)) (msg : S.Msg → A.J → E),
    A.H.lkb.Adm p →
    (A.sub S E₀ Kc Wp msg).OK
      ⟨A.v' + 1, A.d, fun st ym => A.key st (msg ym.2), A.tab, fun _ _ => True⟩
      (fun st ym => A.ValidMu st (msg ym.2)) R0 fun ym => msg ym.2

def ldLkpAsm2_ok_first : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
      (R0 : Rels Kc A.St E₀ (S.Msg × Wp)) (msg : S.Msg → A.J → E),
    A.H.lkb.Adm p →
    (A.sub S E₀ Kc Wp msg).OK
      ⟨A.v' + 1, A.d, fun st ym => A.key st (msg ym.2), A.tab, fun _ _ => True⟩
      (fun st ym => A.H.lkb.IsMult st (msg ym.2)) R0 fun ym => msg ym.2

/-- All rows of the read-out are 0 outside the named places. -/
def ldLkpAsm2_suppRows : Prop :=
  ∀ (A : LkAsm2 E) (G : A.J → Prop), A.PlacesIn G → ∀ o, RowsSupp G (A.rd o).2.2
/-- So is the mask form of the masked claim on the keys. -/
def ldLkpAsm2_suppForm : Prop :=
  ∀ (A : LkAsm2 E) (G : A.J → Prop), A.PlacesIn G → ∀ o, SuppIn G (A.rd o).2.1.mf

/-- The corollary for callers. -/
def ldLkpAsm2_suppOut : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) [Fintype N] (ι : N → A.J), Function.Injective ι →
    A.PlacesIn (fun j => j ∈ Set.range ι) →
    ∀ (o : A.XB) (k : ℕ) (f : ℕ → E) (m : A.J → E),
      (((A.rd o).2.1.pull ι).Holds k f (fun n => m (ι n)) ↔ (A.rd o).2.1.Holds k f m) ∧
      (RowsHold ((A.rd o).2.2.map (Row.pull ι)) (fun n => m (ι n)) ↔ RowsHold (A.rd o).2.2 m)

/-- At the base. -/
def ldLkpAsm2N_base : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec) (Kc M Wp : Type)
      (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOn Mu →
    (A.baseN ι Ex M Wp Kc msg).Good (cj R0 msg id (A.lk.inP Mu) A.lk.inR)
      (cj R0 msg Prod.fst (A.lk.out id (A.entN ι)) (A.lk.out id (A.entN ι)))

/-- The interface, with its clause (by type: they are forms on N) on what rows and mask form read.
-/
def ldLkpAsm2N_ok : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
      (R0 : Rels Kc A.St E₀ (S.Msg × Wp)) (msg : S.Msg → A.J → E),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOn Mu →
    (A.subN ι S E₀ Kc Wp msg).OK
      ⟨A.v' + 1, A.d, fun st ym => A.key st (msg ym.2), A.tab, fun _ _ => True⟩
      (fun st ym => Mu st (msg ym.2)) R0 fun ym => A.entN ι (msg ym.2)

/-- With an encoded index decoded by the statement. -/
def ldLkpAsm2N_idx : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (rc : A.St → C.Rec)
      (R0 : Rels Unit A.St C.E0 ((C.Msg × S.Msg) × Unit)) (msg : C.Msg × S.Msg → A.J → E),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOn Mu →
    GoodB (A.subIN ι C S msg).R (A.subIN ι C S msg).H
      (S.over (idxAt C rc (cj R0 msg id (A.lk.inP Mu) A.lk.inR)))
      (S.over (idxAt C (fun x => rc x.1)
          (cj R0 msg Prod.fst (A.lk.out id (A.entN ι)) (A.lk.out id (A.entN ι)))))
      (A.subIN ι C S msg).ext (A.subIN ι C S msg).P

def ldLkpAsm2N_plain : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseN ι Ex M Wp Kc msg).Plain
def ldLkpAsm2N_plainI : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (M : Type) (msg : C.Msg × M → A.J → E),
    (A.baseIN ι C M msg).Plain
def ldLkpAsm2N_idxStep : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E),
    (A.subIN ι C S msg).R.IdxStep
def ldLkpAsm2N_passes : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E),
    (A.subIN ι C S msg).R.Passes (fun x => x) (fun x => (x.1.1, x.2))
def ldLkpAsm2N_same : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E)
      (msg : C.Msg × S.Msg → A.J → E) w x c ρ,
    (((A.subIN ι C S msg).H.strat w x c).run ρ).2.2 = w

def ldLkpAsm2N_len : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec)
      (M Wp Kc : Type) (msg : M → A.J → E) x y τ xo,
    (A.baseN ι Ex M Wp Kc msg).R.out x y τ = some xo → xo.2.2.length = A.nRows

end
end Cb.Spec
