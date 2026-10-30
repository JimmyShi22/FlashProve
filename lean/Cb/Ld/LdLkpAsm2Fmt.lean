-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpAsm2Fmt.lean: the assembled lookup `LkAsm2` (Cb/Ld/LdLkpAsm2.lean): formats of `A.sub`;
every round's oracle part has at most one value; blindness to the masks of later blocks; the chain
as a Piece; the mask form reads two entries; its rows as a family of fixed size.

Definitions, statements (in `Cb.Spec`) and proofs. Glue; no protocol.
The lookup is the sub-protocol for the claim that every key is an entry of a table (`Lk.inR`,
Cb/Ld/LdLkp.lean). This file collects properties of its shape and of its honest prover.
`BkA.Good` (Cb/Ld/LdLkpTreeP.lean) is `GoodAt` (Cb/Ld/LdSigLift.lean) with the identity as
extractor: among its fields, completeness in the sense of `Honest.Acc` (Ior/Honest.lean) and, for
each fixed tuple of messages, round-by-round knowledge soundness (`Know`, Ior/Know.lean).
This file has the statements of `LkAsm` (Cb/Ld/LdLkpAsm.lean), word for word, at the data and the
chain of Cb/Ld/LdLkpAsm2.lean, with `H.MuOn` for `H.MuOK`: from Cb/Ld/LdLkpFormatAsm.lean
(ldLkpFmt_*), Cb/Ld/LdLkpFormatPiece.lean (`noOrcs_base`, `ldLkpFmt_blind`),
Cb/Ld/LdLkpFormatBlindIdx.lean (`ldLkpFmt_blindIdx`), Cb/Ld/LdLkpMaskAsmPiece.lean
(`ldLkpMaskAsm_piece`), Cb/Ld/LdLkpSuppFine.lean (`FormIn`, ldLkpSuppF_*), Cb/Ld/LdLkpAsmFam.lean
(`rdF`, `baseF`, ldLkpAsmF_*). All that is generic there is used as it stands.

Main names:
  `ldLkpFmt2_plain`, `ldLkpFmt2_pass`, `ldLkpFmt2_idx`, `ldLkpFmt2_passes`, `ldLkpFmt2_same`,
  `ldLkpFmt2_hands`, `ldLkpFmt2_need`, `ldLkpFmt2_bud`, `ldLkpFmt2_free`, `ldLkpFmt2_bears`:
  `A.baseA` is plain (`BkA.Plain`, Cb/Ld/LdLkpFormat.lean) and hands the state on; `A.sub`: further
  oracles not read, not tied, copied; state and samples handed on; the honest prover ends with its
  witness; budgets.
  `noOrcs2_chain`, `noOrcs2_baseN`: every round's oracle part has at most one value.
  `ldLkpFmt2_blind`, `ldLkpFmt2_blindIdx`: from a Piece (Cb/Ld/LdLkpMaskKit.lean) on `A.baseA`
    (`A.baseN` at tuples with the index's message), with both reading maps `fun w => msg w.1` and
    sets Sr, Sw: `A.sub` (`A.subIN`) is blind (`Honest.Blind kc kc Mk put put`) for every kc, Mk,
    put such that, whenever kc of a second witness is put m of kc of the first, the two witnesses'
    entries in Sr, the entries that the lookup reads, agree.
  `ldLkpMaskAsm2_piece`: under the hypotheses of its statement,
    `(A.mjChain Ex M Wp Kc msg Rd).narrow C` is a Piece for the honest side of `A.chainA`, with Sr =
    `A.srAll Dt`, Sw = `A.swAll`; both its reading maps are `fun w => msg w.1`, all entries, not cut
    down to Rd.
  `A.FormIn G`, `ldLkpSuppF2_form`, `ldLkpSuppF2_pull`: the mask form of the claim on the keys is 0
    outside the two inner masks of the last level of the keys' tree.
  `ldLkpAsm2F_plain`, `ldLkpAsm2F_pass`, `ldLkpAsm2F_noOrcs`: the formats of `A.baseF ι`
    (ι : N → A.J) (`BkA.Plain`, Cb/Ld/LdLkpFormat.lean; `noOrcs`, Cb/Ld/LdPscGood.lean).
  `ldLkpAsm2F_base`: for every M, Wp, Kc, Ex, msg and every joint R0 that is carried along:
    `A.baseF ι` is `BkA.Good` from "every key in the table [exact: and Mu]" to the output claim on
    the family. Conditions: ι injective; `A.PlacesIn` of the range of ι; `A.H.lkb.Adm p`, p the
    characteristic of E; `A.H.MuOn Mu`.

`H.Blind kci kco Mk puti puto` (`Honest.Blind`) asks that, for all input witnesses w and w', every M
in `Mk`, every explicit part x of an input statement, all coins c of the honest prover and every
value ρ of the verifier's randomness, if `kci w' = puti M (kci w)`, then the honest prover's runs
from w' and from w, at x, c and ρ, have the same full transcript and end with the same explicit part
of the output statement, and `kco` of the output witness with which the run from w' ends is `puto M`
of `kco` of the output witness with which the run from w ends. In `ldLkpFmt2_blind` and
`ldLkpFmt2_blindIdx` it stands as the conclusion.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpAsm2GoodMProofs
import Cb.Ld.LdLkpFormatBlindIdx
import Cb.Ld.LdLkpMaskAsmPiece
import Cb.Ld.LdLkpSuppFine
import Cb.Ld.LdLkpAsmFamProofs

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

/-- G holds of the two inner masks of the last sumcheck of the keys' tree. -/
def LkAsm2.FormIn {E : Type} [Field E] [Fintype E] (A : LkAsm2 E) (G : A.J → Prop) : Prop :=
  ∀ b, G (A.cK A.v' b)

noncomputable section
namespace LkAsm2
variable {E : Type} [Field E] [Fintype E] (A : LkAsm2 E) {N : Type} (ι : N → A.J)

/-- The read-out with a family of rows. -/
def rdF (o : A.XB) : FX A.St E N A.nRows := toFam A.nRows (A.rdN ι o)

/-- At the base. -/
def baseF (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E) :
    BkA Kc M A.St (FX A.St E N A.nRows) Ex Wp :=
  (A.chainA Ex M Wp Kc msg).postM (A.rdF ι)

end LkAsm2
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

def ldLkpFmt2_plain : Prop :=
  ∀ (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseA Ex M Wp Kc msg).Plain
def ldLkpFmt2_pass : Prop :=
  ∀ (A : LkAsm2 E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseA Ex M Wp Kc msg).R.Passes id fun x' => x'.1
/-- The further oracles are not read, not tied, copied. -/
def ldLkpFmt2_idx : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E),
    (A.sub S E₀ Kc Wp msg).R.IdxStep
/-- State and samples are handed on. -/
def ldLkpFmt2_passes : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E),
    (A.sub S E₀ Kc Wp msg).R.Passes (fun x => x) fun x => (x.1.1, x.2)
/-- The honest prover ends with the witness with which it began. -/
def ldLkpFmt2_same : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) w x c ρ,
    (((A.sub S E₀ Kc Wp msg).H.strat w x c).run ρ).2.2 = w
def ldLkpFmt2_hands : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp Pw : Type) (msg : S.Msg → A.J → E)
      (Ri : A.St × S.Smp → (E₀.prod S.ext).Str → S.Wit × Wp → Prop) (px : S.Wit × Wp → Pw),
    (A.sub S E₀ Kc Wp msg).H.Hands Ri px px
def ldLkpFmt2_need : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) ρ U,
    (A.sub S E₀ Kc Wp msg).R.need ρ U = U
def ldLkpFmt2_bud : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) ρ T,
    (A.sub S E₀ Kc Wp msg).P.bud ρ T
def ldLkpFmt2_free : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E) w x,
    (A.sub S E₀ Kc Wp msg).H.withheld w x = ∅
def ldLkpFmt2_bears : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E)
      (q : Finset (E₀.prod S.ext).Pos → Prop),
    (A.sub S E₀ Kc Wp msg).R.Bears (A.sub S E₀ Kc Wp msg).P.bud q q

/-- Under the hypotheses below, the assembled lookup is blind to the masks of later blocks
(`Honest.Blind`, Ior/KnowCollRulesMask.lean). One hypothesis is its masked item with what it reads
(a `Piece`, Cb/Ld/LdLkpMaskKit.lean). -/
def ldLkpFmt2_blind : Prop :=
  ∀ (A : LkAsm2 E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type) (msg : S.Msg → A.J → E)
      (D : MJ E A.J (A.baseA E₀ S.Msg Wp Kc msg).R) (Sr Sw : A.J → Prop),
    D.Piece (A.baseA E₀ S.Msg Wp Kc msg).H (fun w => msg w.1) (fun w => msg w.1) Sr Sw →
    ∀ (Kk : Type) (kc : S.Wit × Wp → Kk) (Mk : Type) (put : Mk → Kk → Kk),
      (∀ w w' m, kc w' = put m (kc w) → ∀ j, Sr j → msg (S.msgs w'.1) j = msg (S.msgs w.1) j) →
      (A.sub S E₀ Kc Wp msg).H.Blind kc kc Mk put put

/-- With keys over an encoded index. -/
def ldLkpFmt2_blindIdx : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E) (msg : C.Msg × S.Msg → A.J → E)
      (D : MJ E A.J (A.baseN ι C.E0 (C.Msg × S.Msg) Unit Unit msg).R) (Sr Sw : A.J → Prop),
    D.Piece (A.baseN ι C.E0 (C.Msg × S.Msg) Unit Unit msg).H (fun w => msg w.1)
      (fun w => msg w.1) Sr Sw →
    ∀ (Kk : Type) (kc : S.Wit × (C.PIdx × Unit) → Kk) (Mk : Type) (put : Mk → Kk → Kk),
      (∀ w w' m, kc w' = put m (kc w) →
        ∀ j, Sr j → msg (w'.2.1.1.1, S.msgs w'.1) j = msg (w.2.1.1.1, S.msgs w.1) j) →
      (A.subIN ι C S msg).H.Blind kc kc Mk put put

/-- Under the hypotheses below, the chain is a Piece. -/
def ldLkpMaskAsm2_piece : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (Mu : A.St → (A.J → E) → Prop)
      (Ex : ExtSpec) [Nonempty Ex.Str] (M Wp Kc : Type) (msg : M → A.J → E)
      (Dt Rd : A.J → Prop) (C : A.St → (A.J → E) → Prop),
    A.H.lkb.Adm p → A.H.MuOn Mu → A.MaskOK Dt → (∀ j, A.srAll Dt j → Rd j) →
    (∀ st k, C st k → A.lk.inP Mu st k) → MjStab C A.swAll →
    (∀ k k' st, (∀ j, A.srAll Dt j → k j = k' j) → C st k → C st k') →
    ((A.mjChain Ex M Wp Kc msg Rd).narrow C).Piece
      (A.chainA Ex M Wp Kc msg).H (fun w => msg w.1) (fun w => msg w.1) (A.srAll Dt) A.swAll

def ldLkpSuppF2_form : Prop :=
  ∀ (A : LkAsm2 E) (G : A.J → Prop), A.FormIn G → ∀ o, SuppIn G (A.rd o).2.1.mf

def ldLkpSuppF2_pull : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) [Fintype N] (ι : N → A.J), Function.Injective ι →
    A.FormIn (fun j => j ∈ Set.range ι) →
    ∀ (o : A.XB) (k : ℕ) (f : ℕ → E) (m : A.J → E),
      ((A.rd o).2.1.pull ι).Holds k f (fun n => m (ι n)) ↔ (A.rd o).2.1.Holds k f m

/-- The lookup at the base, its rows a family. -/
def ldLkpAsm2F_base : Prop :=
  ∀ (p : ℕ) [CharP E p] (A : LkAsm2 E) (N : Type) [Fintype N] (ι : N → A.J)
      (Mu : A.St → (A.J → E) → Prop) (Ex : ExtSpec) (Kc M Wp : Type)
      (R0 : Rels Kc A.St Ex (M × Wp)) (msg : M → A.J → E),
    Function.Injective ι → A.PlacesIn (fun j => j ∈ Set.range ι) → A.H.lkb.Adm p → A.H.MuOn Mu →
    (A.baseF ι Ex M Wp Kc msg).Good (cj R0 msg id (A.lk.inP Mu) A.lk.inR)
      (cj R0 msg Prod.fst (A.lk.outF id (A.entN ι)) (A.lk.outF id (A.entN ι)))

def ldLkpAsm2F_plain : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseF ι Ex M Wp Kc msg).Plain
def ldLkpAsm2F_pass : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseF ι Ex M Wp Kc msg).R.Passes id fun x' => x'.1
def ldLkpAsm2F_noOrcs : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    noOrcs (A.baseF ι Ex M Wp Kc msg).R.shape
def ldLkpAsm2F_shape : Prop :=
  ∀ (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → A.J → E),
    (A.baseF ι Ex M Wp Kc msg).R.shape = (A.baseA Ex M Wp Kc msg).R.shape

end
end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec) (M Wp Kc : Type)

theorem noOrcs_core (Y : PscPar E) : noOrcs (Y.core Ex).shape :=
  ⟨inferInstanceAs (Subsingleton Unit), by simpa using noOrcs_rounds Y.fmt [] trivial⟩

theorem noOrcs2_forest (A : LkAsm2 E) (msg : M → A.J → E) :
    ∀ l, noOrcs (A.forest Ex M Wp Kc msg l).R.shape
  | 0 => noOrcs_tree Ex M Wp Kc (A.IK.setV (A.v' + 1)).DK msg A.v'
  | l + 1 => noOrcs_app _ _ (noOrcs2_forest A msg l) (noOrcs_lev Ex M Wp Kc A.D msg l)

theorem noOrcs2_chain (A : LkAsm2 E) (msg : M → A.J → E) :
    noOrcs (A.chainA Ex M Wp Kc msg).R.shape :=
  noOrcs_app _ _
    (noOrcs_app _ _
      (noOrcs_app _ _ (noOrcs_app _ _ (noOrcs_head Ex M Wp Kc A.H msg) (noOrcs_draw _))
        (noOrcs2_forest Ex M Wp Kc A msg A.d))
      (noOrcs_core Ex A.En.par))
    (noOrcs_app _ _ (noOrcs_draw _) (noOrcs_psc A.Bt.zc.next.par Ex))

theorem noOrcs2_base (A : LkAsm2 E) (msg : M → A.J → E) : noOrcs (A.baseA Ex M Wp Kc msg).R.shape :=
  noOrcs2_chain Ex M Wp Kc A msg
theorem noOrcs2_baseN (A : LkAsm2 E) {N : Type} (ι : N → A.J) (msg : M → A.J → E) :
    noOrcs (A.baseN ι Ex M Wp Kc msg).R.shape :=
  noOrcs2_chain Ex M Wp Kc A msg

end

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpFmt2_plain : Spec.ldLkpFmt2_plain E := fun A Ex M Wp Kc msg =>
  plain_postM (A.plain2 E Ex M Wp Kc msg) A.rd

theorem ldLkpFmt2_pass : Spec.ldLkpFmt2_pass E := fun A Ex M Wp Kc msg =>
  (A.pass2 E Ex M Wp Kc msg).post _ _ fun o x' e => by
    obtain rfl := Option.some.inj e
    rfl

theorem ldLkpFmt2_idx : Spec.ldLkpFmt2_idx E := fun A S E₀ Kc Wp msg =>
  lift_idxStep S (ldLkpFmt2_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt2_passes : Spec.ldLkpFmt2_passes E := fun A S E₀ Kc Wp msg =>
  lift_passes S (ldLkpFmt2_pass E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt2_same : Spec.ldLkpFmt2_same E := fun A S E₀ Kc Wp msg =>
  lift_keepsW S (ldLkpFmt2_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt2_hands : Spec.ldLkpFmt2_hands E := fun A S E₀ Kc Wp _ msg Ri px =>
  lift_hands S (ldLkpFmt2_plain E A E₀ S.Msg Wp Kc msg) Ri px
theorem ldLkpFmt2_need : Spec.ldLkpFmt2_need E := fun A S E₀ Kc Wp msg =>
  lift_need S (ldLkpFmt2_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt2_bud : Spec.ldLkpFmt2_bud E := fun A S E₀ Kc Wp msg =>
  lift_bud S (ldLkpFmt2_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt2_free : Spec.ldLkpFmt2_free E := fun A S E₀ Kc Wp msg =>
  lift_free S (ldLkpFmt2_plain E A E₀ S.Msg Wp Kc msg)
theorem ldLkpFmt2_bears : Spec.ldLkpFmt2_bears E := fun A S E₀ Kc Wp msg =>
  lift_bears S (ldLkpFmt2_plain E A E₀ S.Msg Wp Kc msg)

theorem ldLkpFmt2_blind : Spec.ldLkpFmt2_blind E := fun A S E₀ Kc Wp msg _ _ _ hP _ kc Mk put hk =>
  blind_of_piece S (ldLkpFmt2_plain E A E₀ S.Msg Wp Kc msg)
    (noOrcs2_base E₀ S.Msg Wp Kc A msg) hP kc Mk put hk

theorem ldLkpFmt2_blindIdx :
    Spec.ldLkpFmt2_blindIdx E := fun A N ι C S msg _ _ _ hP _ kc Mk put hk =>
  blind_of_sameOnW (b := A.baseIN ι C S.Msg msg) S (ldLkpAsm2N_plainI E A N ι C S.Msg msg)
    (sameOnW_idx C (sameOn_of_piece (noOrcs2_baseN C.E0 (C.Msg × S.Msg) Unit Unit A ι msg) hP))
    kc Mk put hk

theorem ldLkpMaskAsm2_piece :
    Spec.ldLkpMaskAsm2_piece E := fun p _ A Mu Ex _ M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs hcl =>
  mjp_full (b := A.chainA Ex M Wp Kc msg)
    (ldLkpMaskAsm2_link E p A Mu Ex M Wp Kc msg Dt Rd C hA hMu hOK hRd hC hs)
    (A.plain2 E Ex M Wp Kc msg) hRd hcl

theorem ldLkpSuppF2_form : Spec.ldLkpSuppF2_form E := by
  intro A G h o j hj
  show - pushJ ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).toJ
        (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).T.slS (A.oldT o).2) j = 0
  exact neg_eq_zero.2
    (supp_pushJ _ _ G (tree_slS_succ (A.IK.setV (A.v' + 1)).DK G A.v' h (A.oldT o).2) j hj)

theorem ldLkpSuppF2_pull : Spec.ldLkpSuppF2_pull E := fun A N _ ι hι h o k f m =>
  ldLkpSupp_cl_pull E A.J N ι hι _ (ldLkpSuppF2_form E A _ h o) k f m

theorem rdN2_len (A : LkAsm2 E) {N : Type} (ι : N → A.J) (o : A.XB) :
    (A.rdN ι o).2.2.length = A.nRows :=
  (List.length_map _).trans (ldLkpAsm2_len E A o)

theorem ldLkpAsm2F_base : Spec.ldLkpAsm2F_base E := by
  intro p _ A N _ ι Mu Ex Kc M Wp R0 msg hι hP hA hMu
  have g := A.chain_good E p Mu Ex Kc M Wp R0 msg hA hMu
  have hf : ∀ (o : A.XB) (m : A.J → E),
      A.lk.outF id (A.entN ι) (A.rdF ι o) m ↔ A.lk.out id id (A.rd o) m := fun o m =>
    (ldLkpAsmF_fam E A.St (A.J → E) (A.J → E) N A.lk id (A.entN ι) A.nRows (A.rdN ι o)
        m (rdN2_len E A ι o)).trans
      (A.outN_iff E N ι hι hP o m)
  unfold BkA.Good at g ⊢
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ _ _ _ (A.rdF ι) g ?_ ?_ ?_ ?_
  · intro o y w h
    exact ⟨h.1,
      (hf o _).mpr ((A.out_iff o _).mpr ⟨⟨⟨⟨h.2.1.1.1.1, trivial⟩, h.2.1.1.2⟩, h.2.1.2⟩, h.2.2⟩)⟩
  · exact fun _ _ h => h
  · exact fun _ => rfl
  · intro o y w _ h
    exact ⟨h.1, (A.out_iff o _).mp ((hf o _).mp h.2)⟩

theorem ldLkpAsm2F_plain : Spec.ldLkpAsm2F_plain E := fun A _ ι Ex M Wp Kc msg =>
  plain_postM (A.plain2 E Ex M Wp Kc msg) (A.rdF ι)

theorem ldLkpAsm2F_pass : Spec.ldLkpAsm2F_pass E := fun A _ ι Ex M Wp Kc msg =>
  (A.pass2 E Ex M Wp Kc msg).post _ _ fun o x' e => by
    obtain rfl := Option.some.inj e
    rfl

theorem ldLkpAsm2F_noOrcs : Spec.ldLkpAsm2F_noOrcs E := fun A _ _ Ex M Wp Kc msg =>
  noOrcs2_chain Ex M Wp Kc A msg

theorem ldLkpAsm2F_shape : Spec.ldLkpAsm2F_shape E := fun _ _ _ _ _ _ _ _ => rfl

end
end Cb
