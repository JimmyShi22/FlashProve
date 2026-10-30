-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpFormatPiece.lean: from the masked item of a base chain, with what it reads, to its
blindness to the masks of later blocks.

Statements and proofs. Glue; no protocol.

Cb/Ld/LdLkpMaskKit.lean has the bundle `MJ.Piece D H rdi rdo Sr Sw`: the honest side H has the item
"masked messages" with the `MJ` D. Its messages and its claim depend on the entries in Sr only. Its
own masks lie in Sw. Cb/Ld/LdLkpFormatBlind.lean has: a plain base chain whose honest run is the
same at tuples that agree on Rd is blind for all kc, Mk, put that change no entry in Rd (exactly:
the premise `hk` in its statement, `blind_of_sameOn`, which speaks of all pairs of witnesses whose
readings by kc differ by the overwriting: `kc w' = put m (kc w)`). Here the two are joined.

Main names:
  `noOrcs_app` to `noOrcs_base`: every round's oracle part has at most one value (`noOrcs`,
    Cb/Ld/LdPscGood.lean), block by block, up to the assembled lookup: so a transcript is its plain
    parts and the verifier's messages.
  `sameOn_of_piece`: under `noOrcs b.R.shape`, a Piece with both reading maps `fun w => msg w.1`
    gives `b.SameOn msg Sr`.
  `blind_of_piece`: under the hypotheses of its statement, over a signature: `S.liftH b.H` is blind
    (Ior/KnowCollRulesMask.lean: `Honest.Blind`) for every kc, Mk, put such that, whenever kc of a
    second witness is put m of kc of the first, the two witnesses' entries in Sr agree.
  `blind_of_pieces`: under the hypotheses of its statement, in particular for kc the tuple of all
    entries and for Mk, put those of a later piece D' whose own masks Sw' (`D'.Writes Sw'`) do not
    meet Sr.
  `Spec.ldLkpFmt_blind`: under the hypotheses of its statement, for the assembled lookup (`LkAsm`,
    Cb/Ld/LdLkpAsm.lean), from a Piece on `A.baseA`.

`H.Blind kci kco Mk puti puto` (`Honest.Blind`) asks that, for all input witnesses w and w', every M
in `Mk`, every explicit part x of an input statement, all coins c of the honest prover and every
value ρ of the verifier's randomness, if `kci w' = puti M (kci w)`, then the honest prover's runs
from w' and from w, at x, c and ρ, have the same full transcript and end with the same explicit part
of the output statement, and `kco` of the output witness with which the run from w' ends is `puto M`
of `kco` of the output witness with which the run from w ends. In `blind_of_piece`,
`blind_of_pieces` and `Spec.ldLkpFmt_blind` it stands as the conclusion.

Limits: this file does not say that the assembled lookup has a Piece, and with which Sr, Sw: that is
the masked item's matter.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpFormatBlind
import Cb.Ld.LdLkpFormatAsm
import Cb.Ld.LdLkpMaskKit

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

/-! ### Every round's oracle part has at most one value -/

theorem noOrcs_app : ∀ (s t : Shape), noOrcs s → noOrcs t → noOrcs (s ++ t)
  | [], _, _, h => h
  | _ :: s, t, h, h' => ⟨h.1, noOrcs_app s t h.2 h'⟩

theorem noOrcs_draw (D : Type) [Fintype D] [Nonempty D] : noOrcs [IOR.drawRound D] :=
  ⟨inferInstanceAs (Subsingleton Unit), trivial⟩

theorem noOrcs_psc {E : Type} [Field E] [Fintype E] (Y : PscPar E) (Ex : ExtSpec) :
    noOrcs (Y.psc Ex).shape :=
  ⟨inferInstanceAs (Subsingleton Unit),
    noOrcs_rounds Y.fmt [pRoundV E Y.A] ⟨inferInstanceAs (Subsingleton Unit), trivial⟩⟩

section
variable {K M : Type} {Ex : ExtSpec} {Wp : Type}

theorem noOrcs_seq {X₁ X₂ X₃ : Type} {a : BkA K M X₁ X₂ Ex Wp} {b : BkA K M X₂ X₃ Ex Wp}
    (ha : noOrcs a.R.shape) (hb : noOrcs b.R.shape) : noOrcs (a.seq b).R.shape :=
  noOrcs_app _ _ ha hb

theorem noOrcs_chain (X : ℕ → Type) (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp)
    (h : ∀ l, noOrcs (b l).R.shape) :
    ∀ n, noOrcs (BkA.chain X b n).R.shape
  | 0 => h 0
  | n + 1 => noOrcs_seq (noOrcs_chain X b h n) (h (n + 1))

end

section
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec) (M Wp Kc : Type)

theorem noOrcs_tie (D : TieP E) (msg : M → D.J → E) (n : ℕ) :
    noOrcs (D.tieA Ex Wp Kc msg n).R.shape :=
  noOrcs_chain _ _ (fun l => noOrcs_psc (D.lv l).T.par Ex) n
theorem noOrcs_lev (D : TreeP E) (msg : M → D.J → E) (l : ℕ) :
    noOrcs (D.levA Ex Wp Kc msg l).R.shape :=
  noOrcs_app _ _ (noOrcs_psc (D.lv l).T.par Ex) (noOrcs_draw _)
theorem noOrcs_tree (D : TreeP E) (msg : M → D.J → E) (n : ℕ) :
    noOrcs (D.treeA Ex Wp Kc msg n).R.shape :=
  noOrcs_chain _ _ (noOrcs_lev Ex M Wp Kc D msg) n
theorem noOrcs_head (H : LkHead E) (msg : M → H.J → E) : noOrcs (H.headA Ex M Wp Kc msg).R.shape :=
  noOrcs_app _ _ (noOrcs_draw E) (noOrcs_tie Ex M Wp Kc H.tie msg H.n)
theorem noOrcs_forest (Q : SegTab E) (msg : M → Q.I.J → E) :
    ∀ l, noOrcs (Q.forest Ex Wp Kc msg l).R.shape
  | 0 => noOrcs_draw _
  | l + 1 => noOrcs_app _ _ (noOrcs_forest Q msg l) (noOrcs_lev Ex M Wp Kc Q.D msg l)
theorem noOrcs_segT (Q : SegTab E) (msg : M → Q.I.J → E) : noOrcs (Q.segT Ex Wp Kc msg).R.shape :=
  noOrcs_app _ _
    (noOrcs_app _ _ (noOrcs_forest Ex M Wp Kc Q msg Q.I.d) (noOrcs_psc Q.En.psc.par Ex))
    (noOrcs_app _ _ (noOrcs_draw _) (noOrcs_psc Q.Bt.zc.next.par Ex))
theorem noOrcs_base (A : LkAsm E) (msg : M → A.J → E) : noOrcs (A.baseA Ex M Wp Kc msg).R.shape :=
  noOrcs_app _ _
    (noOrcs_app _ _ (noOrcs_head Ex M Wp Kc A.H msg)
      (noOrcs_tree Ex M Wp Kc (A.IK.setV (A.v' + 1)).DK msg A.v'))
    (noOrcs_segT Ex M Wp Kc A.Q msg)

end

/-! ### From a piece to blindness -/

section
variable {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp E J : Type}

theorem sameOn_of_piece {b : BkA K M X₁ X₂ Ex Wp} (hn : noOrcs b.R.shape) {D : MJ E J b.R}
    {msg : M → J → E} {Sr Sw : J → Prop}
    (hP : D.Piece b.H (fun w => msg w.1) (fun w => msg w.1) Sr Sw) : b.SameOn msg Sr := by
  intro u u' x c ρ hu
  have hm : D.msg (msg u'.1) x ρ = D.msg (msg u.1) x ρ := hP.reads.msg _ _ x ρ hu
  refine ⟨tr_ext_noOrcs _ hn _ _ ?_ ?_, ?_⟩
  · rw [hP.fits.mm.run, hP.fits.mm.run]
    exact hm
  · rw [Strat.rho_run, Strat.rho_run]
  · rw [hP.fits.hand, hP.fits.hand]
    show D.nxt x (D.msg (msg u'.1) x ρ) ρ = D.nxt x (D.msg (msg u.1) x ρ) ρ
    rw [hm]

end

section
variable {E : Type} (S : Sig E) {K St X' Wp J : Type} {E₀ : ExtSpec} {b : BkA K S.Msg St X' E₀ Wp}

theorem blind_of_piece (hp : b.Plain) (hn : noOrcs b.R.shape) {D : MJ E J b.R} {msg : S.Msg → J → E}
    {Sr Sw : J → Prop} (hP : D.Piece b.H (fun w => msg w.1) (fun w => msg w.1) Sr Sw) {Kk : Type}
    (kc : S.Wit × Wp → Kk) (Mk : Type) (put : Mk → Kk → Kk)
    (hk : ∀ w w' m, kc w' = put m (kc w) → ∀ j, Sr j → msg (S.msgs w'.1) j = msg (S.msgs w.1) j) :
    (S.liftH b.H).Blind kc kc Mk put put :=
  blind_of_sameOn S hp (sameOn_of_piece hn hP) kc Mk put hk

/-- Under the hypotheses below, an earlier piece is blind to a later piece's own masks, if these do
not meet what the earlier one reads. -/
theorem blind_of_pieces (hp : b.Plain) (hn : noOrcs b.R.shape) {D : MJ E J b.R}
    {msg : S.Msg → J → E} {Sr Sw : J → Prop}
    (hP : D.Piece b.H (fun w => msg w.1) (fun w => msg w.1) Sr Sw) {Xi Xo : Type}
    {Ei Eo : ExtSpec} {R' : IOR Xi Ei Xo Eo} (D' : MJ E J R') {Sw' : J → Prop}
    (hW : D'.Writes Sw') (hd : ∀ j, Sr j → ¬ Sw' j) :
    (S.liftH b.H).Blind (fun w : S.Wit × Wp => msg (S.msgs w.1))
      (fun w : S.Wit × Wp => msg (S.msgs w.1)) D'.Mk D'.put D'.put :=
  blind_of_piece S hp hn hP _ _ _ fun w w' m hw j hj => by
    have := congrFun hw j
    rw [this]
    exact hW m _ j (hd j hj)

end

namespace Spec

/-- Under the hypotheses below, the assembled lookup is blind to the masks of later blocks
(`Honest.Blind`, Ior/KnowCollRulesMask.lean). One hypothesis is its masked item with what it reads
(a `Piece`, Cb/Ld/LdLkpMaskKit.lean). -/
def ldLkpFmt_blind : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (A : LkAsm E) (S : Sig E) (E₀ : ExtSpec) (Kc Wp : Type)
      (msg : S.Msg → A.J → E) (D : MJ E A.J (A.baseA E₀ S.Msg Wp Kc msg).R) (Sr Sw : A.J → Prop),
    D.Piece (A.baseA E₀ S.Msg Wp Kc msg).H (fun w => msg w.1) (fun w => msg w.1) Sr Sw →
    ∀ (Kk : Type) (kc : S.Wit × Wp → Kk) (Mk : Type) (put : Mk → Kk → Kk),
      (∀ w w' m, kc w' = put m (kc w) → ∀ j, Sr j → msg (S.msgs w'.1) j = msg (S.msgs w.1) j) →
      (A.sub S E₀ Kc Wp msg).H.Blind kc kc Mk put put

end Spec

theorem ldLkpFmt_blind :
    Spec.ldLkpFmt_blind := fun E _ _ A S E₀ Kc Wp msg _ _ _ hP _ kc Mk put hk =>
  blind_of_piece S (ldLkpFmt_plain E A E₀ S.Msg Wp Kc msg)
    (noOrcs_base E₀ S.Msg Wp Kc A msg) hP kc Mk put hk

end Cb
