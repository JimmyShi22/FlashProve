-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinProofsChain.lean: the proofs of the statements of Cb/Ld/LdLin.lean on the chain: the
chain up to the rows that are left (`ldLin_core`); the test with any closing (`ldLin_tail`, under
the hypotheses of its statement; which closings it reaches: Cb/Ld/LdLin.lean, Limits). That a
sending of a family is a piece: Cb/Ld/LdSendPiece.lean.

The rules for chains are those of Cb/Ld/LdTowerKit.lean (a piece, then a piece; a piece, then a
tail) at the joints whose conditions may fail (`Rels.cf`, Ior/KnowCollGood.lean): in `A.cf` the
condition is moved into the relaxed relation. `ldLin_core` joins seven pieces in the order of the
chain: `step0`, `sW`, `pt` (under `P.FoldErr on0 εf`), `sU`, `loc` (for a nonempty ι), `sO`, `zeta`
(for an injective `P.D.py`); the four own blocks are first moved to the joints `.cf`
(`ldk_pieceTr_cf`); the three sendings are, under `S.OK`, pieces at such joints (`ldSendFam_piece`,
Cb/Ld/LdSendPiece.lean).
In `ldk_pieceTr_cf`, `PieceTr` is hypothesis and conclusion. `PieceTr`, a piece of a chain, asks of
a reduction between two joints the bundle `IOR.GoodT` and three further clauses, `noHid`, `noTie`
and `bears`, which Cb/Ld/LdTowerKit.lean states (`bears` through `IOR.Bears`, Ior/Bears.lean);
`IOR.Piece` (Ior/Tail.lean) asks the same over `IOR.Good`. What a tail of a chain (`TailTr`) and the
bundle `IOR.GoodT` ask: Cb/Ld/LdLin.lean, after Main names.
-/
import Cb.Ld.LdLinProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- a piece from A to B is a piece from `A.cf` to `B.cf` -/
theorem ldk_pieceTr_cf {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} {R : IOR Xi Ei Xo Eo}
    {H : R.Honest Wi Wo} {A : Rels K Xi Ei Wi} {B : Rels K Xo Eo Wo}
    {ext : Xi × Ei.Str → Tr R.shape → Wo → Wi} {P : Nums K R} {qi : Finset Ei.Pos → Prop}
    {qo : Finset Eo.Pos → Prop} (h : PieceTr R H A B ext P qi qo) :
    PieceTr R H A.cf B.cf ext P qi qo :=
  ⟨goodT_cf _ _ _ _ _ _ _ _ _ _ _ _ _ h.good, h.noHid, h.noTie, h.bears⟩

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLin_core : Spec.ldLin_core E ι κ J Y := by
  intro P on0 εf S qa d hF hpy hS
  have h0 := ldk_pieceTr_cf (ldLin_step0 P on0 (P.q0 qa))
  have hW := ldSendFam_piece E P.NW P.SdW Unit P.X0 P.WA P.W0 P.E0 (P.jA on0) P.backW S.dW S.LW S.tW
    (P.q0 qa) hS.lawsW hS.fairW hS.listW hS.evW hS.sndW hS.blW hS.hidW
  have hP := ldk_pieceTr_cf (ldLin_pt P on0 εf (P.q1 S qa) hF)
  have hU := ldSendFam_piece E P.NU P.SdU Unit P.X2 P.W2 P.W1 P.E1 (P.j2 on0) P.backU S.dU S.LU S.tU
    (P.q1 S qa) hS.lawsU hS.fairU hS.listU hS.evU hS.sndU hS.blU hS.hidU
  have hL := ldk_pieceTr_cf (ldLin_loc P on0 S qa)
  have hO := ldSendFam_piece E P.NO P.SdO Unit P.X4 P.W4 P.W3 P.E4 P.j4 P.backO S.dO S.LO S.tO
    (P.q4 S qa) hS.lawsO hS.fairO hS.listO hS.evO hS.sndO hS.blO hS.hidO
  have hZ := ldk_pieceTr_cf (ldLin_zeta P (P.q5 S qa) hpy)
  have c6 := pieceTr_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.2.2.2.2.2 _ _ _ _ _ hO hZ
  have c5 := pieceTr_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.2.2.2.2.1 _ _ _ _ _ hL c6
  have c4 := pieceTr_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.2.2.2.1 _ _ _ _ _ hU c5
  have c3 := pieceTr_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.2.2.1 _ _ _ _ _ hP c4
  have c2 := pieceTr_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.2.1 _ _ _ _ _ hW c3
  exact pieceTr_seq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.1 _ _ _ _ _ h0 c2

theorem ldLin_tail : Spec.ldLin_tail E ι κ J Y := by
  intro P on0 εf S qa d Z hF hpy hS hZ
  have h := tailTr_cons _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ d.1 _ _ _ _
    (ldLin_core P on0 εf S qa d hF hpy hS) hZ
  exact ⟨goodT_cf_out _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ => trivial) h.good,
    h.noHid, h.tied, h.bears⟩

end
end Cb
