-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5TopLTrue.lean

The bundle "OrdsL" of Johnson/Road/Lane5TopL.lean is met by the honest trace of every request that
is true under its policy, at every index: no true request is lost.

Johnson/Road/Lane5TopLMet.lean shows that "OrdsL" has a value, at one index and one request: all
weights and all tokens 0. Its proof fixes that pair in its first line and then reads of it only that
the request is true under the policy. Here the pair is a letter.

The value is named. T is the family of matrices of the honest trace with the ledger,
"Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x)", at s the table of scales that the
layers' shape and scales give. One family by labels for every link: "zTrue" = "Hd.zOf T"; the
attention links' lists: "zaTrue" = "zsOf (SA g) g T".

Main definitions and theorem:
* "zTrue", "zaTrue": the two families.
* "ordsL_of_true": under the public hypotheses of "ordsL_met", for every index i and every request x
  with "Policy.IsTrueUnder s pol i x": "OrdsL" holds at i.mat, x, "zTrue", "zaTrue".

Use: with the equivalences between a link's bundle and "its meaning without the lookup clause, and
the clause on keys" ("attOrd_iff_usual", Johnson/Road/Lane5AttSeamMet.lean; "layerOrd_iff_forIn",
Johnson/Road/Lane5KeysIffG.lean), it gives for every true request matrices that meet both together.
The key vectors in those clauses are terms of this library.

Limits. Which true requests there are is not said here. The library exhibits some: at every lawful
table and all weights 0, every request that has its form, with y = 0 if e = 1,024, whatever its
other tokens, under a policy with 257 ≤ θ and 257 ≤ C (Policy/Rel/TrueGuards.lean: zero_all); at the
reference table alone, requests with 1,023 counted positions at made-up weights whose 48 layers are
all zero (Policy/Rel/PosGuards.lean: real_gap, step_gap). This file's conclusion at the first family
and at real_gap's request: Johnson/Road/Lane5TopLTrueAt.lean; at real_gap's request, at the record
that the verifier's publicOf returns (under "Hd.PublicAt X.P", if the scale file's words are
"scalesKF"): Johnson/Road/Lane5ScalesRef.lean. The library's model has no cell for a lookup's
counts. So in "zTrue" the matrix b of a group of layers and in "zaTrue" the matrix bA of attention
are 0, which no honest prover of the protocol would commit to. The statements do not read them. The
numbering is that of these files' dictionary. For the labels of the layers' lists it is the
verifier's by a theorem (labA_tails, Johnson/Road/FormsKeysDictA.lean). For the places of
attention's cells it is written by a reading of the verifier's texts; no theorem ties it to them
(Johnson/Road/Lane5AttDef.lean).

Not claimed: that a prover's committed cells are these matrices; that a proof file which a verifier
accepts has such matrices; that an honest prover's proof is accepted (completeness of the protocol);
that the public hypotheses hold of any parameter file. It is a statement on integers and tables
alone.

-/
import Johnson.Road.Lane5TopLMet

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Layer (Lay matIx)

/-- The honest trace's matrices with the ledger, as one family by labels, the same for every link.
-/
noncomputable def zTrue (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx) (x : Instance ppref) :
    ℕ → ℕ → ℕ → ℕ → ℤ :=
  fun _ => Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x))

/-- The honest trace's matrices with the ledger, read back into the attention links' lists. -/
noncomputable def zaTrue (SA : ℕ → Attention.Shape) (s : Cm.Scales) (pol : AcceptancePolicy) (i : Cm.Idx)
    (x : Instance ppref) : ℕ → Zs :=
  fun g => zsOf (SA g) g (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x))

section TrueL

variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  {hH : Model.Head.Shape} {tau : Array F} {L : Model.Head.HL} {sc : Model.Layer.Scales}
  {nf : NormPar} {pol : AcceptancePolicy} {SA : ℕ → Attention.Shape}

/-- **The honest trace of every request that is true under its policy meets the whole bundle.** -/
theorem ordsL_of_true (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hw : ∀ g < 12, 7200 ≤ (SA g).kAs / (SA g).cf.NAs * (SA g).cf.NAs)
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (hs : (scalesOf hL sc nf).Lawful) (hpol : Policy.PolCond pol)
    (i : Cm.Idx) (x : Instance ppref) (ht : Policy.IsTrueUnder (scalesOf hL sc nf) pol i x) :
    OrdsL hL sc y hH L nf pol SA i.mat x (zTrue (scalesOf hL sc nf) pol i x)
      (zaTrue SA (scalesOf hL sc nf) pol i x) := by
  unfold zTrue zaTrue
  have P := (premiseL_of_under hs hpol ht).2
  have hT := honest_smallL hs hpol ht
  have hp := Hd.parts_ref hy S Z2
  have hZ : ∀ l r c, |Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
      (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x)) l r c| < 2 ^ 18 :=
    fun l r c => lt_trans (Hd.zOf_small hT (by norm_num) l r c) (by norm_num)
  have hD : ∀ k < Cm.Seg.nSeg, k % 2 = 0 → ∀ q ∈ Cm.Seg.reads Cm.Seg.Hd.main k,
      Cm.Seg.at' (Hd.D5 hH y (fun _ _ _ => 0) (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
      (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x)))) q =
      Cm.Seg.at' (Cm.Seg.toMat Cm.Seg.Hd.main
      (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x)) q :=
    fun k hk h2 q hq => Hd.D5_zOf Policy.mainOK h12 hF.NHf hp.1 hp.2 _ _ k hk q hq
      ((reads_even_or_own hq).elim id fun e => by rw [e]; exact h2)
  refine ⟨fun g hg => ?_, fun g hg => ?_, fun g hg r c => ?_, ?_, Hd.labelsAgree_one y _⟩
  · have hk : 2 * g < Cm.Seg.nSeg := by
      show 2 * g < 25
      omega
    exact (layerOrd_iff hy S Zd Z2 hp4 Cm.Seg.Hd.main _ i.mat hg sc nf x).2
      ⟨fun _ _ _ _ => hZ _ _ _,
        linkOK_seg (Policy.segPol_ne _ pol (by omega))
          (linkOK_congr (laws_main _ pol) hk
            (fun q hq => ((dict_D5 hy S Zd Z2 hp4 hH Cm.Seg.Hd.main _ _ hg q hq).trans
              (hD (2 * g) hk (by omega) q hq)).symm)
            (P.link (2 * g) hk))⟩
  · have hk : 2 * g + 1 < Cm.Seg.nSeg := by
      show 2 * g + 1 < 25
      omega
    have hH := (linkOK_seg (Policy.segPol_ne _ pol (by omega)) (P.link (2 * g + 1) hk)).holds
    have hb : ∀ c : AttSeg.Raw, c.Valid All.DA →
        |Cm.Seg.at' (Cm.Seg.toMat Cm.Seg.Hd.main
          (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x)) (Cm.Seg.ownAtt g c).place| <
          2 ^ 18 :=
      fun c _ => lt_trans (hT (Cm.Seg.ownAtt g c).place.1 (Cm.Seg.ownAtt g c).place.2.1
        (Cm.Seg.ownAtt g c).place.2.2) (by norm_num)
    have hA := ord_of_holds hg (hSA g hg) (hw g hg) (hsh g hg) (hE g hg) hb hH
    exact hA
  · exact (Hd.zOf_qa hp.1 hp.2 _ hg r c).trans (zsOf_qa (SA g) g _ r c).symm
  · have hk : 24 < Cm.Seg.nSeg := by
      show 24 < 25
      omega
    exact Hd.ordLB_of_ord ((Hd.link24L_iff hF hLy hy S Zd Z2 (scalesOf hL sc nf) pol x i.mat _).1
      ⟨fun _ _ _ => hZ _ _ _,
        (linkOK_congr (laws_main _ pol) hk
          (fun q hq => ((Hd.headMx_D5 Cm.Seg.Hd.main hH h12 _ _ q hq).trans
            (hD 24 hk (by norm_num) q hq)).symm)
          (P.link 24 hk)).holds⟩)

end TrueL

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.ordsL_of_true
