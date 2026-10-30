-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5TopLMet.lean

The statements of Lane5TopL.lean can be met: a witness for the whole bundle "OrdsL", at the head
with the cost ledger.

The twin of Lane5TopMet.lean. Under the public hypotheses of "premiseL_of_ords", at a lawful table
and every policy within its bounds, there are an index, a request and matrices that meet all of
"OrdsL" together.

The value. The matrices T of the honest trace with the ledger ("Cm.trace (Policy.ppOf s pol)") of
the request of "Policy.TrueGuards.some_true": all weights and all tokens 0, r = 1,023, e = 1,024.
One family by labels for every link, "Hd.zOf T"; the attention links' lists "zsOf". Nothing is cut
to a shape.

Main theorems:
* "honest_smallL": every entry of T is below 129, also where no cell stands ("Policy.segPol_admit",
  "Cm.lay_toMat_off").
* "ordsL_met": the witness, for attention shapes SA that meet four public hypotheses.
* "ordsL_met_at": the same at the shape "shapeAt" (Lane5AttMet.lean), where these four are theorems.

What it shows: that OrdsL and the hypotheses on attention's shapes are not contradictory; so
"premiseL_of_ords" and "under_of_ords" are not empty, given the remaining public hypotheses. No
more: the request has NO COUNTED POSITION, so the policy's two clauses on costs are met for free;
all weights and tokens are 0; "shapeAt" is a record that is typed by hand; that the remaining public
hypotheses hold of any parameter file is not shown here.

Not claimed: that a proof file which a verifier accepts has such matrices.
-/
import Johnson.Road.Lane5TopL
import Johnson.Road.Lane5TopMet
import Policy.Rel.TrueGuards

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Layer (Lay matIx)

/-- **Every entry of the honest trace's matrices, with the ledger, is below 129 in absolute value.**
-/
theorem honest_smallL {s : Cm.Scales} {pol : AcceptancePolicy} {i : Cm.Idx} {x : Instance ppref}
    (hs : s.Lawful) (hpol : Policy.PolCond pol) (ht : Policy.IsTrueUnder s pol i x) (a r c : ℕ) :
    |Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x) a r c| < 129 := by
  have H := Policy.segPol_admit s pol i x _
    ((Policy.ledger_trace_iff Cb.Gl.p Code.pGold_prime Policy.ledger_gl_big (Policy.ppOf s pol)
      (Policy.tableOK_ppOf hs hpol) i x).2 ht)
  by_cases e : ∃ n : Cm.Seg.Name, n.Valid Cm.Seg.Hd.main ∧ n.place = (a, r, c)
  · obtain ⟨n, hn, hp⟩ := e
    have hI : Cm.Seg.InShape (a, r, c) := hp ▸ Cm.lay_inShape _ Policy.mainOK n hn
    exact H.2.1 (a, r, c) hI
  · have h0 : Cm.Seg.at' (Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x))
        (a, r, c) = 0 :=
      Cm.lay_toMat_off Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x) (a, r, c) e
    have h1 : Cm.Seg.toMat Cm.Seg.Hd.main (Cm.trace (Policy.ppOf s pol) i x) a r c = 0 := h0
    rw [h1]
    norm_num

section MetL

variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  {hH : Model.Head.Shape} {tau : Array F} {L : Model.Head.HL} {sc : Model.Layer.Scales}
  {nf : NormPar} {pol : AcceptancePolicy} {SA : ℕ → Attention.Shape}

/-- **The bundle of Lane5TopL.lean has a value.** -/
theorem ordsL_met (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hw : ∀ g < 12, 7200 ≤ (SA g).kAs / (SA g).cf.NAs * (SA g).cf.NAs)
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (hs : (scalesOf hL sc nf).Lawful) (hpol : Policy.PolCond pol) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧ OrdsL hL sc y hH L nf pol SA i.mat x Z ZA := by
  obtain ⟨i, x, hr, he, ht⟩ : ∃ (i : Cm.Idx) (x : Instance ppref), x.r = 1023 ∧ x.e = 1024 ∧
      Policy.IsTrueUnder (scalesOf hL sc nf) pol i x :=
    ⟨_, _, rfl, rfl, Policy.TrueGuards.some_true hs pol⟩
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
  refine ⟨i, x, fun _ => Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.main
      (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x)),
    fun g => zsOf (SA g) g (Cm.Seg.toMat Cm.Seg.Hd.main
      (Cm.trace (Policy.ppOf (scalesOf hL sc nf) pol) i x)),
    hr, he, ⟨fun g hg => ?_, fun g hg => ?_, fun g hg r c => ?_, ?_, Hd.labelsAgree_one y _⟩⟩
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

/-- **The same at an attention shape that is written out**: its four public hypotheses are
theorems. -/
theorem ordsL_met_at (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hs : (scalesOf hL sc nf).Lawful) (hpol : Policy.PolCond pol) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧
        OrdsL hL sc y hH L nf pol (fun g => shapeAt ((scalesOf hL sc nf).kap (4 * g)).sh) i.mat x
          Z ZA :=
  ordsL_met hy S Zd Z2 hp4 h12 hF hLy (fun _ _ => sized_at _) (fun _ _ => wide_at _)
    (fun _ _ => rfl) (fun _ _ => exp_at _) hs hpol

end MetL

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.honest_smallL
#print axioms OnBytes.Road.L5.ordsL_met
#print axioms OnBytes.Road.L5.ordsL_met_at
