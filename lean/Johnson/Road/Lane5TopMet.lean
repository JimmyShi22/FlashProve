-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5TopMet.lean

The statements of Lane5Top.lean can be met: a witness for the whole bundle "Ords". They are on the
plain head, which the programs do not run (Lane5Ledger.lean).

Under the public hypotheses of "premise_of_ords", at a lawful table, there are an index, a request
for the next token and matrices that meet all of "Ords" together: the 25 statements, the 12 ties and
the 24 equations between the matrices of two links.

The value. The matrices T of the honest trace of a true request ("Cm.Seg.toMat", "Cm.trace2"), with
all weights and all tokens 0 ("Hd.Top.next_true_exists"). One family by labels for every link, read
back out of T: "Hd.zOf T" (HeadZ.lean), a right inverse of the dictionary by labels at the places of
cells. The attention links' lists: "zsOf" (Lane5AttBack.lean). Nothing is cut to a shape: T is 0
where no cell stands ("honest_small", Lane5Honest.lean).

Main theorems:
* "reads_even_or_own": a place that segment k may read lies in an even segment or in segment k.
* "ords_met": the witness, for attention shapes SA that meet four public hypotheses.
* "ords_met_at": the same at a shape that is written out ("shapeAt", Lane5AttMet.lean), where these
  four are
  theorems. Left as hypotheses: the layers' layout and its four conditions, twelve groups, the
  head's shape and layout, and that the table is lawful.

What it shows: that Ords and the hypotheses on attention's shapes are not contradictory; so
"premise_of_ords" and "reply_of_ords" are not empty, given the remaining public hypotheses. No more:
all weights and tokens are 0; "shapeAt" is a record that is typed here, with refExp as its table
of exponentials, not what the verifier's function returns; that the remaining public hypotheses hold
of any parameter file is not shown here.

Not claimed: that a proof file which a verifier accepts has such matrices.
-/
import Johnson.Road.Lane5Top
import Johnson.Road.Lane5Honest
import Johnson.Road.HeadZ
import Johnson.Road.Lane5AttBack
import Johnson.Road.Lane5AttMet

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

open OnBytes.Model.Layer (Lay matIx)

/-- **A place that segment k may read lies in an even segment or in segment k itself.** -/
theorem reads_even_or_own {hd : Cm.Seg.Hd} {k : ℕ} {q : Cb.Place} (hq : q ∈ Cm.Seg.reads hd k) :
    q.1 % 2 = 0 ∨ q.1 = k := by
  rcases hq with ⟨g, c, rfl, _, _, rfl⟩ | ⟨g, c, rfl, _, _, rfl⟩ |
    ⟨rfl, ⟨n, _, hn, rfl⟩ | ⟨φ, i, _, _, rfl⟩⟩
  · left
    rcases Cm.Seg.ownFF_cases g c with e | ⟨_, _, e⟩
    · rw [e]
      show 2 * g % 2 = 0
      omega
    · rw [e]
      show 2 * (g - 1) % 2 = 0
      omega
  · rcases Cm.Seg.ownAtt_cases g c with e | ⟨c', e, _⟩
    · right
      rw [e]
      rfl
    · left
      rw [e]
      show 2 * g % 2 = 0
      omega
  · exact Or.inr hn
  · left
    show 2 * (All.nGr - 1) % 2 = 0
    omega

section Met

variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
  {hH : Model.Head.Shape} {tau : Array F} {L : Model.Head.HL} {sc : Model.Layer.Scales}
  {nf : NormPar} {SA : ℕ → Attention.Shape}

/-- **The bundle of Lane5Top.lean has a value.** -/
theorem ords_met (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hw : ∀ g < 12, 7200 ≤ (SA g).kAs / (SA g).cf.NAs * (SA g).cf.NAs)
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (hs : (scalesOf hL sc nf).Lawful) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧ Ords hL sc y hH L nf SA i.mat x Z ZA := by
  obtain ⟨i, x, hr, he, ht⟩ := Hd.Top.next_true_exists hs
  have P := premise_of_true hs ht
  have hT := honest_small hs ht
  have hp := Hd.parts_ref hy S Z2
  have ok := (laws_plain (scalesOf hL sc nf)).ok
  have hZ : ∀ l r c, |Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.plain
      (Cm.trace2 (scalesOf hL sc nf) i x)) l r c| < 2 ^ 18 :=
    fun l r c => lt_trans (Hd.zOf_small hT (by norm_num) l r c) (by norm_num)
  have hD : ∀ k < Cm.Seg.nSeg, k % 2 = 0 → ∀ q ∈ Cm.Seg.reads Cm.Seg.Hd.plain k,
      Cm.Seg.at' (Hd.D5 hH y (fun _ _ _ => 0) (Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.plain
        (Cm.trace2 (scalesOf hL sc nf) i x)))) q =
      Cm.Seg.at' (Cm.Seg.toMat Cm.Seg.Hd.plain (Cm.trace2 (scalesOf hL sc nf) i x)) q :=
    fun k hk h2 q hq => Hd.D5_zOf ok h12 hF.NHf hp.1 hp.2 _ _ k hk q hq
      ((reads_even_or_own hq).elim id fun e => by rw [e]; exact h2)
  refine ⟨i, x, fun _ => Hd.zOf (Cm.Seg.toMat Cm.Seg.Hd.plain
      (Cm.trace2 (scalesOf hL sc nf) i x)),
    fun g => zsOf (SA g) g (Cm.Seg.toMat Cm.Seg.Hd.plain (Cm.trace2 (scalesOf hL sc nf) i x)),
    hr, he, ⟨fun g hg => ?_, fun g hg => ?_, fun g hg r c => ?_, ?_, Hd.labelsAgree_one y _⟩⟩
  · have hk : 2 * g < Cm.Seg.nSeg := by
      show 2 * g < 25
      omega
    exact (layerOrd_iff hy S Zd Z2 hp4 Cm.Seg.Hd.plain _ i.mat hg sc nf x).2
      ⟨fun _ _ _ _ => hZ _ _ _,
        linkOK_congr (laws_plain _) hk
          (fun q hq => ((dict_D5 hy S Zd Z2 hp4 hH Cm.Seg.Hd.plain _ _ hg q hq).trans
            (hD (2 * g) hk (by omega) q hq)).symm)
          (P.link (2 * g) hk)⟩
  · have hA := ord_of_premise hg (hSA g hg) (hw g hg) (hsh g hg) (hE g hg) P
    exact hA
  · exact (Hd.zOf_qa hp.1 hp.2 _ hg r c).trans (zsOf_qa (SA g) g _ r c).symm
  · have hk : 24 < Cm.Seg.nSeg := by
      show 24 < 25
      omega
    exact Hd.ordB_of_ord (Hd.ord_of_link24 hF hLy hy S Zd Z2 (s := scalesOf hL sc nf) he
      (fun _ _ _ => hZ _ _ _)
      (linkOK_congr (laws_plain _) hk
        (fun q hq => ((Hd.headMx_D5 Cm.Seg.Hd.plain hH h12 _ _ q hq).trans
          (hD 24 hk (by norm_num) q hq)).symm)
        (P.link 24 hk)).holds)

/-- **The same at an attention shape that is written out**: its four public hypotheses are
theorems. -/
theorem ords_met_at (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (h12 : y.NGr = 12)
    (hF : Hd.FullH hH) (hLy : Model.Head.layout hH tau = .ok L)
    (hs : (scalesOf hL sc nf).Lawful) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Z : ℕ → ℕ → ℕ → ℕ → ℤ) (ZA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧
        Ords hL sc y hH L nf (fun g => shapeAt ((scalesOf hL sc nf).kap (4 * g)).sh) i.mat x Z ZA :=
  ords_met hy S Zd Z2 hp4 h12 hF hLy (fun _ _ => sized_at _) (fun _ _ => wide_at _)
    (fun _ _ => rfl) (fun _ _ => exp_at _) hs

end Met

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.reads_even_or_own
#print axioms OnBytes.Road.L5.ords_met
#print axioms OnBytes.Road.L5.ords_met_at
