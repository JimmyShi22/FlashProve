-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/LayerEnds3Y.lean: the end values of the second token sumcheck of a layer
sub-proof: what the claims on them say on cells, and what the summand is on the values that were
sent.

The second token sumcheck shows the reciprocal of every norm and, with routed experts, the score and
the selector's entries of every layer that has them, each at the sumcheck's end point. What is sent
is the hidden value plus beta times a mask entry. The verifier claims that each hidden value equals
a form in the reads (claimsTerms, OnBytes/Model/Layer.lean). The sent values stand as constants in
the panels of the batched sumcheck.

Main definitions.
 - Pub34.EndsL3: each hidden end value is the true contraction of the cells at the end point.
 - Pub34.SentL3: each sent value is the hidden one plus beta times a number.
 - L3EndY: the summand on the sent values is the summand Gpos at the end point plus beta times
   lin3 at m, for any beta and m that meet SentL3, under EndsL3. Proved: l3EndY. That m is the mask
   row, fixed before beta is drawn, is said by nothing here: by reading, the line of pscEnds that
   puts the sent values under their slots (OnBytes/Model/Psc.lean).
Main theorems: sig1_congr (the sum of the late panels' shares reads the three families inside the
library's ranges alone), l3EndY.

What is not claimed. Nothing on soundness, and nothing on hiding. All statements are identities in
one world. The program does not read this file.

-/
import Johnson.Road.Rows.LayerEnds34

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading World Aff)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW Pan Rd pans Sig1 Gpos hhU)

variable {K : Type} [Field K]

/-! ## The late panels read the three families inside their ranges -/

/-- A share whose A side is changed outside the panel's rows and columns alone. -/
theorem congr_sums (c : K) (n m : ℕ) (wt : ℕ → K) (A A' B : ℕ → ℕ → K)
    (h : ∀ a b, a < n → b < m → A a b = A' a b) :
    c * ∑ a ∈ range n, wt a * ∑ b ∈ range m, A a b * B a b =
      c * ∑ a ∈ range n, wt a * ∑ b ∈ range m, A' a b * B a b := by
  congr 1
  refine sum_congr rfl fun a ha => ?_
  congr 1
  exact sum_congr rfl fun b hb => by rw [h a b (mem_range.mp ha) (mem_range.mp hb)]

section Congr

variable [scl : Scl] (D : Dim) (r : Rd K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z zh : ℕ → K)

/-- The sum of the late panels' shares reads the reciprocals of the norms below 2 nl, the scores of
the layers below ne, and the selectors' entries of these layers below nx. -/
theorem sig1_congr {R R' sc sc' : ℕ → K} {sel sel' : ℕ → ℕ → K}
    (hR : ∀ ν, ν < 2 * D.nl → R ν = R' ν) (hsc : ∀ l, l < D.ne → sc l = sc' l)
    (hsel : ∀ l e, l < D.ne → e < D.nx → sel l e = sel' l e) :
    Sig1 D (withEnds r R sc sel) tb L0 w z zh = Sig1 D (withEnds r R' sc' sel') tb L0 w z zh := by
  unfold Sig1
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  have hl' : ∀ l', (p = .Gr l' ∨ p = .Ur l' ∨ p = .Dr l') → l' < D.ne := by
    intro l' h
    rw [late_pans D] at hp
    simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at hp
    rcases h with rfl | rfl | rfl <;> simpa using hp
  have hlate : p.late = true := by simpa using (List.mem_filter.mp hp).2
  unfold Pan.share
  cases p with
  | G | U | O | D | V | LR => cases hlate
  | QK => rfl
  | N1 =>
    refine congr_sums _ _ _ _ _ _ _ fun a b ha _ => ?_
    have ha' : a < D.nl := ha
    exact hR (2 * a) (by omega)
  | N2 =>
    refine congr_sums _ _ _ _ _ _ _ fun a b ha _ => ?_
    have ha' : a < D.nl := ha
    exact hR (2 * a + 1) (by omega)
  | XR => exact congr_sums _ _ _ _ _ _ _ fun a b ha _ => hsc a ha
  | DD | MR => exact congr_sums _ _ _ _ _ _ _ fun a b ha hb => hsel a b ha hb
  | Gr l' | Ur l' =>
    refine congr_sums _ _ _ _ _ _ _ fun a b ha _ => ?_
    show sel l' a * r.xr2 l' b = sel' l' a * r.xr2 l' b
    rw [hsel l' a (hl' l' (by simp)) ha]
  | Dr l' =>
    refine congr_sums _ _ _ _ _ _ _ fun a b ha _ => ?_
    show sel l' a * r.hh2 l' b = sel' l' a * r.hh2 l' b
    rw [hsel l' a (hl' l' (by simp)) ha]

end Congr

/-! ## The end values -/

namespace Pub34

variable (X : Pub34 K) (Wo : World K) (Mm : Mats K) (M : Wm K) (hh : ℕ → ℕ → K)

/-- The record of the true contractions of the cells, with the never-sent vectors hh. -/
def rTrue : Rd K :=
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  rTrueP X.p.v.y hh X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) (zOf X.ρ X.H.fo.zx X.H.fo.zy)
    (pt X.ρ X.c.rt)

/-- The number of the score of layer 2 l' + 1 among the end values. -/
def iSc (l' : ℕ) : ℕ := X.p.v.y.NN * X.p.v.y.Lam + l'

/-- The number of entry e of the selector of layer 2 l' + 1 among the end values. -/
def iSel (l' e : ℕ) : ℕ := X.p.v.y.NN * X.p.v.y.Lam + X.p.v.y.LamM + l' * X.p.v.y.h.NE + e

/-- Each hidden end value of the second token sumcheck is the true contraction of the cells at the
end point. The ranges are the library's. -/
def EndsL3 : Prop :=
  (∀ ν, ν < 2 * X.D.nl → Wo.slot (X.tT.sEnd + ν) = (X.rTrue Mm hh).R2 ν) ∧
  (∀ l', l' < X.D.ne → Wo.slot (X.tT.sEnd + X.iSc l') = (X.rTrue Mm hh).sc2 l') ∧
  (∀ l' e, l' < X.D.ne → e < X.D.nx →
    Wo.slot (X.tT.sEnd + X.iSel l' e) = (X.rTrue Mm hh).sel2 l' e)

/-- Each sent end value is the hidden one plus β times a number. m i: the number for end value
number i; in a run, the mask entry of its slot. -/
def SentL3 (β : K) (m : ℕ → K) : Prop :=
  (∀ ν, ν < 2 * X.D.nl → sentAt X.ρ X.p.shownT ν = Wo.slot (X.tT.sEnd + ν) + β * m ν) ∧
  (∀ l', l' < X.D.ne →
    sentAt X.ρ X.p.shownT (X.iSc l') = Wo.slot (X.tT.sEnd + X.iSc l') + β * m (X.iSc l')) ∧
  (∀ l' e, l' < X.D.ne → e < X.D.nx →
    sentAt X.ρ X.p.shownT (X.iSel l' e) =
      Wo.slot (X.tT.sEnd + X.iSel l' e) + β * m (X.iSel l' e))

/-- The routed never-sent vectors are the vectors of the routed gated products at the end point of
the second token sumcheck. This fixes letters; it is no claim. -/
def Honest1 : Prop :=
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  ∀ l', l' < X.D.ne → ∀ j, j < X.D.fe →
    hh (1 + l') j = hhU X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) (2 * l' + 1) (X.D.fe + j)
      (pt X.ρ X.c.rt)

/-- What the panel QK asks of the sizes and of the shifts of queries and keys: public. Concluded in
Johnson/Road/Rows/LayerEnds34Ref.lean: the shifts for every record, the sizes at the reference. -/
def QKOk : Prop :=
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  X.D.ChOK ∧ ∀ l, l < X.D.nl →
    (X.D.Pl l).kq = (X.D.Pl l).kk ∨ (16 ≤ (X.D.Pl l).kq ∧ 16 ≤ (X.D.Pl l).kk)

/-- The linear part of the summand in the shown maps, at the numbers m. It reads the cells, the
weights, the points and m. -/
def lin3 (m : ℕ → K) : K :=
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  Sig1 X.D (withEnds (X.rTrue Mm hh) m (fun l' => m (X.iSc l')) fun l' e => m (X.iSel l' e)) X.tb
      X.L0 (X.w M) X.z X.zh -
    Pan.QK.share X.D (X.rTrue Mm hh) X.tb X.L0 (X.w M) X.z X.zh

end Pub34

/-! ## The ends -/

/-- The summand on the sent values is the summand at the end point plus β times lin3 at m, for any
β and m that meet SentL3. lin3 at m does not read β; that m does not hang on β is not said here. -/
def L3EndY (X : Pub34 K) : Prop :=
  ∀ (Wo : World K) (Mm : Mats K) (M : Wm K) (hh : ℕ → ℕ → K) (β : K) (m : ℕ → K),
    X.QKOk → X.Honest1 Mm hh → X.EndsL3 Wo Mm hh → X.SentL3 Wo β m →
      X.sig1 Mm M hh = X.gpos Mm M (pt X.ρ X.c.rt) + β * X.lin3 Mm M hh m

theorem l3EndY (X : Pub34 K) : L3EndY X := by
  intro Wo Mm M hh β m hq hH2 hE hS
  obtain ⟨hq1, hq2⟩ := hq
  obtain ⟨hE1, hE2, hE3⟩ := hE
  obtain ⟨hS1, hS2, hS3⟩ := hS
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  have c1 := sig1_congr X.D (X.rTrue Mm hh) X.tb X.L0 (X.w M) X.z X.zh
    (R := fun ν => sentAt X.ρ X.p.shownT ν)
    (R' := fun ν => (X.rTrue Mm hh).R2 ν + β * m ν)
    (sc := fun l' => sentAt X.ρ X.p.shownT (X.iSc l'))
    (sc' := fun l' => (X.rTrue Mm hh).sc2 l' + β * m (X.iSc l'))
    (sel := fun l' e => sentAt X.ρ X.p.shownT (X.iSel l' e))
    (sel' := fun l' e => (X.rTrue Mm hh).sel2 l' e + β * m (X.iSel l' e))
    (fun ν hν => by beta_reduce; rw [hS1 ν hν, hE1 ν hν])
    (fun l' hl => by beta_reduce; rw [hS2 l' hl, hE2 l' hl])
    (fun l' e hl he => by beta_reduce; rw [hS3 l' e hl he, hE3 l' e hl he])
  have c2 := sig1_affine X.D (X.rTrue Mm hh) X.tb X.L0 (X.w M) X.z X.zh
    (X.rTrue Mm hh).R2 m (X.rTrue Mm hh).sc2 (fun l' => m (X.iSc l'))
    (X.rTrue Mm hh).sel2 (fun l' e => m (X.iSel l' e)) β
  have g : Sig1 X.D (X.rTrue Mm hh) X.tb X.L0 (X.w M) X.z X.zh = X.gpos Mm M (pt X.ρ X.c.rt) :=
    sig1_gpos X.D (cellsOf X.D (cellsAt X.p.v.y Mm)) X.tb _ _ _ _ _ _ hq1 hq2 hH2
  have e0 : withEnds (X.rTrue Mm hh) (X.rTrue Mm hh).R2 (X.rTrue Mm hh).sc2
      (X.rTrue Mm hh).sel2 = X.rTrue Mm hh := rfl
  rw [e0, g] at c2
  exact c1.trans c2

end OnBytes.Road.Rows
