-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPortSig.lean: the sum of the verifier's panels is the library's.

The batched sumcheck of a layer sub-proof sums a product of two long vectors, made of panels.
Johnson/Road/FormsKeysEnd.lean shows that this sum is the sum, over the verifier's placed panels, of
the claim's weight times the panel's share. The library has its own two sums over its own panels:
Sig0 over the early ones and Sig1 over the late ones (Inst/Model/FF/Objects.lean). This file shows
that the verifier's sum is Sig0 plus the weight of claim 1 times Sig1.

What is compared with what. The verifier's own placed list of panels, with shareP
(Johnson/Road/FormsKeysPort.lean) for a panel's share and wvOf (Johnson/Road/FormsKeysWv.lean) for
the vectors of its weight claims, both definitions of these files on the verifier's records, against
the library's Sig0 and Sig1. The library's sums are taken at the record rPort, which holds the sent
end values of the second token sumcheck and the never-sent vectors where the library's true record
has contractions of the cells (see the head of FormsKeysPort.lean), and at the weights that the
library's own layout reads in the same matrix M: w l := layerR D.P lk M (L0 + l).

The parts, none of which is shown here.
 - Johnson/Road/FormsKeysPans.lean: the placed list is the library's list pans D, member by member
   and in order, each panel with the step that appended it and with its claims.
 - Johnson/Road/FormsKeysEarly.lean and Johnson/Road/FormsKeysLate.lean: for each of the fifteen
   kinds, the share of the panel that the step appends is the call's weight times the library's
   share without its call's weight.
 - Johnson/Road/FormsKeysWvB.lean: the vectors wvOf are the library's B sides, and 0 past their
   columns.
 - Johnson/Road/FormsKeysRet.lean: the forms of a panel's sides are there, if stackEnd returns.

Here: which call a segment's name belongs to (call_of_seg); a few fields of the appended panels
(facts_acc to facts_MR); the vectors in the form that the shares ask (wvRows_AtA, wvTri_AtR); from a
share to a term of the sum (term_of_share); one panel (panel_term, by the fifteen kinds); the sum
(port_sig; sum_early_late); the same in the words of FormsKeysEnd.lean (port_sig_end); the third
clause of stack_slots there by itself, which asks nothing of the world (stack_sum); joined with it,
the sum over all places of the product of the two long vectors that FormsKeysEnd.lean defines
(stack_sig); and that sum against the library's own two long vectors (stack_sa_sb, through sa_sb of
Johnson/Road/FormsKeysSigC.lean). In stack_sig and stack_sa_sb the left side is a definition of
these files: what ties the two long vectors to the verifier's own end of the sumcheck is the first
two clauses of stack_slots, which are not used here.

What is asked. The record SigFits names it, field by field: the records PortFits and AimFits; one
environment; the library's eight lines of calls; for the calls 0, 1, 2 and 5, that the layers'
weights and the call's weight are the library's; the ties of the calls of six families; the weights
of the entries of five families and of the blocks of two; profile 4 and the array o; and what the
panel QK asks. Beside it: both lists are returned; the calls of the second walk are 0, 1, 2, 5; the
weight of claim 0 is 1; stackEnd returns on the placed list.

Where it can be applied. The ties ask that the points of the verifier's calls 0, 1, 2 and 5 read as
the library's points of these calls. Where the verifier's least number of columns makes a call
longer than the library's, the ties of that call fail. By the runs of
Johnson/Road/FormsKeysRunK.lean that is so for the calls 0 and 5 at the small public example, and
for no call at the full-size one. So these theorems cannot be applied at the small example's
numbers.

What shows that the hypotheses can be met. The record SigFits is concluded in
Johnson/Road/FormsKeysCaller.lean (sigFits_of_look): from the verifier's own lines and tests, the
library's lines of calls, the letters in which the lookup makes the calls' points and weights, the
rotary tables, and the truth of the tables that the panels read; where no call is longer than the
library's. That one point z of the library then serves all calls at once is shown in
Johnson/Road/FormsKeysLookT.lean. The calls of the second walk: Johnson/Road/FormsKeysPansTS.lean.
The weight of claim 0 is 1 for the powers of one element: powers_two in FormsKeysRet.lean. That all
hypotheses hold together at some numbers is shown by no closed term and no run. The CONCLUSION is
run, panel by panel, on made-up numbers, with the library's own definitions evaluated
(Johnson/Road/FormsKeysRunP.lean), at sizes that agree with the made-up shape and have a vocabulary
(dimV of Johnson/Road/FormsKeysAimV.lean); that the record holds at these numbers is not run.

Main definitions: SigFits. Main theorems: panel_term, port_sig, port_sig_end, stack_sum, stack_sig,
stack_sa_sb.

What is not claimed. That the sent values in rPort are the hidden ones, or that the never-sent
vectors are the gated products: rPort is not the library's true record. M is any matrix: that it is
the committed one, or that a hidden value is what its claim says of M, is neither asked nor shown.
Nothing is said on the sumcheck's rounds, on probability, or on what a verifier's acceptance shows.
See also Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysPans
import Johnson.Road.FormsKeysWvB
import Johnson.Road.FormsKeysEarly
import Johnson.Road.FormsKeysLate
import Johnson.Road.FormsKeysRet
import Johnson.Road.FormsKeysSigC

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab WsShape WsClaim Seg CallD)
open OnBytes.Model.Layer (Lay SBlk Panels PanelEnv ClaimEnv StackEnd isAcc callsAC panelA panelT
  panelsA panelsT placePanels stackEnd)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam Arr LW Pan Rd pans fams call wc zpos layerR aC zc Sig0 Sig1 SA
  SB lamS)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- In lists that are related member by member, each pair's first member is a member of the first
list. -/
theorem f2_mem_left {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β},
    List.Forall₂ R l l' → List.Forall₂ (fun a b => a ∈ l ∧ R a b) l l'
  | _, _, .nil => List.Forall₂.nil
  | _, _, .cons h1 h2 => List.Forall₂.cons ⟨List.mem_cons_self, h1⟩
      ((f2_mem_left h2).imp fun _ _ k => ⟨List.mem_cons_of_mem _ k.1, k.2⟩)

/-- A sum over panels under the claims' weights, 1 for an early panel and rJ for a late one, is the
sum over the early panels plus rJ times the sum over the late ones. -/
theorem sum_early_late (f : Pan → K) (rJ : K) : ∀ l : List Pan,
    (l.map fun p => p.om rJ * f p).sum =
      ((l.filter fun p => !p.late).map f).sum + rJ * ((l.filter fun p => p.late).map f).sum
  | [] => by simp
  | p :: l => by
    rw [List.map_cons, List.sum_cons, sum_early_late f rJ l, List.filter_cons, List.filter_cons]
    unfold Pan.om
    cases p.late
    · simp only [Bool.not_false, Bool.false_eq_true, if_true, if_false, List.map_cons,
        List.sum_cons]
      ring
    · simp only [Bool.not_true, Bool.false_eq_true, if_true, if_false, List.map_cons,
        List.sum_cons]
      ring

/-- With the library's lines, a call below 8 that holds a segment with the name of a family is the
library's call of the family. -/
theorem call_of_seg {y : Lay} (hN : LinesAre y) {q : ℕ} (hq : q < 8) {g : Seg}
    (hg : g ∈ (y.calls.getD q default).segs) {s0 : Fam} (hn : g.name = segName s0) :
    q = (call s0).val := by
  have e := line_at hN ⟨q, hq⟩
  have hm : g.name ∈ (fams ⟨q, hq⟩).map segName := by
    rw [← e]
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  obtain ⟨s1, h1, h2⟩ := List.mem_map.mp hm
  have e1 : s1 = s0 := segName_inj (h2.trans hn)
  subst e1
  rw [Inst.Model.FFSeg.IndexFacts.call_of_mem _ _ h1]

/-! ## What the appended panels hold beside their sides -/

section Facts

variable {p : PanelEnv} {ec : E} {el : Array E} {s s' : Panels} {b : SBlk}

/-- The panel that panelA appends for one of its six segments belongs to claim 0 and has no B side
given as forms. Unless the segment is D, it has no never-sent vector either. -/
theorem facts_acc {sn : String} (h : isAcc sn = true)
    (hb : (panelA p ec el sn s).bl = s.bl.push b) :
    b.claim = 0 ∧ b.B = none ∧ ((sn == "D") = false → b.virt = none) := by
  rcases (isAcc_iff sn).mp h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (obtain rfl := push_inj hb
     first
       | exact ⟨rfl, rfl, fun _ => rfl⟩
       | exact ⟨rfl, rfl, fun k => Bool.noConfusion (show true = false from k)⟩)

/-- The panel that panelT appends for the segment QK belongs to claim 1, has no B side given as
forms and no never-sent vector. -/
theorem facts_QK (h : panelT p ec el "QK" s = some s') (hb : s'.bl = s.bl.push b) :
    b.claim = 1 ∧ b.B = none ∧ b.virt = none := by
  rw [panelT_QK_eq] at h
  cases h
  obtain rfl := push_inj hb
  exact ⟨rfl, rfl, rfl⟩

/-- The panel that a step of triStep appends belongs to claim 1 and has NE rows. -/
theorem facts_tri {sn : String} {lm : ℕ} (h : triStep p ec el sn s lm = some s')
    (hb : s'.bl = s.bl.push b) : b.claim = 1 ∧ b.ni = p.v.y.h.NE := by
  simp only [triStep] at h
  split_ifs at h <;> first
    | (cases h; obtain rfl := push_inj hb; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h; obtain rfl := push_inj hb; exact ⟨rfl, rfl⟩)

/-- The panel that panelT appends for N1 belongs to claim 1 and has no never-sent vector. -/
theorem facts_N1 (h : panelT p ec el "N1" s = some s') (hb : s'.bl = s.bl.push b) :
    b.claim = 1 ∧ b.virt = none := by
  rw [panelT_N1_eq] at h
  obtain ⟨_, _, e⟩ := of_bind_some h
  rw [e, plain_push] at hb
  obtain rfl := push_inj hb
  exact ⟨rfl, rfl⟩

/-- The same for N2. -/
theorem facts_N2 (h : panelT p ec el "N2" s = some s') (hb : s'.bl = s.bl.push b) :
    b.claim = 1 ∧ b.virt = none := by
  rw [panelT_N2_eq] at h
  obtain ⟨_, _, e⟩ := of_bind_some h
  rw [e, plain_push] at hb
  obtain rfl := push_inj hb
  exact ⟨rfl, rfl⟩

/-- The same for XR, with routed experts. -/
theorem facts_XR (h3 : p.v.y.h.p3 = true) (h : panelT p ec el "XR" s = some s')
    (hb : s'.bl = s.bl.push b) : b.claim = 1 ∧ b.virt = none := by
  rw [panelT_XR_eq, h3] at h
  obtain ⟨_, _, e⟩ := of_bind_some (o := p.v.ewOf "XR") h
  rw [e, plain_push] at hb
  obtain rfl := push_inj hb
  exact ⟨rfl, rfl⟩

/-- The same for DD. -/
theorem facts_DD (h3 : p.v.y.h.p3 = true) (h : panelT p ec el "DD" s = some s')
    (hb : s'.bl = s.bl.push b) : b.claim = 1 ∧ b.virt = none := by
  rw [panelT_DD_eq, h3] at h
  obtain ⟨_, _, e⟩ := of_bind_some (o := p.v.ewOf "DD") h
  rw [e, plain_push] at hb
  obtain rfl := push_inj hb
  exact ⟨rfl, rfl⟩

/-- The same for MR. -/
theorem facts_MR (h3 : p.v.y.h.p3 = true) (h : panelT p ec el "MR" s = some s')
    (hb : s'.bl = s.bl.push b) : b.claim = 1 ∧ b.virt = none := by
  rw [panelT_MR_eq, h3] at h
  obtain ⟨_, _, e⟩ := of_bind_some (o := p.v.ewOf "MR") h
  rw [e, plain_push] at hb
  obtain rfl := push_inj hb
  exact ⟨rfl, rfl⟩

end Facts

/-! ## The vectors of the weight claims, in the form that the shares ask -/

section Vectors

variable {ρ : Reading K} {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)}
  {s : WsShape} {D : Dim} {lk L0 : ℕ} {z ζ : ℕ → K} (A : AimFits ρ c h pc s D lk L0 ζ)
  (M : Wm K) (r : Rd K) (tb : Tables) (zh : ℕ → K)

include A

/-- For a panel of which AtA holds: the vectors wvOf are the rows of the library's B side on its
columns, and 0 past them. -/
theorem wvRows_AtA {p : PanelEnv} {cl : List WsClaim} {b : SBlk} {v0 q : ℕ} {g : Seg}
    (T : CallTie ρ c h D z (panOf g.name).fam) (H : AtA p c cl b v0 q g) :
    WvRows (wvOf ρ c.wsLay M cl) v0 b.ni b.wy ((panOf g.name).nc D)
      ((panOf g.name).B D r tb L0 (fun l => layerR D.P lk M (L0 + l)) z zh) := by
  intro i hi yv _
  split_ifs with k
  · exact wvOf_AtA A M r tb zh T H i hi yv k
  · exact wvOf_AtA_zero ρ A M H i hi yv (Nat.le_of_not_lt k)

/-- For a panel of which AtR holds: the vector wvOf holds the library's B side, row after row, and 0
past its columns. -/
theorem wvTri_AtR {p : PanelEnv} (hv : p.v = c.v) {cl : List WsClaim} {b : SBlk} {v0 q : ℕ}
    {g : Seg} {lm : ℕ} (T : CallTie ρ c h D z (panR g.name lm).fam)
    (H : AtR p c cl b v0 q g lm) (hni : b.ni = (panR g.name lm).nr D) :
    WvTri (wvOf ρ c.wsLay M cl) v0 b.ni b.wy ((panR g.name lm).nc D)
      ((panR g.name lm).B D r tb L0 (fun l => layerR D.P lk M (L0 + l)) z zh) := by
  intro e he yv hy
  split_ifs with k
  · exact wvOf_AtR A M r tb zh hv T H e (hni ▸ he) yv k
  · exact wvOf_AtR_zero ρ A.claim M hv H e yv hy (Nat.le_of_not_lt k)

end Vectors

/-! ## One panel -/

section One

variable [scl : Scl] {ρ : Reading K} {Wo : World K} {D : Dim} {p : PanelEnv} {om : Array E}
  {hh wv : ℕ → ℕ → K} {r : Rd K} {tb : Tables} {L0 : ℕ} {w : ℕ → LW K} {z zh : ℕ → K}

/-- From a panel's share to its term in the sum. If the share of the verifier's panel b is the
weight of call number q times the library's share of pn without its call's weight, q is the
library's call of the family of pn, the verifier's weight of that call is the library's, b belongs
to claim 1 if pn is late and to claim 0 if not, and the weight of claim 0 is 1, then the weight of
the claim of b times its share is the library's weight of the claim of pn times its share. -/
theorem term_of_share {b : SBlk} {pn : Pan} {q : ℕ}
    (e : shareP ρ Wo p.v.y hh wv b = ρ.val (p.e.getD q zeroE) * shareL D r tb L0 w z zh pn)
    (hq : q = (call pn.fam).val)
    (hwc : ρ.val (p.e.getD (call pn.fam).val zeroE) = wc D z (call pn.fam))
    (hcl : b.claim = if pn.late then 1 else 0) (hom : ρ.val (om.getD 0 zeroE) = 1) :
    omK ρ om b * shareP ρ Wo p.v.y hh wv b =
      pn.om (ρ.val (om.getD 1 zeroE)) * pn.share D r tb L0 w z zh := by
  unfold omK Pan.om
  rw [hcl, e, hq, hwc, share_wc]
  cases pn.late
  · simp only [Bool.false_eq_true, if_false, hom]
  · simp only [if_true]

end One

/-! ## All that is asked -/

section Whole

variable [scl : Scl]

/-- All that the comparison of the two sums asks, beside the verifier's own lists. -/
structure SigFits (ρ : Reading K) (Wo : World K) (p : PanelEnv) (c : ClaimEnv)
    (h : Model.Layer.Shape) (pc : List (List String)) (s : WsShape) (D : Dim) (lk L0 : ℕ)
    (cc : Cells K) (t : Cell → K) (low z zh ζ : ℕ → K) (tb : Tables) : Prop where
  /-- the record of Johnson/Road/FormsKeysPort.lean, on the panels' environment -/
  port : PortFits ρ Wo p.v D cc t low z zh
  /-- the record of Johnson/Road/FormsKeysAim.lean, on the claims' environment -/
  aim : AimFits ρ c h pc s D lk L0 ζ
  /-- the panels and the claims are made from one environment -/
  env : p.v = c.v
  /-- the eight lines of calls are the library's -/
  lines : LinesAre p.v.y
  /-- the layers' weights in the points of the calls 0, 1, 2, 5 are the library's -/
  el : ∀ k : Fin 8, k ∈ [(0 : Fin 8), 1, 2, 5] → ElTie ρ p.v D z k.val k
  /-- the weights of the calls 0, 1, 2, 5 are the library's -/
  wc : ∀ k : Fin 8, k ∈ [(0 : Fin 8), 1, 2, 5] → ρ.val (p.e.getD k.val zeroE) = wc D z k
  /-- the ties of the calls of the six families with a matrix product in the lookup's join -/
  tie : ∀ s0 : Fam, s0 ∈ [Fam.G, Fam.U, Fam.V, Fam.O, Fam.D, Fam.LR] → CallTie ρ c h D z s0
  /-- the weights of the entries of five families are the library's -/
  ew : ∀ s0 : Fam, s0 ∈ [Fam.N1, Fam.N2, Fam.XR, Fam.DD, Fam.MR] → EwTie ρ p.v D z s0
  /-- the weights of the blocks and of the entries of the two norms' families are one set -/
  wts : ∀ s0 : Fam, s0 ∈ [Fam.N1, Fam.N2] → WtsTie ρ p.v D low s0
  /-- profile 4 -/
  p4 : p.v.y.h.p4 = true
  /-- the array o is found, tied and true at the library's token point -/
  o : HasShort ρ Wo p.v D cc t (zpos D z) .o
  /-- the call that holds the segment QK: the record of Johnson/Road/FormsKeysQK.lean, and its point
  reads as the library's -/
  qk : ∃ (q : ℕ) (cd : CallD) (sg : Seg), QKFits c D q cd sg ∧
    ∀ j < aC D (call .QK), pt ρ (c.v.zk.getD q #[]) j = zc D z (call .QK) j
  /-- the end point of the second token sumcheck has the coordinates of a position -/
  rt : c.rt.size = D.lT
  /-- the rotary tables -/
  rope : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb L0 lam
  /-- zh is the reading of that end point -/
  zh : ∀ j < D.lT, zh j = pt ρ c.rt j

variable {ρ : Reading K} {Wo : World K} {p : PanelEnv} {c : ClaimEnv} {h : Model.Layer.Shape}
  {pc : List (List String)} {s : WsShape} {D : Dim} {lk L0 : ℕ} {cc : Cells K} {t : Cell → K}
  {low z zh ζ : ℕ → K} {tb : Tables}

/-- ONE PANEL. If b is the verifier's panel of the library's panel pn (IsPanelOf), the weight of the
claim of b times its share, with the vectors of the weight claims read from the matrix M, is the
library's weight of the claim of pn times its share, at the record rPort and at the weights that the
library's layout reads in M. hr: the forms of the sides of b are there, if b is a panel whose sides
are read as forms. hh: the never-sent vectors, free. -/
theorem panel_term (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (M : Wm K)
    (hh : ℕ → ℕ → K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {cl : List WsClaim} {om : Array E}
    (hom : ρ.val (om.getD 0 zeroE) = 1) {b : SBlk} {pn : Pan} (hI : IsPanelOf p c TS cl b pn)
    (hr : b.tri = false → b.virt = none → (∀ v0, b.v0 = some v0 → b.B = none) → Returns b) :
    omK ρ om b * shareP ρ Wo p.v.y hh (wvOf ρ c.wsLay M cl) b =
      pn.om (ρ.val (om.getD 1 zeroE)) * pn.share D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
        (fun l => layerR D.P lk M (L0 + l)) z zh := by
  have hAC := callsAC_of_lines S.lines
  have h3 : p.v.y.h.p3 = true := by
    rw [S.env]
    exact S.aim.claim.p3
  cases pn with
  | G =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.G).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    have hw := wvRows_AtA S.aim M (rPort ρ p.v.y p.shownT hh D t z zh) tb zh
      (S.tie _ (panOf_fam g.name)) H
    rw [hn] at hbl hw f3
    rw [← hst] at hw
    exact term_of_share
      (shareP_G S.port p rfl _ st hh _ tb L0 _ q (by rw [hq']; exact S.el _ (by decide))
        hbl (hr ht (f3 rfl) fun _ _ => f2) hw)
      hq' (S.wc _ (by decide)) f1 hom
  | U =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.U).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    have hw := wvRows_AtA S.aim M (rPort ρ p.v.y p.shownT hh D t z zh) tb zh
      (S.tie _ (panOf_fam g.name)) H
    rw [hn] at hbl hw f3
    rw [← hst] at hw
    exact term_of_share
      (shareP_U S.port p rfl _ st hh _ tb L0 _ q (by rw [hq']; exact S.el _ (by decide))
        hbl (hr ht (f3 rfl) fun _ _ => f2) hw)
      hq' (S.wc _ (by decide)) f1 hom
  | O =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.O).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    have hw := wvRows_AtA S.aim M (rPort ρ p.v.y p.shownT hh D t z zh) tb zh
      (S.tie _ (panOf_fam g.name)) H
    rw [hn] at hbl hw f3
    rw [← hst] at hw
    exact term_of_share
      (shareP_O S.port p rfl _ st hh _ tb L0 _ q (by rw [hq']; exact S.el _ (by decide)) S.p4 S.o
        hbl (hr ht (f3 rfl) fun _ _ => f2) hw)
      hq' (S.wc _ (by decide)) f1 hom
  | D =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.D).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    have hw := wvRows_AtA S.aim M (rPort ρ p.v.y p.shownT hh D t z zh) tb zh
      (S.tie _ (panOf_fam g.name)) H
    rw [hn] at hbl hw f3
    rw [← hst] at hw
    exact term_of_share
      (shareP_D S.port p rfl _ st hh _ tb L0 _ q (by rw [hq']; exact S.el _ (by decide))
        hbl hw)
      hq' (S.wc _ (by decide)) f1 hom
  | V =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.V).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    have hw := wvRows_AtA S.aim M (rPort ρ p.v.y p.shownT hh D t z zh) tb zh
      (S.tie _ (panOf_fam g.name)) H
    rw [hn] at hbl hw f3
    rw [← hst] at hw
    exact term_of_share
      (shareP_V S.port p rfl _ st hh _ tb L0 _ q (by rw [hq']; exact S.el _ (by decide))
        hbl (hr ht (f3 rfl) fun _ _ => f2) hw)
      hq' (S.wc _ (by decide)) f1 hom
  | LR =>
    obtain ⟨v0, -, ht, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, l, hacc, hst, hbl, -, -, -⟩ := id H
    rw [hAC] at hq
    have hq' : q = (call Fam.LR).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2, f3⟩ := facts_acc hacc hbl
    have hw := wvRows_AtA S.aim M (rPort ρ p.v.y p.shownT hh D t z zh) tb zh
      (S.tie _ (panOf_fam g.name)) H
    rw [hn] at hbl hw f3
    rw [← hst] at hw
    exact term_of_share
      (shareP_LR S.port p rfl _ st hh _ tb L0 _ q (by rw [hq']; exact S.el _ (by decide))
        hbl (hr ht (f3 rfl) fun _ _ => f2) hw)
      hq' (S.wc _ (by decide)) f1 hom
  | Gr lm =>
    obtain ⟨v0, -, -, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, st', l, -, -, hlm, hst, hstep, hbl, -, -, -⟩ := id H
    rw [hTS] at hq
    have hq' : q = (call Fam.G).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2⟩ := facts_tri hstep hbl
    have hni : b.ni = (panR g.name lm).nr D := by
      rw [f2, S.env, S.aim.claim.NE, hn]
      rfl
    have hw := wvTri_AtR S.aim M (rPort ρ p.v.y p.shownT hh D t z zh) tb zh S.env
      (S.tie _ (panR_fam g.name lm)) H hni
    rw [hn] at hstep hw
    rw [← hst] at hw
    exact term_of_share
      (panelP_Gr S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) p rfl _ st hh _ tb L0 _
        (by rw [← S.aim.claim.LamM, ← S.env]; exact hlm) hstep hbl hw)
      hq' (S.wc (call Fam.G) (by decide)) f1 hom
  | Ur lm =>
    obtain ⟨v0, -, -, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, st', l, -, -, hlm, hst, hstep, hbl, -, -, -⟩ := id H
    rw [hTS] at hq
    have hq' : q = (call Fam.U).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2⟩ := facts_tri hstep hbl
    have hni : b.ni = (panR g.name lm).nr D := by
      rw [f2, S.env, S.aim.claim.NE, hn]
      rfl
    have hw := wvTri_AtR S.aim M (rPort ρ p.v.y p.shownT hh D t z zh) tb zh S.env
      (S.tie _ (panR_fam g.name lm)) H hni
    rw [hn] at hstep hw
    rw [← hst] at hw
    exact term_of_share
      (panelP_Ur S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) p rfl _ st hh _ tb L0 _
        (by rw [← S.aim.claim.LamM, ← S.env]; exact hlm) hstep hbl hw)
      hq' (S.wc (call Fam.U) (by decide)) f1 hom
  | N1 =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.N1).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_N1 hs hbl
    exact term_of_share
      (panelP_N1 S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
        (S.wts _ (by simp))
        p rfl _ st hh _ tb L0 _ hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k))
      hq' (S.wc _ (by decide)) f1 hom
  | N2 =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.N2).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_N2 hs hbl
    exact term_of_share
      (panelP_N2 S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
        (S.wts _ (by simp))
        p rfl _ st hh _ tb L0 _ hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k))
      hq' (S.wc _ (by decide)) f1 hom
  | Dr lm =>
    obtain ⟨v0, -, -, q, hq, g, hg, hn, H⟩ := hI
    obtain ⟨st, st', l, -, -, hlm, hst, hstep, hbl, -, -, -⟩ := id H
    rw [hTS] at hq
    have hq' : q = (call Fam.D).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    obtain ⟨f1, f2⟩ := facts_tri hstep hbl
    have hni : b.ni = (panR g.name lm).nr D := by
      rw [f2, S.env, S.aim.claim.NE, hn]
      rfl
    have hw := wvTri_AtR S.aim M (rPort ρ p.v.y p.shownT hh D t z zh) tb zh S.env
      (S.tie _ (panR_fam g.name lm)) H hni
    rw [hn] at hstep hw
    rw [← hst] at hw
    exact term_of_share
      (panelP_Dr S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) p rfl _ st hh _ tb L0 _
        (by rw [← S.aim.claim.LamM, ← S.env]; exact hlm) hstep hbl hw)
      hq' (S.wc (call Fam.D) (by decide)) f1 hom
  | QK =>
    obtain ⟨v0, -, ht, q, hq, g, hg, H⟩ := hI
    obtain ⟨st, st', l, hn, hst, hs, hbl, -, -, -⟩ := id H
    rw [hTS] at hq
    have hq' : q = (call Fam.QK).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨f1, f2, f3⟩ := facts_QK hs hbl
    obtain ⟨q0, cd, sg, F, hz⟩ := S.qk
    have hw : WvRows (wvOf ρ c.wsLay M cl) st.nextV b.ni b.wy (Pan.QK.nc D)
        (Pan.QK.B D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
          (fun l => layerR D.P lk M (L0 + l)) z zh) := by
      intro i hi yv _
      rw [hst]
      split_ifs with k
      · exact wvOf_AtQK ρ S.aim.claim F S.rt S.rope hz S.zh _ M H i hi yv k
      · exact wvOf_AtQK_zero ρ S.aim.claim M H i hi yv (Nat.le_of_not_lt k)
    exact term_of_share
      (shareP_QK S.port p rfl _ st hh _ tb L0 _ q (by rw [hq']; exact S.el _ (by decide)) hs hbl
        (hr ht f3 fun _ _ => f2) hw)
      hq' (S.wc _ (by decide)) f1 hom
  | XR =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.XR).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_XR h3 hs hbl
    exact term_of_share
      (panelP_XR S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
        p rfl _ st hh _ tb L0 _ hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k))
      hq' (S.wc _ (by decide)) f1 hom
  | DD =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.DD).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_DD h3 hs hbl
    exact term_of_share
      (panelP_DD S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
        p rfl _ st hh _ tb L0 _ hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k))
      hq' (S.wc _ (by decide)) f1 hom
  | MR =>
    obtain ⟨h0, ht, q, hq, g, hg, hn, st, st', hs, hbl⟩ := hI
    rw [hTS] at hq
    have hq' : q = (call Fam.MR).val := call_of_seg S.lines (by simp at hq; omega) hg hn
    rw [hn] at hs
    obtain ⟨f1, f2⟩ := facts_MR h3 hs hbl
    exact term_of_share
      (panelP_MR S.port (q := q) (by rw [hq']; exact S.el _ (by decide)) (S.ew _ (by simp))
        p rfl _ st hh _ tb L0 _ hs hbl (hr ht f2 fun v0 k => by rw [h0] at k; cases k))
      hq' (S.wc _ (by decide)) f1 hom

/-- THE SUM OF THE VERIFIER'S PANELS IS THE LIBRARY'S. On the verifier's own placed list of panels,
with its own list of weight claims: the sum over the panels of the claim's weight times the panel's
share, with the vectors of the weight claims read from the matrix M, is the library's Sig0 plus the
weight of claim 1 times its Sig1, at the record rPort and at the weights that the library's layout
reads in M. Asked: SigFits; both lists are returned; the calls of the second walk are 0, 1, 2, 5;
the weight of claim 0 is 1; stackEnd has returned on the placed list, on whatever arrays. hh: the
never-sent vectors, free. -/
theorem port_sig (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (M : Wm K)
    (hh : ℕ → ℕ → K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {pans' : Panels}
    {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1)
    {rs H1 V : Array E} {lam : ℕ} {shownA shownB : E} {s' : StackEnd}
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s') :
    ((placePanels pans'.bl).1.toList.map fun b =>
        omK ρ om b * shareP ρ Wo p.v.y hh (wvOf ρ c.wsLay M cl) b).sum =
      Sig0 D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
          (fun l => layerR D.P lk M (L0 + l)) z zh +
        ρ.val (om.getD 1 zeroE) *
          Sig1 D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
            (fun l => layerR D.P lk M (L0 + l)) z zh := by
  have h3 : p.v.y.h.p3 = true := by
    rw [S.env]
    exact S.aim.claim.p3
  have hne : p.v.y.LamM = D.ne := by
    rw [S.env]
    exact S.aim.claim.LamM
  have F2 := f2_mem_left (placed_are_pans p c S.env hp hc h3 hne S.lines hTS)
  unfold Sig0 Sig1
  rw [← sum_early_late]
  refine sum_of_f2 _ _ (fun b' pn k => ?_) F2
  obtain ⟨hm, b, ⟨o, rfl⟩, hI⟩ := k
  have hr : b.tri = false → b.virt = none → (∀ v0, b.v0 = some v0 → b.B = none) → Returns b := by
    intro ht hk hB
    have r := returns_of_stackEnd hst { b with off := o } hm ht hk hB
    exact r
  have e := panel_term S M hh hTS hom hI hr
  exact e

end Whole

#print axioms sum_early_late
#print axioms call_of_seg
#print axioms term_of_share
#print axioms panel_term
#print axioms port_sig

/-! ## In the words of the end of the batched sumcheck -/

section End

variable [scl : Scl] {ρ : Reading K} {Wo : World K} {p : PanelEnv} {c : ClaimEnv}
  {h : Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim} {lk L0 : ℕ}
  {cc : Cells K} {t : Cell → K} {low z zh ζ : ℕ → K} {tb : Tables}

/-- port_sig with the left side as the third clause of stack_slots, stack_hidden and stack_at
(Johnson/Road/FormsKeysEnd.lean) writes it. -/
theorem port_sig_end (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (M : Wm K)
    (hh : ℕ → ℕ → K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {pans' : Panels}
    {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1)
    {rs H1 V : Array E} {lam : ℕ} {shownA shownB : E} {s' : StackEnd}
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s') :
    ((placePanels pans'.bl).1.toList.map fun b =>
        omK ρ om b * ρ.val b.ec * ∑ i ∈ range (nRows p.v.y b), rowW ρ b i *
          ∑ yv ∈ range (2 ^ b.wy), aRaw ρ Wo hh b i yv *
            bRaw ρ Wo (wvOf ρ c.wsLay M cl) b i yv).sum =
      Sig0 D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
          (fun l => layerR D.P lk M (L0 + l)) z zh +
        ρ.val (om.getD 1 zeroE) *
          Sig1 D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
            (fun l => layerR D.P lk M (L0 + l)) z zh := by
  rw [← port_sig S M hh hTS hp hc hom hst]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  unfold shareP
  rw [mul_assoc]

omit scl in
/-- The third clause of stack_at, stack_hidden and stack_slots (Johnson/Road/FormsKeysEnd.lean) by
itself. On the verifier's own list of panels, under the caller's test of the number of places: the
sum over all places of the product of the two long vectors is the sum over the placed panels of the
claim's weight times the call's weight times the sum over the rows of the row's weight times the
inner product of the row's two sides. Nothing is asked of the world, of the challenges or of what
stackEnd returns: hv and wv are any vectors. -/
theorem stack_sum {TS : List ℕ} {pans' : Panels}
    (hp : panelsT p TS (panelsA p {}) = some pans') {lam : ℕ}
    (hlam : (ceilLog2 (placePanels pans'.bl).2 == lam) = true) (om : Array E)
    (hv wv : ℕ → ℕ → K) :
    ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hv) (placePanels pans'.bl).1.toList Y *
        vecOf (bG ρ Wo wv) (placePanels pans'.bl).1.toList Y =
      ((placePanels pans'.bl).1.toList.map fun b =>
        omK ρ om b * ρ.val b.ec * ∑ i ∈ range (nRows p.v.y b), rowW ρ b i *
          ∑ yv ∈ range (2 ^ b.wy), aRaw ρ Wo hv b i yv * bRaw ρ Wo wv b i yv).sum := by
  have hN := places_le hlam
  have ok := placed_ok (y := p.v.y) (rs := Array.replicate lam zeroE) pans'.bl
    (shape_panels p TS hp) hN (by simp)
  rw [placed_sum _ _ pans'.bl hN]
  congr 1
  refine List.map_congr_left fun b hb => ?_
  refine share_rows ρ Wo om hv wv (ok b hb).wy_le ?_
  unfold nRows
  by_cases ht : b.tri = true
  · rw [if_pos ht]
    exact (ok b hb).ne_le ht
  · rw [if_neg ht]
    exact (ok b hb).ni_le

/-- THE SUM OF THE BATCHED SUMCHECK. port_sig joined with stack_sum: the sum over all places of the
product of the verifier's two long vectors is the library's Sig0 plus the weight of claim 1 times
its Sig1. Asked beside port_sig's hypotheses: the caller's test of the number of places. Nothing is
asked of the hidden end values of the batched sumcheck. Of its challenges and of what was sent at
its end only this is asked, as in port_sig: that stackEnd returns on the placed list for some
arrays (hst), which is read for one thing alone, that the forms of the panels' sides are there. -/
theorem stack_sig (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (M : Wm K)
    (hh : ℕ → ℕ → K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {pans' : Panels}
    {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1)
    {rs H1 V : Array E} {lam : ℕ} {shownA shownB : E} {s' : StackEnd}
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s')
    (hlam : (ceilLog2 (placePanels pans'.bl).2 == lam) = true) :
    ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hh) (placePanels pans'.bl).1.toList Y *
        vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans'.bl).1.toList Y =
      Sig0 D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
          (fun l => layerR D.P lk M (L0 + l)) z zh +
        ρ.val (om.getD 1 zeroE) *
          Sig1 D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
            (fun l => layerR D.P lk M (L0 + l)) z zh := by
  rw [stack_sum hp hlam]
  exact port_sig_end S M hh hTS hp hc hom hst

/-- stack_sig joined with sa_sb of Johnson/Road/FormsKeysSigC.lean: the sum over all places of the
product of the two long vectors that FormsKeysEnd.lean defines is the sum over the library's places
of the product of the library's own two long vectors SA and SB, at the record rPort and with the
weight of claim 1 for the library's rJ. The two sums run over 2^lam and 2^lamS D places: that the
two numbers are one, and that a panel's first place is the library's, is not said here. Side by side
the vectors differ (at the down product's panel): only the sums are compared. -/
theorem stack_sa_sb (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (M : Wm K)
    (hh : ℕ → ℕ → K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {pans' : Panels}
    {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1)
    {rs H1 V : Array E} {lam : ℕ} {shownA shownB : E} {s' : StackEnd}
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s')
    (hlam : (ceilLog2 (placePanels pans'.bl).2 == lam) = true) :
    ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hh) (placePanels pans'.bl).1.toList Y *
        vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans'.bl).1.toList Y =
      ∑ y ∈ range (2 ^ lamS D),
        SA D (rPort ρ p.v.y p.shownT hh D t z zh) z (ρ.val (om.getD 1 zeroE)) y *
          SB D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
            (fun l => layerR D.P lk M (L0 + l)) z zh y := by
  rw [stack_sig S M hh hTS hp hc hom hst hlam, sa_sb]

end End

#print axioms port_sig_end
#print axioms stack_sum
#print axioms stack_sig
#print axioms stack_sa_sb

end OnBytes.Road
