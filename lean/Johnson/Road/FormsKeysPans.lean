-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPans.lean: the verifier's list of panels, member by member and in order.

The summand of a layer sub-proof's batched sumcheck is made of panels. The verifier lists them by
two walks over the segments of the lookup's calls (panelsA and panelsT in
OnBytes/Model/LayerPanels.lean). The library has a list of its own (pans in
Inst/Model/FF/Objects.lean). Johnson/Road/FormsKeysFold.lean says of each panel of the verifier's
list from which segment it comes and which weight claims are its own, but not at which place of the
list it stands. This file says that: the list has, member by member and in order, one panel for each
member of a list of marks, and, if the lines of the calls are the library's, one for each member of
the library's list.

What is compared with what. panels_src: the verifier's two lists, of panels and of weight claims,
with each other and with the names of the segments of its own layout. panels_are_pans,
panels_of_lines, placed_are_pans: the order of the verifier's list against the order of the
library's list pans D. What "b is the panel of the library's panel pn" says (IsPanelOf) is on the
verifier's side alone: which step of the walks has appended b, for a segment of which name, and
where its claims stand. That the panel's sides, weights and numbers are the library's is not part of
it.

The file goes in five steps.
 1. Three walks in step: the state, the claims, a list of marks (foldl_step3 and its like). They are
    the lemmas of FormsKeysFold.lean with a third list.
 2. The marks (Src), what it says that a panel has a mark (IsSrc), and the marks that a segment's
    name gives in each walk (tagsA, tagsT, which follows the cases of panelT in their order).
 3. One segment keeps the walks in step (stepA3, stepT3; tri_list for the inner walk over the layers
    with routed experts); so do the whole walks (walkA3, walkT3); panels_src.
 4. With the library's lines, the marks are those of pans D (srcOf, pans_src; tagsA_0 to tagsT_5 by
    evaluation): panels_are_pans. The calls of the first walk and the four lines follow from the
    eight lines (LinesAre; callsAC_of_lines, line_at): panels_of_lines.
 5. The placing changes a panel's first place alone and keeps the order (placed_f2):
    placed_are_pans. A sum over the one list is a sum over the other, if the two summands agree on
    each panel and its member (sum_of_f2).

What is asked, and what shows that it can be met.
 - hv, hp, hc: the two lists are made from one environment and both functions return: as in
   FormsKeysFold.lean.
 - h3, hne: there are routed experts, on as many layers of a group as in the library's sizes.
 - hN: the eight lines of calls are the library's.
 - hTS: the calls of the second walk are 0, 1, 2, 5. The check of a layer sub-proof finds them by
   the calls' own names (the names that readsOf lists, each looked up by callNo). That this gives 0,
   1, 2, 5, on a layout that the verifier returns with these lines and routed experts, is shown in
   Johnson/Road/FormsKeysPansTS.lean (ts_of_lines): the verifier refuses two calls of one name.
 Johnson/Road/FormsKeysPansRun.lean evaluates all of these together at a made-up shape, on the
 verifier's own functions. That is a run, not a theorem.

Main definitions: Src, IsSrc, tagsA, tagsT, InStep3; srcOf, IsPanelOf; LinesAre.
Main theorems: panels_src; panels_are_pans, panels_of_lines, placed_are_pans; sum_of_f2;
callsAC_of_lines, line_at, placed_f2.

What is not claimed. Every theorem begins "if the function returns a value": none says that it does.
Nothing is said for a layout without routed experts beyond panels_src, or for lines in another
order: there the verifier's list stands in another order. A panel is a record without a name: two
panels of the list may be equal as records; the statements are on places of the list. See also
Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysFold
import Inst.Model.FF.Objects

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (eqTab WsClaim Seg)
open OnBytes.Model.Layer (SBlk Panels PanelEnv ClaimEnv isAcc callsAC panelA panelT panelsA
  panelsT)
open Inst.Model.FFSeg (Dim Pan pans fams)

/-! ## Tools: three walks in step -/

section Tools

variable {α β γ σ τ : Type}

/-- Lists that are related member by member stay so when they are joined. -/
theorem f2_append {R : α → β → Prop} : ∀ {l1 : List α} {l1' : List β} {l2 : List α}
    {l2' : List β}, List.Forall₂ R l1 l1' → List.Forall₂ R l2 l2' →
    List.Forall₂ R (l1 ++ l2) (l1' ++ l2')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h1 h2, h => List.Forall₂.cons h1 (f2_append h2 h)

/-- Three walks over one list in step. One changes a state, one gives for each member a list that
may be refused, one gives a list of marks. If each step keeps a relation between the state and the
two joined lists so far, the whole walks keep it. -/
theorem foldl_step3 (I : σ → List β → List τ → Prop) (f : σ → α → σ) (k : α → Option (List β))
    (t : α → List τ) :
    ∀ (xs : List α) (s : σ) (pre : List β) (tg : List τ) (ls : List (List β)),
      (∀ x ∈ xs, ∀ s pre tg l, I s pre tg → k x = some l → I (f s x) (pre ++ l) (tg ++ t x)) →
      I s pre tg → xs.mapM k = some ls →
      I (xs.foldl f s) (pre ++ ls.flatten) (tg ++ xs.flatMap t)
  | [], s, pre, tg, ls, _, h, e => by
    have hl : ls = [] := by simpa using e.symm
    subst hl
    simpa using h
  | x :: xs, s, pre, tg, ls, H, h, e => by
    obtain ⟨l, ls', hl, hls, rfl⟩ := mapM_cons_some e
    rw [List.foldl_cons, List.flatten_cons, ← List.append_assoc, List.flatMap_cons,
      ← List.append_assoc]
    exact foldl_step3 I f k t xs (f s x) (pre ++ l) (tg ++ t x) ls'
      (fun x' hx' => H x' (List.mem_cons_of_mem _ hx')) (H x List.mem_cons_self s pre tg l h hl)
      hls

/-- The same where the first walk's steps may refuse. -/
theorem foldlM_step3 (I : σ → List β → List τ → Prop) (f : σ → α → Option σ)
    (k : α → Option (List β)) (t : α → List τ) :
    ∀ (xs : List α) (s s' : σ) (pre : List β) (tg : List τ) (ls : List (List β)),
      (∀ x ∈ xs, ∀ s s' pre tg l, I s pre tg → k x = some l → f s x = some s' →
        I s' (pre ++ l) (tg ++ t x)) →
      I s pre tg → xs.mapM k = some ls → xs.foldlM f s = some s' →
      I s' (pre ++ ls.flatten) (tg ++ xs.flatMap t)
  | [], s, s', pre, tg, ls, _, h, e, e' => by
    have hl : ls = [] := by simpa using e.symm
    have hs : s = s' := by simpa using e'
    subst hl hs
    simpa using h
  | x :: xs, s, s', pre, tg, ls, H, h, e, e' => by
    obtain ⟨l, ls', hl, hls, rfl⟩ := mapM_cons_some e
    rw [List.foldlM_cons] at e'
    obtain ⟨s1, h1, e2⟩ := bind_some e'
    rw [List.flatten_cons, ← List.append_assoc, List.flatMap_cons, ← List.append_assoc]
    exact foldlM_step3 I f k t xs s1 s' (pre ++ l) (tg ++ t x) ls'
      (fun x' hx' => H x' (List.mem_cons_of_mem _ hx'))
      (H x List.mem_cons_self s s1 pre tg l h hl h1) hls e2

/-- Three walks in step, one level up: the first goes over a list qs, the second over the members of
seg q for each q of qs, all in one list; t q are the marks of q. -/
theorem foldl_step3' (I : σ → List β → List τ → Prop) (f : σ → γ → σ) (seg : γ → List α)
    (k : α → Option (List β)) (t : γ → List τ) :
    ∀ (qs : List γ) (s : σ) (pre : List β) (tg : List τ) (a : List (List β)),
      (∀ q ∈ qs, ∀ s pre tg ls, I s pre tg → (seg q).mapM k = some ls →
        I (f s q) (pre ++ ls.flatten) (tg ++ t q)) →
      I s pre tg → (qs.flatMap seg).mapM k = some a →
      I (qs.foldl f s) (pre ++ a.flatten) (tg ++ qs.flatMap t)
  | [], s, pre, tg, a, _, h, e => by
    have hl : a = [] := by simpa using e.symm
    subst hl
    simpa using h
  | q :: qs, s, pre, tg, a, H, h, e => by
    rw [List.flatMap_cons] at e
    obtain ⟨r1, r2, h1, h2, rfl⟩ := mapM_append_some _ _ _ e
    rw [List.foldl_cons, List.flatten_append, ← List.append_assoc, List.flatMap_cons,
      ← List.append_assoc]
    exact foldl_step3' I f seg k t qs (f s q) (pre ++ r1.flatten) (tg ++ t q) r2
      (fun q' hq' => H q' (List.mem_cons_of_mem _ hq'))
      (H q List.mem_cons_self s pre tg r1 h h1) h2

/-- The same where the first walk's steps may refuse. -/
theorem foldlM_step3' (I : σ → List β → List τ → Prop) (f : σ → γ → Option σ)
    (seg : γ → List α) (k : α → Option (List β)) (t : γ → List τ) :
    ∀ (qs : List γ) (s s' : σ) (pre : List β) (tg : List τ) (a : List (List β)),
      (∀ q ∈ qs, ∀ s s' pre tg ls, I s pre tg → (seg q).mapM k = some ls → f s q = some s' →
        I s' (pre ++ ls.flatten) (tg ++ t q)) →
      I s pre tg → (qs.flatMap seg).mapM k = some a → qs.foldlM f s = some s' →
      I s' (pre ++ a.flatten) (tg ++ qs.flatMap t)
  | [], s, s', pre, tg, a, _, h, e, e' => by
    have hl : a = [] := by simpa using e.symm
    have hs : s = s' := by simpa using e'
    subst hl hs
    simpa using h
  | q :: qs, s, s', pre, tg, a, H, h, e, e' => by
    rw [List.flatMap_cons] at e
    obtain ⟨r1, r2, h1, h2, rfl⟩ := mapM_append_some _ _ _ e
    rw [List.foldlM_cons] at e'
    obtain ⟨s1, hs1, e2⟩ := bind_some e'
    rw [List.flatten_append, ← List.append_assoc, List.flatMap_cons, ← List.append_assoc]
    exact foldlM_step3' I f seg k t qs s1 s' (pre ++ r1.flatten) (tg ++ t q) r2
      (fun q' hq' => H q' (List.mem_cons_of_mem _ hq'))
      (H q List.mem_cons_self s s1 pre tg r1 h h1 hs1) h2 e2

end Tools

/-! ## Where a panel comes from, as a mark -/

/-- The mark of a panel: the step of the verifier's walks that appends it. acc sn: panelA for the
segment sn. qk: panelT for the segment QK. routed sn lm: step lm of the inner walk of panelT for the
segment sn. form sn: panelT for a segment sn whose panel has a B side that is given as a form. -/
inductive Src
  | acc (sn : String)
  | qk
  | routed (sn : String) (lm : ℕ)
  | form (sn : String)

/-- Panel b has the mark: it is appended by that step, for a segment of that name of a call of the
walk, and, if its B side is a weight matrix, its claims stand in the list cl from its number v0 on
(AtA, AtQK, AtR in Johnson/Road/FormsKeysFold.lean). -/
def IsSrc (p : PanelEnv) (c : ClaimEnv) (TS : List ℕ) (cl : List WsClaim) (b : SBlk) : Src → Prop
  | .acc sn => ∃ v0, b.v0 = some v0 ∧ b.tri = false ∧ ∃ q ∈ callsAC p.v.y,
      ∃ g ∈ (p.v.y.calls.getD q default).segs, g.name = sn ∧ AtA p c cl b v0 q g
  | .qk => ∃ v0, b.v0 = some v0 ∧ b.tri = false ∧ ∃ q ∈ TS,
      ∃ g ∈ (p.v.y.calls.getD q default).segs, AtQK p c cl b v0 q g
  | .routed sn lm => ∃ v0, b.v0 = some v0 ∧ b.tri = true ∧ ∃ q ∈ TS,
      ∃ g ∈ (p.v.y.calls.getD q default).segs, g.name = sn ∧ AtR p c cl b v0 q g lm
  | .form sn => b.v0 = none ∧ b.tri = false ∧ ∃ q ∈ TS,
      ∃ g ∈ (p.v.y.calls.getD q default).segs, g.name = sn ∧ ∃ s s' : Panels,
        panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s' ∧ s'.bl = s.bl.push b

/-- IsSrc stays true when claims are added at the list's end. -/
theorem IsSrc.mono {p : PanelEnv} {c : ClaimEnv} {TS : List ℕ} {cl : List WsClaim} {b : SBlk}
    {t : Src} (x : List WsClaim) (h : IsSrc p c TS cl b t) : IsSrc p c TS (cl ++ x) b t := by
  cases t with
  | acc sn =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := h
    exact ⟨v0, h0, ht, q, hq, g, hg, hn, H.mono x⟩
  | qk =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, H⟩ := h
    exact ⟨v0, h0, ht, q, hq, g, hg, H.mono x⟩
  | routed sn lm =>
    obtain ⟨v0, h0, ht, q, hq, g, hg, hn, H⟩ := h
    exact ⟨v0, h0, ht, q, hq, g, hg, hn, H.mono x⟩
  | form sn => exact h

/-- The marks of the panels that panelA appends for a segment. -/
def tagsA (sn : String) : List Src := if isAcc sn then [.acc sn] else []

/-- The marks of the panels that panelT appends for a segment. p3: there are routed experts; n: the
layers with routed experts. The cases are those of the verifier's text, in its order. -/
def tagsT (p3 : Bool) (n : ℕ) (sn : String) : List Src :=
  if sn == "N1" || sn == "N2" then [.form sn]
  else if sn == "QK" then [.qk]
  else if !p3 then []
  else if sn == "XR" then [.form sn]
  else if sn == "DD" || sn == "MR" then [.form sn]
  else if sn == "G" || sn == "U" || sn == "D" then (List.range n).map (.routed sn)
  else []

/-- What the three walks keep. s: the panels so far; pre: the claims so far; tg: the marks so far.
The number of the next claim is the number of the claims so far, and the panels so far have the
marks so far, member by member. -/
def InStep3 (p : PanelEnv) (c : ClaimEnv) (TS : List ℕ) (s : Panels) (pre : List WsClaim)
    (tg : List Src) : Prop :=
  s.nextV = pre.length ∧ List.Forall₂ (IsSrc p c TS pre) s.bl.toList tg

section Steps

variable {p : PanelEnv} {c : ClaimEnv} {TS : List ℕ}

/-- The panels so far keep their marks when claims are added. -/
theorem marks_mono {l : List SBlk} {tg : List Src} {pre : List WsClaim} (x : List WsClaim)
    (h : List.Forall₂ (IsSrc p c TS pre) l tg) : List.Forall₂ (IsSrc p c TS (pre ++ x)) l tg :=
  h.imp fun _ _ k => k.mono x

/-- One segment of a call of the lookup's join keeps the three walks in step. -/
theorem stepA3 (hv : p.v = c.v) {q : ℕ} (hq : q ∈ callsAC p.v.y) {g : Seg}
    (hg : g ∈ (p.v.y.calls.getD q default).segs) {s : Panels} {pre l : List WsClaim}
    {tg : List Src} (hI : InStep3 p c TS s pre tg) (hl : c.claimsA g.name = some l) :
    InStep3 p c TS (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) (pre ++ l)
      (tg ++ tagsA g.name) := by
  obtain ⟨hn, hb⟩ := hI
  unfold tagsA
  cases ha : isAcc g.name with
  | false =>
    rw [claimsA_not c _ ha] at hl
    cases hl
    rw [panelA_not p _ _ _ s ha, List.append_nil, if_neg (by simp), List.append_nil]
    exact ⟨hn, hb⟩
  | true =>
    obtain ⟨b0, hbl, hnv, hv0, ht, hat⟩ := newA hv q hn ha hl
    rw [if_pos rfl]
    refine ⟨hnv, ?_⟩
    rw [hbl, Array.toList_push]
    exact f2_append (marks_mono l hb)
      (List.Forall₂.cons ⟨s.nextV, hv0, ht, q, hq, g, hg, rfl, hat⟩ List.Forall₂.nil)

end Steps

/-! ## One segment of a call that has terms in the second token sumcheck -/

section StepT

/-- The walk of triStep over the numbers below n, in order: it appends n panels; panel number lm is
the one that step lm appends to a state in which the number of the next claim has grown by lm. -/
theorem tri_list (p : PanelEnv) (ec : E) (el : Array E) (sn : String) :
    ∀ (n : ℕ) (s s' : Panels), (List.range n).foldlM (triStep p ec el sn) s = some s' →
      s'.nextV = s.nextV + n ∧ ∃ bs : List SBlk, s'.bl.toList = s.bl.toList ++ bs ∧
        List.Forall₂ (fun b lm => ∃ st st' : Panels, lm < n ∧ st.nextV = s.nextV + lm ∧
          triStep p ec el sn st lm = some st' ∧ st'.bl = st.bl.push b ∧ b.tri = true ∧
          b.v0 = some st.nextV) bs (List.range n)
  | 0, s, s', h => by
    have hs : s = s' := by simpa using h
    subst hs
    exact ⟨rfl, [], (List.append_nil _).symm, List.Forall₂.nil⟩
  | n + 1, s, s', h => by
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨s1, h1, h2⟩ := bind_some h
    obtain ⟨hn, bs, hbs, hall⟩ := tri_list p ec el sn n s s1 h1
    rw [List.foldlM_cons] at h2
    obtain ⟨s2, h3, h4⟩ := bind_some h2
    have hs : s2 = s' := by simpa using h4
    subst hs
    obtain ⟨b0, hbl, hnv, ht, hv0⟩ := triStep_spec h3
    refine ⟨by rw [hnv, hn, Nat.add_assoc], bs ++ [b0], ?_, ?_⟩
    · rw [hbl, Array.toList_push, hbs, List.append_assoc]
    · rw [List.range_succ]
      exact f2_append
        (hall.imp fun _ _ ⟨st, st', hlt, r⟩ => ⟨st, st', Nat.lt_succ_of_lt hlt, r⟩)
        (List.Forall₂.cons ⟨s1, s2, Nat.lt_succ_self n, hn, h3, hbl, ht, hv0⟩ List.Forall₂.nil)

/-- A name that is one of two is no third name. -/
theorem beq_of_or {sn a b x : String} (h : (sn == a || sn == b) = true) (ha : (a == x) = false)
    (hb : (b == x) = false) : (sn == x) = false := by
  rcases Bool.or_eq_true _ _ ▸ h with e | e
  · rw [beq_iff_eq.mp e]
    exact ha
  · rw [beq_iff_eq.mp e]
    exact hb

variable {p : PanelEnv} {c : ClaimEnv} {TS : List ℕ}

/-- A step of panelT that appends one panel whose B side is given as a form, and for which claimsT
gives no claim, keeps the three walks in step. -/
theorem step_form {q : ℕ} (hq : q ∈ TS) {g : Seg} (hg : g ∈ (p.v.y.calls.getD q default).segs)
    {s s' : Panels} {pre : List WsClaim} {tg : List Src} (hI : InStep3 p c TS s pre tg)
    (hs : panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s') {b : SBlk}
    (hbl : s'.bl = s.bl.push b) (hnv : s'.nextV = s.nextV) (hv0 : b.v0 = none)
    (ht : b.tri = false) : InStep3 p c TS s' (pre ++ []) (tg ++ [.form g.name]) := by
  obtain ⟨hn, hb⟩ := hI
  rw [List.append_nil]
  refine ⟨by rw [hnv, hn], ?_⟩
  rw [hbl, Array.toList_push]
  exact f2_append hb
    (List.Forall₂.cons ⟨hv0, ht, q, hq, g, hg, rfl, s, s', hs, hbl⟩ List.Forall₂.nil)

/-- One segment of a call that has terms in the second token sumcheck keeps the three walks in
step. -/
theorem stepT3 (hv : p.v = c.v) {q : ℕ} (hq : q ∈ TS) {g : Seg}
    (hg : g ∈ (p.v.y.calls.getD q default).segs) {s s' : Panels} {pre l : List WsClaim}
    {tg : List Src} (hI : InStep3 p c TS s pre tg) (hl : c.claimsT g.name = some l)
    (hs : panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s') :
    InStep3 p c TS s' (pre ++ l) (tg ++ tagsT p.v.y.h.p3 p.v.y.LamM g.name) := by
  have hs0 := hs
  unfold tagsT
  cases c1 : (g.name == "N1" || g.name == "N2") with
  | true =>
    have hQ : (g.name == "QK") = false := beq_of_or c1 rfl rfl
    have hG : (g.name == "G") = false := beq_of_or c1 rfl rfl
    have hU : (g.name == "U") = false := beq_of_or c1 rfl rfl
    have hD : (g.name == "D") = false := beq_of_or c1 rfl rfl
    rw [claimsT_other c _ (by rw [hQ]; exact Bool.false_ne_true)
      (by rw [hG, hU, hD]; simp)] at hl
    cases hl
    rw [if_pos rfl]
    simp only [panelT, c1, if_true] at hs
    obtain ⟨_, _, hs⟩ := bind_some hs
    cases hs
    exact step_form hq hg hI hs0 rfl rfl rfl rfl
  | false =>
    rw [if_neg Bool.false_ne_true]
    cases c2 : (g.name == "QK") with
    | true =>
      rw [if_pos rfl]
      obtain ⟨hn, hb⟩ := hI
      obtain ⟨b0, hbl, hnv, hv0, ht, hat⟩ := newQK hv q hn (beq_iff_eq.mp c2) hl hs
      refine ⟨hnv, ?_⟩
      rw [hbl, Array.toList_push]
      exact f2_append (marks_mono l hb)
        (List.Forall₂.cons ⟨s.nextV, hv0, ht, q, hq, g, hg, hat⟩ List.Forall₂.nil)
    | false =>
      rw [if_neg Bool.false_ne_true]
      have hQ : ¬ (g.name == "QK") = true := by rw [c2]; exact Bool.false_ne_true
      cases c3 : p.v.y.h.p3 with
      | false =>
        rw [claimsT_other c _ hQ (by rw [← hv, c3]; simp)] at hl
        cases hl
        rw [if_pos (show (!false) = true from rfl), List.append_nil, List.append_nil]
        simp only [panelT, c1, c2, c3, Bool.not_false, Bool.false_eq_true, if_true, if_false] at hs
        cases hs
        exact hI
      | true =>
        rw [if_neg (by simp)]
        cases c4 : (g.name == "XR") with
        | true =>
          have e : g.name = "XR" := beq_iff_eq.mp c4
          rw [claimsT_other c _ hQ (by rw [e]; simp)] at hl
          cases hl
          rw [if_pos rfl]
          simp only [panelT, c1, c2, c3, c4, Bool.not_true, Bool.false_eq_true, if_true,
            if_false] at hs
          obtain ⟨_, _, hs⟩ := bind_some hs
          cases hs
          exact step_form hq hg hI hs0 rfl rfl rfl rfl
        | false =>
          rw [if_neg Bool.false_ne_true]
          cases c5 : (g.name == "DD" || g.name == "MR") with
          | true =>
            have hG : (g.name == "G") = false := beq_of_or c5 rfl rfl
            have hU : (g.name == "U") = false := beq_of_or c5 rfl rfl
            have hD : (g.name == "D") = false := beq_of_or c5 rfl rfl
            rw [claimsT_other c _ hQ (by rw [hG, hU, hD]; simp)] at hl
            cases hl
            rw [if_pos rfl]
            simp only [panelT, c1, c2, c3, c4, c5, Bool.not_true, Bool.false_eq_true, if_true,
              if_false] at hs
            obtain ⟨_, _, hs⟩ := bind_some hs
            cases hs
            exact step_form hq hg hI hs0 rfl rfl rfl rfl
          | false =>
            rw [if_neg Bool.false_ne_true]
            cases c6 : (g.name == "G" || g.name == "U" || g.name == "D") with
            | true =>
              rw [if_pos rfl]
              have c6' := c6
              simp only [Bool.or_eq_true, beq_iff_eq] at c6'
              have hname : g.name = "G" ∨ g.name = "U" ∨ g.name = "D" := by
                rcases c6' with (h | h) | h
                · exact Or.inl h
                · exact Or.inr (Or.inl h)
                · exact Or.inr (Or.inr h)
              obtain ⟨hn, hb⟩ := hI
              have hlen : l.length = p.v.y.LamM := by
                rw [(claimsT_routed_at c _ (hv ▸ c3) hname hl).1, hv]
              rw [panelT_routed p _ _ _ s c3 hname] at hs
              obtain ⟨hnv, bs, hbs, hall⟩ := tri_list p _ _ _ _ s s' hs
              refine ⟨by rw [hnv, hn, List.length_append, hlen], ?_⟩
              rw [hbs]
              refine f2_append (marks_mono l hb) ?_
              rw [List.forall₂_map_right_iff]
              refine hall.imp ?_
              rintro b lm ⟨st, st', hlm, hst, hstep, hbl, ht, hv0⟩
              exact ⟨st.nextV, hv0, ht, q, hq, g, hg, rfl, st, st', l, c3, hname, hlm, rfl, hstep,
                hbl, hl, hlen, by rw [hst, hn]; exact getElem?_append_new pre l lm⟩
            | false =>
              rw [claimsT_other c _ hQ (by rw [c6]; simp)] at hl
              cases hl
              rw [if_neg Bool.false_ne_true, List.append_nil, List.append_nil]
              simp only [panelT, c1, c2, c3, c4, c5, c6, Bool.not_true, Bool.false_eq_true,
                if_false] at hs
              cases hs
              exact hI

end StepT

/-! ## The three walks, whole -/

section Walks

variable {p : PanelEnv} {c : ClaimEnv} {TS : List ℕ}

/-- panelsA, the first half of weightClaims and the marks tagsA are in step. -/
theorem walkA3 (hv : p.v = c.v) {s : Panels} {pre : List WsClaim} {tg : List Src}
    {a : List (List WsClaim)} (h : InStep3 p c TS s pre tg)
    (ha : ((callsAC p.v.y).flatMap fun q =>
      (p.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsA = some a) :
    InStep3 p c TS (panelsA p s) (pre ++ a.flatten)
      (tg ++ (callsAC p.v.y).flatMap fun q =>
        (p.v.y.calls.getD q default).segs.flatMap fun g => tagsA g.name) := by
  unfold panelsA
  refine foldl_step3' (InStep3 p c TS) _ _ _ _ _ _ _ _ _ (fun q hq s pre tg ls hI e => ?_) h ha
  rw [mapM_map_eq] at e
  exact foldl_step3 (InStep3 p c TS) _ _ _ _ _ _ _ _
    (fun g hg s pre tg l hI e => stepA3 hv hq hg hI e) hI e

/-- panelsT, the second half of weightClaims and the marks tagsT are in step. -/
theorem walkT3 (hv : p.v = c.v) {s s' : Panels} {pre : List WsClaim} {tg : List Src}
    {t : List (List WsClaim)} (h : InStep3 p c TS s pre tg)
    (ht : (TS.flatMap fun q =>
      (p.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsT = some t)
    (hp : panelsT p TS s = some s') :
    InStep3 p c TS s' (pre ++ t.flatten)
      (tg ++ TS.flatMap fun q => (p.v.y.calls.getD q default).segs.flatMap fun g =>
        tagsT p.v.y.h.p3 p.v.y.LamM g.name) := by
  unfold panelsT at hp
  refine foldlM_step3' (InStep3 p c TS) _ _ _ _ _ _ _ _ _ _
    (fun q hq s s' pre tg ls hI e e' => ?_) h ht hp
  rw [mapM_map_eq] at e
  exact foldlM_step3 (InStep3 p c TS) _ _ _ _ _ _ _ _ _
    (fun g hg s s' pre tg l hI e e' => stepT3 hv hq hg hI e e') hI e e'

end Walks

/-- The verifier's list of panels, member by member and in order, on any layout. Asked: the lists of
panels and of weight claims are made from one environment and for the same calls, and both functions
return. Then the panels have, member by member, the marks that tagsA gives for the segments of the
calls of the lookup's join, followed by those that tagsT gives for the segments of the calls TS;
each panel with its claims (IsSrc). -/
theorem panels_src (p : PanelEnv) (c : ClaimEnv) (hv : p.v = c.v) (TS : List ℕ) {pans' : Panels}
    {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) :
    List.Forall₂ (IsSrc p c TS cl) pans'.bl.toList
      (((callsAC p.v.y).flatMap fun q =>
          (p.v.y.calls.getD q default).segs.flatMap fun g => tagsA g.name) ++
        TS.flatMap fun q => (p.v.y.calls.getD q default).segs.flatMap fun g =>
          tagsT p.v.y.h.p3 p.v.y.LamM g.name) := by
  obtain ⟨a, t, ha, ht, rfl⟩ := weightClaims_some hv hc
  have h0 : InStep3 p c TS {} [] [] := ⟨rfl, List.Forall₂.nil⟩
  exact (walkT3 hv (walkA3 hv h0 ha) ht hp).2

/-! ## Against the library's list of panels -/

/-- The mark of the verifier's panel that stands for a panel of the library. -/
def srcOf : Pan → Src
  | .G => .acc "G"
  | .U => .acc "U"
  | .O => .acc "O"
  | .D => .acc "D"
  | .V => .acc "V"
  | .LR => .acc "LR"
  | .Gr l => .routed "G" l
  | .Ur l => .routed "U" l
  | .Dr l => .routed "D" l
  | .N1 => .form "N1"
  | .N2 => .form "N2"
  | .QK => .qk
  | .XR => .form "XR"
  | .DD => .form "DD"
  | .MR => .form "MR"

/-- Panel b of the verifier is the panel of the library's panel pn: it has that panel's mark. -/
def IsPanelOf (p : PanelEnv) (c : ClaimEnv) (TS : List ℕ) (cl : List WsClaim) (b : SBlk)
    (pn : Pan) : Prop :=
  IsSrc p c TS cl b (srcOf pn)

/-- The marks of a list of segments hang on the names alone. -/
theorem flatMap_names {τ : Type} (t : String → List τ) : ∀ l : List Seg,
    (l.flatMap fun g => t g.name) = (l.map (·.name)).flatMap t
  | [] => rfl
  | g :: l => by
    rw [List.flatMap_cons, List.map_cons, List.flatMap_cons, flatMap_names t l]

/-- The marks for the families of the library's call 0 in the first walk. -/
theorem tagsA_0 : ((fams 0).map segName).flatMap tagsA = [.acc "G", .acc "U"] := rfl

/-- The marks for the families of the library's call 1 in the first walk. -/
theorem tagsA_1 : ((fams 1).map segName).flatMap tagsA = [.acc "O", .acc "D", .acc "V"] := rfl

/-- The marks for the families of the library's call 2 in the first walk. -/
theorem tagsA_2 : ((fams 2).map segName).flatMap tagsA = [.acc "LR"] := rfl

/-- The marks for the families of the library's call 0 in the second walk, with routed experts. -/
theorem tagsT_0 (n : ℕ) : ((fams 0).map segName).flatMap (tagsT true n) =
    (List.range n).map (.routed "G") ++ ((List.range n).map (.routed "U") ++ []) := rfl

/-- The marks for the families of the library's call 1 in the second walk, with routed experts. -/
theorem tagsT_1 (n : ℕ) : ((fams 1).map segName).flatMap (tagsT true n) =
    .form "N1" :: .form "N2" :: ((List.range n).map (.routed "D") ++ []) := rfl

/-- The marks for the families of the library's call 2 in the second walk, with routed experts. -/
theorem tagsT_2 (n : ℕ) : ((fams 2).map segName).flatMap (tagsT true n) =
    [.qk, .form "XR", .form "DD"] := rfl

/-- The marks for the families of the library's call 5 in the second walk, with routed experts. -/
theorem tagsT_5 (n : ℕ) : ((fams 5).map segName).flatMap (tagsT true n) = [.form "MR"] := rfl

/-- The marks of the library's list of panels. -/
theorem pans_src (D : Dim) : (pans D).map srcOf =
    [.acc "G", .acc "U", .acc "O", .acc "D", .acc "V", .acc "LR"] ++
      (List.range D.ne).map (.routed "G") ++ (List.range D.ne).map (.routed "U") ++
      [.form "N1", .form "N2"] ++ (List.range D.ne).map (.routed "D") ++
      [.qk, .form "XR", .form "DD", .form "MR"] := by
  unfold pans
  simp only [List.map_append, List.map_map]
  rfl

/-- THE VERIFIER'S LIST OF PANELS IS THE LIBRARY'S, MEMBER BY MEMBER AND IN ORDER. Asked beside the
hypotheses of panels_src: there are routed experts; as many layers have them as in the library; the
calls of the first walk are the calls 0, 1, 2 and those of the second 0, 1, 2, 5; and the lines of
these four calls name the families of the library's calls of these numbers, in the library's order.
Then the verifier's list has one panel for each member of the library's list pans D, in that list's
order, and each is the panel of that member (IsPanelOf): appended by the step of the member's mark,
with its weight claims where it has any. -/
theorem panels_are_pans (p : PanelEnv) (c : ClaimEnv) (hv : p.v = c.v) {TS : List ℕ}
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) {D : Dim} (h3 : p.v.y.h.p3 = true)
    (hne : p.v.y.LamM = D.ne) (hAC : callsAC p.v.y = [0, 1, 2]) (hTS : TS = [0, 1, 2, 5])
    (n0 : (p.v.y.calls.getD 0 default).segs.map (·.name) = (fams 0).map segName)
    (n1 : (p.v.y.calls.getD 1 default).segs.map (·.name) = (fams 1).map segName)
    (n2 : (p.v.y.calls.getD 2 default).segs.map (·.name) = (fams 2).map segName)
    (n5 : (p.v.y.calls.getD 5 default).segs.map (·.name) = (fams 5).map segName) :
    List.Forall₂ (IsPanelOf p c TS cl) pans'.bl.toList (pans D) := by
  have h := panels_src p c hv TS hp hc
  have e : (((callsAC p.v.y).flatMap fun q =>
          (p.v.y.calls.getD q default).segs.flatMap fun g => tagsA g.name) ++
        TS.flatMap fun q => (p.v.y.calls.getD q default).segs.flatMap fun g =>
          tagsT p.v.y.h.p3 p.v.y.LamM g.name) = (pans D).map srcOf := by
    rw [hAC, hTS, h3, hne, pans_src]
    simp only [List.flatMap_cons, List.flatMap_nil, flatMap_names, n0, n1, n2, n5, tagsA_0,
      tagsA_1, tagsA_2, tagsT_0, tagsT_1, tagsT_2, tagsT_5, List.append_nil, List.append_assoc,
      List.cons_append, List.nil_append]
  rw [e, List.forall₂_map_right_iff] at h
  exact h

/-- A sum over the verifier's list is the sum over the library's, if the summands agree on each
panel and its member. -/
theorem sum_of_f2 {α β M : Type} [AddCommMonoid M] {R : α → β → Prop} (F : α → M) (G : β → M)
    (H : ∀ a b, R a b → F a = G b) : ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
    (l.map F).sum = (l'.map G).sum
  | _, _, .nil => rfl
  | _, _, .cons h1 h2 => by
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, H _ _ h1, sum_of_f2 F G H h2]

#print axioms stepA3
#print axioms stepT3
#print axioms panels_src
#print axioms pans_src
#print axioms panels_are_pans
#print axioms sum_of_f2

/-! ## From the eight lines of calls -/

section Lines

open OnBytes.Model (CallD)
open OnBytes.Model.Layer (Lay)

/-- The numbers of the members of a list that pass a test on an image of theirs can be found in the
list of the images. n: the number of the first member. -/
theorem filter_zipIdx {α β : Type} (f : α → β) (P : β → Bool) : ∀ (l : List α) (n : ℕ),
    ((l.zipIdx n).filter fun c => P (f c.1)).map (·.2) =
      (((l.map f).zipIdx n).filter fun c => P c.1).map (·.2)
  | [], _ => rfl
  | a :: l, n => by
    rw [List.zipIdx_cons, List.map_cons, List.zipIdx_cons, List.filter_cons, List.filter_cons]
    by_cases h : P (f a) = true
    · rw [if_pos h, if_pos h, List.map_cons, List.map_cons, filter_zipIdx f P l]
    · rw [if_neg h, if_neg h, filter_zipIdx f P l]

/-- The eight lines of calls are the library's: call number cc names the families of the library's
call cc, in the library's order, and there are no other calls. -/
def LinesAre (y : Lay) : Prop :=
  y.calls.toList.map (fun cd => cd.segs.map (·.name)) =
    (List.finRange 8).map fun cc => (fams cc).map segName

/-- With the library's lines, the calls that hold a segment with a product with a weight matrix in
the lookup's join are the calls 0, 1 and 2. -/
theorem callsAC_of_lines {y : Lay} (h : LinesAre y) : callsAC y = [0, 1, 2] := by
  unfold callsAC
  have e : (fun c : CallD × ℕ => c.1.segs.any fun s => isAcc s.name) =
      fun c => (fun ns : List String => ns.any isAcc)
        ((fun cd : CallD => cd.segs.map (·.name)) c.1) := by
    funext c
    simp only [List.any_map]
    rfl
  rw [e, filter_zipIdx (fun cd : CallD => cd.segs.map (·.name)) (fun ns => ns.any isAcc), h]
  rfl

/-- With the library's lines, the line of call number q. -/
theorem line_at {y : Lay} (h : LinesAre y) (q : Fin 8) :
    (y.calls.getD q.val default).segs.map (·.name) = (fams q).map segName := by
  have hlen : y.calls.size = 8 := by
    have := congrArg List.length h
    simpa using this
  have hq : q.val < y.calls.size := by
    rw [hlen]
    exact q.isLt
  have e := congrArg (fun l => l[q.val]?) h
  simp only [List.getElem?_map] at e
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem hq,
    List.getElem?_eq_getElem (by simp)] at e
  have e' := Option.some.inj e
  have eg : y.calls.getD q.val default = y.calls[q.val] := by simp [Array.getD, hq]
  rw [eg]
  refine e'.trans ?_
  simp only [List.getElem_finRange]
  rfl

/-- panels_are_pans from the eight lines. -/
theorem panels_of_lines (p : PanelEnv) (c : ClaimEnv) (hv : p.v = c.v) {TS : List ℕ}
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) {D : Dim} (h3 : p.v.y.h.p3 = true)
    (hne : p.v.y.LamM = D.ne) (hN : LinesAre p.v.y) (hTS : TS = [0, 1, 2, 5]) :
    List.Forall₂ (IsPanelOf p c TS cl) pans'.bl.toList (pans D) :=
  panels_are_pans p c hv hp hc h3 hne (callsAC_of_lines hN) hTS (line_at hN 0) (line_at hN 1)
    (line_at hN 2) (line_at hN 5)

end Lines

/-! ## The placed panels -/

section Placed

open OnBytes.Model.Layer (placePanels)

/-- The placed panels are the panels of the list, member by member and in order, each with another
first place. -/
theorem placed_f2 (bl : Array SBlk) :
    List.Forall₂ (fun b' b : SBlk => ∃ o, b' = { b with off := o }) (placePanels bl).1.toList
      bl.toList := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [placePanels_size bl], fun i h1 h2 => ?_⟩
  have hi' : i < bl.size := by simpa using h2
  have hi2 : i < (placePanels bl).1.size := by simpa using h1
  obtain ⟨o, ho⟩ := place_keeps bl (placeOrder bl) (bl, 0) i hi'
  rw [← placePanels_eq] at ho
  refine ⟨o, ?_⟩
  have e1 : (placePanels bl).1.toList.get ⟨i, h1⟩ = (placePanels bl).1.getD i {} := by
    simp [Array.getD, hi2]
  have e2 : bl.toList.get ⟨i, h2⟩ = bl.getD i {} := by simp [Array.getD, hi']
  rw [e1, e2, ho]

/-- Two relations, one after the other, member by member. -/
theorem f2_trans {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop} :
    ∀ {l1 : List α} {l2 : List β} {l3 : List γ}, List.Forall₂ R l1 l2 → List.Forall₂ S l2 l3 →
      List.Forall₂ (fun a c => ∃ b, R a b ∧ S b c) l1 l3
  | _, _, _, .nil, .nil => List.Forall₂.nil
  | _, _, _, .cons h1 h2, .cons k1 k2 => List.Forall₂.cons ⟨_, h1, k1⟩ (f2_trans h2 k2)

/-- The placed panels against the library's list: member by member and in order, each placed panel
is the panel of its member with some first place. Which place is not said: that it is the library's
offP is run at a made-up shape (Johnson/Road/FormsKeysRunP.lean) and shown by
no theorem. -/
theorem placed_are_pans (p : PanelEnv) (c : ClaimEnv) (hv : p.v = c.v) {TS : List ℕ}
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hc : c.weightClaims TS = some cl) {D : Dim} (h3 : p.v.y.h.p3 = true)
    (hne : p.v.y.LamM = D.ne) (hN : LinesAre p.v.y) (hTS : TS = [0, 1, 2, 5]) :
    List.Forall₂ (fun b' pn => ∃ b, (∃ o, b' = { b with off := o }) ∧ IsPanelOf p c TS cl b pn)
      (placePanels pans'.bl).1.toList (pans D) :=
  f2_trans (placed_f2 pans'.bl) (panels_of_lines p c hv hp hc h3 hne hN hTS)

end Placed

#print axioms callsAC_of_lines
#print axioms line_at
#print axioms panels_of_lines
#print axioms placed_f2
#print axioms placed_are_pans

end OnBytes.Road
