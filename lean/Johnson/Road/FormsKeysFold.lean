-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysFold.lean: the verifier's list of panels and its list of weight claims are in
step.

The check of a layer sub-proof lists the panels of its batched sumcheck (panelsA, panelsT in
OnBytes/Model/LayerPanels.lean) and, in another place, the claims on the committed matrix of weights
that these panels leave (weightClaims there). The two lists are made by two separate walks over the
same calls and segments. A panel whose B side is a weight matrix does not hold its claims. It holds
one number, v0: how many claims the panels before it have left. At the sumcheck's end the verifier
reads for row i of the panel the shown value number v0 + i (stackEndOf there). By reading of the
caller (OnBytes/Model/Layer.lean), it later settles claim number v0 + i of the other list under that
value, and it compares only the lengths of the two lists with the plan. If the walks fell out of
step, a panel would be tied to the claim of another matrix.

This file proves that the walks are in step, in the sense of its two main theorems. What is compared
with what: functions of the verifier with each other, with one exception. Where a statement speaks
of the panel of a routed product (tri_fold, AtR, FromR, and so Claimed, InStep, Cov, the steps and
the two main theorems), the verifier's function is replaced by triStep, a copy that this file makes
of a step that has no name in the verifier's text; panelT_routed shows that panelT is the walk of
that copy. No name of the library stands in a statement.

 1. What one segment adds to each list: panelA and claimsA (panelA_acc, panelA_not, claimsA_eq,
    claimsA_not); panelT and claimsT (panelT_QK_eq, panelT_routed, panelT_other, claimsT_QK_eq,
    claimsT_routed_eq, claimsT_other).
 2. What each claim of a segment is, in the words of the verifier's text (claimsA_at, with one
    corollary for each segment; claimsT_QK_at; claimsT_routed_at).
 3. The two walks, segment by segment and call by call, keep this: the number of the next claim is
    the number of the claims so far, and each panel so far that has a number v0 finds its own claims
    from v0 on (InStep; stepA, stepT). A panel that is in the list stays there, with its claims
    (Cov; keepA, keepT).
 4. The whole, in two directions: from a panel to a segment and that segment's claims
    (claims_of_panels), and from a segment to a panel and the segment's claims (panels_of_segments).

Three predicates of this file say that a panel b is the panel of a segment g of a call q and which
claims are its own: AtA, AtQK, AtR. Each says of b "the verifier's function, run as the walk runs it
for q and g on a state in which the number of the next claim is v0, appends b": for example
(panelA p ec el sn s).bl = s.bl.push b. A statement on what panelA appends to any state can so be
carried over to b. FromA, FromQK, FromR say the same of some call and segment of the walk.

A panel is a record without a name. Where the verifier's function gives the same record for two
segments, from states with the same number of the next claim, "b is the panel of g" is true of both.
So claims_of_panels alone does not tell such segments apart; panels_of_segments says that each of
them has a panel with its own claims.

That the hypotheses of the two main theorems can be met together is shown by runs, not by a theorem:
Johnson/Road/FormsKeysRun.lean evaluates both lists in both groups of a made-up shape, with one
environment for both, and both return (18 panels, 32 claims). Johnson/Road/FormsKeysRunW.lean does
so at two made-up shapes and compares each panel's v0 and each claim's unit with a list that it
expects (w5 there).

Main definitions: triStep; AtA, AtQK, AtR; FromA, FromQK, FromR, Claimed, InStep, Cov.
Main theorems: claims_of_panels, panels_of_segments; claimsA_at, claimsT_QK_at, claimsT_routed_at;
panelT_routed.

What is not claimed. Every theorem begins "if the function returns a value": none says that it does.
Nothing is said on what a claim's factors weigh or on how a claim is settled; on a panel without a
number v0; on the embedding's claim, which follows these claims in the caller's list; on whether the
caller reads the shown values and the claims by the same numbers. Not stated: that every claim
belongs to some panel; that two places of the walks have two panels (where a segment stands twice in
a walk, panels_of_segments speaks of one of its panels); the order of the panels in the list. See
also Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysEnd

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (eqTab WsGrp WsFac WsClaim Seg)
open OnBytes.Model.Layer (SBlk Panels PanelEnv ClaimEnv plain tri isAcc callsAC kT kTM Lkd Lkq
  panelA panelT panelsA panelsT)

/-! ## Tools: lists -/

section Tools

variable {α β γ σ : Type}

/-- If a function that may refuse is run over a list with a first member and nothing is refused, the
result is the first member's result before the results of the others. -/
theorem mapM_cons_some {f : α → Option β} {x : α} {xs : List α} {r : List β}
    (h : (x :: xs).mapM f = some r) :
    ∃ y ys, f x = some y ∧ xs.mapM f = some ys ∧ r = y :: ys := by
  rw [List.mapM_cons] at h
  obtain ⟨y, hy, h⟩ := bind_some h
  obtain ⟨ys, hys, h⟩ := bind_some h
  cases h
  exact ⟨y, ys, hy, hys, rfl⟩

/-- The same over two lists, one after the other. -/
theorem mapM_append_some {f : α → Option β} : ∀ (l1 l2 : List α) (r : List β),
    (l1 ++ l2).mapM f = some r →
      ∃ r1 r2, l1.mapM f = some r1 ∧ l2.mapM f = some r2 ∧ r = r1 ++ r2
  | [], _, r, h => ⟨[], r, by simp, h, rfl⟩
  | x :: l1, l2, r, h => by
    obtain ⟨y, ys, hy, hys, rfl⟩ := mapM_cons_some (xs := l1 ++ l2) h
    obtain ⟨r1, r2, h1, h2, rfl⟩ := mapM_append_some l1 l2 ys hys
    refine ⟨y :: r1, r2, ?_, h2, rfl⟩
    rw [List.mapM_cons, hy, h1]
    rfl

/-- To run k over the images under n is to run "n, then k" over the list. -/
theorem mapM_map_eq (n : α → γ) (k : γ → Option β) : ∀ xs : List α,
    (xs.map n).mapM k = xs.mapM fun x => k (n x)
  | [] => by simp
  | x :: xs => by rw [List.map_cons, List.mapM_cons, List.mapM_cons, mapM_map_eq n k xs]

/-- A member that stands in a list still stands at its number when the list is made longer. l[i] is
there to say that the member exists. -/
theorem getElem?_append_keep {cl x l : List α} {a i : ℕ} (hi : i < l.length)
    (h : cl[a]? = l[i]?) : (cl ++ x)[a]? = l[i]? := by
  have ha : a < cl.length := by
    by_contra hn
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn), List.getElem?_eq_getElem hi] at h
    cases h
  rw [List.getElem?_append_left ha, h]

/-- Member i of the second of two joined lists has the number "length of the first, plus i". -/
theorem getElem?_append_new (pre l : List α) (i : ℕ) : (pre ++ l)[pre.length + i]? = l[i]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- Two walks over one list in step. One walk changes a state, the other gives a list for each
member. If each step keeps a relation between the state and the lists so far, joined, then the whole
walks keep it. -/
theorem foldl_step (I : σ → List β → Prop) (f : σ → α → σ) (k : α → Option (List β)) :
    ∀ (xs : List α) (s : σ) (pre : List β) (ls : List (List β)),
      (∀ x ∈ xs, ∀ s pre l, I s pre → k x = some l → I (f s x) (pre ++ l)) →
      I s pre → xs.mapM k = some ls → I (xs.foldl f s) (pre ++ ls.flatten)
  | [], s, pre, ls, _, h, e => by
    have hl : ls = [] := by simpa using e.symm
    subst hl
    simpa using h
  | x :: xs, s, pre, ls, H, h, e => by
    obtain ⟨l, ls', hl, hls, rfl⟩ := mapM_cons_some e
    rw [List.foldl_cons, List.flatten_cons, ← List.append_assoc]
    exact foldl_step I f k xs (f s x) (pre ++ l) ls'
      (fun x' hx' => H x' (List.mem_cons_of_mem _ hx')) (H x List.mem_cons_self s pre l h hl) hls

/-- The same where the first walk's steps may refuse. -/
theorem foldlM_step (I : σ → List β → Prop) (f : σ → α → Option σ) (k : α → Option (List β)) :
    ∀ (xs : List α) (s s' : σ) (pre : List β) (ls : List (List β)),
      (∀ x ∈ xs, ∀ s s' pre l, I s pre → k x = some l → f s x = some s' → I s' (pre ++ l)) →
      I s pre → xs.mapM k = some ls → xs.foldlM f s = some s' → I s' (pre ++ ls.flatten)
  | [], s, s', pre, ls, _, h, e, e' => by
    have hl : ls = [] := by simpa using e.symm
    have hs : s = s' := by simpa using e'
    subst hl hs
    simpa using h
  | x :: xs, s, s', pre, ls, H, h, e, e' => by
    obtain ⟨l, ls', hl, hls, rfl⟩ := mapM_cons_some e
    rw [List.foldlM_cons] at e'
    obtain ⟨s1, h1, e2⟩ := bind_some e'
    rw [List.flatten_cons, ← List.append_assoc]
    exact foldlM_step I f k xs s1 s' (pre ++ l) ls'
      (fun x' hx' => H x' (List.mem_cons_of_mem _ hx'))
      (H x List.mem_cons_self s s1 pre l h hl h1) hls e2

/-- Two walks in step, one level up. The first walk goes over a list qs. The second goes over the
members of seg q for each q of qs, all in one list. -/
theorem foldl_step2 (I : σ → List β → Prop) (f : σ → γ → σ) (seg : γ → List α)
    (k : α → Option (List β)) :
    ∀ (qs : List γ) (s : σ) (pre : List β) (a : List (List β)),
      (∀ q ∈ qs, ∀ s pre ls, I s pre → (seg q).mapM k = some ls → I (f s q) (pre ++ ls.flatten)) →
      I s pre → (qs.flatMap seg).mapM k = some a → I (qs.foldl f s) (pre ++ a.flatten)
  | [], s, pre, a, _, h, e => by
    have hl : a = [] := by simpa using e.symm
    subst hl
    simpa using h
  | q :: qs, s, pre, a, H, h, e => by
    rw [List.flatMap_cons] at e
    obtain ⟨r1, r2, h1, h2, rfl⟩ := mapM_append_some _ _ _ e
    rw [List.foldl_cons, List.flatten_append, ← List.append_assoc]
    exact foldl_step2 I f seg k qs (f s q) (pre ++ r1.flatten) r2
      (fun q' hq' => H q' (List.mem_cons_of_mem _ hq')) (H q List.mem_cons_self s pre r1 h h1) h2

/-- The same where the first walk's steps may refuse. -/
theorem foldlM_step2 (I : σ → List β → Prop) (f : σ → γ → Option σ) (seg : γ → List α)
    (k : α → Option (List β)) :
    ∀ (qs : List γ) (s s' : σ) (pre : List β) (a : List (List β)),
      (∀ q ∈ qs, ∀ s s' pre ls, I s pre → (seg q).mapM k = some ls → f s q = some s' →
        I s' (pre ++ ls.flatten)) →
      I s pre → (qs.flatMap seg).mapM k = some a → qs.foldlM f s = some s' →
      I s' (pre ++ a.flatten)
  | [], s, s', pre, a, _, h, e, e' => by
    have hl : a = [] := by simpa using e.symm
    have hs : s = s' := by simpa using e'
    subst hl hs
    simpa using h
  | q :: qs, s, s', pre, a, H, h, e, e' => by
    rw [List.flatMap_cons] at e
    obtain ⟨r1, r2, h1, h2, rfl⟩ := mapM_append_some _ _ _ e
    rw [List.foldlM_cons] at e'
    obtain ⟨s1, hs1, e2⟩ := bind_some e'
    rw [List.flatten_append, ← List.append_assoc]
    exact foldlM_step2 I f seg k qs s1 s' (pre ++ r1.flatten) r2
      (fun q' hq' => H q' (List.mem_cons_of_mem _ hq'))
      (H q List.mem_cons_self s s1 pre r1 h h1 hs1) h2 e2

/-- Two walks over one list in step, with a member x0 of the list in view. Each step keeps a
relation I and keeps a relation J, and the step of x0 leads from I to J. Then the whole walks lead
from I to J. -/
theorem foldl_reach (I J : σ → List β → Prop) (f : σ → α → σ) (k : α → Option (List β)) (x0 : α)
    (hit : ∀ s pre l, I s pre → k x0 = some l → J (f s x0) (pre ++ l)) :
    ∀ (xs : List α) (s : σ) (pre : List β) (ls : List (List β)), x0 ∈ xs →
      (∀ x ∈ xs, ∀ s pre l, I s pre → k x = some l → I (f s x) (pre ++ l)) →
      (∀ x ∈ xs, ∀ s pre l, J s pre → k x = some l → J (f s x) (pre ++ l)) →
      I s pre → xs.mapM k = some ls → J (xs.foldl f s) (pre ++ ls.flatten)
  | [], _, _, _, hx, _, _, _, _ => absurd hx List.not_mem_nil
  | x :: xs, s, pre, ls, hx, HI, HJ, h, e => by
    obtain ⟨l, ls', hl, hls, rfl⟩ := mapM_cons_some e
    rw [List.foldl_cons, List.flatten_cons, ← List.append_assoc]
    rcases List.mem_cons.mp hx with hx' | hx'
    · subst hx'
      exact foldl_step J f k xs _ _ ls' (fun x' h' => HJ x' (List.mem_cons_of_mem _ h'))
        (hit s pre l h hl) hls
    · exact foldl_reach I J f k x0 hit xs _ _ ls' hx'
        (fun x' h' => HI x' (List.mem_cons_of_mem _ h'))
        (fun x' h' => HJ x' (List.mem_cons_of_mem _ h')) (HI x List.mem_cons_self s pre l h hl) hls

/-- The same where the first walk's steps may refuse. -/
theorem foldlM_reach (I J : σ → List β → Prop) (f : σ → α → Option σ) (k : α → Option (List β))
    (x0 : α)
    (hit : ∀ s s' pre l, I s pre → k x0 = some l → f s x0 = some s' → J s' (pre ++ l)) :
    ∀ (xs : List α) (s s' : σ) (pre : List β) (ls : List (List β)), x0 ∈ xs →
      (∀ x ∈ xs, ∀ s s' pre l, I s pre → k x = some l → f s x = some s' → I s' (pre ++ l)) →
      (∀ x ∈ xs, ∀ s s' pre l, J s pre → k x = some l → f s x = some s' → J s' (pre ++ l)) →
      I s pre → xs.mapM k = some ls → xs.foldlM f s = some s' → J s' (pre ++ ls.flatten)
  | [], _, _, _, _, hx, _, _, _, _, _ => absurd hx List.not_mem_nil
  | x :: xs, s, s', pre, ls, hx, HI, HJ, h, e, e' => by
    obtain ⟨l, ls', hl, hls, rfl⟩ := mapM_cons_some e
    rw [List.foldlM_cons] at e'
    obtain ⟨s1, h1, e2⟩ := bind_some e'
    rw [List.flatten_cons, ← List.append_assoc]
    rcases List.mem_cons.mp hx with hx' | hx'
    · subst hx'
      exact foldlM_step J f k xs s1 s' _ ls' (fun x' h' => HJ x' (List.mem_cons_of_mem _ h'))
        (hit s s1 pre l h hl h1) hls e2
    · exact foldlM_reach I J f k x0 hit xs s1 s' _ ls' hx'
        (fun x' h' => HI x' (List.mem_cons_of_mem _ h'))
        (fun x' h' => HJ x' (List.mem_cons_of_mem _ h'))
        (HI x List.mem_cons_self s s1 pre l h hl h1) hls e2

/-- The same as foldl_reach, one level up: the first walk goes over qs, the second over the members
of seg q for each q of qs. -/
theorem foldl_reach2 (I J : σ → List β → Prop) (f : σ → γ → σ) (seg : γ → List α)
    (k : α → Option (List β)) (q0 : γ)
    (hit : ∀ s pre ls, I s pre → (seg q0).mapM k = some ls → J (f s q0) (pre ++ ls.flatten)) :
    ∀ (qs : List γ) (s : σ) (pre : List β) (a : List (List β)), q0 ∈ qs →
      (∀ q ∈ qs, ∀ s pre ls, I s pre → (seg q).mapM k = some ls → I (f s q) (pre ++ ls.flatten)) →
      (∀ q ∈ qs, ∀ s pre ls, J s pre → (seg q).mapM k = some ls → J (f s q) (pre ++ ls.flatten)) →
      I s pre → (qs.flatMap seg).mapM k = some a → J (qs.foldl f s) (pre ++ a.flatten)
  | [], _, _, _, hx, _, _, _, _ => absurd hx List.not_mem_nil
  | q :: qs, s, pre, a, hx, HI, HJ, h, e => by
    rw [List.flatMap_cons] at e
    obtain ⟨r1, r2, h1, h2, rfl⟩ := mapM_append_some _ _ _ e
    rw [List.foldl_cons, List.flatten_append, ← List.append_assoc]
    rcases List.mem_cons.mp hx with hx' | hx'
    · subst hx'
      exact foldl_step2 J f seg k qs _ _ r2 (fun q' h' => HJ q' (List.mem_cons_of_mem _ h'))
        (hit s pre r1 h h1) h2
    · exact foldl_reach2 I J f seg k q0 hit qs _ _ r2 hx'
        (fun q' h' => HI q' (List.mem_cons_of_mem _ h'))
        (fun q' h' => HJ q' (List.mem_cons_of_mem _ h')) (HI q List.mem_cons_self s pre r1 h h1) h2

/-- The same where the first walk's steps may refuse. -/
theorem foldlM_reach2 (I J : σ → List β → Prop) (f : σ → γ → Option σ) (seg : γ → List α)
    (k : α → Option (List β)) (q0 : γ)
    (hit : ∀ s s' pre ls, I s pre → (seg q0).mapM k = some ls → f s q0 = some s' →
      J s' (pre ++ ls.flatten)) :
    ∀ (qs : List γ) (s s' : σ) (pre : List β) (a : List (List β)), q0 ∈ qs →
      (∀ q ∈ qs, ∀ s s' pre ls, I s pre → (seg q).mapM k = some ls → f s q = some s' →
        I s' (pre ++ ls.flatten)) →
      (∀ q ∈ qs, ∀ s s' pre ls, J s pre → (seg q).mapM k = some ls → f s q = some s' →
        J s' (pre ++ ls.flatten)) →
      I s pre → (qs.flatMap seg).mapM k = some a → qs.foldlM f s = some s' →
      J s' (pre ++ a.flatten)
  | [], _, _, _, _, hx, _, _, _, _, _ => absurd hx List.not_mem_nil
  | q :: qs, s, s', pre, a, hx, HI, HJ, h, e, e' => by
    rw [List.flatMap_cons] at e
    obtain ⟨r1, r2, h1, h2, rfl⟩ := mapM_append_some _ _ _ e
    rw [List.foldlM_cons] at e'
    obtain ⟨s1, hs1, e2⟩ := bind_some e'
    rw [List.flatten_append, ← List.append_assoc]
    rcases List.mem_cons.mp hx with hx' | hx'
    · subst hx'
      exact foldlM_step2 J f seg k qs s1 s' _ r2 (fun q' h' => HJ q' (List.mem_cons_of_mem _ h'))
        (hit s s1 pre r1 h h1 hs1) h2 e2
    · exact foldlM_reach2 I J f seg k q0 hit qs s1 s' _ r2 hx'
        (fun q' h' => HI q' (List.mem_cons_of_mem _ h'))
        (fun q' h' => HJ q' (List.mem_cons_of_mem _ h'))
        (HI q List.mem_cons_self s s1 pre r1 h h1 hs1) h2 e2

/-- What is appended to an array is a member of the result. -/
theorem mem_push_self (a : Array α) (b : α) : b ∈ (a.push b).toList := by simp

/-- A member of an array is a member of the array with one more appended. -/
theorem mem_push_of_mem {a : Array α} {x : α} (b : α) (h : x ∈ a.toList) :
    x ∈ (a.push b).toList := by
  rw [Array.toList_push]
  exact List.mem_append_left _ h

/-- If "not a" is false and b is true, then "a and b" is true. -/
theorem and_of_not {a b : Bool} (h : ¬ (!a) = true) (hb : b = true) : (a && b) = true := by
  cases a
  · exact absurd rfl h
  · exact hb

end Tools

/-! ## One segment of a call of the lookup's join -/

/-- The six segments for which isAcc is true. -/
theorem isAcc_iff (sn : String) : isAcc sn = true ↔
    sn = "G" ∨ sn = "U" ∨ sn = "V" ∨ sn = "O" ∨ sn = "D" ∨ sn = "LR" := by
  simp [isAcc]

/-- For each of the six segments panelA appends one panel. It has no selector, its number v0 is the
number of the next claim, and the number of the next claim grows by the panel's rows: the layers
with routed experts for LR, all layers of the group for the others. -/
theorem panelA_acc (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (h : isAcc sn = true) :
    ∃ b : SBlk, (panelA p ec el sn s).bl = s.bl.push b ∧
      (panelA p ec el sn s).nextV = s.nextV + b.ni ∧ b.tri = false ∧ b.v0 = some s.nextV ∧
      b.ni = if sn == "LR" then p.v.y.LamM else p.v.y.Lam := by
  rcases (isAcc_iff sn).mp h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- For every other segment panelA changes nothing. -/
theorem panelA_not (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (h : isAcc sn = false) : panelA p ec el sn s = s := by
  have hn : ¬ (sn = "G" ∨ sn = "U" ∨ sn = "V" ∨ sn = "O" ∨ sn = "D" ∨ sn = "LR") := fun h' => by
    rw [(isAcc_iff sn).mpr h'] at h
    cases h
  simp only [not_or] at hn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hn
  simp [panelA, h1, h2, h3, h4, h5, h6]

/-- For each of the six segments claimsA runs over the rows of the segment's panel. The right side
is the verifier's text with its local names written out. -/
theorem claimsA_eq (c : ClaimEnv) (sn : String) (h : isAcc sn = true) :
    c.claimsA sn = (List.range (if sn == "LR" then c.v.y.LamM else c.v.y.Lam)).mapM fun i =>
      c.claim
        (if sn == "G" then (if c.v.isMoe (if sn == "LR" then 2 * i + 1 else i) then 5 else 3)
          else if sn == "U" then (if c.v.isMoe (if sn == "LR" then 2 * i + 1 else i) then 6 else 4)
          else if sn == "V" then 1 else if sn == "O" then 2 else if sn == "D" then 9 else 11)
        (if sn == "LR" then 2 * i + 1 else i)
        fun G => if G.name == "kk" then
            c.facRs G 0 (ceilLog2
              (if sn == "O" then c.v.y.dq else if sn == "D" then c.v.y.h.f else c.v.y.h.d))
          else c.facEw G sn 0 := by
  unfold ClaimEnv.claimsA
  rw [h]
  rfl

/-- For every other segment claimsA gives no claim. -/
theorem claimsA_not (c : ClaimEnv) (sn : String) (h : isAcc sn = false) :
    c.claimsA sn = some [] := by
  unfold ClaimEnv.claimsA
  rw [h]
  rfl

/-- The claims of one of the six segments are as many as the rows of its panel. -/
theorem claimsA_length (c : ClaimEnv) (sn : String) {l : List WsClaim}
    (h : c.claimsA sn = some l) (ha : isAcc sn = true) :
    l.length = if sn == "LR" then c.v.y.LamM else c.v.y.Lam := by
  rw [claimsA_eq c sn ha] at h
  rw [(list_mapM_some _ _ _ h).1, List.length_range]

/-- Claim number i of one of the six segments, in the words of the verifier's text: the kind of the
unit, the layer of the group, and the factor for each index group of the unit. -/
theorem claimsA_at (c : ClaimEnv) (sn : String) {l : List WsClaim} (h : c.claimsA sn = some l)
    (ha : isAcc sn = true) (i : ℕ) (hi : i < l.length) :
    l[i]? = c.claim
      (if sn == "G" then (if c.v.isMoe (if sn == "LR" then 2 * i + 1 else i) then 5 else 3)
        else if sn == "U" then (if c.v.isMoe (if sn == "LR" then 2 * i + 1 else i) then 6 else 4)
        else if sn == "V" then 1 else if sn == "O" then 2 else if sn == "D" then 9 else 11)
      (if sn == "LR" then 2 * i + 1 else i)
      fun G => if G.name == "kk" then
          c.facRs G 0
            (ceilLog2 (if sn == "O" then c.v.y.dq else if sn == "D" then c.v.y.h.f else c.v.y.h.d))
        else c.facEw G sn 0 := by
  rw [claimsA_eq c sn ha] at h
  obtain ⟨hl, hat⟩ := list_mapM_some _ _ _ h
  rw [List.length_range] at hl
  obtain ⟨b, hb, hF⟩ := hat i i (List.getElem?_range (hl ▸ hi))
  exact hb.trans hF.symm

/-- Claim number i of segment G: on the unit of layer i of the group that has kind 5 if isMoe is
true of the layer, and kind 3 if not. -/
theorem claimsA_at_G (c : ClaimEnv) {l : List WsClaim} (h : c.claimsA "G" = some l) (i : ℕ)
    (hi : i < l.length) :
    l[i]? = c.claim (if c.v.isMoe i then 5 else 3) i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "G" 0 :=
  claimsA_at c "G" h rfl i hi

/-- Claim number i of segment U: on the unit of layer i of the group that has kind 6 if isMoe is
true of the layer, and kind 4 if not. -/
theorem claimsA_at_U (c : ClaimEnv) {l : List WsClaim} (h : c.claimsA "U" = some l) (i : ℕ)
    (hi : i < l.length) :
    l[i]? = c.claim (if c.v.isMoe i then 6 else 4) i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "U" 0 :=
  claimsA_at c "U" h rfl i hi

/-- Claim number i of segment V: on the unit of kind 1 of layer i of the group. -/
theorem claimsA_at_V (c : ClaimEnv) {l : List WsClaim} (h : c.claimsA "V" = some l) (i : ℕ)
    (hi : i < l.length) :
    l[i]? = c.claim 1 i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "V" 0 :=
  claimsA_at c "V" h rfl i hi

/-- Claim number i of segment O: on the unit of kind 2 of layer i of the group. -/
theorem claimsA_at_O (c : ClaimEnv) {l : List WsClaim} (h : c.claimsA "O" = some l) (i : ℕ)
    (hi : i < l.length) :
    l[i]? = c.claim 2 i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.dq) else c.facEw G "O" 0 :=
  claimsA_at c "O" h rfl i hi

/-- Claim number i of segment D: on the unit of kind 9 of layer i of the group. -/
theorem claimsA_at_D (c : ClaimEnv) {l : List WsClaim} (h : c.claimsA "D" = some l) (i : ℕ)
    (hi : i < l.length) :
    l[i]? = c.claim 9 i fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.f) else c.facEw G "D" 0 :=
  claimsA_at c "D" h rfl i hi

/-- Claim number i of segment LR: on the unit of kind 11 of layer 2 i + 1 of the group. -/
theorem claimsA_at_LR (c : ClaimEnv) {l : List WsClaim} (h : c.claimsA "LR" = some l) (i : ℕ)
    (hi : i < l.length) :
    l[i]? = c.claim 11 (2 * i + 1) fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "LR" 0 :=
  claimsA_at c "LR" h rfl i hi

/-! ## One segment of a call that has terms in the second token sumcheck -/

/-- A panel that plain appends with a B side given as a form has no number v0, and the number of the
next claim stays. -/
theorem plain_form (y : Model.Layer.Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A : Option (ℕ → ℕ → Option Model.Aff)) (B : ℕ → ℕ → Option Model.Aff) (wt : ℕ → E)
    (virt : Option ℕ) (s : Panels) :
    (plain y ec claim moeSet ny A (some B) wt virt s).nextV = s.nextV ∧
      ∀ b ∈ (plain y ec claim moeSet ny A (some B) wt virt s).bl.toList,
        b ∈ s.bl.toList ∨ b.v0 = none := by
  refine ⟨rfl, fun b hb => ?_⟩
  unfold plain at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact Or.inl hb
  · exact Or.inr rfl

/-- What panelT appends for the segment QK. -/
theorem panelT_QK_eq (p : PanelEnv) (ec : E) (el : Array E) (s : Panels) :
    panelT p ec el "QK" s = some (plain p.v.y ec 1 false p.v.y.h.d
      (some fun lam k2 => p.v.shIn (p.v.tensorAt "a" "rt") lam k2) none
      (fun lam => mulE (el.getD lam zeroE) (kT p.v.sc (p.v.lay lam) Lkq)) none s) := rfl

/-- For the segment QK panelT appends one panel. It has no selector, its number v0 is the number of
the next claim, and the number of the next claim grows by the panel's rows, the group's layers. -/
theorem panelT_QK (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (hs : sn = "QK") (h : panelT p ec el sn s = some s') :
    ∃ b : SBlk, s'.bl = s.bl.push b ∧ s'.nextV = s.nextV + b.ni ∧ b.tri = false ∧
      b.v0 = some s.nextV ∧ b.ni = p.v.y.Lam := by
  subst hs
  rw [panelT_QK_eq] at h
  cases h
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- One step of the inner walk of panelT for a routed product (segment G, U or D, with routed
experts): the panel of the routed experts of layer 2 lm + 1 of the group. This is a copy of the
verifier's text, where the step has no name; panelT_routed ties the two. -/
def triStep (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels) (lm : ℕ) :
    Option Panels := do
  let v := p.v
  let y := v.y
  let h := y.h
  let lam := 2 * lm + 1
  let sl := (Array.range h.NE).map fun e =>
    p.shownT.getD (y.NN * y.Lam + y.LamM + lm * h.NE + e) zeroE
  if sn == "D" then
    pure (tri y ec 1 h.fe sl #[] (some (1 + lm))
      (mulE (el.getD lam zeroE) (kT v.sc (v.lay lam) Lkd)) s)
  else
    let xr := v.tensorAt "xr" "rt"
    let xx ← (Array.range h.d).mapM fun k2 => v.shIn xr lm k2
    pure (tri y ec 1 h.d sl xx none
      (mulE (el.getD lam zeroE) (kTM v.sc (v.lay lam) (if sn == "U" then 2 else 1))) s)

/-- With routed experts, for the segments G, U and D, panelT is the walk of triStep over the layers
with routed experts. -/
theorem panelT_routed (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (h3 : p.v.y.h.p3 = true) (hs : sn = "G" ∨ sn = "U" ∨ sn = "D") :
    panelT p ec el sn s = (List.range p.v.y.LamM).foldlM (triStep p ec el sn) s := by
  rcases hs with rfl | rfl | rfl
  · have e : panelT p ec el "G" s = (if !p.v.y.h.p3 then pure s
        else (List.range p.v.y.LamM).foldlM (triStep p ec el "G") s) := rfl
    rw [e, h3]
    rfl
  · have e : panelT p ec el "U" s = (if !p.v.y.h.p3 then pure s
        else (List.range p.v.y.LamM).foldlM (triStep p ec el "U") s) := rfl
    rw [e, h3]
    rfl
  · have e : panelT p ec el "D" s = (if !p.v.y.h.p3 then pure s
        else (List.range p.v.y.LamM).foldlM (triStep p ec el "D") s) := rfl
    rw [e, h3]
    rfl

/-- A step of that walk appends one panel. It has the selector, its number v0 is the number of the
next claim, and the number of the next claim grows by one. -/
theorem triStep_spec {p : PanelEnv} {ec : E} {el : Array E} {sn : String} {s s' : Panels} {lm : ℕ}
    (h : triStep p ec el sn s lm = some s') :
    ∃ b : SBlk, s'.bl = s.bl.push b ∧ s'.nextV = s.nextV + 1 ∧ b.tri = true ∧
      b.v0 = some s.nextV := by
  simp only [triStep] at h
  split_ifs at h <;> first
    | (cases h; exact ⟨_, rfl, rfl, rfl, rfl⟩)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h; exact ⟨_, rfl, rfl, rfl, rfl⟩)

/-- The walk of triStep over the numbers below n. The number of the next claim grows by n. Each new
panel is the one that step lm appends, for some lm below n, to a state in which the number of the
next claim has grown by lm. The panels that were there stay. For each lm below n there is such a new
panel. -/
theorem tri_fold (p : PanelEnv) (ec : E) (el : Array E) (sn : String) :
    ∀ (n : ℕ) (s s' : Panels), (List.range n).foldlM (triStep p ec el sn) s = some s' →
      s'.nextV = s.nextV + n ∧
      (∀ b ∈ s'.bl.toList, b ∈ s.bl.toList ∨
        ∃ (lm : ℕ) (st st' : Panels), lm < n ∧ st.nextV = s.nextV + lm ∧
          triStep p ec el sn st lm = some st' ∧ st'.bl = st.bl.push b ∧ b.tri = true ∧
          b.v0 = some st.nextV) ∧
      (∀ b ∈ s.bl.toList, b ∈ s'.bl.toList) ∧
      ∀ lm, lm < n → ∃ b ∈ s'.bl.toList, ∃ (st st' : Panels), st.nextV = s.nextV + lm ∧
        triStep p ec el sn st lm = some st' ∧ st'.bl = st.bl.push b ∧ b.tri = true ∧
        b.v0 = some st.nextV
  | 0, s, s', h => by
    have hs : s = s' := by simpa using h
    subst hs
    exact ⟨rfl, fun b hb => Or.inl hb, fun b hb => hb, fun lm hlm => absurd hlm (Nat.not_lt_zero _)⟩
  | n + 1, s, s', h => by
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨s1, h1, h2⟩ := bind_some h
    obtain ⟨hn, hb, hg, hc⟩ := tri_fold p ec el sn n s s1 h1
    rw [List.foldlM_cons] at h2
    obtain ⟨s2, h3, h4⟩ := bind_some h2
    have hs : s2 = s' := by simpa using h4
    subst hs
    obtain ⟨b0, hbl, hnv, ht, hv0⟩ := triStep_spec h3
    refine ⟨by rw [hnv, hn, Nat.add_assoc], fun b hb' => ?_, fun b hb' => ?_, fun lm hlm => ?_⟩
    · rw [hbl, Array.toList_push, List.mem_append, List.mem_singleton] at hb'
      rcases hb' with hb' | rfl
      · rcases hb b hb' with h | ⟨lm, st, st', hlt, r⟩
        · exact Or.inl h
        · exact Or.inr ⟨lm, st, st', Nat.lt_succ_of_lt hlt, r⟩
      · exact Or.inr ⟨n, s1, s2, Nat.lt_succ_self n, hn, h3, hbl, ht, hv0⟩
    · rw [hbl]
      exact mem_push_of_mem b0 (hg b hb')
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hlm with hlt | rfl
      · obtain ⟨b, hb', r⟩ := hc lm hlt
        exact ⟨b, by rw [hbl]; exact mem_push_of_mem b0 hb', r⟩
      · exact ⟨b0, by rw [hbl]; exact mem_push_self _ _, s1, s2, hn, h3, hbl, ht, hv0⟩

/-- For every other segment, and for G, U, D without routed experts, panelT leaves the number of the
next claim as it is, and a panel that it appends has no number v0. -/
theorem panelT_other (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (hQ : ¬ (sn == "QK") = true)
    (hR : ¬ (p.v.y.h.p3 && (sn == "G" || sn == "U" || sn == "D")) = true)
    (h : panelT p ec el sn s = some s') :
    s'.nextV = s.nextV ∧ ∀ b ∈ s'.bl.toList, b ∈ s.bl.toList ∨ b.v0 = none := by
  simp only [panelT] at h
  split_ifs at h <;> first
    | exact absurd ‹(sn == "QK") = true› hQ
    | exact absurd (and_of_not ‹¬ (!p.v.y.h.p3) = true›
        ‹(sn == "G" || sn == "U" || sn == "D") = true›) hR
    | (cases h; exact ⟨rfl, fun b hb => Or.inl hb⟩)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h; exact plain_form _ _ _ _ _ _ _ _ _ _)

/-- plain keeps the panels that were there. -/
theorem plain_grows (y : Model.Layer.Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Model.Aff)) (wt : ℕ → E) (virt : Option ℕ) (s : Panels) :
    ∀ b ∈ s.bl.toList, b ∈ (plain y ec claim moeSet ny A B wt virt s).bl.toList :=
  fun _ hb => mem_push_of_mem _ hb

/-- tri keeps the panels that were there. -/
theorem tri_grows (y : Model.Layer.Lay) (ec : E) (claim nk : ℕ) (sl : Array E)
    (xx : Array Model.Aff) (virt : Option ℕ) (wt : E) (s : Panels) :
    ∀ b ∈ s.bl.toList, b ∈ (tri y ec claim nk sl xx virt wt s).bl.toList :=
  fun _ hb => mem_push_of_mem _ hb

/-- panelA keeps the panels that were there. -/
theorem growA (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels) :
    ∀ b ∈ s.bl.toList, b ∈ (panelA p ec el sn s).bl.toList := by
  simp only [panelA]
  split_ifs <;> first
    | exact fun _ hb => hb
    | exact plain_grows _ _ _ _ _ _ _ _ _ _

/-- panelT keeps the panels that were there. -/
theorem growT (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (h : panelT p ec el sn s = some s') : ∀ b ∈ s.bl.toList, b ∈ s'.bl.toList := by
  simp only [panelT] at h
  split_ifs at h <;> first
    | (cases h; exact fun _ hb => hb)
    | (cases h; exact plain_grows _ _ _ _ _ _ _ _ _ _)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h; exact plain_grows _ _ _ _ _ _ _ _ _ _)
    | exact foldlM_inv (fun t : Panels => ∀ b ∈ s.bl.toList, b ∈ t.bl.toList) _
        (fun t _ t' ht h => by
          first
            | (cases h; exact fun b hb => tri_grows _ _ _ _ _ _ _ _ _ b (ht b hb))
            | (obtain ⟨_, _, h⟩ := bind_some h; cases h
               exact fun b hb => tri_grows _ _ _ _ _ _ _ _ _ b (ht b hb)))
        _ _ _ (fun _ hb => hb) h

/-- The claims of the segment QK: the verifier's text with its local names written out. -/
theorem claimsT_QK_eq (c : ClaimEnv) :
    c.claimsT "QK" = (do
      let (AH, lfc) ← c.headWeights
      (List.range c.v.y.Lam).mapM fun lam =>
        c.claim 0 lam fun G =>
          if G.name == "hd" then some { AV := AH }
          else if G.name == "cd" then some { AV := c.ropeFactor (eqTab c.rt) lfc lam }
          else c.facRs G 0 (ceilLog2 c.v.y.h.d)) := rfl

/-- Claim number i of the segment QK, in the words of the verifier's text: on the unit of kind 0 of
layer i of the group; the claims are as many as the group's layers. AH and lfc are what headWeights
returns. -/
theorem claimsT_QK_at (c : ClaimEnv) {l : List WsClaim} (h : c.claimsT "QK" = some l) :
    l.length = c.v.y.Lam ∧ ∃ AH lfc, c.headWeights = some (AH, lfc) ∧ ∀ i, i < l.length →
      l[i]? = c.claim 0 i fun G =>
        if G.name == "hd" then some { AV := AH }
        else if G.name == "cd" then some { AV := c.ropeFactor (eqTab c.rt) lfc i }
        else c.facRs G 0 (ceilLog2 c.v.y.h.d) := by
  rw [claimsT_QK_eq] at h
  obtain ⟨⟨AH, lfc⟩, hw, h⟩ := bind_some h
  obtain ⟨hl, hat⟩ := list_mapM_some _ _ _ h
  rw [List.length_range] at hl
  refine ⟨hl, AH, lfc, hw, fun i hi => ?_⟩
  obtain ⟨b, hb, hF⟩ := hat i i (List.getElem?_range (hl ▸ hi))
  exact hb.trans hF.symm

/-- The claims of a routed product: the verifier's text with its local names written out. -/
theorem claimsT_routed_eq (c : ClaimEnv) (sn : String) (h3 : c.v.y.h.p3 = true)
    (hs : sn = "G" ∨ sn = "U" ∨ sn = "D") :
    c.claimsT sn = (List.range c.v.y.LamM).mapM fun lm =>
      c.claim (if sn == "G" then 7 else if sn == "U" then 8 else 10) (2 * lm + 1) fun G =>
        if G.name == "kk" then c.facRs G 0 (ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d))
        else if G.name == "e" then
          c.facRs G (ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d))
            (ceilLog2 (max c.v.y.h.NE 1))
        else c.facEw G sn (if sn == "D" then 0 else c.v.y.h.fe) := by
  rcases hs with rfl | rfl | rfl <;>
  · simp only [ClaimEnv.claimsT, h3]
    rfl

/-- Claim number lm of a routed product, in the words of the verifier's text: on the unit of kind 7
(G), 8 (U) or 10 (D) of layer 2 lm + 1 of the group; the claims are as many as the group's layers
with routed experts. -/
theorem claimsT_routed_at (c : ClaimEnv) (sn : String) (h3 : c.v.y.h.p3 = true)
    (hs : sn = "G" ∨ sn = "U" ∨ sn = "D") {l : List WsClaim} (h : c.claimsT sn = some l) :
    l.length = c.v.y.LamM ∧ ∀ lm, lm < l.length →
      l[lm]? = c.claim (if sn == "G" then 7 else if sn == "U" then 8 else 10) (2 * lm + 1) fun G =>
        if G.name == "kk" then c.facRs G 0 (ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d))
        else if G.name == "e" then
          c.facRs G (ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d))
            (ceilLog2 (max c.v.y.h.NE 1))
        else c.facEw G sn (if sn == "D" then 0 else c.v.y.h.fe) := by
  rw [claimsT_routed_eq c sn h3 hs] at h
  obtain ⟨hl, hat⟩ := list_mapM_some _ _ _ h
  rw [List.length_range] at hl
  refine ⟨hl, fun lm hlm => ?_⟩
  obtain ⟨b, hb, hF⟩ := hat lm lm (List.getElem?_range (hl ▸ hlm))
  exact hb.trans hF.symm

/-- For every other segment, and for G, U, D without routed experts, claimsT gives no claim. -/
theorem claimsT_other (c : ClaimEnv) (sn : String) (hQ : ¬ (sn == "QK") = true)
    (hR : ¬ (c.v.y.h.p3 && (sn == "G" || sn == "U" || sn == "D")) = true) :
    c.claimsT sn = some [] := by
  simp only [ClaimEnv.claimsT]
  rw [if_neg hQ, if_neg hR]
  rfl

/-! ## Where a panel comes from, and which claims are its own -/

/-- Panel b, with the number v0, is the panel of segment g of call q in the walk over the calls of
the lookup's join, and its claims stand in the list cl from v0 on. That is: isAcc is true of g;
there is a state s in which the number of the next claim is v0, such that panelA, run as panelsA
runs it for q and g, appends b to s; and claimsA returns for that segment a list l of as many claims
as b has rows, whose member i is member v0 + i of cl. -/
def AtA (p : PanelEnv) (c : ClaimEnv) (cl : List WsClaim) (b : SBlk) (v0 q : ℕ) (g : Seg) : Prop :=
  ∃ (s : Panels) (l : List WsClaim), isAcc g.name = true ∧ s.nextV = v0 ∧
    (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s).bl = s.bl.push b ∧
    c.claimsA g.name = some l ∧ l.length = b.ni ∧ ∀ i, i < b.ni → cl[v0 + i]? = l[i]?

/-- The same for a segment g named QK of a call q of the other walk: panelT, run as panelsT runs it,
returns a state that is s with b appended, and the claims are those of claimsT. -/
def AtQK (p : PanelEnv) (c : ClaimEnv) (cl : List WsClaim) (b : SBlk) (v0 q : ℕ) (g : Seg) :
    Prop :=
  ∃ (s s' : Panels) (l : List WsClaim), g.name = "QK" ∧ s.nextV = v0 ∧
    panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s' ∧ s'.bl = s.bl.push b ∧
    c.claimsT g.name = some l ∧ l.length = b.ni ∧ ∀ i, i < b.ni → cl[v0 + i]? = l[i]?

/-- Panel b, with the number v0, is the panel of the routed product of segment g of call q on the
layer with routed experts number lm, and its one claim is member v0 of cl. That is: there are routed
experts; g is named G, U or D; lm is below the number of layers with routed experts; there is a
state s in which the number of the next claim is v0, such that triStep at lm, run with what panelsT
gives panelT for q and g, returns s with b appended; and claimsT returns for that segment a list l
of one claim for each such layer, whose member lm is member v0 of cl. -/
def AtR (p : PanelEnv) (c : ClaimEnv) (cl : List WsClaim) (b : SBlk) (v0 q : ℕ) (g : Seg)
    (lm : ℕ) : Prop :=
  ∃ (s s' : Panels) (l : List WsClaim), p.v.y.h.p3 = true ∧
    (g.name = "G" ∨ g.name = "U" ∨ g.name = "D") ∧ lm < p.v.y.LamM ∧ s.nextV = v0 ∧
    triStep p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s lm = some s' ∧
    s'.bl = s.bl.push b ∧ c.claimsT g.name = some l ∧ l.length = p.v.y.LamM ∧
    cl[v0]? = l[lm]?

/-- AtA for some segment of some call of the walk over the calls of the lookup's join. -/
def FromA (p : PanelEnv) (c : ClaimEnv) (cl : List WsClaim) (b : SBlk) (v0 : ℕ) : Prop :=
  ∃ q ∈ callsAC p.v.y, ∃ g ∈ (p.v.y.calls.getD q default).segs, AtA p c cl b v0 q g

/-- AtQK for some segment of some call of TS. -/
def FromQK (p : PanelEnv) (c : ClaimEnv) (TS : List ℕ) (cl : List WsClaim) (b : SBlk) (v0 : ℕ) :
    Prop :=
  ∃ q ∈ TS, ∃ g ∈ (p.v.y.calls.getD q default).segs, AtQK p c cl b v0 q g

/-- AtR for some segment of some call of TS and some layer with routed experts. -/
def FromR (p : PanelEnv) (c : ClaimEnv) (TS : List ℕ) (cl : List WsClaim) (b : SBlk) (v0 : ℕ) :
    Prop :=
  ∃ q ∈ TS, ∃ g ∈ (p.v.y.calls.getD q default).segs, ∃ lm, AtR p c cl b v0 q g lm

/-- If panel b has a number v0, then it has no selector and comes with its claims from one of the
two walks, or it has the selector and is the panel of a routed product with its claim. -/
def Claimed (p : PanelEnv) (c : ClaimEnv) (TS : List ℕ) (cl : List WsClaim) (b : SBlk) : Prop :=
  ∀ v0, b.v0 = some v0 →
    (b.tri = false ∧ (FromA p c cl b v0 ∨ FromQK p c TS cl b v0)) ∨
    (b.tri = true ∧ FromR p c TS cl b v0)

/-- What the two walks keep. s: the panels so far; pre: the claims so far. The number of the next
claim is the number of the claims so far, and each panel so far finds its claims among them. -/
def InStep (p : PanelEnv) (c : ClaimEnv) (TS : List ℕ) (s : Panels) (pre : List WsClaim) : Prop :=
  s.nextV = pre.length ∧ ∀ b ∈ s.bl.toList, Claimed p c TS pre b

/-- InStep, and among the panels so far there is one of which P holds with the claims so far. -/
def Cov (p : PanelEnv) (c : ClaimEnv) (TS : List ℕ) (P : List WsClaim → SBlk → Prop) (s : Panels)
    (pre : List WsClaim) : Prop :=
  InStep p c TS s pre ∧ ∃ b ∈ s.bl.toList, P pre b

section Steps

variable {p : PanelEnv} {c : ClaimEnv} {TS : List ℕ}

/-- AtA stays true when claims are added at the list's end. -/
theorem AtA.mono {cl : List WsClaim} {b : SBlk} {v0 q : ℕ} {g : Seg} (x : List WsClaim)
    (h : AtA p c cl b v0 q g) : AtA p c (cl ++ x) b v0 q g := by
  obtain ⟨s, l, ha, hs, hb, hl, hn, hi⟩ := h
  exact ⟨s, l, ha, hs, hb, hl, hn, fun i h => getElem?_append_keep (by omega) (hi i h)⟩

/-- AtQK stays true when claims are added at the list's end. -/
theorem AtQK.mono {cl : List WsClaim} {b : SBlk} {v0 q : ℕ} {g : Seg} (x : List WsClaim)
    (h : AtQK p c cl b v0 q g) : AtQK p c (cl ++ x) b v0 q g := by
  obtain ⟨s, s', l, ha, hs, hp, hb, hl, hn, hi⟩ := h
  exact ⟨s, s', l, ha, hs, hp, hb, hl, hn, fun i h => getElem?_append_keep (by omega) (hi i h)⟩

/-- AtR stays true when claims are added at the list's end. -/
theorem AtR.mono {cl : List WsClaim} {b : SBlk} {v0 q : ℕ} {g : Seg} {lm : ℕ} (x : List WsClaim)
    (h : AtR p c cl b v0 q g lm) : AtR p c (cl ++ x) b v0 q g lm := by
  obtain ⟨s, s', l, h3, ha, hlm, hs, hp, hb, hl, hn, hi⟩ := h
  exact ⟨s, s', l, h3, ha, hlm, hs, hp, hb, hl, hn, getElem?_append_keep (by omega) hi⟩

/-- Claimed stays true when claims are added at the list's end. -/
theorem Claimed.mono {cl : List WsClaim} {b : SBlk} (x : List WsClaim)
    (h : Claimed p c TS cl b) : Claimed p c TS (cl ++ x) b := by
  intro v0 h0
  rcases h v0 h0 with ⟨ht, ⟨q, hq, g, hg, hA⟩ | ⟨q, hq, g, hg, hQ⟩⟩ | ⟨ht, q, hq, g, hg, lm, hR⟩
  · exact Or.inl ⟨ht, Or.inl ⟨q, hq, g, hg, hA.mono x⟩⟩
  · exact Or.inl ⟨ht, Or.inr ⟨q, hq, g, hg, hQ.mono x⟩⟩
  · exact Or.inr ⟨ht, q, hq, g, hg, lm, hR.mono x⟩

/-- The panel that panelA appends for one of the six segments, when the number of the next claim is
the number of the claims so far: its claims are those that claimsA adds. -/
theorem newA (hv : p.v = c.v) (q : ℕ) {g : Seg} {s : Panels} {pre l : List WsClaim}
    (hn : s.nextV = pre.length) (ha : isAcc g.name = true) (hl : c.claimsA g.name = some l) :
    ∃ b : SBlk, (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s).bl = s.bl.push b ∧
      (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s).nextV = (pre ++ l).length ∧
      b.v0 = some s.nextV ∧ b.tri = false ∧ AtA p c (pre ++ l) b s.nextV q g := by
  obtain ⟨b0, hbl, hnv, ht, hv0, hni⟩ :=
    panelA_acc p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s ha
  have hlen : l.length = b0.ni := by rw [claimsA_length c _ hl ha, hni, hv]
  exact ⟨b0, hbl, by rw [hnv, hn, List.length_append, hlen], hv0, ht, s, l, ha, rfl, hbl, hl, hlen,
    fun i _ => by rw [hn]; exact getElem?_append_new pre l i⟩

/-- The same for the panel that panelT appends for a segment named QK. -/
theorem newQK (hv : p.v = c.v) (q : ℕ) {g : Seg} {s s' : Panels} {pre l : List WsClaim}
    (hn : s.nextV = pre.length) (e : g.name = "QK") (hl : c.claimsT g.name = some l)
    (hs : panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s') :
    ∃ b : SBlk, s'.bl = s.bl.push b ∧ s'.nextV = (pre ++ l).length ∧ b.v0 = some s.nextV ∧
      b.tri = false ∧ AtQK p c (pre ++ l) b s.nextV q g := by
  obtain ⟨b0, hbl, hnv, ht, hv0, hni⟩ := panelT_QK p _ _ _ s s' e hs
  have hlen : l.length = b0.ni := by
    have hl' := hl
    rw [e] at hl'
    rw [(claimsT_QK_at c hl').1, hni, hv]
  exact ⟨b0, hbl, by rw [hnv, hn, List.length_append, hlen], hv0, ht, s, s', l, e, rfl, hs, hbl, hl,
    hlen, fun i _ => by rw [hn]; exact getElem?_append_new pre l i⟩

/-- The same for the panels that panelT appends for a routed product. The number of the next claim
grows by the claims that claimsT adds; the panels that were there stay; each new panel is that of
some layer with routed experts, with its claim; and each such layer has its panel. -/
theorem newR (hv : p.v = c.v) (q : ℕ) {g : Seg} {s s' : Panels} {pre l : List WsClaim}
    (hn : s.nextV = pre.length) (h3 : p.v.y.h.p3 = true)
    (hname : g.name = "G" ∨ g.name = "U" ∨ g.name = "D") (hl : c.claimsT g.name = some l)
    (hs : panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s') :
    s'.nextV = (pre ++ l).length ∧
      (∀ b ∈ s'.bl.toList, b ∈ s.bl.toList ∨
        ∃ lm v0, b.v0 = some v0 ∧ b.tri = true ∧ AtR p c (pre ++ l) b v0 q g lm) ∧
      ∀ lm, lm < p.v.y.LamM →
        ∃ b ∈ s'.bl.toList, ∃ v0, b.v0 = some v0 ∧ b.tri = true ∧
          AtR p c (pre ++ l) b v0 q g lm := by
  have hlen : l.length = p.v.y.LamM := by
    rw [(claimsT_routed_at c _ (hv ▸ h3) hname hl).1, hv]
  rw [panelT_routed p _ _ _ s h3 hname] at hs
  obtain ⟨hnv, hnew, _, hall⟩ := tri_fold p _ _ _ _ s s' hs
  refine ⟨by rw [hnv, hn, List.length_append, hlen], fun b hb' => ?_, fun lm hlm => ?_⟩
  · rcases hnew b hb' with hold | ⟨lm, st, st', hlm, hst, hstep, hbl, ht, hv0⟩
    · exact Or.inl hold
    · exact Or.inr ⟨lm, st.nextV, hv0, ht, st, st', l, h3, hname, hlm, rfl, hstep, hbl, hl, hlen,
        by rw [hst, hn]; exact getElem?_append_new pre l lm⟩
  · obtain ⟨b, hb', st, st', hst, hstep, hbl, ht, hv0⟩ := hall lm hlm
    exact ⟨b, hb', st.nextV, hv0, ht, st, st', l, h3, hname, hlm, rfl, hstep, hbl, hl, hlen,
      by rw [hst, hn]; exact getElem?_append_new pre l lm⟩

/-- One segment of a call of the lookup's join keeps the two walks in step. -/
theorem stepA (hv : p.v = c.v) {q : ℕ} (hq : q ∈ callsAC p.v.y) {g : Seg}
    (hg : g ∈ (p.v.y.calls.getD q default).segs) {s : Panels} {pre l : List WsClaim}
    (hI : InStep p c TS s pre) (hl : c.claimsA g.name = some l) :
    InStep p c TS (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) (pre ++ l) := by
  obtain ⟨hn, hb⟩ := hI
  cases ha : isAcc g.name with
  | false =>
    rw [claimsA_not c _ ha] at hl
    cases hl
    rw [panelA_not p _ _ _ s ha, List.append_nil]
    exact ⟨hn, hb⟩
  | true =>
    obtain ⟨b0, hbl, hnv, hv0, ht, hat⟩ := newA hv q hn ha hl
    refine ⟨hnv, fun b hb' => ?_⟩
    rw [hbl, Array.toList_push, List.mem_append, List.mem_singleton] at hb'
    rcases hb' with hb' | rfl
    · exact (hb b hb').mono l
    · intro v0 h0
      rw [hv0] at h0
      cases h0
      exact Or.inl ⟨ht, Or.inl ⟨q, hq, g, hg, hat⟩⟩

/-- One segment of a call that has terms in the second token sumcheck keeps the two walks in
step. -/
theorem stepT (hv : p.v = c.v) {q : ℕ} (hq : q ∈ TS) {g : Seg}
    (hg : g ∈ (p.v.y.calls.getD q default).segs) {s s' : Panels} {pre l : List WsClaim}
    (hI : InStep p c TS s pre) (hl : c.claimsT g.name = some l)
    (hs : panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s') :
    InStep p c TS s' (pre ++ l) := by
  obtain ⟨hn, hb⟩ := hI
  by_cases hQ : (g.name == "QK") = true
  · obtain ⟨b0, hbl, hnv, hv0, ht, hat⟩ := newQK hv q hn (beq_iff_eq.mp hQ) hl hs
    refine ⟨hnv, fun b hb' => ?_⟩
    rw [hbl, Array.toList_push, List.mem_append, List.mem_singleton] at hb'
    rcases hb' with hb' | rfl
    · exact (hb b hb').mono l
    · intro v0 h0
      rw [hv0] at h0
      cases h0
      exact Or.inl ⟨ht, Or.inr ⟨q, hq, g, hg, hat⟩⟩
  · by_cases hR : (p.v.y.h.p3 && (g.name == "G" || g.name == "U" || g.name == "D")) = true
    · have hR' := hR
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hR'
      obtain ⟨h3, hgud⟩ := hR'
      have hname : g.name = "G" ∨ g.name = "U" ∨ g.name = "D" := by
        rcases hgud with (h | h) | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      obtain ⟨hnv, hnew, _⟩ := newR hv q hn h3 hname hl hs
      refine ⟨hnv, fun b hb' => ?_⟩
      rcases hnew b hb' with hold | ⟨lm, v1, hv1, ht, hat⟩
      · exact (hb b hold).mono l
      · intro v0 h0
        rw [hv1] at h0
        cases h0
        exact Or.inr ⟨ht, q, hq, g, hg, lm, hat⟩
    · rw [claimsT_other c _ hQ (hv ▸ hR)] at hl
      cases hl
      obtain ⟨hnv, hnew⟩ := panelT_other p _ _ _ s s' hQ hR hs
      rw [List.append_nil]
      refine ⟨by rw [hnv, hn], fun b hb' => ?_⟩
      rcases hnew b hb' with hold | hnone
      · exact hb b hold
      · intro v0 h0
        rw [hnone] at h0
        cases h0

/-- A segment of a call of the lookup's join keeps Cov, if P stays true when claims are added at the
list's end. -/
theorem keepA (hv : p.v = c.v) {P : List WsClaim → SBlk → Prop}
    (hP : ∀ pre x b, P pre b → P (pre ++ x) b) {q : ℕ} (hq : q ∈ callsAC p.v.y) {g : Seg}
    (hg : g ∈ (p.v.y.calls.getD q default).segs) {s : Panels} {pre l : List WsClaim}
    (hJ : Cov p c TS P s pre) (hl : c.claimsA g.name = some l) :
    Cov p c TS P (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) (pre ++ l) := by
  obtain ⟨hI, b, hb, h⟩ := hJ
  exact ⟨stepA hv hq hg hI hl, b, growA p _ _ _ s b hb, hP _ _ _ h⟩

/-- The same for a segment of a call that has terms in the second token sumcheck. -/
theorem keepT (hv : p.v = c.v) {P : List WsClaim → SBlk → Prop}
    (hP : ∀ pre x b, P pre b → P (pre ++ x) b) {q : ℕ} (hq : q ∈ TS) {g : Seg}
    (hg : g ∈ (p.v.y.calls.getD q default).segs) {s s' : Panels} {pre l : List WsClaim}
    (hJ : Cov p c TS P s pre) (hl : c.claimsT g.name = some l)
    (hs : panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s') :
    Cov p c TS P s' (pre ++ l) := by
  obtain ⟨hI, b, hb, h⟩ := hJ
  exact ⟨stepT hv hq hg hI hl hs, b, growT p _ _ _ s s' hs b hb, hP _ _ _ h⟩

end Steps

/-! ## The two walks, whole -/

section Walks

variable {p : PanelEnv} {c : ClaimEnv}

/-- panelsA and the first half of weightClaims keep a relation R between the panels and the claims
so far, if each segment keeps it. -/
theorem walkA (R : Panels → List WsClaim → Prop)
    (H : ∀ q ∈ callsAC p.v.y, ∀ g ∈ (p.v.y.calls.getD q default).segs, ∀ s pre l, R s pre →
      c.claimsA g.name = some l →
      R (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) (pre ++ l))
    {s : Panels} {pre : List WsClaim} {a : List (List WsClaim)} (h : R s pre)
    (ha : ((callsAC p.v.y).flatMap fun q =>
      (p.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsA = some a) :
    R (panelsA p s) (pre ++ a.flatten) := by
  unfold panelsA
  refine foldl_step2 R _ _ _ _ _ _ _ (fun q hq s pre ls hI e => ?_) h ha
  rw [mapM_map_eq] at e
  exact foldl_step R _ _ _ _ _ _ (fun g hg s pre l hI e => H q hq g hg s pre l hI e) hI e

/-- The same for panelsT and the second half of weightClaims. -/
theorem walkT (R : Panels → List WsClaim → Prop) {TS : List ℕ}
    (H : ∀ q ∈ TS, ∀ g ∈ (p.v.y.calls.getD q default).segs, ∀ s s' pre l, R s pre →
      c.claimsT g.name = some l →
      panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s' → R s' (pre ++ l))
    {s s' : Panels} {pre : List WsClaim} {t : List (List WsClaim)} (h : R s pre)
    (ht : (TS.flatMap fun q =>
      (p.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsT = some t)
    (hp : panelsT p TS s = some s') : R s' (pre ++ t.flatten) := by
  unfold panelsT at hp
  refine foldlM_step2 R _ _ _ _ _ _ _ _ (fun q hq s s' pre ls hI e e' => ?_) h ht hp
  rw [mapM_map_eq] at e
  exact foldlM_step R _ _ _ _ _ _ _
    (fun g hg s s' pre l hI e e' => H q hq g hg s s' pre l hI e e') hI e e'

/-- panelsA and the first half of weightClaims lead from a relation R to a relation J, if each
segment keeps R and keeps J and the segment g0 of the call q0 leads from R to J. -/
theorem reachA (R J : Panels → List WsClaim → Prop)
    (HR : ∀ q ∈ callsAC p.v.y, ∀ g ∈ (p.v.y.calls.getD q default).segs, ∀ s pre l, R s pre →
      c.claimsA g.name = some l →
      R (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) (pre ++ l))
    (HJ : ∀ q ∈ callsAC p.v.y, ∀ g ∈ (p.v.y.calls.getD q default).segs, ∀ s pre l, J s pre →
      c.claimsA g.name = some l →
      J (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) (pre ++ l))
    {q0 : ℕ} (hq0 : q0 ∈ callsAC p.v.y) {g0 : Seg}
    (hg0 : g0 ∈ (p.v.y.calls.getD q0 default).segs)
    (hit : ∀ s pre l, R s pre → c.claimsA g0.name = some l →
      J (panelA p (p.e.getD q0 zeroE) (eqTab (p.v.zl q0)) g0.name s) (pre ++ l))
    {s : Panels} {pre : List WsClaim} {a : List (List WsClaim)} (h : R s pre)
    (ha : ((callsAC p.v.y).flatMap fun q =>
      (p.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsA = some a) :
    J (panelsA p s) (pre ++ a.flatten) := by
  unfold panelsA
  refine foldl_reach2 R J _ _ _ q0 (fun s pre ls hI e => ?_) _ _ _ _ hq0
    (fun q hq s pre ls hI e => ?_) (fun q hq s pre ls hI e => ?_) h ha
  · rw [mapM_map_eq] at e
    exact foldl_reach R J _ _ g0 hit _ _ _ _ hg0 (fun g hg => HR q0 hq0 g hg)
      (fun g hg => HJ q0 hq0 g hg) hI e
  · rw [mapM_map_eq] at e
    exact foldl_step R _ _ _ _ _ _ (fun g hg => HR q hq g hg) hI e
  · rw [mapM_map_eq] at e
    exact foldl_step J _ _ _ _ _ _ (fun g hg => HJ q hq g hg) hI e

/-- The same for panelsT and the second half of weightClaims. -/
theorem reachT (R J : Panels → List WsClaim → Prop) {TS : List ℕ}
    (HR : ∀ q ∈ TS, ∀ g ∈ (p.v.y.calls.getD q default).segs, ∀ s s' pre l, R s pre →
      c.claimsT g.name = some l →
      panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s' → R s' (pre ++ l))
    (HJ : ∀ q ∈ TS, ∀ g ∈ (p.v.y.calls.getD q default).segs, ∀ s s' pre l, J s pre →
      c.claimsT g.name = some l →
      panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s' → J s' (pre ++ l))
    {q0 : ℕ} (hq0 : q0 ∈ TS) {g0 : Seg} (hg0 : g0 ∈ (p.v.y.calls.getD q0 default).segs)
    (hit : ∀ s s' pre l, R s pre → c.claimsT g0.name = some l →
      panelT p (p.e.getD q0 zeroE) (eqTab (p.v.zl q0)) g0.name s = some s' → J s' (pre ++ l))
    {s s' : Panels} {pre : List WsClaim} {t : List (List WsClaim)} (h : R s pre)
    (ht : (TS.flatMap fun q =>
      (p.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsT = some t)
    (hp : panelsT p TS s = some s') : J s' (pre ++ t.flatten) := by
  unfold panelsT at hp
  refine foldlM_reach2 R J _ _ _ q0 (fun s s' pre ls hI e e' => ?_) _ _ _ _ _ hq0
    (fun q hq s s' pre ls hI e e' => ?_) (fun q hq s s' pre ls hI e e' => ?_) h ht hp
  · rw [mapM_map_eq] at e
    exact foldlM_reach R J _ _ g0 hit _ _ _ _ _ hg0 (fun g hg => HR q0 hq0 g hg)
      (fun g hg => HJ q0 hq0 g hg) hI e e'
  · rw [mapM_map_eq] at e
    exact foldlM_step R _ _ _ _ _ _ _ (fun g hg => HR q hq g hg) hI e e'
  · rw [mapM_map_eq] at e
    exact foldlM_step J _ _ _ _ _ _ _ (fun g hg => HJ q hq g hg) hI e e'

/-- What weightClaims returns: the claims of the segments of the first walk, then those of the
second. The calls are read in the panels' environment, which is the claims' own. -/
theorem weightClaims_some (hv : p.v = c.v) {TS : List ℕ} {cl : List WsClaim}
    (hc : c.weightClaims TS = some cl) :
    ∃ a t, ((callsAC p.v.y).flatMap fun q =>
        (p.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsA = some a ∧
      (TS.flatMap fun q =>
        (p.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsT = some t ∧
      cl = a.flatten ++ t.flatten := by
  have hc' : (do
      let a ← ((callsAC c.v.y).flatMap fun q =>
        (c.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsA
      let t ← (TS.flatMap fun q =>
        (c.v.y.calls.getD q default).segs.map (·.name)).mapM c.claimsT
      pure (a.flatten ++ t.flatten)) = some cl := hc
  obtain ⟨a, ha, hc'⟩ := bind_some hc'
  obtain ⟨t, ht, hc'⟩ := bind_some hc'
  cases hc'
  rw [← hv] at ha ht
  exact ⟨a, t, ha, ht, rfl⟩

/-- Before the first panel and the first claim the two walks are in step. -/
theorem inStep_start (p : PanelEnv) (c : ClaimEnv) (TS : List ℕ) : InStep p c TS {} [] :=
  ⟨rfl, fun _ hb => absurd hb List.not_mem_nil⟩

end Walks

/-! ## The whole -/

/-- From a panel to its segment and its claims. The verifier's list of panels and its list of weight
claims are in step. Asked: the two lists are made from one environment (p.v = c.v) and for the same
calls TS, and both functions return. Then the number of the next claim after the last panel is the
number of the claims. And for every panel b of the list that has a number v0: if b has no selector,
it is the panel that panelA or, for a segment named QK, panelT appends for a segment of one of the
calls, and the claims number v0 to v0 + b.ni - 1 are, in order, the claims that claimsA or claimsT
returns for that same segment (FromA, FromQK); if b has the selector, it is the panel that step lm
of triStep, this file's copy of the step of panelT's inner walk, appends for a segment G, U or D,
and claim number v0 is claim number lm of those that claimsT returns for that same segment (FromR).
What these claims are is said by claimsA_at, claimsT_QK_at and claimsT_routed_at. -/
theorem claims_of_panels (p : PanelEnv) (c : ClaimEnv) (hv : p.v = c.v) (TS : List ℕ)
    {pans : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans)
    (hc : c.weightClaims TS = some cl) :
    pans.nextV = cl.length ∧ ∀ b ∈ pans.bl.toList, ∀ v0, b.v0 = some v0 →
      (b.tri = false → FromA p c cl b v0 ∨ FromQK p c TS cl b v0) ∧
      (b.tri = true → FromR p c TS cl b v0) := by
  obtain ⟨a, t, ha, ht, rfl⟩ := weightClaims_some hv hc
  have hA : InStep p c TS (panelsA p {}) a.flatten :=
    walkA (InStep p c TS) (fun q hq g hg s pre l hI e => stepA hv hq hg hI e)
      (inStep_start p c TS) ha
  have hT : InStep p c TS pans (a.flatten ++ t.flatten) :=
    walkT (InStep p c TS) (fun q hq g hg s s' pre l hI e e' => stepT hv hq hg hI e e') hA ht hp
  refine ⟨hT.1, fun b hb v0 h0 => ?_⟩
  rcases hT.2 b hb v0 h0 with ⟨ht, h⟩ | ⟨ht, h⟩
  · exact ⟨fun _ => h, fun h' => absurd (ht.symm.trans h') Bool.false_ne_true⟩
  · exact ⟨fun h' => absurd (h'.symm.trans ht) Bool.false_ne_true, fun _ => h⟩

/-- From a segment to its panel and its claims. Asked: as in claims_of_panels. Then each segment of
the first walk for which isAcc is true has in the list a panel without selector that is its own,
with its claims (AtA); each segment named QK of the second walk has one (AtQK); and, with routed
experts, each segment named G, U or D of the second walk has for each layer with routed experts a
panel with the selector that is its own, with its claim (AtR). Where a segment stands twice in a
walk, this speaks of one of its two panels only. -/
theorem panels_of_segments (p : PanelEnv) (c : ClaimEnv) (hv : p.v = c.v) (TS : List ℕ)
    {pans : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans)
    (hc : c.weightClaims TS = some cl) :
    (∀ q ∈ callsAC p.v.y, ∀ g ∈ (p.v.y.calls.getD q default).segs, isAcc g.name = true →
      ∃ b ∈ pans.bl.toList, ∃ v0, b.v0 = some v0 ∧ b.tri = false ∧ AtA p c cl b v0 q g) ∧
    (∀ q ∈ TS, ∀ g ∈ (p.v.y.calls.getD q default).segs, g.name = "QK" →
      ∃ b ∈ pans.bl.toList, ∃ v0, b.v0 = some v0 ∧ b.tri = false ∧ AtQK p c cl b v0 q g) ∧
    (p.v.y.h.p3 = true → ∀ q ∈ TS, ∀ g ∈ (p.v.y.calls.getD q default).segs,
      (g.name = "G" ∨ g.name = "U" ∨ g.name = "D") → ∀ lm, lm < p.v.y.LamM →
      ∃ b ∈ pans.bl.toList, ∃ v0, b.v0 = some v0 ∧ b.tri = true ∧ AtR p c cl b v0 q g lm) := by
  obtain ⟨a, t, ha, ht, rfl⟩ := weightClaims_some hv hc
  have sA : ∀ q ∈ callsAC p.v.y, ∀ g ∈ (p.v.y.calls.getD q default).segs, ∀ s pre l,
      InStep p c TS s pre → c.claimsA g.name = some l →
      InStep p c TS (panelA p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s) (pre ++ l) :=
    fun q hq g hg s pre l hI e => stepA hv hq hg hI e
  have sT : ∀ q ∈ TS, ∀ g ∈ (p.v.y.calls.getD q default).segs, ∀ s s' pre l,
      InStep p c TS s pre → c.claimsT g.name = some l →
      panelT p (p.e.getD q zeroE) (eqTab (p.v.zl q)) g.name s = some s' →
      InStep p c TS s' (pre ++ l) :=
    fun q hq g hg s s' pre l hI e e' => stepT hv hq hg hI e e'
  have hA : InStep p c TS (panelsA p {}) a.flatten :=
    walkA (InStep p c TS) sA (inStep_start p c TS) ha
  refine ⟨fun q0 hq0 g0 hg0 hacc => ?_, fun q0 hq0 g0 hg0 hname => ?_,
    fun h3 q0 hq0 g0 hg0 hname lm hlm => ?_⟩
  · have hP : ∀ (pre x : List WsClaim) (b : SBlk),
        (∃ v0, b.v0 = some v0 ∧ b.tri = false ∧ AtA p c pre b v0 q0 g0) →
        ∃ v0, b.v0 = some v0 ∧ b.tri = false ∧ AtA p c (pre ++ x) b v0 q0 g0 :=
      fun pre x b ⟨v0, h0, h1, h2⟩ => ⟨v0, h0, h1, h2.mono x⟩
    have h1 : Cov p c TS (fun pre b => ∃ v0, b.v0 = some v0 ∧ b.tri = false ∧
        AtA p c pre b v0 q0 g0) (panelsA p {}) a.flatten :=
      reachA (InStep p c TS) _ sA (fun q hq g hg s pre l hJ e => keepA hv hP hq hg hJ e) hq0 hg0
        (fun s pre l hI e => by
          obtain ⟨b, hbl, _, hv0, htri, hat⟩ := newA hv q0 hI.1 hacc e
          exact ⟨stepA hv hq0 hg0 hI e, b, by rw [hbl]; exact mem_push_self _ _, _, hv0, htri,
            hat⟩)
        (inStep_start p c TS) ha
    exact (walkT _ (fun q hq g hg s s' pre l hJ e e' => keepT hv hP hq hg hJ e e') h1 ht hp).2
  · have hP : ∀ (pre x : List WsClaim) (b : SBlk),
        (∃ v0, b.v0 = some v0 ∧ b.tri = false ∧ AtQK p c pre b v0 q0 g0) →
        ∃ v0, b.v0 = some v0 ∧ b.tri = false ∧ AtQK p c (pre ++ x) b v0 q0 g0 :=
      fun pre x b ⟨v0, h0, h1, h2⟩ => ⟨v0, h0, h1, h2.mono x⟩
    exact (reachT (InStep p c TS) (Cov p c TS fun pre b => ∃ v0, b.v0 = some v0 ∧ b.tri = false ∧
        AtQK p c pre b v0 q0 g0) sT
      (fun q hq g hg s s' pre l hJ e e' => keepT hv hP hq hg hJ e e') hq0 hg0
      (fun s s' pre l hI e e' => by
        obtain ⟨b, hbl, _, hv0, htri, hat⟩ := newQK hv q0 hI.1 hname e e'
        exact ⟨stepT hv hq0 hg0 hI e e', b, by rw [hbl]; exact mem_push_self _ _, _, hv0, htri,
          hat⟩)
      hA ht hp).2
  · have hP : ∀ (pre x : List WsClaim) (b : SBlk),
        (∃ v0, b.v0 = some v0 ∧ b.tri = true ∧ AtR p c pre b v0 q0 g0 lm) →
        ∃ v0, b.v0 = some v0 ∧ b.tri = true ∧ AtR p c (pre ++ x) b v0 q0 g0 lm :=
      fun pre x b ⟨v0, h0, h1, h2⟩ => ⟨v0, h0, h1, h2.mono x⟩
    exact (reachT (InStep p c TS) (Cov p c TS fun pre b => ∃ v0, b.v0 = some v0 ∧ b.tri = true ∧
        AtR p c pre b v0 q0 g0 lm) sT
      (fun q hq g hg s s' pre l hJ e e' => keepT hv hP hq hg hJ e e') hq0 hg0
      (fun s s' pre l hI e e' =>
        ⟨stepT hv hq0 hg0 hI e e', (newR hv q0 hI.1 h3 hname e e').2.2 lm hlm⟩)
      hA ht hp).2

#print axioms panelA_acc
#print axioms panelA_not
#print axioms claimsA_at
#print axioms panelT_routed
#print axioms panelT_other
#print axioms claimsT_QK_at
#print axioms claimsT_routed_at
#print axioms stepA
#print axioms stepT
#print axioms claims_of_panels
#print axioms panels_of_segments

end OnBytes.Road
