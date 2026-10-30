-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/RowsRide.lean
(kind K9's soundness lemma; the law of a link on the road of moves): THEOREMS: THE PAYERS OF THE
THREE PREMISES hR1, hR2, hR3 OF inMoves_rows (Law/RowsNumber.lean) AT THE SENTENCE "the plan's
claims and the ties' and reads' indices are at most the rows of the batching element's round", READ
OFF THE STATE.
  numOf u s     what the sentence reads of a state: the smallness test's record with its written
                fields blanked (blank u), the list of tables, the plan's number of claims.
  rowsAt rows u s   the sentence; rowsAt_congr: it hangs on numOf alone.
  addAll_plan   the adding leaves the plan's number, with no premise on sizes.
  num_set       K9's lens's writing leaves numOf where the part written has the plan's number.
  MoveNum u     THE DUTY OF A MOVE: where it returns, numOf reads the same.
  moves_num, drawMoves_num   along a row of moves; along a draw with moves behind it.
  rows_hR3      **hR3: THE ONE EQUATION's PIECE GIVES THE SENTENCE IN FRONT OF ITSELF FROM ITS OWN
                YES** (door_rows), where the condition on2 says two public things of the state: the
                rows owed are p.rows; the indices laid are top8 of the blanked record.
  rows_hR2      hR2: the second piece hands it backward: one duty a move.
  rows_hR1      hR1: behind the first piece it gives rowsFit p.rows pi of the fixed part in front:
                one duty a move, and hpi (what pi reads of phi: Law/K8Run.lean's).
  k8Run_num, k8LsTail_num, k8Tests_num   the duty at the smallness test's three runs.
Not claimed: the duty at any other run; the two public things at on2 (who makes them: the draw
writes the rows owed; eq_laid (Johnson/Meaning/K8Rows.lean) ties what "K8.equations" lays to topOf).

-/
import Johnson.Desc.First.Batch.Law.RowsNumber
import Johnson.Desc.First.Batch.Law.K8Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.TailClaims.Law (blank eq_blank eq_side blank_lsTail)
open _root_.Run (ckP)

/-- What the sentence reads of a state. -/
def numOf (u : HTailF2) (s : S) : Option HTailF2 × Option (Array HFun) × Option ℕ :=
  (s.tl?.map (blank u), s.funs?, s.fork?.map (·.planClaimsF))

/-- The sentence, read off the state. -/
def rowsAt (rows : ℕ) (u : HTailF2) (s : S) : Prop :=
  ∀ tlb funs n, numOf u s = (some tlb, some funs, some n) → n + top8 tlb funs ≤ rows

theorem rowsAt_congr (rows : ℕ) (u : HTailF2) (s s' : S) (h : numOf u s' = numOf u s) :
    rowsAt rows u s' → rowsAt rows u s := fun hr tlb funs n e => hr tlb funs n (h.trans e)

/-! ## The adding leaves the plan's number -/

theorem push_plan (F G : Fork) (w : E) (a : Aff) (h : F.push w a = some G) :
    G.planClaimsF = F.planClaimsF := by
  unfold Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rw [← Option.some.inj h]
    · simp at h

theorem addClaim_plan (F G : Fork) (cl : Claim) (h : addClaim F cl = some G) :
    G.planClaimsF = F.planClaimsF := by
  simp only [addClaim, Option.bind_eq_some_iff] at h
  obtain ⟨⟨k0, F1⟩, hk, k, _, F2, hp, h3⟩ := h
  obtain ⟨_, hF1, _, _⟩ := Fork.kap_spec F F1 k0 hk
  have hG : G.planClaimsF = F2.planClaimsF := by
    unfold Fork.pushRuns at h3
    simp only [Option.map_eq_some_iff] at h3
    obtain ⟨tr, _, rfl⟩ := h3
    rfl
  have q1 : F1.planClaimsF = F.planClaimsF := by rw [hF1]
  rw [hG, push_plan F1 F2 k cl.form hp, q1]

theorem addAll_plan : ∀ (l : List Claim) (F G : Fork), addAll F l = some G →
    G.planClaimsF = F.planClaimsF
  | [], F, G, h => by
    have hF : F = G := by simpa [addAll] using h
    rw [hF]
  | cl :: l, F, G, h => by
    unfold addAll at h
    rw [List.foldlM_cons] at h
    cases hq : addClaim F cl with
    | none => simp [hq] at h
    | some F1 =>
      rw [hq] at h
      have h2 : addAll F1 l = some G := by simpa [addAll] using h
      rw [addAll_plan l F1 G h2, addClaim_plan F F1 cl hq]

/-! ## The lens's writing -/

/-- K9's part holds the record's own ledger. -/
theorem fork_part (s : S) (a : K9.Part) (h : atS.get? s = some a) : s.fork? = some a.F := by
  simp only [atS] at h
  obtain ⟨L, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨tl, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨x, _, h⟩ := Option.bind_eq_some_iff.1 h
  rw [← Option.some.inj h]
  exact hG

/-- The lens's writing leaves numOf where the part written has the plan's number. -/
theorem num_set (u : HTailF2) (s : S) (a a' : K9.Part) (ha : atS.get? s = some a)
    (hp : a'.F.planClaimsF = a.F.planClaimsF) : numOf u (atS.set s a') = numOf u s := by
  have hF := fork_part s a ha
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x =>
    have e : x.F = a.F := Option.some.inj hF
    simp [numOf, atS, S.putLink, S.putFork, S.tl?, S.funs?, S.fork?, hp, e]
  | att x =>
    have e : x.F = a.F := Option.some.inj hF
    simp [numOf, atS, S.putLink, S.putFork, S.tl?, S.funs?, S.fork?, hp, e]
  | head x =>
    by_cases ho : x.opened = true
    · have e : x.F = a.F := by simpa [S.fork?, ho] using hF
      simp [numOf, atS, S.putLink, S.putFork, S.tl?, S.funs?, S.fork?, ho, hp, e]
    · simp [S.fork?, ho] at hF
  | between => simp [S.fork?] at hF
  | fin x => simp [S.fork?] at hF
  | mem x => simp [S.fork?] at hF

/-! ## Along the moves -/

/-- The duty of a move. -/
def MoveNum (u : HTailF2) : Move S → Prop
  | .add g => ∀ e c e₁, g e = .ok (c, e₁) → numOf u e₁ = numOf u e
  | .quiet h => ∀ e e₁, h e = .ok e₁ → numOf u e₁ = numOf u e

theorem moves_num (u : HTailF2) : ∀ (ms : List (Move S)), (∀ m ∈ ms, MoveNum u m) →
    ∀ (e e' : S) (c : List Claim), MovesYes atS ms e e' c → numOf u e' = numOf u e
  | [], _, e, e', c, hy => by
    obtain ⟨rfl, _⟩ := hy
    rfl
  | m :: l, hms, e, e', c, hy => by
    obtain ⟨x, c₁, c₂, h1, h2, _⟩ := hy
    have i := moves_num u l (fun q hq => hms q (List.mem_cons_of_mem _ hq)) x e' c₂ h2
    have hm := hms m List.mem_cons_self
    rw [i]
    cases m with
    | add g =>
      obtain ⟨e₁, s, G, hg, hs, hG, rfl⟩ := h1
      rw [num_set u e₁ s { s with F := G } hs (addAll_plan _ _ _ hG)]
      exact hm e c₁ e₁ hg
    | quiet h => exact hm e x h1.1

/-- A draw with moves behind it. -/
theorem drawMoves_num {Cl : Type} (u : HTailF2) (p : Where) (ms : List (Move S)) (b : Block S Cl)
    (hb : DrawMoves atS p ms b) (hms : ∀ m ∈ ms, MoveNum u m) (ft : ℕ) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : b.step ft s rs cols = .ok (s', k)) : numOf u s' = numOf u s := by
  obtain ⟨r, x, a, o, cls, _, _, ha, ho, hy⟩ := hb ft s rs cols s' k h
  obtain ⟨_, _, _, d4, _⟩ := drawnClean_ok _ _ _ _ _ _ _ ho
  rw [moves_num u ms hms _ _ _ hy]
  exact num_set u s a _ ha d4

section
variable {α W Cl : Type} {F : Frame}

/-- **hR3.** -/
theorem rows_hR3 (u : HTailF2) (p pw : Where) (b₃ : Block S Cl)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
    (pe : Piece (ckP .two) F S Cl W) (hpe : pe.b = below b₃) (on2 : S × F.E.Str → Prop)
    (hon2 : ∀ a, on2 a → ∀ x tl funs, atS.get? a.1 = some x → a.1.tl? = some tl →
      a.1.funs? = some funs → x.owed = some p.rows ∧ x.laid = some (top8 (blank u tl) funs)) :
    ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → rowsAt p.rows u a.1 := by
  intro a τ b' ha hout tlb funs n e
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨k, hs⟩ := fold_one hfold
  have hs' := hb₃ _ _ _ _ _ hs
  obtain ⟨x, out, hx, _, _⟩ := oneEquation_inv atS pw _ _ _ _ _ k hs'
  have hF := fork_part a.1 x hx
  simp only [numOf, Prod.mk.injEq, Option.map_eq_some_iff] at e
  obtain ⟨⟨tl, ht, rfl⟩, hf, G, hG, rfl⟩ := e
  obtain rfl : x.F = G := Option.some.inj (hF.symm.trans hG)
  obtain ⟨o1, o2⟩ := hon2 a ha x tl funs hx ht hf
  exact Nat.le_of_eq (door_rows pw _ _ _ _ _ k hs' x hx _ _ o1 o2).symm

/-- **hR2.** -/
theorem rows_hR2 (u : HTailF2) (rows : ℕ) (ms : List (Move S)) (b₂ : Block S Cl)
    (hb₂ : IsMoves atS ms b₂) (hms : ∀ m ∈ ms, MoveNum u m)
    (pq : Piece (ckP .two) F S Cl W) (hpq : pq.b = below b₂) (a b' : S × F.E.Str)
    (τ : _root_.Iop.Tr (uLT (ckP .two) pq.ds)) (hout : pq.ior.red.out a τ = some b') :
    rowsAt rows u b'.1 → rowsAt rows u a.1 := by
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpq hout
  obtain ⟨k, hs⟩ := fold_one hfold
  obtain ⟨rs', gs, hd⟩ := step_decide b₂ _ _ _ _ _ k hs
  obtain ⟨cls, hy⟩ := hb₂.dec _ _ _ _ hd
  exact rowsAt_congr rows u a.1 b'.1 (moves_num u ms hms _ _ _ hy)

/-- **hR1.** -/
theorem rows_hR1 (u : HTailF2) (φ : S → α) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) (p : Where) (ms : List (Move S))
    (b₁ : Block S Cl) (hb₁ : DrawMoves atS p ms b₁) (hms : ∀ m ∈ ms, MoveNum u m)
    (pb : Piece (ckP .two) F S Cl W) (hpb : pb.b = below b₁) (a b' : S × F.E.Str)
    (τ : _root_.Iop.Tr (uLT (ckP .two) pb.ds)) (hout : pb.ior.red.out a τ = some b') :
    rowsAt p.rows u b'.1 → rowsFit p.rows π (fixed9 φ a.1) := by
  intro hr v tlb funs hv hq
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
  obtain ⟨k, hs⟩ := fold_one hfold
  have h0 := rowsAt_congr p.rows u a.1 b'.1 (drawMoves_num u p ms b₁ hb₁ hms _ _ _ _ _ k hs) hr
  simp only [fixed9, Option.map_eq_some_iff] at hv
  obtain ⟨x, hx, rfl⟩ := hv
  have e1 : π (φ a.1) = (some tlb, some funs) := hq
  rw [hπ] at e1
  refine h0 tlb funs _ ?_
  simp only [numOf, fork_part a.1 x hx, Option.map_some]
  rw [(Prod.mk.inj e1).1, (Prod.mk.inj e1).2]
  rfl

end

/-! ## The duty at the smallness test's three runs -/

theorem num_puts (u : HTailF2) (s : S) (tl tl' : HTailF2) (G G' : Fork) (ht : s.tl? = some tl)
    (hG : s.fork? = some G) (hb : blank u tl' = blank u tl)
    (hp : G'.planClaimsF = G.planClaimsF) : numOf u ((s.putTl tl').putFork G') = numOf u s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x =>
    obtain rfl : x.tl = tl := Option.some.inj ht
    obtain rfl : x.F = G := Option.some.inj hG
    simp [numOf, S.putTl, S.putFork, S.tl?, S.funs?, S.fork?, hb, hp]
  | att x =>
    obtain rfl : x.tl = tl := Option.some.inj ht
    obtain rfl : x.F = G := Option.some.inj hG
    simp [numOf, S.putTl, S.putFork, S.tl?, S.funs?, S.fork?, hb, hp]
  | head x =>
    by_cases ho : x.opened = true
    · have e1 : x.tl = tl := by simpa [S.tl?, ho] using ht
      have e2 : x.F = G := by simpa [S.fork?, ho] using hG
      simp [numOf, S.putTl, S.putFork, S.tl?, S.funs?, S.fork?, ho, hb, hp, e1, e2]
    · simp [S.tl?, ho] at ht
  | between => simp [S.tl?] at ht
  | fin x => simp [S.tl?] at ht
  | mem x => simp [S.tl?] at ht

theorem num_putTl (u : HTailF2) (s : S) (tl tl' : HTailF2) (ht : s.tl? = some tl)
    (hb : blank u tl' = blank u tl) : numOf u (s.putTl tl') = numOf u s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x =>
    obtain rfl : x.tl = tl := Option.some.inj ht
    simp [numOf, S.putTl, S.tl?, S.funs?, S.fork?, hb]
  | att x =>
    obtain rfl : x.tl = tl := Option.some.inj ht
    simp [numOf, S.putTl, S.tl?, S.funs?, S.fork?, hb]
  | head x =>
    by_cases ho : x.opened = true
    · have e1 : x.tl = tl := by simpa [S.tl?, ho] using ht
      simp [numOf, S.putTl, S.tl?, S.funs?, S.fork?, ho, hb, e1]
    · simp [S.tl?, ho] at ht
  | between => simp [S.tl?] at ht
  | fin x => simp [S.tl?] at ht
  | mem x => simp [S.tl?] at ht

theorem k8Run_num (u : HTailF2) (front : Nat) (e e₁ : S) (c : List Claim)
    (h : k8Run.2 front e = .ok (c, e₁)) : numOf u e₁ = numOf u e := by
  obtain ⟨G, tl, funs, tl', F1, hG, ht, _, he, rfl⟩ := k8Run_ok front e e₁ c h
  exact num_puts u e tl tl' G F1 ht hG (eq_blank u he) (eq_side he).plan

theorem k8LsTail_num (u : HTailF2) (e e₁ : S) (h : k8LsTail e = .ok e₁) :
    numOf u e₁ = numOf u e := by
  obtain ⟨G, tl, _, ht, rfl⟩ := k8LsTail_ok e e₁ h
  exact num_putTl u e tl _ ht (blank_lsTail u tl _)

theorem k8Tests_num (u : HTailF2) (nU : Array Nat) (e e₁ : S) (h : k8Tests nU e = .ok e₁) :
    numOf u e₁ = numOf u e := by
  obtain ⟨G, tl, g, hG, ht, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
  exact num_puts u e tl tl G _ ht hG rfl (coef_side tl g G).2.2.2.2.2.2.1

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.addAll_plan
#print axioms VerifiableInference.Desc.K9L.num_set
#print axioms VerifiableInference.Desc.K9L.drawMoves_num
#print axioms VerifiableInference.Desc.K9L.rows_hR3
#print axioms VerifiableInference.Desc.K9L.rows_hR2
#print axioms VerifiableInference.Desc.K9L.rows_hR1
#print axioms VerifiableInference.Desc.K9L.k8Run_num
#print axioms VerifiableInference.Desc.K9L.k8LsTail_num
#print axioms VerifiableInference.Desc.K9L.k8Tests_num
