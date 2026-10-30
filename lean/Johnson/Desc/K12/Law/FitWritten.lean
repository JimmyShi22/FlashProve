-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FitWritten.lean: roundsFit (Johnson/Desc/Block.lean), the first line of
Block.step, holds at written rounds, whatever the transcript.

Why. The verifier accK of the lemma on the proximity test (the kind K12;
Johnson/Desc/K12/Law/K12Lemma.lean) is Block.step at the written view. The step has three lines:
"the rounds" (roundsFit), "the columns", and the decision. Johnson/Desc/K12/Law/ViewWide.lean with
kpw_colsOf (Johnson/Desc/K12/Law/ViewK.lean) pays the second; this file pays the first. Each stands
under its own premises, and neither file has accK on the left-hand side of a theorem. The premises
that must stand with any sentence "accK's yes is then the decision's yes and the tests of work":
nzOk (Johnson/Desc/K12/Law/NzOk.lean); the first round r0 fits the declared round "BAT"; planOk;
dealOk; tieOk; the yes of the test on the group's plain data; DeepK, its field wide too. Statements
and proofs.
Main names:
  `isE`, `isP`, `tritN`, `toU_zero`, `toU3_ne`, `elems_forall`, `poss_all`, `trit_cases`,
    `trits_all`: of Fmt.collect (outAll .two ds v), for any list of draws ds: one element for each
    draw of an element, in turn, and one that must not be 0 is not (0, 0, 0); one position for each
    draw of a position, below its range; the matrix entries as many as asked, each -1, 0 or 1.
  `dsSeeds_isE`, `dsSeeds_length`, `dsElems_isE`, `dsElems_length`, `dsOf_isE`, `dsOf_isP`,
    `dsOf_pos`, `dsOf_trits`: the counts of a round's own list of draws (Fmt.dsOf e k).
  `FitsDrawn`, `fitsDrawn`, `fitsDrawn_ckP`: six clauses on what a written round draws, at the
    library's challenge kit ckP .two: elems (under drawNZ ≤ drawE), poss, trits, below, signs, nz.
    All six are spent here.
  `gots_items`: the items that a written round shows are those cut, but for the roots.
  `IsOf`, `IsOfK`, `zip_all_of_forall₂`, `roundsFit_written`: for declared rounds and written rounds
    that are theirs one by one and have the kind of their entry's name.
  `layW_isOf`: layW (Johnson/Desc/K12/Law/PubOk.lean) lays such rounds, and each has the kind of its
    entry's name (for drawsMarkedNonzeroHaveNonzeroWords).
  `roundsFit_place`, `roundsFit_cons`, `roundsFit_behind`: at the place's numbers: all its written
    rounds; or a first round r0 that fits "BAT" and the written rounds behind it.
Limits: No soundness is claimed, and nothing is said on hiding.
Premises of roundsFit_behind: the declared rounds and the written rounds off the place's numbers; no
entry behind "BAT" asks more elements other than 0 than elements (nzOk, with nz_of_ok of
Johnson/Desc/K12/Law/NzLaw.lean); r0 fits the declared round "BAT" (all seven clauses).
Of the library it uses definitions and no lemma: out, outAll, toU3, trit (Run/DrawTie.lean); drawnOf
(Run/PlanDraws.lean); ckP (Run/PlanPull.lean); rvSL (Run/PlanQS.lean); dsOf, dsElems, dsSeeds,
collect (Fmt/Rules6Draws.lean).
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.ChainOf

set_option autoImplicit false
namespace H2K.Fit
open Run

def isE : Fmt.Draw → Bool
  | .elem => true
  | .elemNZ => true
  | _ => false

def isP : Fmt.Draw → Bool
  | .pos _ => true
  | _ => false

def tritN : Fmt.Draw → ℕ
  | .trits n => n
  | _ => 0

theorem toU_zero {x : FV .two} (h : toU x = 0) : x.val = 0 := by
  unfold toU at h
  have h1 := congrArg UInt64.toNat h
  rw [UInt64.toNat_ofNat'] at h1
  have hx : x.val < 2 ^ 64 := lt_of_lt_of_le x.isLt (by decide)
  rw [Nat.mod_eq_of_lt hx] at h1
  exact h1

theorem toU3_ne (e : NZ .two) : toU3 e.1 ≠ (0, 0, 0) := by
  intro h
  apply e.2
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  obtain ⟨h2, h3⟩ := Prod.mk.inj h2
  exact Prod.ext (Fin.ext (toU_zero h1)) (Prod.ext (Fin.ext (toU_zero h2)) (Fin.ext (toU_zero h3)))

/-- The elements drawn, one for each draw of an element, in turn; one that must not be 0 is not. -/
theorem elems_forall : ∀ (ds : List Fmt.Draw) (v : Vals .two ds),
    List.Forall₂ (fun d x => d = Fmt.Draw.elemNZ → x ≠ ((0, 0, 0) : Fmt.Ext)) (ds.filter isE)
      (Fmt.collect (outAll .two ds v)).elems
  | [], _ => List.Forall₂.nil
  | .elem :: ds, v => List.Forall₂.cons (fun h => nomatch h) (elems_forall ds v.2)
  | .elemNZ :: ds, v => List.Forall₂.cons (fun _ => toU3_ne v.1) (elems_forall ds v.2)
  | .pos _ :: ds, v => elems_forall ds v.2
  | .trits _ :: ds, v => elems_forall ds v.2
  | .sealed :: ds, v => elems_forall ds v.2

/-- The positions drawn: one for each draw of a position; each below its draw's range. -/
theorem poss_all (k : ℕ) : ∀ (ds : List Fmt.Draw) (v : Vals .two ds),
    (∀ k', Fmt.Draw.pos k' ∈ ds → k' = k) →
    (Fmt.collect (outAll .two ds v)).poss.length = (ds.filter isP).length ∧
      ∀ x ∈ (Fmt.collect (outAll .two ds v)).poss, x < 2 ^ k
  | [], _, _ => ⟨rfl, fun _ h => nomatch h⟩
  | .elem :: ds, v, h => poss_all k ds v.2 fun k' hk => h k' (List.mem_cons_of_mem _ hk)
  | .elemNZ :: ds, v, h => poss_all k ds v.2 fun k' hk => h k' (List.mem_cons_of_mem _ hk)
  | .trits _ :: ds, v, h => poss_all k ds v.2 fun k' hk => h k' (List.mem_cons_of_mem _ hk)
  | .sealed :: ds, v, h => poss_all k ds v.2 fun k' hk => h k' (List.mem_cons_of_mem _ hk)
  | .pos k0 :: ds, v, h => by
    obtain ⟨a, b⟩ := poss_all k ds v.2 fun k' hk => h k' (List.mem_cons_of_mem _ hk)
    obtain rfl := h k0 List.mem_cons_self
    refine ⟨congrArg (· + 1) a, fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact v.1.isLt
    · exact b x hx

theorem trit_cases (b : Bool × Bool) : trit b = -1 ∨ trit b = 0 ∨ trit b = 1 := by
  unfold trit
  split
  · split
    · exact .inl rfl
    · exact .inr (.inr rfl)
  · exact .inr (.inl rfl)

/-- The matrix entries drawn: as many as the draws say; each -1, 0 or 1. -/
theorem trits_all : ∀ (ds : List Fmt.Draw) (v : Vals .two ds),
    (Fmt.collect (outAll .two ds v)).trits.length = (ds.map tritN).sum ∧
      ∀ t ∈ (Fmt.collect (outAll .two ds v)).trits, t = -1 ∨ t = 0 ∨ t = 1
  | [], _ => ⟨rfl, fun _ h => nomatch h⟩
  | .elem :: ds, v => by
    obtain ⟨a, b⟩ := trits_all ds v.2
    exact ⟨by rw [List.map_cons, List.sum_cons]; show _ = 0 + _; rw [Nat.zero_add]; exact a, b⟩
  | .elemNZ :: ds, v => by
    obtain ⟨a, b⟩ := trits_all ds v.2
    exact ⟨by rw [List.map_cons, List.sum_cons]; show _ = 0 + _; rw [Nat.zero_add]; exact a, b⟩
  | .pos _ :: ds, v => by
    obtain ⟨a, b⟩ := trits_all ds v.2
    exact ⟨by rw [List.map_cons, List.sum_cons]; show _ = 0 + _; rw [Nat.zero_add]; exact a, b⟩
  | .sealed :: ds, v => by
    obtain ⟨a, b⟩ := trits_all ds v.2
    exact ⟨by rw [List.map_cons, List.sum_cons]; show _ = 0 + _; rw [Nat.zero_add]; exact a, b⟩
  | .trits n :: ds, v => by
    obtain ⟨a, b⟩ := trits_all ds v.2
    refine ⟨?_, fun t ht => ?_⟩
    · show ((List.ofFn fun j => trit (v.1 j)) ++ _).length = _
      rw [List.length_append, List.length_ofFn, a, List.map_cons, List.sum_cons]
      rfl
    · have ht' : t ∈ (List.ofFn fun j => trit (v.1 j)) ++ (Fmt.collect (outAll .two ds v.2)).trits
        := ht
      rcases List.mem_append.1 ht' with h1 | h1
      · obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 h1
        exact trit_cases _
      · exact b t h1

/-! ## A round's own list of draws -/

theorem dsSeeds_isE (s v : ℕ) : ∀ d ∈ Fmt.dsSeeds s v, isE d = true := by
  intro d hd
  unfold Fmt.dsSeeds at hd
  obtain ⟨l, hl, hd⟩ := List.mem_flatten.1 hd
  obtain rfl := (List.mem_replicate.1 hl).2
  rcases List.mem_append.1 hd with h | h
  · obtain rfl := (List.mem_replicate.1 h).2
    rfl
  · obtain rfl := List.mem_singleton.1 h
    rfl

theorem dsElems_isE (e : Fmt.Entry) (k : Fmt.Kind) : ∀ d ∈ Fmt.dsElems e k, isE d = true := by
  intro d hd
  unfold Fmt.dsElems at hd
  split at hd
  · rcases List.mem_append.1 hd with h | h
    · exact dsSeeds_isE _ _ d h
    · obtain rfl := (List.mem_replicate.1 h).2
      rfl
  · rcases List.mem_append.1 hd with h | h
    · obtain rfl := (List.mem_replicate.1 h).2
      rfl
    · obtain rfl := (List.mem_replicate.1 h).2
      rfl

theorem dsSeeds_length (s v : ℕ) : (Fmt.dsSeeds s v).length = s * (v + 1) := by
  unfold Fmt.dsSeeds
  simp [List.length_flatten]

theorem dsElems_length (e : Fmt.Entry) (k : Fmt.Kind) (h : e.drawNZ ≤ e.drawE) :
    (Fmt.dsElems e k).length = e.drawE := by
  unfold Fmt.dsElems
  split
  · rw [List.length_append, dsSeeds_length, List.length_replicate]
    have := Nat.div_add_mod (e.drawE - e.drawNZ) e.drawNZ
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · rw [List.length_append, List.length_replicate, List.length_replicate]
    omega

theorem filter_none {α : Type} (p : α → Bool) (l : List α) (h : ∀ x ∈ l, p x = false) :
    l.filter p = [] := List.filter_eq_nil_iff.2 fun x hx => by rw [h x hx]; decide

theorem dsOf_isE (e : Fmt.Entry) (k : Fmt.Kind) : (Fmt.dsOf e k).filter isE = Fmt.dsElems e k := by
  unfold Fmt.dsOf
  rw [List.filter_append, List.filter_append,
    filter_none isE (List.replicate _ _)
      (fun x hx => by obtain rfl := (List.mem_replicate.1 hx).2; rfl),
    List.filter_eq_self.2 (dsElems_isE e k), List.nil_append]
  rw [filter_none isE _ (fun x hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · rfl
    · split at hx
      · obtain rfl := List.mem_singleton.1 hx
        rfl
      · cases hx), List.append_nil]

theorem isP_of_isE {d : Fmt.Draw} (h : isE d = true) : isP d = false := by
  cases d <;> first | rfl | cases h

theorem tritN_of_isE {d : Fmt.Draw} (h : isE d = true) : tritN d = 0 := by
  cases d <;> first | rfl | cases h

theorem dsOf_isP (e : Fmt.Entry) (k : Fmt.Kind) : ((Fmt.dsOf e k).filter isP).length = e.poss := by
  unfold Fmt.dsOf
  rw [List.filter_append, List.filter_append,
    List.filter_eq_self.2 (fun x hx => by obtain rfl := (List.mem_replicate.1 hx).2; rfl),
    filter_none isP (Fmt.dsElems e k) (fun x hx => isP_of_isE (dsElems_isE e k x hx)),
    filter_none isP _ (fun x hx => by
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · split at hx
        · obtain rfl := List.mem_singleton.1 hx
          rfl
        · cases hx)]
  simp

theorem dsOf_pos (e : Fmt.Entry) (k : Fmt.Kind) (k' : ℕ) (h : Fmt.Draw.pos k' ∈ Fmt.dsOf e k) :
    k' = e.logN := by
  unfold Fmt.dsOf at h
  rcases List.mem_append.1 h with h | h
  · have := (List.mem_replicate.1 h).2
    cases this
    rfl
  · rcases List.mem_append.1 h with h | h
    · have := dsElems_isE e k _ h
      cases this
    · rcases List.mem_cons.1 h with h | h
      · cases h
      · split at h
        · have := List.mem_singleton.1 h
          cases this
        · cases h

theorem sum_zero (l : List Fmt.Draw) (h : ∀ x ∈ l, tritN x = 0) : (l.map tritN).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem dsOf_trits (e : Fmt.Entry) (k : Fmt.Kind) : ((Fmt.dsOf e k).map tritN).sum = e.trits := by
  unfold Fmt.dsOf
  rw [List.map_append, List.map_append, List.sum_append, List.sum_append,
    sum_zero _ (fun x hx => by obtain rfl := (List.mem_replicate.1 hx).2; rfl),
    sum_zero _ (fun x hx => tritN_of_isE (dsElems_isE e k x hx)), List.map_cons, List.sum_cons]
  show 0 + (0 + (e.trits + _)) = _
  rw [sum_zero _ (fun x hx => by
    split at hx
    · obtain rfl := List.mem_singleton.1 hx
      rfl
    · cases hx)]
  omega

/-- What a written round's draws are, whatever the challenge: the seven-fold test's six clauses on
what is drawn. -/
structure FitsDrawn (e : Fmt.Entry) (k : Fmt.Kind) (D : Fmt.Drawn) : Prop where
  elems : e.drawNZ ≤ e.drawE → D.elems.length = e.drawE
  poss : D.poss.length = e.poss
  trits : D.trits.length = e.trits
  below : ∀ x ∈ D.poss, x < 2 ^ e.logN
  signs : ∀ t ∈ D.trits, t = -1 ∨ t = 0 ∨ t = 1
  nz : List.Forall₂ (fun d x => d = Fmt.Draw.elemNZ → x ≠ ((0, 0, 0) : Fmt.Ext)) (Fmt.dsElems e k)
      D.elems

theorem fitsDrawn (e : Fmt.Entry) (k : Fmt.Kind) (v : Run.Ch .two e k) :
    FitsDrawn e k (drawnOf .two e k v) := by
  have h1 := elems_forall (Fmt.dsOf e k) v
  rw [dsOf_isE] at h1
  obtain ⟨p1, p2⟩ := poss_all e.logN (Fmt.dsOf e k) v (dsOf_pos e k)
  obtain ⟨t1, t2⟩ := trits_all (Fmt.dsOf e k) v
  exact ⟨fun h => by rw [← dsElems_length e k h]; exact h1.length_eq.symm,
    by rw [← dsOf_isP e k]; exact p1,
    by rw [← dsOf_trits e k]; exact t1, p2, t2, h1⟩

/-- The same of the library's challenge kit at the release's field. -/
theorem fitsDrawn_ckP (e : Fmt.Entry) (k : Fmt.Kind) (c : (ckP .two).Ch e k) :
    FitsDrawn e k ((ckP .two).dr e k c) := fitsDrawn e k _

/-! ## What a written round shows, and roundsFit -/

open VerifiableInference.Desc in
/-- The items that a written round shows are those that are cut, but for the roots. -/
theorem gots_items : ∀ (l : List Fmt.Item) (x : PQ.PlainOf l),
    (PQ.PlainOf.gots l x).map itemOf = l.filter (· != .root)
  | [], _ => rfl
  | .root :: l, x => gots_items l x
  | .f :: l, x => congrArg (Fmt.Item.f :: ·) (gots_items l x.2)
  | .word :: l, x => congrArg (Fmt.Item.word :: ·) (gots_items l x.2)
  | .e :: l, x => congrArg (Fmt.Item.e :: ·) (gots_items l x.2)
  | .answer :: l, x => congrArg (Fmt.Item.answer :: ·) (gots_items l x.2)

/-- A written round is the declared round's: its entry, and the items that the entry cuts. -/
def IsOf (d : Fmt.DeclaredRound) (w : PQ.RD) : Prop := w.entry = d.entry ∧ w.items = d.items

open VerifiableInference.Desc

theorem zip_all_of_forall₂ : ∀ (l : List Fmt.Draw) (m : List Fmt.Ext),
    List.Forall₂ (fun d x => d = Fmt.Draw.elemNZ → x ≠ ((0, 0, 0) : Fmt.Ext)) l m →
    ((l.zip m).all fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true
  | [], [], _ => rfl
  | d :: l, x :: m, h => by
    cases h with
    | cons h1 h2 =>
      rw [List.zip_cons_cons, List.all_cons, zip_all_of_forall₂ l m h2, Bool.and_true]
      by_cases e : d = .elemNZ
      · have := h1 e
        simp [this]
      · simp [e]

/-- A written round is the declared round's, with the kind of its entry's name. -/
def IsOfK (d : Fmt.DeclaredRound) (w : PQ.RD) : Prop := IsOf d w ∧ Fmt.kindOf d.entry.name = some w.kind

/-- roundsFit holds, whatever the transcript, at written rounds that are the declared rounds' one by
one and have the kind of their entry's name (IsOfK), where no declared entry asks more elements
other than 0 than elements. -/
theorem roundsFit_written : ∀ (ds : List Fmt.DeclaredRound) (ws : List PQ.RD),
    List.Forall₂ IsOfK ds ws → (∀ d ∈ ds, d.entry.drawNZ ≤ d.entry.drawE) →
    ∀ τ : Iop.Tr (PQ.uL (ckP .two) ws), roundsFit ds (PQ.rvSL (ckP .two) ws τ) = true
  | [], [], _, _, _ => rfl
  | d :: ds, w :: ws, h, hz, (m, c, τ) => by
    cases h with
    | cons h1 h2 =>
      obtain ⟨⟨e1, e2⟩, e3⟩ := h1
      have F := fitsDrawn_ckP w.entry w.kind (Iop.GChal.old (b := w.entry.work) c)
      have ih := roundsFit_written ds ws h2 (fun x hx => hz x (List.mem_cons_of_mem _ hx)) τ
      generalize hD : (ckP .two).dr w.entry w.kind (Iop.GChal.old (b := w.entry.work) c) = D at F
      have a1 : ((PQ.PlainOf.gots w.items (Iop.GPlain.old (b := w.entry.work) m.2)).map itemOf ==
          d.items.filter (· != .root)) = true := by
        rw [gots_items, e2]
        exact beq_self_eq_true _
      have a2 : (D.elems.length == d.entry.drawE) = true := by
        rw [F.elems (by rw [e1]; exact hz d List.mem_cons_self), e1]
        exact beq_self_eq_true _
      have a3 : (D.poss.length == d.entry.poss) = true := by
        rw [F.poss, e1]
        exact beq_self_eq_true _
      have a4 : (D.trits.length == d.entry.trits) = true := by
        rw [F.trits, e1]
        exact beq_self_eq_true _
      have a5 : (D.poss.all (· < 2 ^ d.entry.logN)) = true := by
        rw [List.all_eq_true]
        intro x hx
        rw [← e1]
        exact decide_eq_true (F.below x hx)
      have a6 : (D.trits.all fun t => t == -1 || t == 0 || t == 1) = true := by
        rw [List.all_eq_true]
        intro t ht
        rcases F.signs t ht with rfl | rfl | rfl <;> rfl
      have a7 : drawsMarkedNonzeroHaveNonzeroWords d ⟨PQ.PlainOf.gots w.items (Iop.GPlain.old (b := w.entry.work) m.2), D⟩ = true
          := by
        unfold drawsMarkedNonzeroHaveNonzeroWords
        rw [e3, Option.any_some, ← e1]
        exact zip_all_of_forall₂ _ _ F.nz
      show (((PQ.PlainOf.gots w.items (Iop.GPlain.old (b := w.entry.work) m.2)).map itemOf ==
          d.items.filter (· != .root) &&
        ((ckP .two).dr w.entry w.kind (Iop.GChal.old (b := w.entry.work) c)).elems.length ==
          d.entry.drawE &&
        ((ckP .two).dr w.entry w.kind (Iop.GChal.old (b := w.entry.work) c)).poss.length ==
          d.entry.poss &&
        ((ckP .two).dr w.entry w.kind (Iop.GChal.old (b := w.entry.work) c)).trits.length ==
          d.entry.trits &&
        ((ckP .two).dr w.entry w.kind (Iop.GChal.old (b := w.entry.work) c)).poss.all
          (· < 2 ^ d.entry.logN) &&
        (((ckP .two).dr w.entry w.kind (Iop.GChal.old (b := w.entry.work) c)).trits.all
          fun t => t == -1 || t == 0 || t == 1) &&
        drawsMarkedNonzeroHaveNonzeroWords d ⟨PQ.PlainOf.gots w.items (Iop.GPlain.old (b := w.entry.work) m.2),
                                       (ckP .two).dr w.entry w.kind (Iop.GChal.old (b := w.entry.work) c)⟩) &&
        roundsFit ds (PQ.rvSL (ckP .two) ws τ)) = true
      rw [hD, a1, a2, a3, a4, a5, a6, a7, ih]
      rfl


/-! ## At the place's own rounds -/

open H2K.Pub (WR layW writtenOf) in
/-- The written rounds that layW lays are the declared rounds', one by one; and each has the kind of
its entry's name. -/
theorem layW_isOf : ∀ (ds : List Fmt.DeclaredRound) (sh : List Fmt.Shape) (ws : List WR),
    layW ds sh = some ws →
    List.Forall₂ (fun d (w : WR) => IsOf d w.rd ∧ Fmt.kindOf d.entry.name = some w.kind) ds ws
  | [], [], ws, h => by
    cases h
    exact List.Forall₂.nil
  | [], _ :: _, ws, h => by cases h
  | r :: rs, sh, ws, h => by
    unfold layW at h
    split at h
    · cases h
    · rename_i k hk
      split at h
      · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
        exact List.Forall₂.cons ⟨⟨rfl, rfl⟩, hk⟩ (layW_isOf rs sh l hl)
      · split at h
        · split at h
          · rename_i s t
            obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
            exact List.Forall₂.cons ⟨⟨rfl, rfl⟩, hk⟩ (layW_isOf rs t l hl)
          · cases h
        · cases h

theorem forall₂_map_right {α β γ : Type} (R : α → γ → Prop) (f : β → γ) :
    ∀ (l : List α) (m : List β), List.Forall₂ (fun a b => R a (f b)) l m → List.Forall₂ R l (m.map
        f)
  | [], [], _ => List.Forall₂.nil
  | _ :: l, _ :: m, h => by
    cases h with
    | cons h1 h2 => exact List.Forall₂.cons h1 (forall₂_map_right R f l m h2)

theorem roundsFit_cons (d : Fmt.DeclaredRound) (ds : List Fmt.DeclaredRound) (r : Fmt.RoundView) (rs : List Fmt.RoundView)
    :
    roundsFit (d :: ds) (r :: rs) = (roundsFit [d] [r] && roundsFit ds rs) := by
  show (_ && roundsFit ds rs) = ((_ && roundsFit [] []) && roundsFit ds rs)
  show (_ && roundsFit ds rs) = ((_ && true) && roundsFit ds rs)
  rw [Bool.and_true]

open H2K.Pub (WR layW writtenOf) in
/-- roundsFit holds at a first round that fits "BAT" followed by the place's written rounds behind
it, where no declared entry behind "BAT" asks more elements other than 0 than elements. -/
theorem roundsFit_behind (N : H2U.TestNums) (d0 : Fmt.DeclaredRound) (ds : List Fmt.DeclaredRound) (w0 : WR)
    (ws : List WR) (hd : H2U.roundsOfNums N = some (d0 :: ds)) (hw : writtenOf N = some (w0 :: ws))
    (hz : ∀ d ∈ ds, d.entry.drawNZ ≤ d.entry.drawE) (r0 : Fmt.RoundView) (h0 : roundsFit [d0] [r0] = true)
    (τ : Iop.Tr (PQ.uL (ckP .two) (ws.map WR.rd))) :
    roundsFit (d0 :: ds) (r0 :: PQ.rvSL (ckP .two) (ws.map WR.rd) τ) = true := by
  unfold writtenOf at hw
  rw [hd] at hw
  have h := layW_isOf (d0 :: ds) _ (w0 :: ws) hw
  cases h with
  | cons _ h2 =>
    rw [roundsFit_cons, h0, Bool.true_and]
    exact roundsFit_written ds _ (forall₂_map_right IsOfK WR.rd ds ws h2) hz τ

open H2K.Pub (WR layW writtenOf) in
/-- At the place: the declared rounds off the place's numbers, and all its written rounds ("BAT"'s
too): roundsFit holds, whatever the transcript. -/
theorem roundsFit_place (N : H2U.TestNums) (ds : List Fmt.DeclaredRound) (ws : List WR)
    (hd : H2U.roundsOfNums N = some ds) (hw : writtenOf N = some ws)
    (hz : ∀ d ∈ ds, d.entry.drawNZ ≤ d.entry.drawE)
    (τ : Iop.Tr (PQ.uL (ckP .two) (ws.map WR.rd))) :
    roundsFit ds (PQ.rvSL (ckP .two) (ws.map WR.rd) τ) = true := by
  unfold writtenOf at hw
  rw [hd] at hw
  exact roundsFit_written ds _ (forall₂_map_right IsOfK WR.rd ds ws (layW_isOf ds _ ws hw)) hz τ

end H2K.Fit
