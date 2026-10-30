-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TablesAnswer.lean: THE TEXT THAT MAKES THE OUTPUT HEAD's TABLES OF READS
(Johnson/Desc/K8/ReadsQuiet.lean: tables) ANSWERS: from one test with code on public numbers
(Law/TablesPlanCode.lean: tabsPlanB) and four facts on the sizes of what was heard. The first stone
of "the silent reader answers behind the accept of the head's own sub-protocol". Statements and
proofs.

  added_alike      whether a table can be added, where the next begins, and the table of tables hang
                   on no weight.
  fold_alike       so for a list of tables.
  tables_end       the text's last three steps, at any list with the skeleton's public halves.
  tables_answers   MAIN: tabsPlanB; the squares' point has at least la coordinates; the norm's
                   columns' point at least ls; the norm's positions' point just lt; the planes'
                   number of rows fits the heard shape: the text answers, and its table of tables
                   (name, first entry, length) is tabsOfPlan's.

WHAT IT IS NOT. An implication. tabsPlanB HAS RUN NOWHERE. The four sizes are premises here. Nothing
on what the tables hold. Nothing on soundness.
LETTERS. t0, tt stand under "there is": tied by tabsOfPlan's and the text's own answers.

-/
import Mathlib
import Johnson.Desc.K8.ReadsQuiet
import Johnson.Desc.Kinds.Law.TablesPlanCode

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (TMat HFun)
open OnBytes.Model.Head (Shape HL HPlanH2 Tables)
open VerifiableInference.Desc (need named)

/-- The second component of the fold inside tableAdded hangs on no weight and no list. -/
theorem added_p (mats : Array TMat) (M0 Lf : Nat) (phi phi' : Array E) :
    ∀ (l : List Nat) (s s' : Array HFun × Nat), s.2 = s'.2 →
      (l.foldl (fun (s : Array HFun × Nat) q =>
        (s.1.push { mat := M0 + q, len := Lf, phi := phi, tree := 2, start := s.2 },
          s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s).2 =
      (l.foldl (fun (s : Array HFun × Nat) q =>
        (s.1.push { mat := M0 + q, len := Lf, phi := phi', tree := 2, start := s.2 },
          s.2 + (mats.getD (M0 + q) {}).k * ((mats.getD (M0 + q) {}).m / Lf))) s').2
  | [], _, _, h => h
  | q :: l, s, s', h => by
    rw [List.foldl_cons, List.foldl_cons]
    exact added_p mats M0 Lf phi phi' l _ _ (by simp only [h])

/-- **Whether a table can be added, and where the next begins, hang on no weight.** -/
theorem added_alike (mats : Array TMat) (t t' u' : Tables) (M0 parts Lf : Nat)
    (phi phi' : Array E) (nm : String) (hp : t.p = t'.p) (hb : t.tab = t'.tab)
    (h : Own.tableAdded mats t' M0 parts Lf phi' nm = some u') :
    ∃ u, Own.tableAdded mats t M0 parts Lf phi nm = some u ∧ u.p = u'.p ∧ u.tab = u'.tab := by
  have e := added_p mats M0 Lf phi phi' (List.range parts) (t.funs, t.p) (t'.funs, t'.p) hp
  unfold Own.tableAdded at h ⊢
  simp only at h ⊢
  rw [e, hp, hb]
  split at h
  · cases h
  · rename_i hne
    rw [if_neg hne]
    obtain rfl := Option.some.inj h
    exact ⟨_, rfl, rfl, rfl⟩

/-- So for a list of tables. -/
theorem fold_alike (mats : Array TMat) :
    ∀ (asks : List (Nat × Nat × Nat × Array E × String)) (t t' u' : Tables), t.p = t'.p →
      t.tab = t'.tab →
      (asks.map fun a => (a.1, a.2.1, a.2.2.1, a.2.2.2.2)).foldlM
        (fun t (a : Nat × Nat × Nat × String) =>
          Own.tableAdded mats t a.1 a.2.1 a.2.2.1 #[] a.2.2.2) t' = some u' →
      ∃ u, asks.foldlM
        (fun t a => Own.tableAdded mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) t = some u ∧
        u.p = u'.p ∧ u.tab = u'.tab
  | [], t, t', u', hp, hb, h => by
    obtain rfl : t' = u' := Option.some.inj h
    exact ⟨t, rfl, hp, hb⟩
  | a :: asks, t, t', u', hp, hb, h => by
    rw [List.map_cons, List.foldlM_cons] at h
    obtain ⟨v', hv', h'⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨v, hv, hpv, hbv⟩ :=
      added_alike mats t t' v' a.1 a.2.1 a.2.2.1 a.2.2.2.1 #[] a.2.2.2.2 hp hb hv'
    obtain ⟨u, hu, hpu⟩ := fold_alike mats asks v v' u' hpv hbv h'
    refine ⟨u, ?_, hpu⟩
    rw [List.foldlM_cons]
    exact Option.bind_eq_some_iff.2 ⟨v, hv, hu⟩

theorem named_at_some {α : Type} (s : String) (a : α) : named s (some a) = .ok a := rfl

theorem need_at_true (s : String) : need s true = .ok () := rfl

theorem bind_at_ok {α β : Type} (a : α) (f : α → Except String β) :
    (Except.ok a >>= f : Except String β) = f a := rfl

/-- The text's last three steps, at any list of tables with the skeleton's public halves. -/
theorem tables_end (mats : Array TMat) (sk : List (Nat × Nat × Nat × String)) (n : Nat)
    (t0 : Tables)
    (h0 : sk.foldlM (fun t a => Own.tableAdded mats t a.1 a.2.1 a.2.2.1 #[] a.2.2.2) {} = some t0)
    (hp0 : t0.p = n) (asks : List (Nat × Nat × Nat × Array E × String))
    (he : (asks.map fun a => (a.1, a.2.1, a.2.2.1, a.2.2.2.2)) = sk) (s1 s2 : String) :
    ∃ tt, (named s1 (asks.foldlM
        (fun t a => Own.tableAdded mats t a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) {}) >>= fun t =>
      need s2 (t.p == n) >>= fun _ => (pure t : Except String Tables)) = .ok tt ∧
      tt.tab = t0.tab := by
  subst he
  obtain ⟨u, hu, hpu, hbu⟩ := fold_alike mats asks {} {} t0 rfl rfl h0
  refine ⟨u, ?_, hbu⟩
  rw [hu, named_at_some, bind_at_ok, hpu, hp0, beq_self_eq_true, need_at_true, bind_at_ok]
  rfl

/-- **THE TEXT ANSWERS.** -/
theorem tables_answers (h : Shape) (L : HL) (hp : HPlanH2) (cov : OnBytes.Model.Head.Covered)
    (x : OnBytes.Model.Head.Heard)
    (hB : tabsPlanB h L hp = true) (h1 : h.la ≤ x.wpl.r.size)
    (h2 : h.ls ≤ (OnBytes.Model.Head.zjOf L x.g1 x.qN).size)
    (h3 : x.tN.r.size = h.lt) (h4 : 5 ≤ h.lmbH) (h5 : h.lmbH ≤ x.g1.shape.kT + 5) :
    ∃ t0, tabsOfPlan h hp = some t0 ∧
      ∃ tt, K8.ReadsQuiet.tables h L hp cov x = .ok tt ∧ tt.tab = t0.tab := by
  unfold tabsPlanB at hB
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hB
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hB
  obtain ⟨qFC, hFC⟩ := Option.isSome_iff_exists.1 c3
  obtain ⟨qROW, hROW⟩ := Option.isSome_iff_exists.1 c4
  obtain ⟨t0, ht0, hp0⟩ := (Option.any_eq_true _ _).1 c5
  have hZ : ∃ ZV, Own.tailOf x.wpl.r h.la = some ZV := by
    unfold Own.tailOf Own.cutTail
    rw [if_neg (by omega)]
    exact ⟨_, rfl⟩
  have hl : ∃ lowN, Own.cutTail (OnBytes.Model.Head.zjOf L x.g1 x.qN) h.ls = some lowN ∧
      lowN.2.size = h.ls := by
    unfold Own.cutTail
    rw [if_neg (by omega)]
    refine ⟨_, rfl, ?_⟩
    simp only [Array.size_extract]
    omega
  have hb : ∀ e, ∃ b, Own.planeWeights x.g1 h.lmbH e = some b := by
    intro e
    unfold Own.planeWeights
    simp only
    rw [if_neg (by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)]
    exact ⟨_, rfl⟩
  obtain ⟨ZV, hZV⟩ := hZ
  obtain ⟨lowN, hlow, hls⟩ := hl
  obtain ⟨b0, hb0⟩ := hb 0
  obtain ⟨b1, hb1⟩ := hb 1
  have hY : ((OnBytes.Model.longPoint lowN.2 x.tN.r).size == h.la && h.la == h.ls + h.lt) =
      true := by
    unfold OnBytes.Model.longPoint
    rw [Array.size_append, hls, h3, c2]
    simp
  have hp0' : t0.p = hp.nU.getD 2 0 := by simpa using hp0
  refine ⟨t0, ht0, ?_⟩
  unfold K8.ReadsQuiet.tables
  simp only [c1, Bool.not_false, need_at_true, hZV, hlow, hFC, hROW, hb0, hb1, named_at_some, hY,
    bind_at_ok]
  exact tables_end hp.tl.mats (skeleton h) _ t0 ht0 hp0' _ rfl _ _

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.tables_answers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.fold_alike
#print axioms VerifiableInference.Desc.Kinds.Head.Law.added_alike
