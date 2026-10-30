-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/BlindPub.lean: THE SMALLNESS TEST's DRAW AND THE PUBLIC TESTS OF THE TABLE OF
JOINTS: every public test that stands open, or tied to an open item, in front of the draw has ONE
VALUE at the verifier's state in front of the draw's yes and behind it. Definitions and theorems.

Why. The draw's yes turns two fields of the open segment's tail alone: the drawn matrix and each
matrix's first column (`Drawn`, Johnson/Desc/First/K8/TieRides.lean). What the promise asks behind
the draw is what it asked in front, and one test more. That the tests which stay do not read these
two fields is owed by the draw's files, test by test.
  `TlBlind f`: f has one value at s and at t wherever `Drawn s t`.
  `drawn_ind`: the three forms of a draw's yes: a feed-forward, an attention or the output head's
    opened segment.
  `blind_fork` ... `blind_tlHeard`: the state's readers: the ledger, the link's context, the
    statement, the book, the roots, the owed count, the chain's results, what the lookups heard.
  `blind_ledgerB` ... `blind_hasRow`: twelve public tests, each by its own text.
  `blind_segAt`, `blind_mergeOf`, `blind_formsIn`: the test that is tied to an open run of forms,
    UNDER "the run's reader is blind".
  `k8Sort m pc`: the sorts of public item that stand open in front of the draw in segment m; of
    the tests tied to runs of forms: those of the segment's pieces in front of the draw's (k < pc).
  `pubAll_blind`: **the composed public test (`pubAll`, Johnson/Desc/First/PubAll.lean) over the
    base "false" is blind at every item of these sorts**, under the like premise on the earlier
    runs.
Limits. That these sorts are all that is open at the draw's borders is a closed fact on the table,
shown elsewhere. Which runs' readers are blind is not shown here. Nothing on soundness or on hiding.

-/
import Johnson.Desc.First.K8.TieRides
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First (S Pub pubAll PubData ledgerB freeAboveB unheardB)

/-- A function of the verifier's state has one value in front of the draw's yes and behind it. -/
def TlBlind {α : Type} (f : S → α) : Prop := ∀ s t, Drawn s t → f t = f s

/-- The three forms of a draw's yes. -/
theorem drawn_ind {motive : S → S → Prop}
    (hl : ∀ (s : S) a mm f, s.here = .lay a →
      motive s { s with here := .lay { a with tl := { a.tl with cfF := mm, cfFirst := f } } })
    (ha : ∀ (s : S) a mm f, s.here = .att a →
      motive s { s with here := .att { a with tl := { a.tl with cfF := mm, cfFirst := f } } })
    (hh : ∀ (s : S) a mm f, s.here = .head a → a.opened = true →
      motive s { s with here := .head { a with tl := { a.tl with cfF := mm, cfFirst := f } } })
    {s t : S} (h : Drawn s t) : motive s t := by
  obtain ⟨tl, mm, f, ht, rfl⟩ := h
  unfold S.tl? at ht
  unfold S.putTl
  cases e : s.here with
  | lay a =>
    rw [e] at ht
    obtain rfl : a.tl = tl := Option.some.inj ht
    exact hl s a mm f e
  | att a =>
    rw [e] at ht
    obtain rfl : a.tl = tl := Option.some.inj ht
    exact ha s a mm f e
  | head a =>
    rw [e] at ht
    by_cases ho : a.opened = true
    · dsimp only at ht ⊢
      rw [if_pos ho] at ht ⊢
      obtain rfl : a.tl = tl := Option.some.inj ht
      exact hh s a mm f e ho
    · simp [ho] at ht
  | between => simp [e] at ht
  | fin a => simp [e] at ht
  | mem a => simp [e] at ht

theorem blind_fork : TlBlind S.fork? := fun s t h => by
  obtain ⟨tl, mm, f, _, rfl⟩ := h
  exact putTl_fork s _

theorem blind_link : TlBlind S.link? := fun s t h => by
  obtain ⟨tl, mm, f, _, rfl⟩ := h
  exact putTl_link s _

theorem blind_st : TlBlind S.st := fun s t h => by
  obtain ⟨tl, mm, f, _, rfl⟩ := h
  exact (putTl_rest s _).1

theorem blind_book : TlBlind S.book := fun s t h => by
  obtain ⟨tl, mm, f, _, rfl⟩ := h
  exact (putTl_rest s _).2.1

theorem blind_roots : TlBlind S.roots := fun s t h => by
  obtain ⟨tl, mm, f, _, rfl⟩ := h
  exact (putTl_rest s _).2.2.1

theorem blind_rowsOwed : TlBlind S.rowsOwed := fun s t h => by
  obtain ⟨tl, mm, f, _, rfl⟩ := h
  exact (putTl_rest s _).2.2.2.1

theorem blind_out : TlBlind S.out := fun s t h => by
  obtain ⟨tl, mm, f, _, rfl⟩ := h
  exact (putTl_rest s _).2.2.2.2.2.2.1

theorem blind_lookHeard : TlBlind S.lookHeard? := fun s t h => by
  refine drawn_ind (motive := fun s t => t.lookHeard? = s.lookHeard?) ?_ ?_ ?_ h <;>
    intros <;> simp_all [S.lookHeard?]

theorem blind_heard5 : TlBlind S.heard5? := fun s t h => by
  refine drawn_ind (motive := fun s t => t.heard5? = s.heard5?) ?_ ?_ ?_ h <;>
    intros <;> simp_all [S.heard5?]

/-- What is heard at the digits' seat. -/
theorem blind_tlHeard (s t : S) (h : Drawn s t) :
    (t.tl?.bind fun x => x.heard) = s.tl?.bind fun x => x.heard := by
  refine drawn_ind (motive := fun s t =>
    (t.tl?.bind fun x => x.heard) = s.tl?.bind fun x => x.heard) ?_ ?_ ?_ h <;>
    intros <;> simp_all [S.tl?]

theorem blind_ledgerB : TlBlind ledgerB := fun s t h => by
  unfold ledgerB
  rw [blind_fork s t h]

theorem blind_freeAboveB (n : Nat) : TlBlind (freeAboveB n) := fun s t h => by
  unfold freeAboveB
  rw [blind_fork s t h]

theorem blind_unheardB : TlBlind unheardB := fun s t h => by
  unfold unheardB
  rw [blind_out s t h]

theorem blind_linkFreshC (d : Look.K3Data) (m : Nat) : TlBlind (Look.linkFreshC d m) :=
  fun s t h => by
  unfold Look.linkFreshC
  rw [blind_tlHeard s t h, blind_link s t h]

theorem blind_heardAt (dg : Bool) : TlBlind (VerifiableInference.Desc.K3.heardAt dg) :=
  fun s t h => by
  unfold VerifiableInference.Desc.K3.heardAt
  rw [blind_tlHeard s t h, blind_lookHeard s t h]

theorem blind_k3OnIn (p : Look.P) : TlBlind (VerifiableInference.Desc.K3.k3OnIn p) :=
  fun s t h => by
  unfold VerifiableInference.Desc.K3.k3OnIn
  rw [blind_heardAt p.digits s t h, blind_rowsOwed s t h, blind_fork s t h]

theorem blind_k3OnOut (p : Look.P) : TlBlind (VerifiableInference.Desc.K3.k3OnOut p) :=
  fun s t h => by
  unfold VerifiableInference.Desc.K3.k3OnOut
  rw [blind_heardAt p.digits s t h, blind_fork s t h]

theorem blind_lookInC (d : Look.K3Data) (m : Nat) (dg : Bool) : TlBlind (Look.lookInC d m dg) :=
  fun s t h => by
  unfold Look.lookInC
  simp only [blind_k3OnIn _ s t h, blind_link s t h]

theorem blind_lookOutC (d : Look.K3Data) (m : Nat) (dg : Bool) : TlBlind (Look.lookOutC d m dg) :=
  fun s t h => by
  unfold Look.lookOutC
  simp only [blind_k3OnOut _ s t h]

theorem blind_sentIsB (d : FillSent.SentData) (m : Nat) : TlBlind (FillSent.sentIsB d m) :=
  fun s t h => by
  unfold FillSent.sentIsB
  rw [blind_link s t h]

theorem blind_okThereB (g : Att.P.Geo) : TlBlind (H2K5.Door.okThereB g) := fun s t h => by
  unfold H2K5.Door.okThereB
  rw [blind_fork s t h, blind_heard5 s t h]

theorem blind_plainThereB (a b : Nat) : TlBlind (H2K5.Door.plainThereB a b) := fun s t h => by
  unfold H2K5.Door.plainThereB
  rw [blind_fork s t h, blind_heard5 s t h]

theorem blind_indexIsC (n : Nat) : TlBlind (VerifiableInference.Desc.K13.indexIsC n) :=
  fun s t h => by
  unfold VerifiableInference.Desc.K13.indexIsC
  rw [blind_out s t h]

theorem blind_indexThereC : TlBlind VerifiableInference.Desc.K13.indexThereC := fun s t h => by
  unfold VerifiableInference.Desc.K13.indexThereC
  rw [blind_out s t h, blind_st s t h]

theorem blind_leftOf : TlBlind Johnson.Desc.First.Walk.Law.leftOf := fun s t h => by
  refine drawn_ind (motive := fun s t =>
    Johnson.Desc.First.Walk.Law.leftOf t = Johnson.Desc.First.Walk.Law.leftOf s) ?_ ?_ ?_ h <;>
    intros <;> simp_all [Johnson.Desc.First.Walk.Law.leftOf, Johnson.Desc.First.Walk.leftLay,
      VerifiableInference.Desc.First.Close.leftHead]

theorem blind_hasRow (lay : OnBytes.Model.WsLay) (n : Nat) (lin : OnBytes.Params.LinShape) :
    TlBlind (Johnson.Desc.First.Walk.Law.hasRow lay n lin) := fun s t h => by
  unfold Johnson.Desc.First.Walk.Law.hasRow Johnson.Desc.First.Walk.Law.rowAt
    Johnson.Desc.First.Walk.Law.rowBy
  rw [blind_leftOf s t h, blind_out s t h, blind_st s t h]

theorem blind_mergeOf : TlBlind VerifiableInference.Desc.K9.mergeOf := fun s t h => by
  refine drawn_ind (motive := fun s t =>
    VerifiableInference.Desc.K9.mergeOf t = VerifiableInference.Desc.K9.mergeOf s) ?_ ?_ ?_ h <;>
    intros <;> simp_all [VerifiableInference.Desc.K9.mergeOf]

theorem blind_segAt : TlBlind VerifiableInference.Desc.K9.segAt? := fun s t h => by
  refine drawn_ind (motive := fun s t =>
    VerifiableInference.Desc.K9.segAt? t = VerifiableInference.Desc.K9.segAt? s) ?_ ?_ ?_ h <;>
    intros <;> simp_all [VerifiableInference.Desc.K9.segAt?, S.link?, S.fork?, S.tl?,
      VerifiableInference.Desc.K9.owedOf, VerifiableInference.Desc.K9.usedOf,
      VerifiableInference.Desc.K9.laidOf, OnBytes.Model.HTailF2.stepF]

/-- The public test that is tied to an open run of forms, where the run's reader is blind. -/
theorem blind_formsIn (Rd : VerifiableInference.Desc.K9.Readers) (own : List (Nat × Nat))
    (piece : Nat) (run : String) (hR : TlBlind (Rd.forms piece run)) :
    TlBlind (VerifiableInference.Desc.K9.formsIn Rd own piece run) := fun s t h => by
  unfold VerifiableInference.Desc.K9.formsIn
  rw [blind_segAt s t h, hR s t h, blind_mergeOf s t h]

/-! ## The composed public test, at the sorts of item that are open at the draw's border -/

theorem all_congr' {α : Type} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- Where no part answers at a name of the attention caller's, the composed test is the base's. -/
theorem pubAll_k5_else {P : Type} (D : PubData) (m' : Nat) (n : String)
    (hn : n = "K5.okAt" ∨ n = "K5.plain") (ha : ¬ D.d5.isAtt m' = true) (a : P × S) :
    pubAll D (fun _ _ => false) (.more (some m') n) a = false := by
  have hf : D.d5.isAtt m' = false := by simpa using ha
  rcases hn with rfl | rfl
  · exact pubAll_else D _ _ rfl rfl rfl rfl rfl rfl (by simp [H2K5.Door.k5Item, hf])
      (by simp [FillSent.sentItem]) (by simp [FillSent.sent1Item]) (by simp [FillBare.leftItem]) rfl
      a
  · exact pubAll_else D _ _ rfl rfl rfl rfl rfl rfl (by simp [H2K5.Door.k5Item, hf])
      (by simp [FillSent.sentItem]) (by simp [FillSent.sent1Item]) (by simp [FillBare.leftItem]) rfl
      a

/-- The sorts of public item that stand open in front of the draw in segment m (pc: the draw's
piece). -/
def k8Sort (m pc : Nat) : Pub → Bool
  | .unheard => true
  | .ledger _ => true
  | .linkFresh _ => true
  | .freeAbove _ => true
  | .lookOut _ _ => true
  | .lookIn _ _ => true
  | .leftOn _ => true
  | .indexIs => true
  | .indexThere => true
  | .hasRow _ => true
  | .more (some _) n => n == "frame.sentIs1" || n == "K5.okAt" || n == "K5.plain"
  | .formsIn m' k _ => m' == m && decide (k < pc)
  | _ => false

theorem pubAll_blind {P : Type} (D : PubData) (m pc : Nat) (q : Pub) (hq : k8Sort m pc q = true)
    (hF : ∀ k r, k < pc → ∀ p ∈ D.runs m k r,
      TlBlind fun s => if D.ah p.1 p.2 then
          VerifiableInference.Desc.K9.formsInA (D.Rd m) (D.N.sent m) (D.N.group m) p.1 p.2 s
        else VerifiableInference.Desc.K9.formsIn (D.Rd m) (D.N.group m) p.1 p.2 s)
    (z : P) : TlBlind fun s => pubAll D (fun _ _ => false) q (z, s) := by
  intro s t h
  cases q with
  | unheard => exact blind_unheardB s t h
  | ledger m' => exact blind_ledgerB s t h
  | linkFresh m' => exact blind_linkFreshC _ _ s t h
  | freeAbove m' =>
    show ((D.nsOf m').any fun n => freeAboveB n t) = (D.nsOf m').any fun n => freeAboveB n s
    simp only [blind_freeAboveB _ s t h]
  | lookOut m' pc' =>
    cases e : Look.k3SortAt D.d3.X m' pc' with
    | some dg =>
      show pubAll D _ (.lookOut m' pc') (z, t) = pubAll D _ (.lookOut m' pc') (z, s)
      rw [pubAll_lookOut D _ m' pc' dg e, pubAll_lookOut D _ m' pc' dg e]
      exact blind_lookOutC _ _ _ s t h
    | none =>
      show (match Look.k3SortAt D.d3.X m' pc' with
        | some dg => Look.lookOutC D.d3 m' dg t
        | none => false) = (match Look.k3SortAt D.d3.X m' pc' with
        | some dg => Look.lookOutC D.d3 m' dg s
        | none => false)
      rw [e]
  | lookIn m' pc' =>
    cases e : Look.k3SortAt D.d3.X m' pc' with
    | some dg =>
      show pubAll D _ (.lookIn m' pc') (z, t) = pubAll D _ (.lookIn m' pc') (z, s)
      rw [pubAll_lookIn D _ m' pc' dg e, pubAll_lookIn D _ m' pc' dg e]
      exact blind_lookInC _ _ _ s t h
    | none =>
      show (match Look.k3SortAt D.d3.X m' pc' with
        | some dg => Look.lookInC D.d3 m' dg t
        | none => false) = (match Look.k3SortAt D.d3.X m' pc' with
        | some dg => Look.lookInC D.d3 m' dg s
        | none => false)
      rw [e]
  | leftOn m' => rfl
  | indexIs => exact blind_indexIsC _ s t h
  | indexThere => exact blind_indexThereC s t h
  | hasRow m' => exact blind_hasRow _ _ _ s t h
  | more sg n =>
    cases sg with
    | none => exact nomatch hq
    | some m' =>
      simp only [k8Sort, Bool.or_eq_true, beq_iff_eq] at hq
      rcases hq with (rfl | rfl) | rfl
      · show pubAll D _ (.more (some m') "frame.sentIs1") (z, t) = pubAll D _ _ (z, s)
        rw [pubAll_more_sentIs1, pubAll_more_sentIs1]
        exact blind_sentIsB _ _ s t h
      · by_cases ha : D.d5.isAtt m' = true
        · show pubAll D _ (.more (some m') "K5.okAt") (z, t) = pubAll D _ _ (z, s)
          rw [pubAll_more_okAt D _ m' ha, pubAll_more_okAt D _ m' ha]
          simp only [blind_okThereB _ s t h]
        · show pubAll D _ (.more (some m') "K5.okAt") (z, t) = pubAll D _ _ (z, s)
          rw [pubAll_k5_else D m' _ (Or.inl rfl) ha, pubAll_k5_else D m' _ (Or.inl rfl) ha]
      · by_cases ha : D.d5.isAtt m' = true
        · show pubAll D _ (.more (some m') "K5.plain") (z, t) = pubAll D _ _ (z, s)
          rw [pubAll_more_plain D _ m' ha, pubAll_more_plain D _ m' ha]
          simp only [blind_plainThereB _ _ s t h]
        · show pubAll D _ (.more (some m') "K5.plain") (z, t) = pubAll D _ _ (z, s)
          rw [pubAll_k5_else D m' _ (Or.inr rfl) ha, pubAll_k5_else D m' _ (Or.inr rfl) ha]
  | formsIn m' k r =>
    simp only [k8Sort, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hq
    obtain ⟨rfl, hk⟩ := hq
    show pubAll D _ (.formsIn m' k r) (z, t) = pubAll D _ (.formsIn m' k r) (z, s)
    rw [pubAll_formsIn, pubAll_formsIn]
    exact all_congr' _ _ _ fun p hp => hF k r hk p hp s t h
  | _ => exact nomatch hq

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.drawn_ind
#print axioms VerifiableInference.Desc.First.K8.blind_formsIn
#print axioms VerifiableInference.Desc.First.K8.pubAll_blind
