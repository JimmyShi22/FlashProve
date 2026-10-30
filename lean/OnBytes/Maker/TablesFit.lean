-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TablesFit.lean: at three chains that the program's reader has read, the tests of
OnBytes/Maker/Tables.lean on the file as read pass, if the plain data fit the descriptions under
which the chains were read.

Statements and proofs. The tables of a whole file ask that the chains as read fit the plain data
(`fitsW`), that every opening passes its tests (`rowOK`, `storedOK`) and that whole paths are there
(`fullPaths`). What a reading gives stands in OnBytes/Maker/ReadFacts.lean (`RoundRead`) and
OnBytes/Maker/ReadWalks.lean (`Walked`), in the letters of the description. What ties a description
to the data is a premise here, `DataFits`: it speaks of no file.

Main names:
  `TreeIs W s j`: the tree number j of the table has the shape s.
  `keyOf x`: what `DataFits` sees of a description's round: the shapes of the trees that it opens,
    and its stored tables.
  `DataFits W xs ds`: round by round the data's round has the description's stored tables, and opens
    as many trees, each of the description's shape by the table.
  `round_fit`, `chain_fit`: one round, one chain.
  `own_walked`, `stored_walked`: whole paths at the members of `ownRows` and `storedRows`.
  `tables_fit`: the three chains of a file.
  `tabsWFull_of_read`, `extWFull_of_read`: so the tables with whole paths return, under `DataFits`
    at the three chains, one number of bytes of a salt, one depth and the item 0 of the stored
    tables, a run's value in each chain, and `SameTwice`.
Limits: `DataFits`, the one number of bytes of a salt, and the stored tables' depth and item are
premises on descriptions and data: they are not proved here. `SameTwice` is a hypothesis that no
reading gives. Nothing is said of what the tables hold. Nothing on soundness.


-/
import OnBytes.Maker.TablesReturn
import OnBytes.Maker.ReadWalks

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run (OpenB Row3 pathFrom)

/-- The tree number j of the table has the shape s. -/
def TreeIs (W : Three.Whole) (s : Fmt.Shape) (j : ℕ) : Prop :=
  ∃ t, W.table[j]? = some t ∧ t.shape = s

/-- What `DataFits` sees of a description's round. -/
def keyOf (x : Fmt.Round × List Fmt.Stored) : List Fmt.Shape × List Fmt.Stored :=
  (x.1.opens.map (·.1), x.2)

/-- One round. -/
def RoundData (W : Three.Whole) (k : List Fmt.Shape × List Fmt.Stored) (d : Three.RDL) : Prop :=
  k.2 = d.stored ∧ List.Forall₂ (TreeIs W) k.1 d.opens

/-- **The plain data fit a description's rounds.** -/
def DataFits (W : Three.Whole) (xs : List (Fmt.Round × List Fmt.Stored)) (ds : List Three.RDL) :
    Prop :=
  List.Forall₂ (RoundData W) (xs.map keyOf) ds

/-- The stored tables of the data's rounds have the depth a and stand under the item 0. -/
def StoredAt (a : ℕ) (ds : List Three.RDL) : Prop :=
  ∀ d ∈ ds, ∀ t ∈ d.stored, t.sh.a = a ∧ t.item = 0

/-! ## Lists -/

/-- Two relations from one list, laid together. -/
theorem forall₂_join {α β γ : Type} {A : α → β → Prop} {B : α → γ → Prop} :
    ∀ {l : List α} {m : List β} {n : List γ}, List.Forall₂ A l m → List.Forall₂ B l n →
    List.Forall₂ (fun c b => ∃ a, B a c ∧ A a b) n m
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h t, .cons h' t' => .cons ⟨_, h', h⟩ (forall₂_join t t')

/-! ## One round -/

/-- What the tests ask of one round. -/
def RoundFit (W : Three.Whole) (sb a : ℕ) (d : Three.RDL) (ro : Fmt.RoundOut) : Prop :=
  ro.opens.length = d.stored.length + d.opens.length ∧
    (∀ x ∈ d.opens.zip (ro.opens.drop d.stored.length), rowOK W sb x = true) ∧
    ∀ x ∈ d.stored.zip ro.opens, storedOK a x = true

theorem round_fit (W : Three.Whole) (a : ℕ) (P : Fmt.Plan) (x : Fmt.Round × List Fmt.Stored)
    (ro : Fmt.RoundOut) (d : Three.RDL) (H : RoundRead P x ro) (F : RoundData W (keyOf x) d)
    (hs : ∀ t ∈ d.stored, t.sh.a = a ∧ t.item = 0) : RoundFit W P.salt a d ro := by
  obtain ⟨cs, co, ho, h1, h2⟩ := H.opens
  obtain ⟨f1, f2⟩ := F
  have f1' : x.2 = d.stored := f1
  have f2' : List.Forall₂ (fun (s : Fmt.Shape × Fmt.Src) j => TreeIs W s.1 j) x.1.opens d.opens :=
    List.forall₂_map_left_iff.1 f2
  rw [f1'] at h1
  have l1 : d.stored.length = cs.length := h1.length_eq
  have l2 : d.opens.length = co.length := f2'.length_eq.symm.trans h2.length_eq
  refine ⟨by rw [ho, List.length_append, l1, l2], ?_, ?_⟩
  · rintro ⟨j, y⟩ hx
    rw [ho, List.drop_left' l1.symm] at hx
    obtain ⟨s, ⟨t, ht, hsh⟩, hy⟩ := (List.forall₂_iff_zip.1 (forall₂_join h2 f2')).2 hx
    unfold rowOK
    show (match W.table[j]? with
      | none => false
      | some t => y.1 == t.shape && (asOpenB y).ok P.salt t.shape.W) = true
    rw [ht]
    show (y.1 == t.shape && (asOpenB y).ok P.salt t.shape.W) = true
    have e1 : y.1 = t.shape := hy.sh.trans hsh.symm
    have e2 : (asOpenB y).ok P.salt t.shape.W = true := by
      have := hy.okb
      rw [← hy.sh] at this
      rw [← e1]
      exact this
    rw [e2, e1]
    simp
  · rintro ⟨t, y⟩ hx
    rw [ho, zip_append_more _ _ _ l1] at hx
    have hy := (List.forall₂_iff_zip.1 h1).2 hx
    obtain ⟨ha, hi⟩ := hs t (List.of_mem_zip hx).1
    show (y.1 == t.sh && t.sh.a == a && t.item == 0 && (asOpenB y).ok t.salt t.sh.W) = true
    have e2 : (asOpenB y).ok t.salt t.sh.W = true := by
      have := hy.okb
      show (⟨y.1.a, _, _, _, _⟩ : OpenB).ok t.salt t.sh.W = true
      rw [hy.sh]
      exact this
    rw [e2, hy.sh, ha, hi]
    simp

/-! ## One chain -/

theorem rounds_fit (W : Three.Whole) (a : ℕ) (P : Fmt.Plan) :
    ∀ {xs : List (Fmt.Round × List Fmt.Stored)} {ros : List Fmt.RoundOut} {ds : List Three.RDL},
    List.Forall₂ (RoundRead P) xs ros → DataFits W xs ds → StoredAt a ds →
    List.Forall₂ (RoundFit W P.salt a) ds ros
  | _, _, _, .nil, F, _ => by
    cases F
    exact .nil
  | x :: xs, ro :: ros, _, .cons h t, F, hs => by
    unfold DataFits at F
    rw [List.map_cons] at F
    cases F with
    | cons f ft =>
      exact .cons (round_fit W a P x ro _ h f (hs _ List.mem_cons_self))
        (rounds_fit W a P t ft fun d hd => hs d (List.mem_cons_of_mem _ hd))

/-- **One chain**: the chain as read fits the data; every opening passes its tests. -/
theorem chain_fit (W : Three.Whole) (sb a : ℕ) (ds : List Three.RDL) (o : Fmt.ChainOut)
    (H : List.Forall₂ (RoundFit W sb a) ds o.rounds.toList) :
    roundsFit ds o = true ∧ (∀ x ∈ ownRows ds o, rowOK W sb x = true) ∧
      ∀ x ∈ storedRows ds o, storedOK a x = true := by
  have Z : ∀ d ro, (d, ro) ∈ ds.zip o.rounds.toList → RoundFit W sb a d ro :=
    fun _ _ h => (List.forall₂_iff_zip.1 H).2 h
  refine ⟨?_, fun x hx => ?_, fun x hx => ?_⟩
  · unfold roundsFit
    rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨by rw [H.length_eq, Array.length_toList], ?_⟩
    rintro ⟨d, ro⟩ hp
    rw [beq_iff_eq]
    exact (Z d ro hp).1
  · obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hx
    exact (Z d ro hp).2.1 x hin
  · obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hx
    exact (Z d ro hp).2.2 x hin

/-- A member of `ownRows` is an opening of a round as read. -/
theorem own_mem {ds : List Three.RDL} {o : Fmt.ChainOut} {x : ℕ × Opened} (hx : x ∈ ownRows ds o) :
    ∃ ro ∈ o.rounds.toList, x.2 ∈ ro.opens := by
  obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hx
  exact ⟨ro, (List.of_mem_zip hp).2, List.mem_of_mem_drop (List.of_mem_zip hin).2⟩

/-- A member of `storedRows` is an opening of a round as read. -/
theorem stored_mem {ds : List Three.RDL} {o : Fmt.ChainOut} {x : Fmt.Stored × Opened}
    (hx : x ∈ storedRows ds o) : ∃ ro ∈ o.rounds.toList, x.2 ∈ ro.opens := by
  obtain ⟨⟨d, ro⟩, hp, hin⟩ := List.mem_flatMap.1 hx
  exact ⟨ro, (List.of_mem_zip hp).2, (List.of_mem_zip hin).2⟩

/-- All that the tables ask of one chain that the program's reader has read. -/
theorem read_fit (W : Three.Whole) (a : ℕ) (ds : List Three.RDL) (S : Fmt.SpecX) (seen : Fmt.Seen)
    (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ) (e : readChain S seen b i = some (o, j))
    (F : DataFits W (S.base.rounds.zip S.stored) ds) (hs : StoredAt a ds) :
    roundsFit ds o = true ∧ (∀ x ∈ ownRows ds o, rowOK W S.base.plan.salt x = true) ∧
      (∀ x ∈ storedRows ds o, storedOK a x = true) ∧
      (∀ x ∈ ownRows ds o, ∃ ps, fullPaths x.2 = some ps) ∧
      ∀ x ∈ storedRows ds o, ∃ ps, fullPaths x.2 = some ps := by
  obtain ⟨-, H⟩ := readChain_read S seen b i o j e
  obtain ⟨w, -⟩ := readChain_entered S seen b i o j e
  obtain ⟨c1, c2, c3⟩ := chain_fit W _ a ds o (rounds_fit W a _ H F hs)
  refine ⟨c1, c2, c3, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨ro, hro, hy⟩ := own_mem hx
    exact walked_full Fmt.formatHash _ (w ro hro x.2 hy)
  · obtain ⟨ro, hro, hy⟩ := stored_mem hx
    exact walked_full Fmt.formatHash _ (w ro hro x.2 hy)

/-! ## The three chains of a file -/

/-- What is asked of the three descriptions and the data. -/
structure FileFits (W : Three.Whole) (sb a : ℕ) (S₁ S₂ S₃ : Fmt.SpecX) : Prop where
  /-- the data fit the three descriptions -/
  d₁ : DataFits W (S₁.base.rounds.zip S₁.stored) W.ds₁
  d₂ : DataFits W (S₂.base.rounds.zip S₂.stored) W.ds₂
  d₃ : DataFits W (S₃.base.rounds.zip S₃.stored) W.ds₃
  /-- the three plans have one number of bytes of a salt -/
  s₁ : S₁.base.plan.salt = sb
  s₂ : S₂.base.plan.salt = sb
  s₃ : S₃.base.plan.salt = sb
  /-- the stored tables have the depth a and stand under the item 0 -/
  a₁ : StoredAt a W.ds₁
  a₂ : StoredAt a W.ds₂
  a₃ : StoredAt a W.ds₃

/-- **The three chains of a file as the program's reader has read them**: the tests on the file as
read pass, and whole paths are there. The records of vertices from which the three were read are
letters here. -/
theorem tables_fit (W : Three.Whole) (sb a : ℕ) (S₁ S₂ S₃ : Fmt.SpecX)
    (F : FileFits W sb a S₁ S₂ S₃) (r : Proof.TailRead) (b : ByteArray) (n₁ n₂ n₃ : Fmt.Seen)
    (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ) (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃)) :
    fitsW W r = true ∧ (∀ x ∈ ownRowsW W r, rowOK W sb x = true) ∧
      (∀ x ∈ storedRowsW W r, storedOK a x = true) ∧
      (∀ x ∈ ownRowsW W r, ∃ ps, fullPaths x.2 = some ps) ∧
      ∀ x ∈ storedRowsW W r, ∃ ps, fullPaths x.2 = some ps := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := read_fit W a W.ds₁ S₁ n₁ b i₁ _ j₁ e₁ F.d₁ F.a₁
  obtain ⟨q1, q2, q3, q4, q5⟩ := read_fit W a W.ds₂ S₂ n₂ b i₂ _ j₂ e₂ F.d₂ F.a₂
  obtain ⟨t1, t2, t3, t4, t5⟩ := read_fit W a W.ds₃ S₃ n₃ b i₃ _ j₃ e₃ F.d₃ F.a₃
  rw [F.s₁] at p2
  rw [F.s₂] at q2
  rw [F.s₃] at t2
  have three : ∀ {α : Type} {l₁ l₂ l₃ : List α} {Q : α → Prop}, (∀ x ∈ l₁, Q x) → (∀ x ∈ l₂, Q x) →
      (∀ x ∈ l₃, Q x) → ∀ x ∈ l₁ ++ (l₂ ++ l₃), Q x := by
    intro α l₁ l₂ l₃ Q h1 h2 h3 x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h1 x hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact h2 x hx
      · exact h3 x hx
  refine ⟨?_, three p2 q2 t2, three p3 q3 t3, three p4 q4 t4, three p5 q5 t5⟩
  unfold fitsW
  rw [p1, q1, t1]
  rfl

/-- **The trees' tables with whole paths return at a file as read.** -/
theorem tabsWFull_of_read (W : Three.Whole) (sb a : ℕ) (S₁ S₂ S₃ : Fmt.SpecX)
    (F : FileFits W sb a S₁ S₂ S₃) (r : Proof.TailRead) (b : ByteArray) (n₁ n₂ n₃ : Fmt.Seen)
    (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ) (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃)) (R : RunsThere r) (T : SameTwice W r) :
    (tabsWFull W sb r).isSome = true := by
  obtain ⟨h1, h2, -, h4, -⟩ := tables_fit W sb a S₁ S₂ S₃ F r b n₁ n₂ n₃ i₁ i₂ i₃ j₁ j₂ j₃ e₁ e₂ e₃
  exact tabsWFull_isSome W sb r h1 h2 R h4 T

/-- **The stored table's openings with whole paths return at a file as read.** -/
theorem extWFull_of_read (W : Three.Whole) (sb a : ℕ) (cfg : ByteArray) (S₁ S₂ S₃ : Fmt.SpecX)
    (F : FileFits W sb a S₁ S₂ S₃) (r : Proof.TailRead) (b : ByteArray) (n₁ n₂ n₃ : Fmt.Seen)
    (i₁ i₂ i₃ j₁ j₂ j₃ : ℕ) (e₁ : readChain S₁ n₁ b i₁ = some (r.first.out, j₁))
    (e₂ : readChain S₂ n₂ b i₂ = some (r.shared.out, j₂))
    (e₃ : readChain S₃ n₃ b i₃ = some (r.second.out, j₃)) (T : SameTwice W r) :
    (extWFull a cfg W r).isSome = true := by
  obtain ⟨h1, -, h3, -, h5⟩ := tables_fit W sb a S₁ S₂ S₃ F r b n₁ n₂ n₃ i₁ i₂ i₃ j₁ j₂ j₃ e₁ e₂ e₃
  exact extWFull_isSome a cfg W r h1 h3 h5 T

end OnBytes.Maker
