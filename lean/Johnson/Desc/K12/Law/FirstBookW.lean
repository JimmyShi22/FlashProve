-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.FirstCut
import Johnson.Desc.K12.Law.PlacesSmall
import Johnson.Desc.K12.Law.PlacesFull
import Fmt.Rules6Laws
/-
Johnson/Desc/K12/Law/FirstBookW.lean: AT THE LAST CHAIN's OWN PROXIMITY TEST: THE SOURCES THAT THE FIRST SWITCH's DECLARED OPENINGS NAME ARE, IN ORDER, THOSE OF THE BOOK's TREES AT THE PLACES D.ts: the first clause of the law's promise «FirstOpens» there, taken apart into a test on the plan, a promise on the record's book, and the block's own guard on labels. In the form of «the book is in order» for the shared chain (BookOrd, Johnson/Desc/Sound/BookOrder.lean). BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
THE BOOK THERE: the first chain's whole book as it is (R₁ trees), then Omega's tree, taken over from the shared chain, then the chain's own, numbered from R₁ + 1.
  BookOrdW R₁ ω B · bookOrdWB     OF THE RECORD: the tree at the place z of the book bears the number z, but at the place R₁: ω (Omega's number on the shared chain) · its test with code · bookOrdW_iff
  srcW R₁ ω z       the declared source of the tree at the place z: taken 0 z (z < R₁) · taken 1 ω (z = R₁) · own (z − R₁ − 1)
  takenOrderB π R₁ ω   ON THE PLAN: the first switch's declared openings are fr ++ [l]: l is «taken 1 ω» under the label ω; every o of fr is «taken 0 n» under the label n < R₁; some label of fr is at least ω
  ts_rises          D.ts rises strictly: BY gpOf's OWN MAKE (Fmt.listOf) and Fmt.listOf_incr
  first_of_bookW    takenOrderB · the labels' equation (the block's guard at a yes) · every place of D.ts has a tree · BookOrdW · D.ts rises ⇒ D.opens.map (·.2) = D.ts.map (srcW R₁ ω)
  first_num_W       the clause at any num
  order_W | order_WFull · controls   the test on the plan at the two closed places (R₁ = 22 | 83 · ω = 1): yes; at the full size with ω := 0, and with R₁ := 82: no. By the kernel. THE PLACES ARE A RUN's PRINT MADE INTO TERMS.
WHY THE LABELS ALONE DO NOT DO: «taken 0 1» and «taken 1 1» both bear the label 1, and the book's trees at the places 1 and R₁ both bear the number 1. What breaks the tie is the order: the record's side rises by places.
WHAT IT DOES NOT SAY: that any record has BookOrdW: (i) «tree z bears z» below R₁ is the first chain's end's to hand on (ii) Omega's tree at R₁ under ω: the last chain's first step's (iii) the own trees' numbers: the block's own receivings' · that R₁ is the first chain's count of roots and π.nums.firstTree = R₁ + 1 · the second clause of FirstOpens.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.First
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.K12

/-- OF THE RECORD. -/
def BookOrdW (R₁ ω : Nat) (B : TreeBook) : Prop :=
  ∀ z T, B.trees[z]? = some T → T.number = if z = R₁ then ω else z

def bookOrdWB (R₁ ω : Nat) (B : TreeBook) : Bool :=
  B.trees.toList.zipIdx.all fun x => x.1.number == if x.2 = R₁ then ω else x.2

theorem bookOrdW_iff (R₁ ω : Nat) (B : TreeBook) : bookOrdWB R₁ ω B = true ↔ BookOrdW R₁ ω B := by
  unfold bookOrdWB BookOrdW
  rw [List.all_eq_true]
  constructor
  · intro h z T hT
    have := h (T, z) (List.mem_zipIdx_iff_getElem?.2 (by simpa using hT))
    simpa using this
  · rintro h ⟨T, z⟩ hm
    have := List.mem_zipIdx_iff_getElem?.1 hm
    simpa using h z T (by simpa using this)

/-- The declared source of the tree at the place z. -/
def srcW (R₁ ω z : Nat) : Fmt.TreeSource :=
  if z < R₁ then .taken 0 z else if z = R₁ then .taken 1 ω else .own (z - R₁ - 1)

/-- A list of openings taken from the first chain, each under its own number below R₁. -/
def frontB (R₁ : Nat) (fr : List (Fmt.Shape × Fmt.TreeSource)) : Bool :=
  fr.all fun o => decide (o.2 = .taken 0 o.1.tree) && decide (o.1.tree < R₁)

/-- The test on a list of openings. -/
def orderL (R₁ ω : Nat) (os : List (Fmt.Shape × Fmt.TreeSource)) : Bool :=
  match os.getLast? with
  | some l => decide (l.2 = .taken 1 ω) && decide (l.1.tree = ω) && frontB R₁ os.dropLast &&
      os.dropLast.any fun o => decide (ω ≤ o.1.tree)
  | none => false

/-- ON THE PLAN. -/
def takenOrderB (π : P12) (R₁ ω : Nat) : Bool :=
  match π.nums.stages with
  | a :: _ => orderL R₁ ω (opensOf π a.k)
  | [] => false

theorem ts_rises (p : P12) (t : T12) (a : Fmt.M1.Stage) (L : GroupLayout) (D : Plain)
    (h : gpOf p t a L = some D) : D.ts.Pairwise (· < ·) := by
  unfold gpOf at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h
  exact Fmt.listOf_incr _

theorem dropLast_last {α : Type} : ∀ (l : List α) (x : α), l.getLast? = some x →
    l = l.dropLast ++ [x]
  | [], _, h => by simp at h
  | [a], x, h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    rfl
  | a :: b :: l, x, h => by
    rw [List.getLast?_cons_cons] at h
    have ih := dropLast_last (b :: l) x h
    rw [List.dropLast_cons₂, List.cons_append, ← ih]

theorem split_last {α β γ : Type} (f : α → γ) (g : β → γ) (l : α) : ∀ (fr : List α) (ts : List β),
    (fr ++ [l]).map f = ts.map g → ∃ tf zl, ts = tf ++ [zl] ∧ fr.map f = tf.map g ∧ f l = g zl
  | [], ts, h => by
    cases ts with
    | nil => simp at h
    | cons z ts' =>
      simp only [List.nil_append, List.map_cons, List.map_nil, List.cons.injEq] at h
      have e : ts' = [] := by
        cases ts' with
        | nil => rfl
        | cons _ _ => simp at h
      subst e
      exact ⟨[], z, rfl, rfl, h.1⟩
  | a :: fr, ts, h => by
    cases ts with
    | nil => simp at h
    | cons z ts' =>
      simp only [List.cons_append, List.map_cons, List.cons.injEq] at h
      obtain ⟨tf, zl, e, h1, h2⟩ := split_last f g l fr ts' h.2
      subst e
      exact ⟨z :: tf, zl, rfl, by rw [List.map_cons, List.map_cons, h.1, h1], h2⟩

theorem mate {α β γ : Type} (f : α → γ) (g : β → γ) (fr : List α) (tf : List β)
    (h : fr.map f = tf.map g) (o : α) (ho : o ∈ fr) : ∃ z ∈ tf, g z = f o := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ho
  have e := congrArg (·[i]?) h
  simp only [List.getElem?_map, hi, Option.map_some] at e
  obtain ⟨z, hz, hg⟩ := Option.map_eq_some_iff.1 e.symm
  exact ⟨z, List.mem_of_getElem? hz, hg⟩

/-- The arithmetic, on lists. nm: the number that the book's tree at a place bears. -/
theorem order_core (R₁ ω : Nat) (nm : Nat → Nat) (os : List (Fmt.Shape × Fmt.TreeSource))
    (ts : List Nat) (hP : orderL R₁ ω os = true) (hl : os.map (·.1.tree) = ts.map nm)
    (hn : ∀ z ∈ ts, nm z = if z = R₁ then ω else z) (hR : ts.Pairwise (· < ·)) :
    os.map (·.2) = ts.map (srcW R₁ ω) := by
  unfold orderL at hP
  cases hlast : os.getLast? with
  | none => rw [hlast] at hP; cases hP
  | some l =>
    rw [hlast] at hP
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hP
    obtain ⟨⟨⟨l2, l1⟩, hfr⟩, o, ho, hoω⟩ := hP
    have hos : os = os.dropLast ++ [l] := dropLast_last os l hlast
    generalize os.dropLast = fr at hos hfr ho
    subst hos
    obtain ⟨tf, zl, rfl, h1, h2⟩ := split_last (fun o : Fmt.Shape × Fmt.TreeSource => o.1.tree) nm l fr ts hl
    have hlt : ∀ z ∈ tf, z < zl := fun z hz =>
      (List.pairwise_append.1 hR).2.2 z hz zl (List.mem_singleton.2 rfl)
    have hfr' : ∀ q ∈ fr, q.2 = .taken 0 q.1.tree ∧ q.1.tree < R₁ := by
      intro q hq
      have := List.all_eq_true.1 hfr q hq
      simpa using this
    have hzl : zl = R₁ := by
      by_cases c : zl = R₁
      · exact c
      · exfalso
        have e1 := hn zl (List.mem_append_right _ (List.mem_singleton.2 rfl))
        rw [if_neg c] at e1
        have e2 : l.1.tree = nm zl := h2
        obtain ⟨z, hz, hg⟩ := mate _ nm fr tf h1 o ho
        have e3 := hn z (List.mem_append_left _ hz)
        have b1 := hlt z hz
        have b2 := (hfr' o ho).2
        have hg' : nm z = o.1.tree := hg
        by_cases c2 : z = R₁
        · omega
        · rw [if_neg c2] at e3
          omega
    subst hzl
    rw [List.map_append, List.map_append, List.map_cons, List.map_cons, List.map_nil, List.map_nil]
    congr 1
    · have e4 : fr.map (·.2) = (fr.map (·.1.tree)).map (Fmt.TreeSource.taken 0) := by
        rw [List.map_map]
        exact List.map_congr_left fun q hq => (hfr' q hq).1
      rw [e4, h1, List.map_map]
      refine List.map_congr_left fun z hz => ?_
      have b1 := hlt z hz
      have e3 := hn z (List.mem_append_left _ hz)
      rw [if_neg (by omega)] at e3
      show Fmt.TreeSource.taken 0 (nm z) = srcW zl ω z
      unfold srcW
      rw [if_pos b1, e3]
    · unfold srcW
      rw [if_neg (Nat.lt_irrefl _), if_pos rfl, l2]


theorem first_of_bookW (π : P12) (R₁ ω : Nat) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : π.nums.stages = a :: rest) (hP : takenOrderB π R₁ ω = true) (D : Plain)
    (hop : D.opens = opensOf π a.k) (hl : D.opens.map (·.1.tree) = D.ts.map (numAt D.book))
    (hts : ∀ z ∈ D.ts, ∃ T, D.book.trees[z]? = some T) (hB : BookOrdW R₁ ω D.book)
    (hR : D.ts.Pairwise (· < ·)) : D.opens.map (·.2) = D.ts.map (srcW R₁ ω) := by
  unfold takenOrderB at hP
  rw [hs] at hP
  refine order_core R₁ ω (numAt D.book) D.opens D.ts (by rw [hop]; exact hP) hl (fun z hz => ?_) hR
  obtain ⟨T, hT⟩ := hts z hz
  unfold numAt
  rw [hT]
  exact hB z T hT

/-- The clause at any num. -/
theorem first_num_W (π : P12) (R₁ ω : Nat) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : π.nums.stages = a :: rest) (hP : takenOrderB π R₁ ω = true) (D : Plain)
    (hop : D.opens = opensOf π a.k) (hl : D.opens.map (·.1.tree) = D.ts.map (numAt D.book))
    (hts : ∀ z ∈ D.ts, ∃ T, D.book.trees[z]? = some T) (hB : BookOrdW R₁ ω D.book)
    (hR : D.ts.Pairwise (· < ·)) (num : Fmt.TreeSource → Nat) :
    D.opens.map (fun o => num o.2) = D.ts.map fun z => num (srcW R₁ ω z) := by
  have h := congrArg (List.map num) (first_of_bookW π R₁ ω a rest hs hP D hop hl hts hB hR)
  rw [List.map_map, List.map_map] at h
  exact h

theorem order_W : takenOrderB H2K.Member.piW 22 1 = true := by decide
theorem order_WFull : takenOrderB H2K.Member.piWFull 83 1 = true := by decide
theorem order_W_omega : takenOrderB H2K.Member.piWFull 83 0 = false := by decide
theorem order_W_short : takenOrderB H2K.Member.piWFull 82 1 = false := by decide

end H2K.First

#print axioms H2K.First.bookOrdW_iff
#print axioms H2K.First.ts_rises
#print axioms H2K.First.first_of_bookW
#print axioms H2K.First.first_num_W
#print axioms H2K.First.order_W
#print axioms H2K.First.order_WFull
