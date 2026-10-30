-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FillOpens.lean: what the key file's declared rounds open, and where `declKOf`
returns.

`declKOf m` (Johnson/G/RoundsOfPlan.lean) is `fileOf` at the key file's arguments. It has seven
steps that can refuse: three calls of `treesSent`, three of `fill`, and a search for a tree that no
round of the file opens. That search walks the declared rounds, one for each of the plan's rounds.
Here it is brought to the short lists from which `fill` made these rounds.

Called, not proved here (Johnson/Unfolds/FillLaw.lean, FileLaw.lean): `fillL`, a routine on
lists that returns what `fill`'s fold of pushes returns; `fill_of`, `fill`'s value from its two
tests; `fileOf_of`, `fileOf`'s value from its seven steps' values.

Definitions.
  `drawing es`: how many of the entries are rounds that draw positions.
  `noneBare plan`: no member of the plan holds neither a tree nor a stored table.
  `toldAtLists`, `allOpened`: `toldIn`'s text and `fileOf`'s last test, at three lists of opened
    trees.
  `lists₀`, `lists₁`, `lists₂`: the lists that the rule puts at the three chains' rounds of
    positions.
  `FillsK m t₀ t₁ t₂`: the seven tests behind the three returns of `treesSent`.
  `declK m t₀ t₁ t₂`: the declared rounds that `declKOf` returns.
Statements.
  `drawing_append`, `fillL_append`: both go over `++`, so a long plan can be taken in pieces.
  `fill_iff`: `fill` returns just where its two tests say yes, and then `fillL`'s value.
  `fillL_opens`, `fill_opens`: the declared rounds open what the plan's lists hold, in order.
  `toldIn_eq`: `toldIn` reads of the declared rounds only what they open.
  `declKOf_returns`: from `TreesK` and `FillsK`, `declKOf m` returns `declK m t₀ t₁ t₂`.
  `declKOf_iff`: behind `TreesK`, `declKOf m` returns just where `FillsK` holds: `FillsK` asks no
    more than the routine.

Limits. It takes a return to give a return: `TreesK` is three returns, and neither `TreesK` nor
`FillsK` is shown at any m. `FillsK` speaks of t₀, t₁, t₂, so it can be decided only where
`treesSent`'s values are known. Whether Lean's kernel bears the seven tests at a plan of full size
is not known. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.Core
import Johnson.Unfolds.FillLaw
import Johnson.Unfolds.FileLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open Johnson.Unfolds (fillL fill_of fileOf_of)
open VerifiableInference.Desc.Key

/-! ## The rounds that draw positions -/

/-- How many of the entries are rounds that draw positions: `fill`'s own count. -/
def drawing (es : List Fmt.Entry) : Nat :=
  (es.filter fun e => Fmt.kindOf e.name == some .positions).length

/-- A round that draws positions counts one. -/
theorem drawing_cons_draws {e : Fmt.Entry} (es : List Fmt.Entry)
    (h : (Fmt.kindOf e.name == some .positions) = true) : drawing (e :: es) = drawing es + 1 := by
  simp [drawing, h]

/-- Any other round counts nothing. -/
theorem drawing_cons_other {e : Fmt.Entry} (es : List Fmt.Entry)
    (h : (Fmt.kindOf e.name == some .positions) = false) : drawing (e :: es) = drawing es := by
  simp [drawing, h]

/-- The count goes over `++`. -/
theorem drawing_append (a b : List Fmt.Entry) : drawing (a ++ b) = drawing a + drawing b := by
  simp [drawing, List.filter_append]

/-! ## `fillL`, arm by arm -/

/-- A round that draws positions takes the next list. -/
theorem fillL_draws {e : Fmt.Entry} (es : List Fmt.Entry) (x : List Told × List Fmt.Stored)
    (rest : List (List Told × List Fmt.Stored))
    (h : (Fmt.kindOf e.name == some .positions) = true) :
    fillL (e :: es) (x :: rest) = ⟨e, x.2, x.1⟩ :: fillL es rest := by
  simp only [fillL, h]

/-- Any other round opens nothing and leaves the lists. -/
theorem fillL_other {e : Fmt.Entry} (es : List Fmt.Entry)
    (plan : List (List Told × List Fmt.Stored))
    (h : (Fmt.kindOf e.name == some .positions) = false) :
    fillL (e :: es) plan = ⟨e, [], []⟩ :: fillL es plan := by
  simp only [fillL, h]

/-- Where no list is left, every round opens nothing. -/
theorem fillL_spent (e : Fmt.Entry) (es : List Fmt.Entry) :
    fillL (e :: es) [] = ⟨e, [], []⟩ :: fillL es [] := by
  cases h : (Fmt.kindOf e.name == some .positions) <;> simp only [fillL, h]

/-- `fillL` goes over `++`: the second part begins with the lists that the first has left. -/
theorem fillL_append (a b : List Fmt.Entry) (plan : List (List Told × List Fmt.Stored)) :
    fillL (a ++ b) plan = fillL a plan ++ fillL b (plan.drop (drawing a)) := by
  induction a generalizing plan with
  | nil => simp [fillL, drawing]
  | cons e a ih =>
    cases h : (Fmt.kindOf e.name == some .positions) with
    | false =>
      rw [List.cons_append, fillL_other _ _ h, fillL_other _ _ h, ih, drawing_cons_other a h,
        List.cons_append]
    | true =>
      cases plan with
      | nil => simp [fillL_spent, ih]
      | cons x rest =>
        rw [List.cons_append, fillL_draws _ _ _ h, fillL_draws _ _ _ h, ih,
          drawing_cons_draws a h, List.drop_succ_cons, List.cons_append]

/-- **The declared rounds open what the lists hold, in order**, where no list is left over. -/
theorem fillL_opens (es : List Fmt.Entry) (plan : List (List Told × List Fmt.Stored))
    (hn : plan.length ≤ drawing es) : (fillL es plan).flatMap (·.opens) = plan.flatMap (·.1) := by
  induction es generalizing plan with
  | nil =>
    have hp : plan = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hn)
    subst hp
    simp [fillL]
  | cons e es ih =>
    cases plan with
    | nil => simp [fillL_spent, ih [] (Nat.zero_le _)]
    | cons x rest =>
      cases h : (Fmt.kindOf e.name == some .positions) with
      | true =>
        rw [drawing_cons_draws es h] at hn
        simp [fillL_draws es x rest h, ih rest (Nat.le_of_succ_le_succ hn)]
      | false =>
        rw [drawing_cons_other es h] at hn
        simp [fillL_other es (x :: rest) h, ih (x :: rest) hn]

/-! ## Two searches that find nothing -/

/-- A search through a numbered list by a test that does not read the number. -/
theorem find_zipIdx_none {α : Type} (p : α → Bool) (l : List α) (k : Nat) :
    (l.zipIdx k).find? (fun x => p x.1) = none ↔ l.all (fun x => !p x) = true := by
  induction l generalizing k with
  | nil => simp
  | cons y l ih =>
    rw [List.zipIdx_cons, List.find?_cons, List.all_cons]
    cases hp : p y with
    | true => simp
    | false =>
      dsimp only
      rw [ih (k + 1)]
      simp

/-- A search for a member that fails a test. -/
theorem find_not_none {α : Type} (q : α → Bool) (l : List α) :
    l.find? (fun x => !q x) = none ↔ l.all q = true := by
  induction l with
  | nil => simp
  | cons y l ih =>
    rw [List.find?_cons, List.all_cons]
    cases hq : q y with
    | false => simp
    | true =>
      simp only [Bool.not_true]
      rw [ih]
      simp

/-! ## `fill` -/

/-- No member holds neither a tree nor a stored table. -/
def noneBare (plan : List (List Told × List Fmt.Stored)) : Bool :=
  plan.all fun x => !(x.1.isEmpty && x.2.isEmpty)

/-- `fill`'s second test finds nothing just where no member is bare. -/
theorem bare_search (plan : List (List Told × List Fmt.Stored)) :
    (plan.zipIdx.find? fun x => x.1.1.isEmpty && x.1.2.isEmpty) = none ↔ noneBare plan = true :=
  find_zipIdx_none (fun y : List Told × List Fmt.Stored => y.1.isEmpty && y.2.isEmpty) plan 0

/-- **`fill` returns just where its two tests say yes**, and then what `fillL` returns. -/
theorem fill_iff (a : String) (es : List Fmt.Entry) (plan : List (List Told × List Fmt.Stored))
    (R : List Fmt.DeclaredRound) :
    fill a es plan = .ok R ↔
      drawing es = plan.length ∧ noneBare plan = true ∧ R = fillL es plan := by
  constructor
  · intro h
    have h0 := h
    unfold fill at h
    dsimp only at h
    split at h
    · rename_i hc
      obtain ⟨_, _, h⟩ := ok_of_bind h
      cases hf : (plan.zipIdx.find? fun x => x.1.1.isEmpty && x.1.2.isEmpty) with
      | none =>
        exact ⟨eq_of_beq hc, (bare_search plan).1 hf,
          Except.ok.inj (h0.symm.trans (fill_of hc hf))⟩
      | some x =>
        rw [hf] at h
        obtain ⟨_, h', _⟩ := ok_of_bind h
        exact nomatch h'
    · obtain ⟨_, h', _⟩ := ok_of_bind h
      exact nomatch h'
  · rintro ⟨hn, hb, rfl⟩
    exact fill_of (beq_iff_eq.2 hn) ((bare_search plan).2 hb)

/-- What the rounds that `fill` returns open. -/
theorem fill_opens (a : String) (es : List Fmt.Entry) (plan : List (List Told × List Fmt.Stored))
    (R : List Fmt.DeclaredRound) (h : fill a es plan = .ok R) :
    R.flatMap (·.opens) = plan.flatMap (·.1) := by
  obtain ⟨hn, _, rfl⟩ := (fill_iff a es plan R).1 h
  exact fillL_opens es plan (Nat.le_of_eq hn.symm)

/-! ## The trees that a file's rounds open -/

/-- `toldIn`'s text, at the three chains' lists of opened trees. -/
def toldAtLists (o₀ o₁ o₂ : List Told) : List (Nat × Nat) :=
  [o₀, o₁, o₂].zipIdx.flatMap fun c => c.1.map fun o =>
    match o.2 with
    | .own n => (c.2, n)
    | .taken k p => (k, p)

/-- `toldIn` reads of the declared rounds only what they open. -/
theorem toldIn_eq (D : Decl3) : toldIn D =
    toldAtLists (D.1.flatMap (·.opens)) (D.2.1.flatMap (·.opens)) (D.2.2.flatMap (·.opens)) := rfl

/-- Every tree of the three chains stands among the opened ones: `fileOf`'s last test. -/
def allOpened (t₀ t₁ t₂ : List (Sent × Nat)) (o₀ o₁ o₂ : List Told) : Bool :=
  ([t₀, t₁, t₂].zipIdx.flatMap fun c => c.1.map fun t => (c.2, t.2)).all
    fun x => (toldAtLists o₀ o₁ o₂).contains x

/-! ## The key file -/

/-- The lists that the rule puts at the first chain's rounds of positions. -/
abbrev lists₀ (t₀ : List (Sent × Nat)) : List (List Told × List Fmt.Stored) :=
  noStored (onceOpens t₀)

/-- The like for the shared chain. -/
abbrev lists₁ (m : Made) (t₁ : List (Sent × Nat)) : List (List Told × List Fmt.Stored) :=
  sharedOpens (shapeK m) t₁

/-- The like for the second chain. -/
abbrev lists₂ (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) : List (List Told × List Fmt.Stored) :=
  noStored (secondOpens (shapeK m) (fun t => t.tag == .indexMask) t₀ t₁ t₂)

/-- What `declKOf` asks behind the three returns of `treesSent`: of each chain, that as many rounds
draw positions as the rule has lists, and that no list is bare; and that every tree is opened. -/
structure FillsK (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) : Prop where
  count₀ : drawing (plan₀ m).rounds = (lists₀ t₀).length
  count₁ : drawing (plan₁ m).rounds = (lists₁ m t₁).length
  count₂ : drawing (plan₂ m).rounds = (lists₂ m t₀ t₁ t₂).length
  bare₀ : noneBare (lists₀ t₀) = true
  bare₁ : noneBare (lists₁ m t₁) = true
  bare₂ : noneBare (lists₂ m t₀ t₁ t₂) = true
  opened : allOpened t₀ t₁ t₂ ((lists₀ t₀).flatMap (·.1)) ((lists₁ m t₁).flatMap (·.1))
    ((lists₂ m t₀ t₁ t₂).flatMap (·.1)) = true

/-- The declared rounds that `declKOf` returns. -/
def declK (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) : Decl3 :=
  (fillL (plan₀ m).rounds (lists₀ t₀), fillL (plan₁ m).rounds (lists₁ m t₁),
    fillL (plan₂ m).rounds (lists₂ m t₀ t₁ t₂))

/-- Under the three counts, what `declK`'s rounds open is what the rule's lists hold. -/
theorem toldIn_declK (m : Made) (t₀ t₁ t₂ : List (Sent × Nat))
    (c₀ : drawing (plan₀ m).rounds = (lists₀ t₀).length)
    (c₁ : drawing (plan₁ m).rounds = (lists₁ m t₁).length)
    (c₂ : drawing (plan₂ m).rounds = (lists₂ m t₀ t₁ t₂).length) :
    toldIn (declK m t₀ t₁ t₂) = toldAtLists ((lists₀ t₀).flatMap (·.1))
      ((lists₁ m t₁).flatMap (·.1)) ((lists₂ m t₀ t₁ t₂).flatMap (·.1)) := by
  rw [toldIn_eq]
  show toldAtLists ((fillL (plan₀ m).rounds (lists₀ t₀)).flatMap (·.opens))
    ((fillL (plan₁ m).rounds (lists₁ m t₁)).flatMap (·.opens))
    ((fillL (plan₂ m).rounds (lists₂ m t₀ t₁ t₂)).flatMap (·.opens)) = _
  rw [fillL_opens _ _ (Nat.le_of_eq c₀.symm), fillL_opens _ _ (Nat.le_of_eq c₁.symm),
    fillL_opens _ _ (Nat.le_of_eq c₂.symm)]

/-- **`declKOf` returns**, from the three returns of `treesSent` and the seven tests. -/
theorem declKOf_returns (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (hT : TreesK m t₀ t₁ t₂)
    (hF : FillsK m t₀ t₁ t₂) : declKOf m = .ok (declK m t₀ t₁ t₂) := by
  have hopen : ([t₀, t₁, t₂].zipIdx.flatMap fun c => c.1.map fun t => (c.2, t.2)).all
      (fun x => (toldIn (declK m t₀ t₁ t₂)).contains x) = true := by
    rw [toldIn_declK m t₀ t₁ t₂ hF.count₀ hF.count₁ hF.count₂]
    exact hF.opened
  unfold declKOf
  exact fileOf_of (hT.first _) (hT.shared _) (hT.second _)
    ((fill_iff _ _ _ _).2 ⟨hF.count₀, hF.bare₀, rfl⟩)
    ((fill_iff _ _ _ _).2 ⟨hF.count₁, hF.bare₁, rfl⟩)
    ((fill_iff _ _ _ _).2 ⟨hF.count₂, hF.bare₂, rfl⟩)
    ((find_not_none _ _).2 hopen)

/-- **Behind the three returns of `treesSent`, `declKOf` returns just where the seven tests say
yes.** -/
theorem declKOf_iff (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (hT : TreesK m t₀ t₁ t₂) (D : Decl3) :
    declKOf m = .ok D ↔ FillsK m t₀ t₁ t₂ ∧ D = declK m t₀ t₁ t₂ := by
  constructor
  · intro h
    unfold declKOf fileOf at h
    obtain ⟨s₀, e₀, h⟩ := ok_of_bind h
    obtain rfl : t₀ = s₀ := Except.ok.inj ((hT.first _).symm.trans e₀)
    obtain ⟨s₁, e₁, h⟩ := ok_of_bind h
    obtain rfl : t₁ = s₁ := Except.ok.inj ((hT.shared _).symm.trans e₁)
    obtain ⟨s₂, e₂, h⟩ := ok_of_bind h
    obtain rfl : t₂ = s₂ := Except.ok.inj ((hT.second _).symm.trans e₂)
    obtain ⟨d₀, f₀, h⟩ := ok_of_bind h
    obtain ⟨d₁, f₁, h⟩ := ok_of_bind h
    obtain ⟨d₂, f₂, h⟩ := ok_of_bind h
    obtain ⟨c₀, b₀, rfl⟩ := (fill_iff _ _ _ _).1 f₀
    obtain ⟨c₁, b₁, rfl⟩ := (fill_iff _ _ _ _).1 f₁
    obtain ⟨c₂, b₂, rfl⟩ := (fill_iff _ _ _ _).1 f₂
    dsimp only at h
    split at h
    · exact nomatch h
    · rename_i hs
      have hall : ([t₀, t₁, t₂].zipIdx.flatMap fun c => c.1.map fun t => (c.2, t.2)).all
          (fun x => (toldIn (declK m t₀ t₁ t₂)).contains x) = true := (find_not_none _ _).1 hs
      rw [toldIn_declK m t₀ t₁ t₂ c₀ c₁ c₂] at hall
      exact ⟨⟨c₀, c₁, c₂, b₀, b₁, b₂, hall⟩, (Except.ok.inj h).symm⟩
  · rintro ⟨hF, rfl⟩
    exact declKOf_returns m t₀ t₁ t₂ hT hF

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.drawing_cons_draws
#print axioms Johnson.AtFull.KeyBack.drawing_cons_other
#print axioms Johnson.AtFull.KeyBack.drawing_append
#print axioms Johnson.AtFull.KeyBack.fillL_draws
#print axioms Johnson.AtFull.KeyBack.fillL_other
#print axioms Johnson.AtFull.KeyBack.fillL_spent
#print axioms Johnson.AtFull.KeyBack.fillL_append
#print axioms Johnson.AtFull.KeyBack.fillL_opens
#print axioms Johnson.AtFull.KeyBack.find_zipIdx_none
#print axioms Johnson.AtFull.KeyBack.find_not_none
#print axioms Johnson.AtFull.KeyBack.bare_search
#print axioms Johnson.AtFull.KeyBack.fill_iff
#print axioms Johnson.AtFull.KeyBack.fill_opens
#print axioms Johnson.AtFull.KeyBack.toldIn_eq
#print axioms Johnson.AtFull.KeyBack.toldIn_declK
#print axioms Johnson.AtFull.KeyBack.declKOf_returns
#print axioms Johnson.AtFull.KeyBack.declKOf_iff
