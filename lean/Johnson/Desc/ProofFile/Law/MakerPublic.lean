-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/MakerPublic.lean: where `onlineDescription` returns a description, the public
record in its public part `Z` is the value of `publicOfO o` at the three public files. That the
blocks are computed from that record is read off `baseOf` (OnlineDescriptionFromBlockTables.lean); it is not stated here.
Theorems only; no file of the description imports this one.
Why. A module that supplies blocks takes the public record `X` as an argument, and nothing there
says where `X` comes from. In the description it is computed by one call (`planned`,
PlanPlain.lean). So a law that holds for every record that `publicOfO` returns can be used in a
theorem about `onlineDescription`, and these lemmas discharge its premise.
  `planned_public`   `planned o pol KL layout = .ok p → publicOfO o pol KL layout = .ok p.X`
  `madeOf_planned`   `madeOf o pol lay KL = .ok m → planned o pol KL (some lay) = .ok m.p`
  `pubBy_made`       `pubBy made st pol lay KL = .ok Z → made pol lay KL = .ok Z.made`
  `pub_public`       `pureRoad.pub o pol lay KL = .ok Z → publicOfO o pol KL (some lay) = .ok Z.p.X`
  `lettersBy_W`, `blankBy_W`   the segments' records that a lot's tables are computed from hold the
                     same record: `G.W = Z.p.X`
  `descPure_made`    `onlineDescription o pol lay KL = .ok F →`
                     `∃ Z, pureRoad.pub o pol lay KL = .ok Z ∧ onlineDescriptionFromPublicPart Z (pureSeat o Z) = .ok F`
  `descPure_public`  the same, with `pub_public`
All hold for every `o`.
Not here: what follows for `F` (Law/PureMade.lean has a first step); anything about `publicOfO`
itself; the library's own planner.

-/
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open OnBytes OnBytes.Model OnBytes.Model.Verify

universe u v w

/-! ### On `Except` -/

theorem error_ne_ok {ε : Type u} {α : Type v} {e : ε} {a : α}
    (h : (Except.error e : Except ε α) = .ok a) : False := by
  cases h

/-- If a bind returns a value, so do both parts. Stated for `Except.bind` itself, whose two types
may live in different universes. -/
theorem exBind_ok {ε : Type u} {α : Type v} {β : Type w} {x : Except ε α} {f : α → Except ε β}
    {b : β} (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact (error_ne_ok (show (Except.error e : Except ε β) = .ok b from h)).elim
  | ok a => exact ⟨a, rfl, h⟩

/-- The same for the monad's bind. -/
theorem bind_ok {ε : Type u} {α β : Type v} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b :=
  exBind_ok (show x.bind f = .ok b from h)

theorem atCall_ok {α : Type} {n : String} {x : Except String α} {a : α}
    (h : atCall n x = .ok a) : x = .ok a := by
  cases x with
  | error e =>
    exact (error_ne_ok (show (Except.error (n ++ ": " ++ e) : Except String α) = .ok a from h)).elim
  | ok b => exact h

/-! ### The planner's record -/

theorem planned_public {o : SecondHashFunctionArgument} {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Planned} (h : ProofFile.Plain.planned o pol KL layout = .ok p) :
    VerifiableInference.PlanWritten.publicOfO o pol KL layout = .ok p.X := by
  unfold ProofFile.Plain.planned at h
  obtain ⟨X, hX, h⟩ := bind_ok h
  suffices hp : p.X = X by rw [hp]; exact hX
  obtain ⟨c, _, h⟩ := bind_ok h
  obtain ⟨b, _, h⟩ := bind_ok h
  exact (congrArg Planned.X (Except.ok.inj h)).symm

theorem madeOf_planned {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {m : Johnson.G.OfPlan.Made}
    (h : ProofFile.PlainG.madeOf o pol lay KL = .ok m) :
    ProofFile.Plain.planned o pol KL (some lay) = .ok m.p := by
  unfold ProofFile.PlainG.madeOf at h
  obtain ⟨p, hp, h⟩ := bind_ok h
  suffices hm : m.p = p by rw [hm]; exact hp
  obtain ⟨l, _, h⟩ := bind_ok h
  split at h
  · exact (congrArg Johnson.G.OfPlan.Made.p (Except.ok.inj h)).symm
  · exact (error_ne_ok h).elim

/-! ### The public part -/

theorem pubBy_made
    {made : ByteArray → ByteArray → ByteArray → Except String Johnson.G.OfPlan.Made} {st : Starts}
    {pol lay KL : ByteArray} {Z : Pub} (h : pubBy made st pol lay KL = .ok Z) :
    made pol lay KL = .ok Z.made := by
  unfold pubBy at h
  obtain ⟨m, hm, h⟩ := bind_ok h
  have hm := atCall_ok hm
  suffices hZ : Z.made = m by rw [hZ]; exact hm
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; rfl)

theorem pub_public {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : pureRoad.pub o pol lay KL = .ok Z) :
    VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) = .ok Z.p.X :=
  planned_public (madeOf_planned (pubBy_made
    (show pubBy (ProofFile.PlainG.madeOf o) plainStarts pol lay KL = .ok Z from h)))

/-! ### The segments' records -/

theorem lettersBy_W {mk : LinksBy} {Z : Pub} {s : VerifiableInference.Desc.First.S} {G : Ground}
    (h : lettersBy mk Z s = .ok G) : G.W = Z.p.X := by
  unfold lettersBy at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | contradiction | (cases h; rfl)

theorem blankBy_W {mk : LinksBy} {Z : Pub} {G : Ground} (h : blankBy mk Z = some G) :
    G.W = Z.p.X := by
  have h' : (lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1]))).toOption =
      some G := h
  cases hx : lettersBy mk Z (Z.s₀.withReq (Array.replicate Z.p.X.T 0 ++ #[0, 1])) with
  | error e =>
    rw [hx] at h'
    cases h'
  | ok G' =>
    rw [hx] at h'
    have hG : G' = G := Option.some.inj h'
    exact hG ▸ lettersBy_W hx

/-! ### The description -/

theorem descPure_made {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : VerifiableInference.Desc.FileDescription Inst} (h : onlineDescription o pol lay KL = .ok F) :
    ∃ Z, pureRoad.pub o pol lay KL = .ok Z ∧ onlineDescriptionFromPublicPart Z (pureSeat o Z) = .ok F :=
  exBind_ok
    (show (pureRoad.pub o pol lay KL).bind (fun Z => onlineDescriptionFromPublicPart Z (pureSeat o Z)) = .ok F from h)

/-- Where `onlineDescription` returns `F`: the public part `Z` is `pureRoad.pub`'s value at the three files,
the public record in it is `publicOfO`'s value at `o` and these files, and `F` is `onlineDescriptionFromPublicPart`'s value.
That a lot is handed this record is not part of the statement. A lot is computed from `Z`, and its
tables from the segments' records of `blankBy`, for which `blankBy_W` gives `G.W = Z.p.X`; that
`onlineDescriptionFromPublicPart` uses just these records can be read off `baseOf` (OnlineDescriptionFromBlockTables.lean). -/
theorem descPure_public {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : VerifiableInference.Desc.FileDescription Inst} (h : onlineDescription o pol lay KL = .ok F) :
    ∃ Z, pureRoad.pub o pol lay KL = .ok Z ∧
      VerifiableInference.PlanWritten.publicOfO o pol KL (some lay) = .ok Z.p.X ∧
      onlineDescriptionFromPublicPart Z (pureSeat o Z) = .ok F := by
  obtain ⟨Z, hZ, hF⟩ := descPure_made h
  exact ⟨Z, hZ, pub_public hZ, hF⟩

end ProofFile.Law

#print axioms ProofFile.Law.planned_public
#print axioms ProofFile.Law.pub_public
#print axioms ProofFile.Law.blankBy_W
#print axioms ProofFile.Law.descPure_public
