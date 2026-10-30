-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruAtPure.lean: what the maker onlineProverFromPublicFiles (Honest/AtPure.lean) returns at
a filling read through (OnlineProverParts.through, Honest/ThruK13.lean) is what it returns at the filling, read
through; and so the run of a prover that it returns there is the run at the filling.

  OnlineProverWithDescription.ofFillWith, OnlineProverWithDescription.ofFill   the value that onlineProverFromPublicFiles returns, as a term
  atPure_value         where the maker has its four and the filling meets its asks, that value
  firstOf_thru         the first chain's sides of lots read through
  OnlineProverWithDescription.thru          the value read through: the prover by Prover.thru (Honest/ThruRun.lean)
  ofFill_through       the value at the filling read through is the value read through
  atPure_through       THE MAKER COMMUTES WITH READING THROUGH, where the new named member is in range
  key_of_atPure, inRange_of_atPure   two fields of the prover that it returns
  made_thru            two returns at the same files: the prover at the filling read through is the
                       other read through
  ready_made, runC_made, outcomeC_made   at the rows' prover of a filling read through

By what. parts_of_atPure (K5/Law/ReturnsOf.lean), makerAsks_through (Honest/ThruMade.lean); the
walk through the maker's text in atPure_value is that of atPure_of_parts.

Limits.
  * atPure_through asks that g d is in range, and that the maker returns at the filling itself.
    Both are premises here.
  * ready_made and the two that follow take the maker's two returns, rows, a committer and the
    equation of the rows as premises; runC_made and outcomeC_made take the columns too.
  * That a return of the maker is a whole honest prover is not said (OnlineProverWithDescription.stillIdle).
  * Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruRows
import Johnson.Desc.ProofFile.Honest.ThruMade
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {W₀ W₀' Rc Rc' Tr X₀ X Sd Xc : Type} {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}

/-- **The value that the maker returns**, at a list of the first chain's sides. -/
def OnlineProverWithDescription.ofFillWith (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : Pub) (G : Ground) (F : FileDescription Inst) (B : ProverCoinCounts)
    (first : List (Placed (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)) :
    OnlineProverWithDescription W₀ Rc Tr X₀ X :=
  { Z := Z, G := G, F := F, B := B, readers := P.readers Z, rows := P.rows Z G
    H := { stored := P.enc Z, trace := P.trace Z, key := pureKey, inRange := P.inRange
           dummy := P.dummy, own₀ := P.own₀, ownShared₀ := P.ownShared₀
           first := first, shared := P.shared Z G, second := P.second Z G, meet := P.meet } }

/-- **The value that the maker returns**, at the filling's lots. -/
def OnlineProverWithDescription.ofFill (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : Pub) (G : Ground) (F : FileDescription Inst) (B : ProverCoinCounts) :
    OnlineProverWithDescription W₀ Rc Tr X₀ X :=
  OnlineProverWithDescription.ofFillWith P Z G F B (firstOf Z G P.lots)

/-- **Where the maker has its four and the filling meets its asks it returns that value.** -/
theorem atPure_value {P : OnlineProverParts W₀ Rc Tr X₀ X} {Z : Pub} {G : Ground} {F : FileDescription Inst} {B : ProverCoinCounts}
    (m : K5.MakerHas o pol lay KL Z G F B) (f : K5.MakerAsks P Z G F) :
    onlineProverFromPublicFiles o pol lay KL P = .ok (OnlineProverWithDescription.ofFill P Z G F B) := by
  obtain ⟨c0, c1, c2, c3, p0, p1, p2, hS, hB⟩ := m.book
  have hG : due? "the blank ground" (blankBy pureRoad.links Z) = .ok G := by
    rw [m.ground]
    rfl
  unfold onlineProverFromPublicFiles
  rw [m.pub]
  simp only [Except.bind]
  rw [hG]
  dsimp only
  rw [m.desc]
  dsimp only
  rw [hS]
  dsimp only
  rw [hB]
  dsimp only
  rw [f.first, f.shared, f.second, f.range]
  rfl

/-- What the maker returned, as that value. -/
theorem eq_ofFill {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) : A = OnlineProverWithDescription.ofFill P A.Z A.G A.F A.B :=
  Except.ok.inj (h.symm.trans
    (atPure_value (K5.parts_of_atPure h).1 (K5.parts_of_atPure h).2))

/-- The first chain's sides of lots read through are the sides read through. -/
theorem firstOf_thru {V V' W W' Y : Type} (see : V' → V) (wit : W' → W) (Z : Pub) (G : Ground) :
    (ls : List (HLot V W Y)) →
      firstOf Z G (ls.map (HLot.thru see wit)) = (firstOf Z G ls).map (Placed.thru see wit)
  | [] => rfl
  | L :: ls => by
    have ih := firstOf_thru see wit Z G ls
    show (L.halves Z G).map (Placed.thru see wit) ++ firstOf Z G (ls.map (HLot.thru see wit)) =
      (L.halves Z G ++ firstOf Z G ls).map (Placed.thru see wit)
    rw [ih, List.map_append]

/-- **The maker's value read through.** -/
def OnlineProverWithDescription.thru (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) :
    OnlineProverWithDescription W₀' Rc' Tr X₀ X :=
  { Z := A.Z, G := A.G, F := A.F, B := A.B, H := A.H.thru g rd d
    readers := fun w rc => A.readers (g w) (rd rc), rows := A.rows }

/-- The value at the filling read through is the value read through. -/
theorem ofFill_through (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : Pub)
    (G : Ground) (F : FileDescription Inst) (B : ProverCoinCounts) :
    OnlineProverWithDescription.ofFill (OnlineProverParts.through g rd d P) Z G F B = (OnlineProverWithDescription.ofFill P Z G F B).thru g rd d := by
  have hf : firstOf Z G (OnlineProverParts.through g rd d P).lots =
      (firstOf Z G P.lots).map (Placed.thru (Local.thru g rd) (Local.thru g rd)) :=
    firstOf_thru (Local.thru g rd) (Local.thru g rd) Z G P.lots
  show OnlineProverWithDescription.ofFillWith (OnlineProverParts.through g rd d P) Z G F B
      (firstOf Z G (OnlineProverParts.through g rd d P).lots) = _
  rw [hf]
  rfl

/-- **THE MAKER COMMUTES WITH READING THROUGH.** Where it returns A at a filling and the new named
member is in range, it returns A read through at the filling read through. -/
theorem atPure_through (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (hd : P.inRange (g d) = true) :
    onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d P) = .ok (A.thru g rd d) := by
  obtain ⟨m, a⟩ := K5.parts_of_atPure h
  rw [atPure_value m (Term.makerAsks_through g rd d a hd), ofFill_through]
  exact congrArg
    (fun A₀ => (Except.ok (OnlineProverWithDescription.thru g rd d A₀) : Except String (OnlineProverWithDescription W₀' Rc' Tr X₀ X)))
    (eq_ofFill h).symm

/-- The key of a prover that the maker returns is the table's key in the instance. -/
theorem key_of_atPure {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) : A.H.key = pureKey :=
  congrArg (fun A₀ : OnlineProverWithDescription W₀ Rc Tr X₀ X => A₀.H.key) (eq_ofFill h)

/-- Its range is the filling's, and its named member the filling's. -/
theorem inRange_of_atPure {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) : A.H.inRange = P.inRange ∧ A.H.dummy = P.dummy :=
  ⟨congrArg (fun A₀ : OnlineProverWithDescription W₀ Rc Tr X₀ X => A₀.H.inRange) (eq_ofFill h),
    congrArg (fun A₀ : OnlineProverWithDescription W₀ Rc Tr X₀ X => A₀.H.dummy) (eq_ofFill h)⟩

section
variable (g : W₀' → W₀) (rd : Rc' → Rc) (d : W₀') {P : OnlineProverParts W₀ Rc Tr X₀ X} {Z : Pub} {Gr : Ground}
  {F : FileDescription Inst} {B : ProverCoinCounts} {H₀ : Prover W₀ Rc Inst OnBytes.TableKey Tr X₀ X}
  {H' : Prover W₀' Rc' Inst OnBytes.TableKey Tr X₀ X} {rds₀ : W₀ → Rc → Tr → Readers}
  {rds : W₀' → Rc' → Tr → Readers} {rws₀ rws : RowDataOf Inst}

/-- **Two returns at the same files**: the prover at the filling read through is the other read
through. -/
theorem made_thru (base : onlineProverFromPublicFiles o pol lay KL P = .ok ⟨Z, Gr, F, B, H₀, rds₀, rws₀⟩)
    (made : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d P) = .ok ⟨Z, Gr, F, B, H', rds, rws⟩)
    (hd : P.inRange (g d) = true) : H' = H₀.thru g rd d :=
  congrArg OnlineProverWithDescription.H (Except.ok.inj (made.symm.trans (atPure_through g rd d base hd)))

/-- The range's test answers alike at the two named members. -/
theorem range_alike (base : onlineProverFromPublicFiles o pol lay KL P = .ok ⟨Z, Gr, F, B, H₀, rds₀, rws₀⟩)
    (hd : P.inRange (g d) = true) : H₀.inRange (g d) = H₀.inRange H₀.dummy := by
  obtain ⟨e₁, e₂⟩ := inRange_of_atPure base
  have e₁' : H₀.inRange = P.inRange := e₁
  have e₂' : H₀.dummy = P.dummy := e₂
  rw [e₁', e₂', hd, (K5.parts_of_atPure base).2.range]

variable (G : Sides F B W₀' Rc' OnBytes.TableKey Tr X₀ X)
  (Cm : Committer W₀' Rc' Sd Xc Inst OnBytes.TableKey) (item₀ : Nat) (w : W₀') (rc : Rc') (x : Inst)
  (c : Coins B) (ρ : Draws)

/-- **ready at the rows' prover of the filling read through.** -/
theorem ready_made (base : onlineProverFromPublicFiles o pol lay KL P = .ok ⟨Z, Gr, F, B, H₀, rds₀, rws₀⟩)
    (made : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d P) = .ok ⟨Z, Gr, F, B, H', rds, rws⟩)
    (hd : P.inRange (g d) = true) (hrows : G.prover H' = H') (hk : Cm.key = pureKey) :
    ready F B (G.prover (Cm.proverAt item₀ H')) w rc x c =
      (ready F B H₀ (g w) (rd rc) x c).map (Ready.thru g rd w rc) := by
  obtain rfl := made_thru g rd d base made hd
  exact ready_rows_thru g rd d G Cm item₀ H₀ w rc x c (range_alike g d base hd) hrows
    (hk.trans (key_of_atPure base).symm)

/-- **The run of the rows' prover of the filling read through is the run at the filling.** -/
theorem runC_made (base : onlineProverFromPublicFiles o pol lay KL P = .ok ⟨Z, Gr, F, B, H₀, rds₀, rws₀⟩)
    (made : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d P) = .ok ⟨Z, Gr, F, B, H', rds, rws⟩)
    (hd : P.inRange (g d) = true) (hrows : G.prover H' = H') (hk : Cm.key = pureKey)
    (hs : CommittedColumns Cm item₀ H₀ g rd w rc) :
    runC F B (G.prover (Cm.proverAt item₀ H')) w rc x c ρ = runC F B H₀ (g w) (rd rc) x c ρ := by
  obtain rfl := made_thru g rd d base made hd
  exact runC_rows_thru g rd d G Cm item₀ H₀ w rc x c ρ (range_alike g d base hd) hrows
    (hk.trans (key_of_atPure base).symm) hs

/-- **And its outcome.** -/
theorem outcomeC_made (base : onlineProverFromPublicFiles o pol lay KL P = .ok ⟨Z, Gr, F, B, H₀, rds₀, rws₀⟩)
    (made : onlineProverFromPublicFiles o pol lay KL (OnlineProverParts.through g rd d P) = .ok ⟨Z, Gr, F, B, H', rds, rws⟩)
    (hd : P.inRange (g d) = true) (hrows : G.prover H' = H') (hk : Cm.key = pureKey)
    (hs : CommittedColumns Cm item₀ H₀ g rd w rc) :
    outcomeC F B (G.prover (Cm.proverAt item₀ H')) w rc x c ρ =
      outcomeC F B H₀ (g w) (rd rc) x c ρ := by
  obtain rfl := made_thru g rd d base made hd
  exact outcomeC_rows_thru g rd d G Cm item₀ H₀ w rc x c ρ (range_alike g d base hd) hrows
    (hk.trans (key_of_atPure base).symm) hs

end

end ProofFile.Honest

#print axioms ProofFile.Honest.OnlineProverWithDescription.ofFillWith
#print axioms ProofFile.Honest.OnlineProverWithDescription.ofFill
#print axioms ProofFile.Honest.atPure_value
#print axioms ProofFile.Honest.eq_ofFill
#print axioms ProofFile.Honest.firstOf_thru
#print axioms ProofFile.Honest.OnlineProverWithDescription.thru
#print axioms ProofFile.Honest.ofFill_through
#print axioms ProofFile.Honest.atPure_through
#print axioms ProofFile.Honest.key_of_atPure
#print axioms ProofFile.Honest.inRange_of_atPure
#print axioms ProofFile.Honest.made_thru
#print axioms ProofFile.Honest.range_alike
#print axioms ProofFile.Honest.ready_made
#print axioms ProofFile.Honest.runC_made
#print axioms ProofFile.Honest.outcomeC_made
