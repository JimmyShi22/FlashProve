-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheSides.lean: the rows of a prover's three chains as one value, with a slot for each lot, and
the structure G (Sides, Johnson/Desc/ProofFile/Honest/Rule.lean) built from them. The completeness
strand reads of G only its prover and its lists of falls. The zero-knowledge strand reads its
simulators and its letters A, B, On and bud as well. So G is one term at a value of the rows and a
way of setting A and B, and the two strands take it at different values of these two arguments:
their provers are the same prover.

  Rows, Rows.Fit          the three chains' lists of rows, and that a prover's sides are their own
  bareUnlettered, bareRows   rows made of a prover's own parts, beside a simulator that tells nothing
  Letters, Letters.bare, Letters.ofThreads   a way of setting A and B
  theSides                G at rows, letters and three lists of falls
  theSides_prover         where the prover's sides are the rows' own, G.prover H = H
  prover_letters          the prover does not depend on the letters or the falls
  castSides, castSides_prover, castSides_of, of_castSides   the sides at a description that equals
                          theirs: every statement on them crosses
  RowSlots, RowSlots.rows, RowSlots.fit   the rows at a filling (OnlineProverParts, Honest/AtPure.lean), lot by
                          lot, with the equations that tie each lot to the filling's
  bareSlot, bareSlots     the filling's own lots beside simulators that tell nothing
  overlayLot, overlaySlots   the same, with a kind's own lot in the place of the lot of its name
  overlayRow, KindRows, KindRows.slots   what the kinds lay on each chain: lots on the first, rows at
                          places on the two others

Limits.
  * bareRows and bareSlots hold no simulator that simulates anything. They serve completeness alone.
  * Nothing here says that a kind's lot in overlaySlots simulates anything: at the public part and
    ground at hand it must equal the filling's lot once its simulators are forgotten, and that is
    all that is asked.
  * This file proves nothing about completeness, soundness or zero knowledge.
-/
import E2E.KeyLaid
import Johnson.Desc.ProofFile.Honest.Thread.Rows
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.TheSides
open ProofFile.Honest
open VerifiableInference.Desc (FileDescription)
open AtPublicFiles.KeyLink (noSim)

section Rows

/-- **The three chains' lists of rows.** -/
structure Rows (W₀ Rc Xi Ky Tr X₀ X : Type) where
  first : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
  shared : List (Unlettered Empty (Common W₀ Rc Ky) X₀ Ky)
  second : List (Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)

variable {W₀ Rc Xi Ky Tr X₀ X : Type}

/-- The prover's sides are the rows' own. -/
def Rows.Fit (R : Rows W₀ Rc Xi Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Prop :=
  H.first = R.first.map (·.half) ∧ H.shared = R.shared.map (·.half) ∧
    H.second = R.second.map (·.half)

variable {V W Y Pb : Type}

/-- A prover's side as a row: each part beside a simulator that tells nothing. -/
def bareUnlettered (h : Placed V W Y) : Unlettered V W Y Pb :=
  ⟨h.place, h.parts.map fun p => (p, noSim), fun _ _ _ _ => True, fun _ _ _ => True⟩

theorem half_bare (h : Placed V W Y) : (bareUnlettered (Pb := Pb) h).half = h := by
  cases h with
  | mk a l =>
    have e : (l.map fun p => (p, (noSim : Sim Pb))).map (·.1) = l := by
      rw [List.map_map]
      exact List.map_id _
    show (⟨a, (l.map fun p => (p, (noSim : Sim Pb))).map (·.1)⟩ : Placed V W Y) = ⟨a, l⟩
    rw [e]

theorem map_half_bare : ∀ l : List (Placed V W Y),
    (l.map (bareUnlettered (Pb := Pb))).map (·.half) = l
  | [] => rfl
  | h :: t => by
    rw [List.map_cons, List.map_cons, map_half_bare t, half_bare]

/-- **Rows made of a prover's own sides.** -/
def bareRows (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Rows W₀ Rc Xi Ky Tr X₀ X :=
  ⟨H.first.map bareUnlettered, H.shared.map bareUnlettered, H.second.map bareUnlettered⟩

theorem bareRows_fit (H : Prover W₀ Rc Xi Ky Tr X₀ X) : (bareRows H).Fit H :=
  ⟨(map_half_bare _).symm, (map_half_bare _).symm, (map_half_bare _).symm⟩

end Rows

section Letters
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **A way of setting the letters A and B of a row.** It leaves the place and the row as they are.
-/
structure Letters (F : FileDescription Xi) (Bk : ProverCoinCounts) (W₀ Rc Ky Tr X₀ X : Type) where
  first : Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi →
    Lettered Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi
  shared : Unlettered Empty (Common W₀ Rc Ky) X₀ Ky →
    Lettered Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky
  second : Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi →
    Lettered Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi
  keeps₁ : ∀ r, (first r).place = r.place ∧ (first r).row = r.row
  keeps₂ : ∀ r, (shared r).place = r.place ∧ (shared r).row = r.row
  keeps₃ : ∀ r, (second r).place = r.place ∧ (second r).row = r.row

/-- A row with letters that say nothing. -/
def bareLetter {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (r : Unlettered V W Y Pb) :
    Lettered Bk S Cl V W Y Pb :=
  ⟨r.place, r.row, fun _ _ _ _ => True, fun _ _ _ _ => True, r.On, r.bud⟩

/-- **Letters that say nothing**: all that completeness needs. -/
def Letters.bare (F : FileDescription Xi) (Bk : ProverCoinCounts) : Letters F Bk W₀ Rc Ky Tr X₀ X :=
  ⟨bareLetter, bareLetter, bareLetter, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩⟩

/-- **The letters of the three chains' threads**: what the rule for simulators takes. -/
def Letters.ofThreads (F : FileDescription Xi) {Bk : ProverCoinCounts}
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) :
    Letters F Bk W₀ Rc Ky Tr X₀ X :=
  ⟨fun r => r.lay T₁ S₁ F.first.blocksInOrder, fun r => r.lay T₂ S₂ F.shared.blocksInOrder,
    fun r => r.lay T₃ S₃ F.second.blocksInOrder, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩,
    fun _ => ⟨rfl, rfl⟩⟩

/-- **The sides**: rows, a way of setting their letters, and each chain's falls. -/
def theSides (F : FileDescription Xi) {Bk : ProverCoinCounts} (L : Letters F Bk W₀ Rc Ky Tr X₀ X)
    (R : Rows W₀ Rc Xi Ky Tr X₀ X) (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂))
    (f₃ : List (Fall F.S₃)) : Sides F Bk W₀ Rc Ky Tr X₀ X :=
  { first := R.first.map L.first, shared := R.shared.map L.shared,
    second := R.second.map L.second, falls₁ := f₁, falls₂ := f₂, falls₃ := f₃ }

/-- At the letters of the threads they are the sides that the rule for simulators takes. -/
theorem theSides_ofThreads (F : FileDescription Xi) {Bk : ProverCoinCounts}
    (T₁ : Local W₀ Rc Xi Tr → Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (T₂ : Common W₀ Rc Ky → Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky)
    (T₃ : Local W₀ Rc Xi Tr → Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (S₁ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (S₂ : Common W₀ Rc Ky → Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop)
    (S₃ : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (R : Rows W₀ Rc Xi Ky Tr X₀ X) (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂))
    (f₃ : List (Fall F.S₃)) :
    theSides F (Letters.ofThreads F T₁ T₂ T₃ S₁ S₂ S₃) R f₁ f₂ f₃ =
      laySides F T₁ T₂ T₃ S₁ S₂ S₃ R.first R.shared R.second f₁ f₂ f₃ := rfl

/-- Rows whose place and row are kept have the rows' own sides. -/
theorem halves_kept {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type}
    (t : Unlettered V W Y Pb → Lettered Bk S Cl V W Y Pb)
    (hk : ∀ r, (t r).place = r.place ∧ (t r).row = r.row) : ∀ rs : List (Unlettered V W Y Pb),
    ((rs.map t).map fun M => (⟨M.place, M.row.map (·.1)⟩ : Placed V W Y)) = rs.map (·.half)
  | [] => rfl
  | r :: rs => by
    have e : (⟨(t r).place, (t r).row.map (·.1)⟩ : Placed V W Y) = r.half := by
      unfold Unlettered.half
      rw [(hk r).1, (hk r).2]
    rw [List.map_cons, List.map_cons, List.map_cons, halves_kept t hk rs, e]

variable {F : FileDescription Xi} {Bk : ProverCoinCounts}

/-- **Where a prover's sides are the rows' own, the sides' prover is that prover.** -/
theorem theSides_prover {L : Letters F Bk W₀ Rc Ky Tr X₀ X} {R : Rows W₀ Rc Xi Ky Tr X₀ X}
    {f₁ : List (Fall F.S₁)} {f₂ : List (Fall F.S₂)} {f₃ : List (Fall F.S₃)}
    {H : Prover W₀ Rc Xi Ky Tr X₀ X} (h : R.Fit H) : (theSides F L R f₁ f₂ f₃).prover H = H :=
  Sides.prover_self (G := theSides F L R f₁ f₂ f₃)
    (h.1.trans (halves_kept L.first L.keeps₁ R.first).symm)
    (h.2.1.trans (halves_kept L.shared L.keeps₂ R.shared).symm)
    (h.2.2.trans (halves_kept L.second L.keeps₃ R.second).symm)

/-- **The prover depends on the rows alone**, not on the letters or the falls. -/
theorem prover_letters (L L' : Letters F Bk W₀ Rc Ky Tr X₀ X) (R : Rows W₀ Rc Xi Ky Tr X₀ X)
    (f₁ g₁ : List (Fall F.S₁)) (f₂ g₂ : List (Fall F.S₂)) (f₃ g₃ : List (Fall F.S₃))
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) :
    (theSides F L R f₁ f₂ f₃).prover H = (theSides F L' R g₁ g₂ g₃).prover H := by
  unfold Sides.prover theSides
  simp only [halves_kept L.first L.keeps₁, halves_kept L.shared L.keeps₂,
    halves_kept L.second L.keeps₃, halves_kept L'.first L'.keeps₁,
    halves_kept L'.shared L'.keeps₂, halves_kept L'.second L'.keeps₃]

/-- The sides at a description that equals theirs. -/
def castSides {F' : FileDescription Xi} (e : F = F') (G : Sides F' Bk W₀ Rc Ky Tr X₀ X) :
    Sides F Bk W₀ Rc Ky Tr X₀ X := e ▸ G

/-- The prover does not move with the description. -/
theorem castSides_prover {F' : FileDescription Xi} (e : F = F') (G : Sides F' Bk W₀ Rc Ky Tr X₀ X)
    (H : Prover W₀ Rc Xi Ky Tr X₀ X) : (castSides e G).prover H = G.prover H := by
  subst e
  rfl

/-- **Every statement on the sides crosses with them**: whatever holds of G at its description holds
of G at the description that equals it. -/
theorem castSides_of {F' : FileDescription Xi} (e : F = F') {G : Sides F' Bk W₀ Rc Ky Tr X₀ X}
    {Q : ∀ F₀ : FileDescription Xi, Sides F₀ Bk W₀ Rc Ky Tr X₀ X → Prop} (h : Q F' G) :
    Q F (castSides e G) := by
  subst e
  exact h

/-- And back. -/
theorem of_castSides {F' : FileDescription Xi} (e : F = F') {G : Sides F' Bk W₀ Rc Ky Tr X₀ X}
    {Q : ∀ F₀ : FileDescription Xi, Sides F₀ Bk W₀ Rc Ky Tr X₀ X → Prop} (h : Q F (castSides e G)) :
    Q F' G := by
  subst e
  exact h

end Letters

section Slots
variable {W₀ Rc Tr X₀ X : Type}

/-- **The rows at a filling, with a slot for each lot of the first chain.** At the public part and
the ground at hand, the rows are the filling's once their simulators, On and bud are forgotten. -/
structure RowSlots (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) where
  lots : List (SLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
  lots_fit : (rowsOfLots Z Gr lots).map (·.half) = firstOf Z Gr P.lots
  shared : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)
  shared_fit : shared.map (·.half) = P.shared Z Gr
  second : List (Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
  second_fit : second.map (·.half) = P.second Z Gr

variable {P : OnlineProverParts W₀ Rc Tr X₀ X} {Z : ProofFile.Pub} {Gr : ProofFile.Ground}

/-- The rows of the slots. -/
def RowSlots.rows (s : RowSlots P Z Gr) : Rows W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X :=
  ⟨rowsOfLots Z Gr s.lots, s.shared, s.second⟩

/-- **At what the maker returns, its prover's sides are the slots' own.** -/
theorem RowSlots.fit {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) (s : RowSlots P A.Z A.G) : s.rows.Fit A.H := by
  obtain ⟨-, -, -, -, -, -, -, h₁, h₂, h₃, -⟩ := atPure_ok hA
  refine ⟨?_, ?_, ?_⟩
  · rw [h₁]
    exact s.lots_fit.symm
  · rw [h₂]
    exact s.shared_fit.symm
  · rw [h₃]
    exact s.second_fit.symm

variable {V W Y Pb : Type}

/-- A lot of the filling beside simulators that tell nothing. -/
def bareSlot (L : HLot V W Y) : SLot V W Y Pb :=
  ⟨L.name, fun Z G => (L.halves Z G).map bareUnlettered⟩

/-- **A kind's own lot, where the list holds one of that name**; else the filling's, bare. -/
def overlayLot (mine : List (SLot V W Y Pb)) (L : HLot V W Y) : SLot V W Y Pb :=
  match mine.find? fun s => s.name == L.name with
  | some s => s
  | none => bareSlot L

theorem overlay_half {mine : List (SLot V W Y Pb)} {L : HLot V W Y}
    (h : ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows Z Gr).map (·.half) = L.halves Z Gr) :
    ((overlayLot mine L).rows Z Gr).map (·.half) = L.halves Z Gr := by
  unfold overlayLot
  cases e : mine.find? fun s => s.name == L.name with
  | some s => exact h s e
  | none => exact map_half_bare _

theorem rows_overlay {mine : List (SLot V W Y Pb)} : ∀ {ls : List (HLot V W Y)},
    (∀ L ∈ ls, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows Z Gr).map (·.half) = L.halves Z Gr) →
    (rowsOfLots Z Gr (ls.map (overlayLot mine))).map (·.half) = firstOf Z Gr ls
  | [], _ => rfl
  | L :: t, h => by
    have e₁ : rowsOfLots Z Gr ((L :: t).map (overlayLot mine)) =
        (overlayLot mine L).rows Z Gr ++ rowsOfLots Z Gr (t.map (overlayLot mine)) := rfl
    have e₂ : firstOf Z Gr (L :: t) = L.halves Z Gr ++ firstOf Z Gr t := rfl
    rw [e₁, e₂, List.map_append, overlay_half (h L List.mem_cons_self),
      rows_overlay fun L' hL' => h L' (List.mem_cons_of_mem _ hL')]

/-- **The filling's lots, with the kinds' own lots laid over them.** Each of the kinds' lots has a
name of its own and the name of a lot of the filling, so that none is left out in silence. The two
other chains' rows are arguments. -/
def overlaySlots (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : ProofFile.Pub) (Gr : ProofFile.Ground)
    (mine : List (SLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst))
    (_named : ∀ s ∈ mine, P.lots.any (fun L => L.name == s.name) = true)
    (_apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ P.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows Z Gr).map (·.half) = L.halves Z Gr)
    (shared : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey))
    (hs : shared.map (·.half) = P.shared Z Gr)
    (second : List (Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst))
    (h₃ : second.map (·.half) = P.second Z Gr) : RowSlots P Z Gr :=
  ⟨P.lots.map (overlayLot mine), rows_overlay hm, shared, hs, second, h₃⟩

/-- **A kind's own row at a side of the chain, where the list holds one at that place**; else the
side, bare. -/
def overlayRow (mine : List (Unlettered V W Y Pb)) (h : Placed V W Y) : Unlettered V W Y Pb :=
  match mine.find? fun r => r.place == h.place with
  | some r => r
  | none => bareUnlettered h

theorem overlayRow_half {mine : List (Unlettered V W Y Pb)} {h : Placed V W Y}
    (hm : ∀ r, (mine.find? fun r => r.place == h.place) = some r → r.half = h) :
    (overlayRow mine h).half = h := by
  unfold overlayRow
  cases e : mine.find? fun r => r.place == h.place with
  | some r => exact hm r e
  | none => exact half_bare h

theorem map_overlayRow_half {mine : List (Unlettered V W Y Pb)} : ∀ {hs : List (Placed V W Y)},
    (∀ h ∈ hs, ∀ r, (mine.find? fun r => r.place == h.place) = some r → r.half = h) →
    (hs.map (overlayRow mine)).map (·.half) = hs
  | [], _ => rfl
  | h :: t, hm => by
    rw [List.map_cons, List.map_cons, overlayRow_half (hm h List.mem_cons_self),
      map_overlayRow_half fun h' hh' => hm h' (List.mem_cons_of_mem _ hh')]

/-- A row of the overlay is a kind's own, or the side's, bare. -/
theorem overlayRow_cases (mine : List (Unlettered V W Y Pb)) (h : Placed V W Y) :
    overlayRow mine h ∈ mine ∨ overlayRow mine h = bareUnlettered h := by
  unfold overlayRow
  cases e : mine.find? fun r => r.place == h.place with
  | some r => exact Or.inl (List.mem_of_find?_eq_some e)
  | none => exact Or.inr rfl

/-- **What each kind lays at a filling, on each chain.** Each of the kinds' own lots has a name of its
own and the name of a lot of the filling, and their rows on the other two chains stand each at a
place of its own, of a side of that chain, so that none is left out in silence. -/
structure KindRows (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) where
  lots : List (SLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
  named : ∀ s ∈ lots, P.lots.any (fun L => L.name == s.name) = true
  apart : (lots.map (·.name)).Nodup
  lots_fit : ∀ L ∈ P.lots, ∀ s, (lots.find? fun s => s.name == L.name) = some s →
    (s.rows Z Gr).map (·.half) = L.halves Z Gr
  shared : List (Unlettered Empty (Common W₀ Rc OnBytes.TableKey) X₀ OnBytes.TableKey)
  shared_named : ∀ r ∈ shared, (P.shared Z Gr).any (fun h => h.place == r.place) = true
  shared_apart : (shared.map (·.place)).Nodup
  shared_fit : ∀ h ∈ P.shared Z Gr, ∀ r, (shared.find? fun r => r.place == h.place) = some r →
    r.half = h
  second : List (Unlettered (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
  second_named : ∀ r ∈ second, (P.second Z Gr).any (fun h => h.place == r.place) = true
  second_apart : (second.map (·.place)).Nodup
  second_fit : ∀ h ∈ P.second Z Gr, ∀ r, (second.find? fun r => r.place == h.place) = some r →
    r.half = h

/-- **The slots that the kinds' rows fill**, on all three chains. -/
def KindRows.slots {P : OnlineProverParts W₀ Rc Tr X₀ X} {Z : ProofFile.Pub} {Gr : ProofFile.Ground}
    (K : KindRows P Z Gr) : RowSlots P Z Gr :=
  overlaySlots P Z Gr K.lots K.named K.apart K.lots_fit
    ((P.shared Z Gr).map (overlayRow K.shared)) (map_overlayRow_half K.shared_fit)
    ((P.second Z Gr).map (overlayRow K.second)) (map_overlayRow_half K.second_fit)

/-- **The filling's own lots, bare**: the value for completeness. -/
def bareSlots (P : OnlineProverParts W₀ Rc Tr X₀ X) (Z : ProofFile.Pub) (Gr : ProofFile.Ground) : RowSlots P Z Gr :=
  overlaySlots P Z Gr [] (fun _ h => by cases h) (by simp) (fun _ _ _ h => by simp at h)
    ((P.shared Z Gr).map bareUnlettered) (map_half_bare _) ((P.second Z Gr).map bareUnlettered)
    (map_half_bare _)

end Slots

end AtPublicFiles.TheSides

#print axioms AtPublicFiles.TheSides.bareRows_fit
#print axioms AtPublicFiles.TheSides.theSides_ofThreads
#print axioms AtPublicFiles.TheSides.theSides_prover
#print axioms AtPublicFiles.TheSides.prover_letters
#print axioms AtPublicFiles.TheSides.castSides_prover
#print axioms AtPublicFiles.TheSides.castSides_of
#print axioms AtPublicFiles.TheSides.of_castSides
#print axioms AtPublicFiles.TheSides.RowSlots.fit
#print axioms AtPublicFiles.TheSides.bareSlots
#print axioms AtPublicFiles.TheSides.KindRows.slots
#print axioms AtPublicFiles.TheSides.overlayRow_cases
