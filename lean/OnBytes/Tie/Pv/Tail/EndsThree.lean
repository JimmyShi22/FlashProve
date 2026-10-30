-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/EndsThree.lean: three lists of claims with exponents, whose exponents lie in
three stretches one behind the other, have together no exponent twice, and all lie below the end of
the last stretch; the list `rowsForm` (OnBytes/Tie/Pv/Tail/EndForms.lean) as the third.

Statements and proofs. Plain facts on lists. A sub-proof's one ledger holds the caller's claims, the
lookup's claims, and the single equations of the smallness test's ties and reads; the last stand
from the plan's number of claims on.
Main names:
  `inj_of_nodup`: where no exponent stands twice, two members with one exponent are one member.
  `exps_numbered`: a list that is numbered from c on has the exponents c, c + 1 and so on.
  `exps_three`: three lists with exponents in [0, a), [a, pc) and [pc, n): no exponent twice; all
    below n.
  `exps_map`: a map on the claims that leaves the exponents leaves both facts.
  `exps_rowsForm`: `rowsForm Y ρ tl funs pc` has no exponent twice, and its exponents lie from pc on
    and below pc + `topOf tl funs`. No run of the verifier is asked, but a premise on the shapes:
    each has as many rows of symbols as its rows of cells want.
  `mS_of_run`: that premise, where objectsF returns and the shapes fit the matrices.
  `exps_ledger`: so for two lists in [0, a) and [a, pc) and `rowsForm`, its forms carried on by any
    map.
Limits: that the caller's and the lookup's claims stand below the plan's number of claims is a
premise.
-/
import OnBytes.Tie.Pv.Tail.EndForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Port

open OnBytes OnBytes.Model OnBytes.Road.Rows

/-- Where no exponent stands twice, two members with one exponent are one member. -/
theorem inj_of_nodup {α : Type} {L : List (Nat × α)} (h : (L.map Prod.fst).Nodup) :
    ∀ z ∈ L, ∀ z' ∈ L, z.1 = z'.1 → z = z' :=
  fun _ hz _ hz' e => List.inj_on_of_nodup_map h hz hz' e

/-- A list that is numbered from c on. -/
theorem exps_numbered {α : Type} (c : Nat) (L : List α) :
    (((List.range' c L.length).zip L).map Prod.fst).Nodup ∧
      ∀ z ∈ (List.range' c L.length).zip L, c ≤ z.1 ∧ z.1 < c + L.length := by
  have e : ((List.range' c L.length).zip L).map Prod.fst = List.range' c L.length :=
    List.map_fst_zip (by rw [List.length_range'])
  refine ⟨by rw [e]; exact List.nodup_range', fun z hz => ?_⟩
  have h1 : z.1 ∈ List.range' c L.length := by
    rw [← e]
    exact List.mem_map.2 ⟨z, hz, rfl⟩
  have h2 := List.mem_range'_1.1 h1
  exact h2

/-- Three lists whose exponents lie in three stretches, one behind the other. -/
theorem exps_three {α : Type} {L₁ L₂ L₃ : List (Nat × α)} {a pc n : Nat}
    (h1 : (L₁.map Prod.fst).Nodup) (h2 : (L₂.map Prod.fst).Nodup) (h3 : (L₃.map Prod.fst).Nodup)
    (b1 : ∀ z ∈ L₁, z.1 < a) (b2 : ∀ z ∈ L₂, a ≤ z.1 ∧ z.1 < pc)
    (b3 : ∀ z ∈ L₃, pc ≤ z.1 ∧ z.1 < n) (ha : a ≤ pc) (hn : pc ≤ n) :
    ((L₁ ++ (L₂ ++ L₃)).map Prod.fst).Nodup ∧ ∀ z ∈ L₁ ++ (L₂ ++ L₃), z.1 < n := by
  constructor
  · rw [List.map_append, List.map_append, List.nodup_append, List.nodup_append]
    refine ⟨h1, ⟨h2, h3, ?_⟩, ?_⟩
    · intro x hx y hy e
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hy
      have := (b2 z hz).2
      have := (b3 z' hz').1
      omega
    · intro x hx y hy e
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
      have := b1 z hz
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hy
        have := (b2 z' hz').1
        omega
      · obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hy
        have := (b3 z' hz').1
        omega
  · intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · have := b1 z hz
      omega
    · rcases List.mem_append.1 hz with hz | hz
      · have := (b2 z hz).2
        omega
      · exact (b3 z hz).2

/-- A map on the claims that leaves the exponents. -/
theorem exps_map {α β : Type} (g : α → β) (L : List (Nat × α)) :
    (L.map fun p => (p.1, g p.2)).map Prod.fst = L.map Prod.fst := by
  rw [List.map_map]
  rfl

variable {K : Type} [Field K] {J : Type} (Y : Lay J)

/-- The exponents of the list of the ties' and reads' single equations. -/
theorem exps_rowsForm (ρ : Reading K) (tl : HTailF2) (funs : Array HFun) (pc : Nat)
    (hmS : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m) :
    ((rowsForm Y ρ tl funs pc).map Prod.fst).Nodup ∧
      ∀ p ∈ rowsForm Y ρ tl funs pc, pc ≤ p.1 ∧ p.1 < pc + topOf tl funs := by
  refine ⟨by rw [fst_rowsForm]; exact nodup_of_rising (rising_rowsTail ρ tl funs pc hmS),
    fun p hp => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hp
  exact bounds_rowsTail ρ tl funs pc hmS r hr

/-- Where objectsF returns and the shapes fit the matrices, each shape has as many rows of symbols
as its rows of cells want. -/
theorem mS_of_run (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (hfit : Fits tl) :
    ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m := by
  obtain ⟨_, Fa0, ca0, tla0, Fb0, cb0, tlb0, Fc0, cc0, tl1, F10, c10, _, _, hJ0, hB0, hWt0, _,
    _, _, _, _⟩ :=
    objectsF_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ tl tl' funs F G c c' h
  have ea := linJoin9_spec tl tla0 Fa0 Fb0 ca0 cb0 hJ0
  have eb := linBits9_spec tla0 tlb0 Fb0 Fc0 cb0 cc0 hB0
  obtain ⟨_, _, hP1, e1⟩ := weightsF_spec tlb0 tl1 Fc0 F10 cc0 c10 hWt0
  have sNM : tl1.NM = tl.NM := carry4 (fun t => t.NM) ea rfl eb rfl e1 rfl rfl rfl
  have sShp : tl1.shp = tl.shp := carry4 (fun t => t.shp) ea rfl eb rfl e1 rfl rfl rfl
  have sMats : tl1.mats = tl.mats := carry4 (fun t => t.mats) ea rfl eb rfl e1 rfl rfl rfl
  intro mu hmu
  have e := (hP1.shape mu (by rw [sNM]; exact hmu)).2.2.2.2
  rw [sShp, sMats] at e
  rw [e, (hfit mu hmu).1]
  rfl

/-- Two lists below the plan's number of claims, and the list of the ties' and reads' single
equations with its forms carried on by a map g: no exponent twice, all below pc + `topOf`. -/
theorem exps_ledger {β : Type} (g : TWhole.Form K J → β) (ρ : Reading K) (tl : HTailF2)
    (funs : Array HFun) (pc : Nat)
    (hmS : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m)
    {L₁ L₂ : List (Nat × β)} {a : Nat} (h1 : (L₁.map Prod.fst).Nodup)
    (h2 : (L₂.map Prod.fst).Nodup) (b1 : ∀ z ∈ L₁, z.1 < a) (b2 : ∀ z ∈ L₂, a ≤ z.1 ∧ z.1 < pc)
    (ha : a ≤ pc) :
    ((L₁ ++ (L₂ ++ (rowsForm Y ρ tl funs pc).map fun p => (p.1, g p.2))).map Prod.fst).Nodup ∧
      ∀ z ∈ L₁ ++ (L₂ ++ (rowsForm Y ρ tl funs pc).map fun p => (p.1, g p.2)),
        z.1 < pc + topOf tl funs := by
  obtain ⟨n3, b3⟩ := exps_rowsForm Y ρ tl funs pc hmS
  refine exps_three h1 h2 (by rw [exps_map]; exact n3) b1 b2 (fun z hz => ?_) ha
    (Nat.le_add_right _ _)
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
  exact b3 p hp

end OnBytes.Tie.Pv.Tail.Port

#print axioms OnBytes.Tie.Pv.Tail.Port.inj_of_nodup
#print axioms OnBytes.Tie.Pv.Tail.Port.exps_numbered
#print axioms OnBytes.Tie.Pv.Tail.Port.exps_three
#print axioms OnBytes.Tie.Pv.Tail.Port.exps_rowsForm
#print axioms OnBytes.Tie.Pv.Tail.Port.mS_of_run
#print axioms OnBytes.Tie.Pv.Tail.Port.exps_ledger
