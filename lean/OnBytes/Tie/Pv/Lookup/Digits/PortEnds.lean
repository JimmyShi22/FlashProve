-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Digits/PortEnds.lean: what the typed verifier of the lookup on the digits of a
smallness test puts out, at the verifier's own record tl : OnBytes.Model.HTailF2, in the terms of
`Fo.EndsHold`, with the caller's forms the digits' forms on the entries of ZZ.

`Fo.hcEnds` asks that the layout's cell of bit j of the count of row t of call c is a cell of a
matrix, by `FoNums.cellRC`, for every t. The array BZ is no such matrix. So the layout here takes
its cells through a virtual matrix with one row for each plane: row = j, column = c 2^kT + t.

Main names:
  `plV tl en row col`: the virtual matrix: bcJ tl en (col % 2^kT) (col / 2^kT) row.
  `digL5`: the caller's layout `digL` (OnBytes/Tie/Pv/Lookup/Digits/PortKnow.lean) with bc t c j :=
    plV tl en j (c 2^kT + t).
  `digL5_bc`: for t < 2^kT that cell is BZ's, bcJ tl en t c j. Beyond, nothing is stated of it.
  `digL5_cell`: the premise of `Fo.hcEnds` on the cells, at lm := 5.
  `KFd`, `dgP_KFokD`: the caller's forms KFlJ tl (some ∘ en) c (zk c), and `Fo.KFok` of them at
    points of the calls' lengths, under `TailOK tl` (OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean).
  `ends_port`: `Fo.hcEnds` at h := tl.f9, L := digL5, lm := 5, KF := KFd at the record's own points:
    the verifier puts out some x, copies the oracles, and its output claim at x is `Fo.EndsHold`.
    Premises: FoNums.ok tl.f9 = true and `TailOK tl`.
Limits: the typed verifier is `forB` at `V₀`, `V₀C`; nothing here compares it with the routine
`Forest.pad` (OnBytes/Model/Look.lean).
Clauses 2 to 4 of `Fo.EndsHold` speak of the planes in the closed form of
`Forest.planeClaims`, on the virtual matrix. The smallness test writes its three claims on BZ by
hand (`linBits9`, OnBytes/Model/Tail.lean): that these are the same forms on BZ's entries is not
shown. Clause 5 is the plain twin of `Forest.join` at `KFd`; the smallness test writes `linJoin9`:
that the two are one form on ZZ's entries is held by a run at one small made-up shape alone.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoOutAll
import OnBytes.Tie.Pv.Lookup.Digits.PortKnow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.DgP
open OnBytes OnBytes.Model CbQ Cb.LdLkp Cb.Lkp Cb.Fo Iop IOR TWhole

variable {J₀ : Type}

/-- The virtual matrix of the planes: row = the plane, column = (call | row of the call's table). -/
def plV (tl : HTailF2) (en : Ent3 → J₀) (row col : ℕ) : J₀ :=
  bcJ tl en (col % 2 ^ tl.f9.kT) (col / 2 ^ tl.f9.kT) row

/-- The caller's layout, its cells by the virtual matrix. -/
def digL5 (E : Type) [Field E] (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (St₀ : Type)
    : Lay E St₀ J₀ where
  K := fun _ ν => KpJ tl en ν
  bc := fun t c j => plV tl en j (c * 2 ^ tl.f9.kT + t)
  mkS := fun s => mk (jLK + s)

section
variable {E : Type} [Field E] {tl : HTailF2}

/-- Below 2^kT the cell is BZ's. -/
theorem digL5_bc (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (St₀ : Type) {t : ℕ} (ht : t < 2 ^
    tl.f9.kT) (c j : ℕ) :
    (digL5 E tl en mk jLK St₀).bc t c j = bcJ tl en t c j := by
  have hpos : 0 < 2 ^ tl.f9.kT := by positivity
  show bcJ tl en ((c * 2 ^ tl.f9.kT + t) % 2 ^ tl.f9.kT) ((c * 2 ^ tl.f9.kT + t) / 2 ^ tl.f9.kT) j =
      _
  rw [Nat.mul_comm c, Nat.mul_add_mod, Nat.mod_eq_of_lt ht, Nat.mul_add_div hpos, Nat.div_eq_of_lt
      ht, Nat.add_zero]

/-- The premise of `Fo.hcEnds` on the cells, at lm := 5. -/
theorem digL5_cell (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (St₀ : Type) (t c j : ℕ) :
    (digL5 E tl en mk jLK St₀).bc t c j =
      plV tl en (FoNums.cellRC tl.f9 5 (t, c, j)).1 (FoNums.cellRC tl.f9 5 (t, c, j)).2 := by
  have e1 : (FoNums.cellRC tl.f9 5 (t, c, j)).1 = j := by
    show (t % 2 ^ (5 - FoNums.w)) * FoNums.planes + j = j
    have : (2 : ℕ) ^ (5 - FoNums.w) = 1 := rfl
    rw [this, Nat.mod_one, Nat.zero_mul, Nat.zero_add]
  have e2 : (FoNums.cellRC tl.f9 5 (t, c, j)).2 = c * 2 ^ tl.f9.kT + t := by
    show c * 2 ^ (tl.f9.kT + FoNums.w - 5) + t / 2 ^ (5 - FoNums.w) = _
    have h1 : (2 : ℕ) ^ (5 - FoNums.w) = 1 := rfl
    have h2 : tl.f9.kT + FoNums.w - 5 = tl.f9.kT := Nat.add_sub_cancel tl.f9.kT 5
    rw [h1, h2, Nat.div_one]
  rw [e1, e2]
  rfl

/-- The caller's forms: the digits' forms on ZZ's entries, at the type with one more entry. -/
def KFd (tl : HTailF2) (en : Ent3 → J₀) (zk : ℕ → List E) (c : ℕ) : Fo.AffK (Option J₀) E :=
  KFlJ tl (fun n => some (en n)) c (zk c)

/-- `Fo.KFok` of these forms, at points of the calls' lengths. -/
theorem dgP_KFokD (hT : TailOK tl) (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) {St₀ : Type} (st : St₀)
    (zk : ℕ → List E)
    (hz : ∀ c < tl.f9.NC, (zk c).length = Port.nOf tl.f9 c) :
    Fo.KFok tl.f9 (forK E (digL5 E tl en mk jLK St₀) st) zk (KFd tl en zk) := by
  intro μ c hc
  have hc2 : c < 2 := by rw [← hT.nc]; exact hc
  have e := dgP_KFokJ (fun n => some (en n)) hT μ hc2 (zk c) (hz c hc)
  have e2 : Fo.extL (KpJ tl (fun n => some (en n)) μ c) (zk c) =
      Blocks.ext (zk c).length (KpJ tl (fun n => some (en n)) μ c) (Blocks.ofList (zk c)) := by
    have e3 := Fo.ext_top (KpJ tl (fun n => some (en n)) μ c) (zk c).length (Fo.ptL (zk c))
    have e4 : (List.range (zk c).length).map (Fo.ptL (zk c)) = zk c := Fo.rho_ptL (zk c)
    rw [e4] at e3
    exact e3
  show Fo.AffK.val (KFlJ tl (fun n => some (en n)) c (zk c)) μ = Fo.extL (KpJ tl (fun n => some (en
      n)) μ c) (zk c)
  rw [e2]
  exact e

end

/-- What the typed verifier of the lookup on the digits puts out, at the verifier's own record. -/
theorem ends_port (E : Type) [Field E] [Fintype E] (St₀ : Type) [Fintype J₀] [DecidableEq J₀] (tl :
    HTailF2)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (jLK : ℕ) (H : FoNums.ok tl.f9 = true) (hT : TailOK tl)
    (Ex : ExtSpec) (a : St₀ × Ex.Str) (τ : Tr (forB E tl.f9 (digL5 E tl en mk jLK St₀) V₀ V₀C (Ex :=
        Ex)).R.shape) :
    ∃ x : TX (St₀ × E) E (Option J₀),
      (forB E tl.f9 (digL5 E tl en mk jLK St₀) V₀ V₀C (Ex := Ex)).R.red.out a τ = some (x, a.2) ∧
      ∀ μ₀ : J₀ → E,
        ((forA E tl.f9 (digL5 E tl en mk jLK St₀)).lk.out id id x (zext μ₀) ↔
          Fo.EndsHold tl.f9 5 jLK (Fo.forFl tl.f9 (digL5 E tl en mk jLK St₀) Ex τ)
            (Fo.mapL (Cb.Fo.NumsEq.placeOf mk (plV tl en))
                (Fo.endsOf tl.f9 5 jLK (Fo.forFl tl.f9 (digL5 E tl en mk jLK St₀) Ex τ)).cEndF,
              (Fo.endsOf tl.f9 5 jLK (Fo.forFl tl.f9 (digL5 E tl en mk jLK St₀) Ex τ)).cEndC)
            (KFd tl en fun c => (Fo.endsOf tl.f9 5 jLK (Fo.forFl tl.f9 (digL5 E tl en mk jLK St₀) Ex
                τ)).zk.getD c [])
            (fun p => zext μ₀ (Cb.Fo.NumsEq.placeOf mk (plV tl en) p)) (zext μ₀)) := by
  obtain ⟨x, h1, h2⟩ := Fo.hcEnds E St₀ J₀ tl.f9 (digL5 E tl en mk jLK St₀) 5 jLK mk (plV tl en) H
      (le_refl 5)
    (Nat.le_add_left 5 tl.f9.kT) (fun _ => rfl) (fun t c j _ => digL5_cell en mk jLK St₀ t c j) Ex a
        τ
  refine ⟨x, h1, fun μ₀ => h2 _ μ₀ (dgP_KFokD hT en mk jLK a.1 _ (fun c hc => ?_) (zext μ₀))⟩
  obtain ⟨_, _, hcalls, _⟩ := ok_parts H
  have hio : FoNums.io tl.f9 c ≤ tl.f9.rK := (Fo.ok_prem H).le c hc
  rw [Fo.ends_zk tl.f9 H 5 jLK _ c hc]
  show (List.drop (tl.f9.rK - FoNums.io tl.f9 c) _ ++ _).length = _
  rw [List.length_append, List.length_drop, Fo.ends_zy_len tl.f9 H, Fo.ends_zx_len tl.f9 H]
  have hn : Port.nOf tl.f9 c = FoNums.io tl.f9 c + tl.f9.dT := (hcalls c hc).2.2.1
  omega

#print axioms digL5_bc
#print axioms digL5_cell
#print axioms dgP_KFokD
#print axioms ends_port

end OnBytes.DgP
