-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/TwTies.lean.
The numbers, the lists and the places of keys and planes of the small lookup `o65A`: each is a field
of `OnBytes.Lkp.o65`, a formula in its fields, or a function of OnBytes/Iop/Lkp.lean at it. The
places of the mask entries are not among them (see Limits).

Statements and proofs. By construction `o65A := keyA Cb.Gl.E (Sizes.ofPublic Lkp.o65)`; here that is
said, field by field.
Main names:
  sizes: `tie_parts`, `tie_d`, `tie_w`, `tie_planes`, `tie_full`; no shift, one part, no tree
    numbers, no dead plane: `tie_bare`; the three index types: `tie_J`; `tie_keys`, `tie_served`,
    `tie_ok`.
  the padding, by fields: `tie_pads`, `tie_key_pad`, `tie_key_const`, `tie_key_entry`.
  the table: `tie_tab` (through `OnBytes.Slice.readE`; `Lkp.rowAt` at theta = `zeroE` alone); the
    planes: `tie_bAt` (entry j + 2^mu u: a formula in the field mu).
  the orders: `tie_oK0` to `tie_oK3`, `tie_oT`, `tie_oE`, `tie_oB` (`Lkp.defaultOrder`,
    `Lkp.orderBeginning` at `lastKeyLevelOrder`), and that they are the lists of
    OnBytes/Tie/Pv/Lookup/Port/TwNums.lean: tie_ord*.
  degs_*: the lists of formats in the types of the fields wAt, wK, wT, wB, wE of `LkAsmH`, written
    out again here, have the degrees `degs` of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean.
  the premises on public numbers of `one_knowAt` (OnBytes/Tie/Pv/Lookup/Know/TwOne.lean), at the
    small lookup: `o65_adm`, `o65_padsOK`, `o65_full`.
What is typed a second time anywhere under the value, and by what it is tied:
(a) OnBytes/Tie/Pv/Lookup/Order/E3O65.lean types 4, [1], 3, 1 in `E3.o65K`, `o65T`, `o65E`, `o65B`:
tied to `o65A` by `o65A_oK` to `o65A_oB` (rfl, OnBytes/Tie/Pv/Lookup/Value/TwO65.lean) and to the
fields of `OnBytes.Lkp.o65` by `tie_E3K`, `tie_E3T`, `tie_E3E`, `tie_E3B` (rfl);
(b) the 15, 16, 104 of `o65J`: rfl (OnBytes/Tie/Pv/Lookup/Value/TwO65.lean), `tie_J`, `tie_Ix`
(OnBytes/Tie/Pv/Lookup/Port/TwSigma.lean [not in this library]);
(c) `tab := fun _ u => u`: `tie_tab`;
(d) "Fin 15" and "u < 2" in `o65_RA_iff` and `o65RA`: the types are those of `o65J`; the rows:
`tie_tab`, `tie_d`.
Limits: all at one value, but for `keyA_bAt` and `degs_tie` to `degs_bit`. The places of the mask
entries are functions of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean, no function of
OnBytes/Iop/Lkp.lean: they are tied to `Psc.hidingForm`, place by place, by tests alone
(OnBytes/Tie/Pv/Lookup/Test/TwTiesTest.lean [not in this library]; so here read: not tested in this
library). They are meant as the places of `Lkp.verify` only where it gets no second mask message
(`keyMasks := none`): the entries of the last key level's two shown values (73, 74) then come from
the same list of places in turn. What does not show at this value: the head of
OnBytes/Tie/Pv/Lookup/Port/TwNumsO65.lean.

-/
import OnBytes.Tie.Pv.Lookup.Lists.TwLen
import OnBytes.Slice.ProgField

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Finset
open TwNums (Sizes o65S)

/-- `OnBytes.Lkp.o65`, by a short name; the field -/
abbrev G1 : OnBytes.Lkp.Public := OnBytes.Lkp.o65
abbrev K : Type := Cb.Gl.E

/-! ### sizes -/
theorem tie_parts : G1.parts = [o65A.v' + 1] := rfl
theorem tie_d : o65A.d = G1.d := rfl
theorem tie_w : o65A.w = G1.mu := rfl
theorem tie_planes : o65A.n + 2 = G1.planes := rfl
theorem tie_full : G1.planes = 2 ^ o65A.w := rfl
/-- no shift block, one part, no tree numbers, no dead plane -/
theorem tie_bare : G1.parts.length = 1 ∧ G1.g = 0 ∧ G1.h = 0 ∧ G1.shifted = false ∧ G1.live = 0 ∧
    G1.readFrom = [0, 1] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
/-- the caller's three index types, in the order keys 0, planes 1, masks 2 -/
theorem tie_J : o65A.J = (Fin (G1.allKeys - OnBytes.Lkp.paddingCount G1) ⊕
    Fin (2 ^ (G1.mu + G1.d)) ⊕ Fin (OnBytes.Lkp.allMasks G1)) := rfl

/-- one block of trees, with function 0, none without a function -/
theorem tie_keys : G1.keys.length = 1 ∧ (G1.keys.all fun b => b.function == some 0) = true :=
  ⟨rfl, rfl⟩
/-- the two Bool tests of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean hold at the value -/
theorem tie_served : Sizes.served G1 = true := by decide
theorem tie_ok : o65S.ok = true := by decide
/-- the four values of OnBytes/Tie/Pv/Lookup/Order/E3O65.lean, which type the small lookup's numbers
a second time, are the total functions `E3.ordKeyW` (the same file) and `E3.ordDefault`
(Cb/Pv/Lookup/Order/E3Ord.lean) at the fields of `OnBytes.Lkp.o65` -/
theorem tie_E3K :
    E3.o65K = fun l => E3.ordKeyW (G1.parts.headD 0) G1.lastKeyLevelOrder (0 + l) := rfl
theorem tie_E3T : E3.o65T = fun l => E3.ordDefault (G1.mu + l) := rfl
theorem tie_E3E : E3.o65E = E3.ordDefault (G1.mu + G1.d) := rfl
theorem tie_E3B : E3.o65B = E3.ordDefault (G1.mu + G1.d) := rfl

/-! ### the padding, by fields -/
theorem tie_pads : o65A.pads = G1.padding.map fun p => (p.row, p.length) := rfl
/-- every place of every run of padding is read as the public constant: that run's row of the
table -/
theorem tie_key_pad (m : o65A.J → K) :
    ∀ p ∈ G1.padding, p.part = 0 ∧
      ∀ i < p.length, o65A.key () m (p.first + i * 2 ^ p.logStep) = o65A.tab () p.row := by
  intro p hp
  have e : p = { part := 0, first := 15, logStep := 0, length := 1, row := 1 } :=
    List.mem_singleton.mp hp
  subst e
  refine ⟨rfl, fun i hi => ?_⟩
  have : i = 0 := by
    have h1 : i < 1 := hi
    omega
  subst this
  rfl
/-- a key number is read as a constant exactly at the places of the runs -/
theorem tie_key_const : ∀ b < 2 ^ (o65A.v' + 1), (kAt K o65S b).isRight =
    G1.padding.any fun p => decide (p.first ≤ b) && ((b - p.first) % 2 ^ p.logStep == 0) &&
      decide ((b - p.first) / 2 ^ p.logStep < p.length) := by
  intro b hb
  have hb' : b < 16 := hb
  interval_cases b <;> rfl
/-- and elsewhere as the entry of its own number (the one run stands behind all keys) -/
theorem tie_key_entry (m : o65A.J → K) (b : Fin 15) : o65A.key () m b.1 = m (.inl b) := by
  show Sum.elim m id (kAt K o65S b.1) = _
  rw [o65_kAt_lt b]
  rfl

/-! ### the table; the planes -/
theorem tie_tab : ∀ u < 2 ^ G1.d,
    OnBytes.Slice.readE (OnBytes.Lkp.rowAt G1 OnBytes.zeroE u) = o65A.tab () u := by
  intro u hu
  have hu' : u < 2 := hu
  interval_cases u <;> decide +kernel

theorem keyA_bAt (E : Type) [Field E] [Fintype E] (S : Sizes) (u j : ℕ)
    (h : j + 2 ^ S.w * u < S.nPlanes) :
    (keyA E S).bAt u j = .inr (.inl ⟨j + 2 ^ S.w * u, h⟩) := by
  show mkP S (S.planeEntry u j) = _
  unfold mkP
  rw [dif_pos (show S.planeEntry u j < S.nPlanes from h)]
  rfl
/-- bit j of row u's count stands at entry j + 2^mu u of the planes' message -/
theorem tie_bAt (u j : ℕ) (hu : u < 2 ^ G1.d) (hj : j < 2 ^ G1.mu) :
    o65A.bAt u j = .inr (.inl ⟨j + 2 ^ G1.mu * u, by
      have h1 : u < 2 := hu
      have h2 : j < 8 := hj
      show j + 8 * u < 16
      omega⟩) :=
  keyA_bAt K o65S u j _

/-! ### the orders: the lists of OnBytes/Iop/Lkp.lean, and those of
OnBytes/Tie/Pv/Lookup/Port/TwNums.lean -/
theorem tie_oK0 : E3.asList (o65A.oK 0) = OnBytes.Lkp.defaultOrder 0 := by rw [o65A_oK]; decide
theorem tie_oK1 : E3.asList (o65A.oK 1) = OnBytes.Lkp.defaultOrder 1 := by rw [o65A_oK]; decide
theorem tie_oK2 : E3.asList (o65A.oK 2) = OnBytes.Lkp.defaultOrder 2 := by rw [o65A_oK]; decide
theorem tie_oK3 : E3.asList (o65A.oK 3) = OnBytes.Lkp.orderBeginning G1.lastKeyLevelOrder 3 := by
  rw [o65A_oK]; decide
theorem tie_oT : E3.asList (o65A.oT 0) = OnBytes.Lkp.defaultOrder (G1.mu + 0) := by
  rw [o65A_oT]; decide
theorem tie_oE : E3.asList o65A.oE = OnBytes.Lkp.defaultOrder (G1.mu + G1.d) := by
  rw [o65A_oE]; decide
theorem tie_oB : E3.asList o65A.oB = OnBytes.Lkp.defaultOrder (G1.mu + G1.d) := by
  rw [o65A_oB]; decide
theorem tie_ordK : ∀ l < o65A.v' + 1, E3.asList (o65A.oK l) = o65S.ordK l := by
  intro l hl
  have hl' : l < 4 := hl
  rw [o65A_oK]
  interval_cases l <;> decide
theorem tie_ordT : E3.asList (o65A.oT 0) = o65S.ordT 0 := by rw [o65A_oT]; decide
theorem tie_ordE : E3.asList o65A.oE = o65S.ordE := by rw [o65A_oE]; decide
theorem tie_ordB : E3.asList o65A.oB = o65S.ordB := by rw [o65A_oB]; decide

/-! ### the typed formats have the degrees of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean -/
section
variable (E : Type) [Field E] [Fintype E] (S : Sizes)
theorem degs_tie (j : ℕ) :
    ((([] : List (PFmt E)) ++ [pDummy E 3]).map PFmt.n) = (S.scTie j).degs := rfl
theorem degs_key (l : ℕ) :
    ((List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]).map PFmt.n) = (S.scKey l).degs := by
  simp [Sizes.scKey, pDummy]
theorem degs_tab (l : ℕ) :
    ((List.replicate (S.w + l) (pfCube E 2) ++ [pDummy E 2]).map PFmt.n) = (S.scTab l).degs := by
  simp [Sizes.scTab, pDummy]
theorem degs_bit :
    ((List.replicate (S.w + S.d) (pfCube E 2) ++ [pDummy E 2]).map PFmt.n) = S.scBit.degs := by
  simp [Sizes.scBit, pDummy]
end
theorem degs_end :
    ((pfMix K (o65A.w + o65A.d) (dgEnd o65A.w o65A.d o65A.oE)).map PFmt.n) = o65S.scEnd.degs := by
  decide

/-! ### the premises on public numbers, at the small lookup -/
theorem o65_adm : o65A.H.lkb.Adm Cb.Gl.p := by
  refine ⟨?_, ?_, ?_⟩ <;> decide
theorem o65_padsOK : padsOK (o65A.v' + 1) o65A.d o65A.pads = true := by decide
theorem o65_full : o65A.n + 1 + 1 = 2 ^ o65A.w := by decide

end Cb.Tw

#print axioms Cb.Tw.tie_J
#print axioms Cb.Tw.tie_key_pad
#print axioms Cb.Tw.tie_key_const
#print axioms Cb.Tw.tie_key_entry
#print axioms Cb.Tw.tie_tab
#print axioms Cb.Tw.tie_bAt
#print axioms Cb.Tw.tie_oK3
#print axioms Cb.Tw.tie_ordK
#print axioms Cb.Tw.degs_end
#print axioms Cb.Tw.o65_adm
