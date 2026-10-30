-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/DrawJoin.lean: the code switch: ALL GENERATOR ROWS, ROW BY ROW: for
each draw and each coordinate of the long symbol, the row that the program lays at a named place of
its list has the symbol read as its target and the typed library's generator row as its vector.

It gathers: RowsAt.lean (rows_gen: where a draw's rows stand in the list of all rows), GenJoin.lean
(gens_main, gens_kept, gens_mask: where each row stands within a draw; main_reads, mask0_reads,
mask1_reads) and KeptJoin.lean (kept_reads).
Main names:
  rowPlace  the place of a coordinate's row among the rows of one draw: the main row 0; the kept
            rows by member and row; then the carried mask row and the fresh mask row
  coordOf   the number of a coordinate's symbol among the symbols read at a position: the main row
            0; kept row number n: 1 + n; mask row j: the program's old.maskRow j
  gen_join  THE JOIN
  names_at_maps, namesK_at_maps  the clauses of Names and NamesK on where entries lie hold BY
            DEFINITION at the two maps iJ and iQ of Johnson/Top/H/SwitchMaps.lean, which are there
            under hJ and hQ (every name lies in a table: InTab), two premises; the other clauses
            stay premises
LIMITS. Those of GenJoin.lean and KeptJoin.lean. The typed complex has two mask rows: old.masks = 2
is a premise. That each drawn position lies below 2 ^ logN of the old main code is a premise (hx).
Nothing is said on the carried claim or on the old sample rows. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hands.KeptJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Johnson.Pack Johnson.Top.H H2K.Lift

section Places
variable (s : Sg) (K : Type) [Fintype K] [DecidableEq K]

/-- The place of a coordinate's row among the rows of one draw. -/
def rowPlace (W : SwitchFrame) (mem row : K → ℕ) : (s.cKept K).Aa → ℕ
  | .inl (none, _) => 0
  | .inl (some κ, _) => 1 + (rowsBefore W.kept (mem κ) + row κ)
  | .inr (.inl _) => 1 + (keptRows W + 0)
  | .inr (.inr _) => 1 + (keptRows W + 1)

/-- The number of a coordinate's symbol among the symbols read at a position. -/
def coordOf (W : SwitchFrame) (old : SingleRows) (mem row : K → ℕ) : (s.cKept K).Aa → ℕ
  | .inl (none, _) => 0
  | .inl (some κ, _) => 1 + (rowsBefore W.kept (mem κ) + row κ)
  | .inr (.inl _) => old.maskRow 0
  | .inr (.inr _) => old.maskRow 1

end Places

section Join
variable {s : Sg} {K : Type} [Fintype K] [DecidableEq K] {cs : Codes} {l : List (OracleShape × ℕ)}
  {iJ : (s.cKept K).J → (sigOf cs l).Ent} {iQ : (s.cKept K).Q → (sigOf cs l).Ent}
  {W : SwitchFrame} {ids : ℕ → ℕ} {aMain aM0 aT0 aM1 aT1 : ℕ} {mem row : K → ℕ}
  {pl : K → KeptPlace} {aKept : K → ℕ}
  {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : ℕ} {anew : Array ℕ}
  {pos : Positions} {y : Array OnBytes.E} {rows : List OnBytes.Row} {carried : OnBytes.Row}

/-- **All generator rows, row by row.** -/
theorem gen_join (L : Laid S old T g anew pos y rows W carried)
    (F : FrameOK W aMain aM0 aT0 aM1 aT1) (D : Names s K cs l iJ iQ W ids aMain aM0 aT0 aM1 aT1)
    (DK : NamesK s K cs l iJ iQ W ids mem row pl aKept)
    (member : ∀ κ, W.kept[mem κ]? = some (pl κ)) (rowIn : ∀ κ, row κ < (pl κ).rows)
    (hm : old.masks = 2) (i x : ℕ) (hi : pos.draws.toList[i]? = some x)
    (hx : x < 2 ^ W.code.logN) (α : (s.cKept K).Aa) :
    ∃ r, rows[1 + (allSamples S W +
        (i * (1 + keptRows W + old.masks) + rowPlace s K W mem row α))]? = some r ∧
      r.target = symAtB old pos y x (coordOf s K W old mem row α) ∧
      ReadsAs cs l ids r (genVec s K iJ iQ x α) := by
  have hR : ∀ x ∈ pos.draws.toList, (switchGenerators W old x (symAtB old pos y x)).length =
      1 + keptRows W + old.masks := fun x _ => gens_length W old x _
  have lay : ∀ c r, (switchGenerators W old x (symAtB old pos y x))[c]? = some r →
      rows[1 + (allSamples S W + (i * (1 + keptRows W + old.masks) + c))]? = some r := by
    intro c r h
    have hc : c < 1 + keptRows W + old.masks := by
      have h' := (List.getElem?_eq_some_iff.1 h).1
      rwa [gens_length] at h'
    rw [rows_gen L _ hR i c x hi hc]
    exact h
  rcases α with ⟨_ | κ, ⟨⟩⟩ | ⟨⟩ | ⟨⟩
  · exact ⟨_, lay _ _ (gens_main W old x _), rfl, main_reads F D x hx _⟩
  · exact ⟨_, lay _ _ (gens_kept W old x _ (mem κ) (row κ) (pl κ) (member κ) (rowIn κ)), rfl,
      kept_reads F D DK κ x hx _⟩
  · exact ⟨_, lay _ _ (gens_mask W old x _ 0 (by omega)), rfl, mask0_reads F D x _⟩
  · exact ⟨_, lay _ _ (gens_mask W old x _ 1 (by omega)), rfl, mask1_reads F D x _⟩

end Join

/-! ## At the two maps that are written out of the frame -/

section Maps
variable (s : Sg) {K : Type} [Fintype K] [DecidableEq K] (W : SwitchFrame) (mem row : K → ℕ)
  (pl : K → KeptPlace) (cs : Codes) (l : List (OracleShape × ℕ)) (ids : ℕ → ℕ)
  (hJ : ∀ x, InTab cs l (nameJ s W mem row pl x)) (hQ : ∀ x, InTab cs l (nameQ s W mem row x))

theorem names_at_maps (codeC : s.C = codeOf W.code) (codeZ : s.Z = codeOf W.zk)
    (gIs : ∀ n : (sigOf cs l).Ent, ids (entAt cs l n).1 = W.g ↔ (entAt cs l n).1 = 0)
    (mainIn : ∀ n : (sigOf cs l).Ent, (entAt cs l n).1 = 0 → (entAt cs l n).2.1 = Part.main →
      (entAt cs l n).2.2 < 2 ^ W.tableBits)
    (restIn : ∀ n : (sigOf cs l).Ent, (entAt cs l n).1 = 0 → (entAt cs l n).2.1 = W.restPart →
      (entAt cs l n).2.2 < 2 ^ W.restBits) :
    Names s K cs l (Johnson.Top.H.iJ s W mem row pl cs l hJ) (Johnson.Top.H.iQ s W mem row cs l hQ)
      W ids W.parts.mainTailAt (W.parts.maskAt.getD 0 0) (W.parts.maskTailAt.getD 0 0)
      (W.parts.maskAt.getD 1 0) (W.parts.maskTailAt.getD 1 0) where
  codeC := codeC
  codeZ := codeZ
  gIs := gIs
  mainIn := mainIn
  restIn := restIn
  mainMsg := fun j => entAt_iJ s W mem row pl cs l hJ (.inl (none, j))
  mainTail := fun q => entAt_iQ s W mem row cs l hQ (.inl (none, q))
  mask0Msg := fun j => entAt_iJ s W mem row pl cs l hJ (.inr (.inl j))
  mask0Tail := fun q => entAt_iQ s W mem row cs l hQ (.inr (.inl q))
  mask1Msg := fun j => entAt_iJ s W mem row pl cs l hJ (.inr (.inr j))
  mask1Tail := fun q => entAt_iQ s W mem row cs l hQ (.inr (.inr q))

theorem namesK_at_maps (rowLt : ∀ κ, row κ < 2 ^ (pl κ).rowBits)
    (anewIs : ∀ κ (n : (sigOf cs l).Ent),
      ids (entAt cs l n).1 = (pl κ).anew ↔ (entAt cs l n).1 = 1 + mem κ)
    (notG : ∀ κ, (pl κ).anew ≠ W.g) (padNodup : ∀ κ, ((pl κ).pad.map (·.index)).Nodup)
    (padIn : ∀ κ q, q < (pl κ).pad.length →
      ((pl κ).pad.getD q default).index < 2 ^ ((pl κ).rowBits + W.code.logEll))
    (keptIn : ∀ κ (n : (sigOf cs l).Ent), (entAt cs l n).1 = 1 + mem κ →
      (entAt cs l n).2.1 = Part.main → (entAt cs l n).2.2 < 2 ^ ((pl κ).rowBits + W.code.logEll))
    (tailPieces : ∀ κ, W.keptTail.getD (rowsBefore W.kept (mem κ) + row κ) [] =
      switchPieces W.places (W.parts.keptTailAt.getD (keptNo W (mem κ) (row κ)) 0) W.code.r)
    (tailInc : ∀ κ i j, i < j → j < W.code.r →
      W.places.get (W.parts.keptTailAt.getD (keptNo W (mem κ) (row κ)) 0 + i) <
        W.places.get (W.parts.keptTailAt.getD (keptNo W (mem κ) (row κ)) 0 + j)) :
    NamesK s K cs l (Johnson.Top.H.iJ s W mem row pl cs l hJ)
      (Johnson.Top.H.iQ s W mem row cs l hQ) W ids mem row pl
      (fun κ => W.parts.keptTailAt.getD (keptNo W (mem κ) (row κ)) 0) where
  rowLt := rowLt
  anewIs := anewIs
  notG := notG
  padNodup := padNodup
  padIn := padIn
  keptIn := keptIn
  tailPieces := tailPieces
  tailInc := tailInc
  keptMsg := fun κ j => entAt_iJ s W mem row pl cs l hJ (.inl (some κ, j))
  keptTail := fun κ q => entAt_iQ s W mem row cs l hQ (.inl (some κ, q))

end Maps

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.gen_join
#print axioms VerifiableInference.Desc.First.K2Hands.names_at_maps
#print axioms VerifiableInference.Desc.First.K2Hands.namesK_at_maps
