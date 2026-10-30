--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/HeadSaysBack.lean: THE WAY BACK AT THE LOOKUP ON THE OUTPUT HEAD's CALLS: from the nine
keys' fields and the two guests' corner values of the head's relation on cells to what the joint in
front of the lookup says of a tuple of messages at a token (`HeadSays`,
Johnson/Desc/First/Look/K3HeadGoodIn.lean: the right side of head_says). Statements and proofs. NO
ACCEPTANCE OF ANY TEXT THAT RUNS IS CLAIMED.

Why. says_rows and says_guests (Johnson/P5J/HeadSaysParts.lean) lead from `HeadSays` to these parts:
what soundness spends. Whoever wants to show that honest messages stand in the joint needs the other
way.

Main names.
  `says_of_rows`: `HeadSays`, from "every place of every call's table on the caller's cells, read,
    is a row's number" AT EVERY COLUMN and CornerGuests. The joint asks every place below 2^n of a
    call: place b is column b / T, position b % T.
  `says_of_fields`: the same from the nine keys' fields on the caller's cells
    (Johnson/Desc/Kinds/Law/OutCallBack.lean: rows_back).
  `says_of_same`: the same from the nine fields and the guests ON ANOTHER RECORD OF CELLS that
    agrees with the caller's inside the ranges (SameCells,
    Johnson/Desc/Kinds/Law/CellsAlike.lean): the caller's weights part from an index's output matrix
    outside k < d, v < V.

Limits. ONE WAY. Premises on public data: the record has six calls; each call's table bits are the
kind's; the kind's tests planOk and rowsOk pass (`HeadTabs`); in `says_of_same` also the test on the
request and y < V. The nine fields and the guests are premises: from the library's clauses to them:
Johnson/Desc/Kinds/Law/LibBack.lean, LibBackNorm.lean. The cells are the caller's (`headCells`): an
entry that is the cast of no small integer is read as 0. The joint is the base joint's right side,
at the decoded messages. The proved lookup block has no honest side.
Not claimed: anything on completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.HeadSaysParts
import Johnson.Desc.Kinds.Law.OutCallBack
import Johnson.Desc.Kinds.Law.CellsAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes (E okE OracleShape)
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Norm (lt ls d S2 T)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look

variable [Sizes] [Policy] [Request]
variable {adr : HeadAdr}
  {x : VerifiableInference.Desc.First.Look.Place} {sT : ℕ} {tl : HTailF2} {D : Sent}
  {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ} {y : ℕ} {m : (laySg x D rad oW).Msg}

/-- **What the joint in front says**, from the rows at every column and the guests. -/
theorem says_of_rows (six : x.fs.NC = 6)
    (bits : ∀ c, c < 6 → Cb.LdLkp.Port.kOf x.fs c = bitsOf c)
    (rows : letI : Token := ⟨y⟩
      ∀ call, call < 6 → ∀ col t, t < T → ∃ u, u < 2 ^ bitsOf call ∧
        rd (keyTable (headCells adr x tl D rad oW wOf nr nc m) call col t) =
          ((rowH x call u : ℕ) : Cb.Gl.E))
    (guests : letI : Token := ⟨y⟩
      CornerGuests (headCells adr x tl D rad oW wOf nr nc m).toCells) :
    HeadSays adr x tl D rad oW wOf nr nc y m := by
  letI : Token := ⟨y⟩
  have hT : 0 < T := Nat.pos_of_ne_zero (by
    unfold T
    exact (Nat.pow_pos (by norm_num)).ne')
  refine ⟨fun k hk b _ => ?_, ?_⟩
  · rw [six] at hk
    obtain ⟨u, hu, e⟩ := rows k hk (b / T) (b % T) (Nat.mod_lt _ hT)
    exact ⟨u, by rw [bits k hk]; exact hu, e⟩
  · refine (tail_src (c := headCaller adr x tl D rad oW wOf nr nc Iop.extNone Unit) lt
      (headArrs adr x tl D rad oW wOf nr nc) m (y, ())).2 fun g hg t ht => ?_
    rcases List.mem_cons.1 hg with rfl | hg
    · show rd (clipAt (headCells adr x tl D rad oW wOf nr nc m).toCells (corner 0 t)) = 0
      rw [(guests t ht).1, rd_zero]
    · obtain rfl := List.mem_singleton.1 hg
      show rd (tableAt (headCells adr x tl D rad oW wOf nr nc m).toCells (corner 0 t)) = 0
      rw [(guests t ht).2, rd_zero]

/-- **The same from the nine keys' fields on the caller's cells.** -/
theorem says_of_fields (six : x.fs.NC = 6) (HT : HeadTabs x sT)
    (keys : letI : Token := ⟨y⟩
      Came.NineKeys (tabOf (rowH x)) (headCells adr x tl D rad oW wOf nr nc m))
    (guests : letI : Token := ⟨y⟩
      CornerGuests (headCells adr x tl D rad oW wOf nr nc m).toCells) :
    HeadSays adr x tl D rad oW wOf nr nc y m := by
  letI : Token := ⟨y⟩
  exact says_of_rows six HT.bits (Came.rows_back sT (rowH x) _ HT.plan HT.rows keys) guests

/-- **The same from another record of cells that agrees with the caller's inside the ranges.** -/
theorem says_of_same (six : x.fs.NC = 6) (HT : HeadTabs x sT) (hreq : Request.ok = true)
    (hy : y < V) (c : NCells)
    (same : letI : Token := ⟨y⟩
      SameCells c (headCells adr x tl D rad oW wOf nr nc m))
    (keys : letI : Token := ⟨y⟩
      Came.NineKeys (tabOf (rowH x)) c)
    (guests : letI : Token := ⟨y⟩
      CornerGuests c.toCells) :
    HeadSays adr x tl D rad oW wOf nr nc y m := by
  letI : Token := ⟨y⟩
  have P := planFacts HT.plan
  refine says_of_rows six HT.bits (fun call hc col t ht => ?_) (Came.rider_same same P guests)
  rw [← Came.keyTable_same same P hreq hy call col ht]
  exact Came.rows_back sT (rowH x) c HT.plan HT.rows keys call hc col t ht

end P5J

#print axioms P5J.says_of_rows
#print axioms P5J.says_of_fields
#print axioms P5J.says_of_same
