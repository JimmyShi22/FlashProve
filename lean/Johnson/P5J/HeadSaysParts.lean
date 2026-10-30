-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/HeadSaysParts.lean: FROM WHAT THE JOINT IN FRONT OF THE LOOKUP ON THE OUTPUT HEAD's
CALLS SAYS OF A TUPLE OF MESSAGES AT A TOKEN (`HeadSays`,
Johnson/Desc/First/Look/K3HeadGoodIn.lean) TO TWO PARTS OF THE HEAD's RELATION ON THE CALLER's
CELLS: every place of every call's table is a row of that call's table; the two guests' arrays are
0 on the corners. Three theorems.
Why. Another author's `head_rows`, `head_lookCalls` and `head_guests`
(Johnson/Desc/First/Look/K3CallerHead.lean, K3CallerHeadParts.lean) conclude the same from the
library's joint `relR`; their proofs spend of it just the two conjuncts that `HeadSays` is. The
table's field "model" hands `HeadSays`, not the joint: so the same proofs are given here from
`HeadSays`.
  `says_rows`, `says_lookCalls`, `says_guests`: as those three, with hS : `HeadSays adr x tl D rad
    oW wOf nr nc y m` for the joint.
Limits: THE PROOFS ARE THAT AUTHOR's, step by step. `HeadOK` and `HeadTabs` (premises on public
data) are premises. The cells are the caller's (`headCells`). No soundness is claimed.

-/
import Johnson.Desc.First.Look.K3HeadGoodIn
import Johnson.Desc.First.Look.K3CallerHeadParts

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
variable {set : OnBytes.Params.Setting} {adr : HeadAdr}
  {x : VerifiableInference.Desc.First.Look.Place} {floor sT : ℕ} {tl : HTailF2} {D : Sent}
  {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ} {y : ℕ} {m : (laySg x D rad oW).Msg}

/-- The keys' half: every place of every call's table, read, is a row's number. -/
theorem says_rows (H : HeadOK set x floor) (hS : HeadSays adr x tl D rad oW wOf nr nc y m) :
    letI : Token := ⟨y⟩
    ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
      ∃ u < 2 ^ Cb.LdLkp.Port.kOf x.fs call,
        rd (keyTable (headCells adr x tl D rad oW wOf nr nc m) call col t) =
          ((FoNums.tauN x.fs call u : ℕ) : Cb.Gl.E) := by
  letI : Token := ⟨y⟩
  intro call hc col hcol t ht
  have hT : 0 < T := Nat.pos_of_ne_zero (by
    unfold T
    exact (Nat.pow_pos (by norm_num)).ne')
  have hb : col * T + t < 2 ^ Cb.LdLkp.Port.nOf x.fs call := by
    refine lt_of_lt_of_le ?_ (Nat.pow_le_pow_right (by norm_num) (H.sizes call hc))
    rw [Nat.pow_add]
    have h1 : col * T + t < (col + 1) * T := by
      rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left ht _
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ hcol)
  obtain ⟨u, hu, e⟩ := hS.1 call (by rw [H.six]; exact hc) _ hb
  refine ⟨u, hu, ?_⟩
  have e1 : (col * T + t) / T = col := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt ht, Nat.zero_add]
  have e2 : (col * T + t) % T = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  have e3 : rd (keyTable (headCells adr x tl D rad oW wOf nr nc m) call
      ((col * T + t) / T) ((col * T + t) % T)) = ((FoNums.tauN x.fs call u : ℕ) : Cb.Gl.E) := e
  rw [e1, e2] at e3
  exact e3

/-- **The part lookCalls, on the caller's cells, at the token.** -/
theorem says_lookCalls (H : HeadOK set x floor) (HT : HeadTabs x sT)
    (hS : HeadSays adr x tl D rad oW wOf nr nc y m) :
    letI : Token := ⟨y⟩
    ∀ call, call < 6 → ∀ col, col < 2 ^ lJ floor (callKeys call) → ∀ t, t < T →
      InTable (tabOf (rowH x)) call
        (keyTable (headCells adr x tl D rad oW wOf nr nc m) call col t) := by
  letI : Token := ⟨y⟩
  intro call hc col hcol t ht
  obtain ⟨u, hu, e⟩ := says_rows H hS call hc col hcol t ht
  rw [HT.bits call hc] at hu
  exact Came.tie_law sT (rowH x) _ HT.plan HT.rows call hc col t u hu e

/-- **The part rider, on the caller's cells, at the token.** -/
theorem says_guests (hS : HeadSays adr x tl D rad oW wOf nr nc y m) :
    letI : Token := ⟨y⟩
    CornerGuests (headCells adr x tl D rad oW wOf nr nc m).toCells := by
  letI : Token := ⟨y⟩
  intro t ht
  have hs := (tail_src (c := headCaller adr x tl D rad oW wOf nr nc Iop.extNone Unit) lt
    (headArrs adr x tl D rad oW wOf nr nc) m (y, ())).1 hS.2
  have h1 := hs (allO x D rad oW, headClip adr x tl D rad oW wOf nr nc) List.mem_cons_self t ht
  have h2 := hs (allO x D rad oW, headTable adr x tl D rad oW wOf nr nc)
    (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)) t ht
  exact ⟨(rd_zero_iff (okE_clipAt _ _)).1 h1, (rd_zero_iff (okE_tableAt _ _)).1 h2⟩

end P5J

#print axioms P5J.says_rows
#print axioms P5J.says_lookCalls
#print axioms P5J.says_guests
