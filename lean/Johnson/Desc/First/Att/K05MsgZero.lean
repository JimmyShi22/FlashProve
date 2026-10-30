-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05MsgZero.lean: a tuple of messages at which the closed caller of the lookup
on an attention link's calls reads 0 everywhere, and out-statements whose point is 0 beyond its dT +
rK coordinates. Both serve as letters of a member of what stands behind the kind K5.

Definitions, statements and proofs.
Main names:
  `cellValS_zero`: the zero symbols unpack to zero cells. The zero column is small and packs to 0,
    and by `packs_unique` (Cb/Pv/Tail/Unique.lean) it is the column behind them.
  `zeroMsg cs l`, `msgZero x D rad`: the tuple of messages whose every entry is 0, at any list and
    at the caller's signature.
  `valAt_zero`, `msgAtt_zero`: at the zero tuple the caller's reading `msgAtt` is 0 at every entry.
  `cells_zero`: (closedOf attBase attLin ns N).msg (msgZero x D rad) (Sum.inr (cellAtt x S tl c)) =
    0 at every cell c. `mats_zero`: matsOfMsg x tl D rad (msgZero x D rad) is 0 everywhere
    (Johnson/Desc/First/Att/K05CellsTie.lean). `maskOf_zero`: so is the mask row.
  `cutOut h st θ pt mf tg`: the out-statement with the shift θ, the point pt cut at dT + rK
    coordinates, the mask form mf, the target tg and no rows. `cutOut_pt`: its point is 0 from dT +
    rK on.
Limits: a member made on purpose to be trivial. The zero tuple is a value of the signature's type of
messages; nothing says that an honest prover sends it. Nothing is claimed on soundness, completeness
or hiding.

-/
import Johnson.Desc.First.Att.K05CellsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.Rows (Addr)
open Johnson.Pack (sigOf)
open Cb.Pv.Tail (JCell Syms cellValS cellVal cellsOf symL Packs packs_unique packs_cellsOf uniq_gl)
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt msgAtt enCell sigListCalls seatCalls valAt readAt symAt
  szOf)

/-- **The zero symbols unpack to zero cells.** -/
theorem cellValS_zero {s : Cb.Pv.Tail.Size} (hu : s.Uniq Cb.Gl.p) (j : JCell s) :
    cellValS (fun _ _ _ => (0 : Cb.Gl.E) : Syms Cb.Gl.E s) j = 0 := by
  have h0 : Packs (symL Cb.Gl.E s) (fun _ _ _ => (0 : Cb.Gl.E) : Syms Cb.Gl.E s) j.1 j.2.1 (fun _ => 0) := by
    refine ⟨fun i => ?_, fun i' => ?_⟩
    · have := hu.1
      simp only [abs_zero]
      omega
    · have e : Alg.pack (s.rad : ℤ) (fun _ : Fin (s.m j.1) => (0 : ℤ)) i' = 0 := by
        unfold Alg.pack Alg.lane
        simp
      rw [e]
      exact Int.cast_zero.symm
  have e := packs_unique (symL Cb.Gl.E s) Cb.Gl.p hu (fun _ => rfl) h0 (packs_cellsOf _ ⟨_, h0⟩)
  show ((cellsOf (symL Cb.Gl.E s) (fun _ _ _ => (0 : Cb.Gl.E) : Syms Cb.Gl.E s) j.1 j.2.1 j.2.2 : ℤ) : Cb.Gl.E) = 0
  rw [← e]
  exact Int.cast_zero

section Zero
variable (cs : Codes) (l : List (OracleShape × Nat))
  (seat : Addr → Option VerifiableInference.Desc.First.Look.Seat)

/-- The tuple of messages whose every entry is 0. -/
noncomputable def zeroMsg : (sigOf cs l).Msg := fun _ _ => 0

/-- At the zero tuple every reading is 0, whether it fails or not. -/
theorem valAt_zero (a : Addr) : (valAt cs l seat (zeroMsg cs l) a).getD 0 = 0 := by
  unfold valAt
  cases seat a with
  | none => rfl
  | some s =>
    show (readAt cs l (zeroMsg cs l) s).getD 0 = 0
    unfold readAt
    split
    · split
      · cases VerifiableInference.Desc.First.Look.finOf _ s.row with
        | none => rfl
        | some r =>
          cases VerifiableInference.Desc.First.Look.finOf _ s.place with
          | none => rfl
          | some c => rfl
      · cases VerifiableInference.Desc.First.Look.finOf _ s.row with
        | none => rfl
        | some r =>
          cases VerifiableInference.Desc.First.Look.finOf _ s.place with
          | none => rfl
          | some c => rfl
    · rfl

/-- **At the zero tuple the caller's reading is 0 at every entry.** -/
theorem msgAtt_zero (tl : HTailF2) (ns : ℕ) (j : JAtt ns tl) : msgAtt cs l seat tl ns (zeroMsg cs l) j = 0 := by
  cases j with
  | none => rfl
  | some j =>
    cases j with
    | inl k => exact valAt_zero cs l seat _
    | inr c =>
      show cellValS (symAt cs l seat tl (zeroMsg cs l)) c = 0
      have e : symAt cs l seat tl (zeroMsg cs l) = fun _ _ _ => 0 := by
        funext μ i' c'
        exact valAt_zero cs l seat _
      rw [e]
      exact cellValS_zero (uniq_gl (s := szOf tl) rfl rfl) c

end Zero

section AtCaller
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat)

/-- The zero tuple at the closed caller's signature. -/
noncomputable def msgZero : (attSg x D rad).Msg := zeroMsg D.codes (sigListCalls D rad x.link)

/-- The matrices read off the zero tuple are 0. -/
theorem mats_zero : matsOfMsg x tl D rad (msgZero x D rad) = fun _ _ _ => 0 := by
  funext a r c
  exact msgAtt_zero _ _ _ tl x.ns _

/-- The mask row read off the zero tuple is 0. -/
theorem maskOf_zero (j : ℕ) : (attLin0 x S tl D rad).maskOf (msgZero x D rad) j = 0 := valAt_zero _ _ _ _

variable (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)

/-- **Every cell entry of the closed parameters' message is 0 at the zero tuple.** -/
theorem cells_zero (c : AttSeg.Raw) :
    (closedOf (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N).msg (msgZero x D rad)
      (Sum.inr (cellAtt x S tl c)) = 0 := msgAtt_zero _ _ _ tl x.ns _

end AtCaller

/-- An out-statement with the point cut at dT + rK coordinates, and no rows. -/
def cutOut {St₀ N : Type} (h : Forest.Shape) (st : St₀) (θ : Cb.Gl.E) (pt : ℕ → Cb.Gl.E) (mf : N → Cb.Gl.E)
    (tg : Cb.Gl.E) : TX (St₀ × Cb.Gl.E) Cb.Gl.E N :=
  ((st, θ), ⟨fun t => if t < h.dT + h.rK then pt t else 0, mf, tg⟩, [])

theorem cutOut_pt {St₀ N : Type} (h : Forest.Shape) (st : St₀) (θ : Cb.Gl.E) (pt : ℕ → Cb.Gl.E) (mf : N → Cb.Gl.E)
    (tg : Cb.Gl.E) (t : ℕ) (ht : h.dT + h.rK ≤ t) : (cutOut h st θ pt mf tg).2.1.pt t = 0 :=
  if_neg (by omega)

end VerifiableInference.Desc.First.Att.P
