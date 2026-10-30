-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/HostLay.lean: the letters of the smallness test in a link, read off a lay of the
committed entries and a record of the verifier: values at which the premises on letters hold.

The committed entries are those of three tuples of messages (`JAll Ja Jb Jc`,
Cb/Pv/Tail/HostSum.lean), with addresses (`Lay`, OnBytes/Tie/Pv/Led/LedJoint.lean). The symbols are
the cells of the symbol arrays, read off the early entries alone; the vector of reads is the one row
of its array, read off the reads' message alone; the tables' weights come from the statement in
front of the round (`funsAt e`); the record of a statement is the public record tl with these tables
and with the drawn matrix (`recLay`).

Main names:
  `symLay`, `u3Lay`, `phiLay`: the three readings. `recLay`: the record of a statement.
  `LayOK`: what is asked of the lay: a cell of a symbol array is an early entry; a cell of the row
    of reads is an entry of the reads' message; every entry of that message is such a cell, at a
    place below N that a table names.
  `sizeOf_recLay`, `fits_recLay`: the record of a statement has the public record's sizes, and fits.
  `atT_lay`: `AtT` (OnBytes/Tie/Pv/Tail/EndsCut.lean) at every statement and every tuple of
    messages, at the letters `thetaQ` (Cb/Pv/Tail/HostT.lean) of these readings.
  `itLay`, `htab_lay`: the read that stands at an entry of the reads' message; the third law of
    Cb/Pv/Tail/InLink.lean.

Limits: premises of `atT_lay`: `LayOK`; the tables of every statement have the public record's
matrices, lengths and first entries; the record's number of matrices is the length of its list, and
its first columns are the running sums; the digits are the cells of the digits' array at the
verifier's columns (two premises: they are the matter of whoever reads the digits off the late
message).

-/
import Cb.Pv.Tail.HostSum
import Cb.Pv.Tail.HostT
import Cb.Pv.Tail.Places
import OnBytes.Tie.Pv.Tail.EndsCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Road.Rows OnBytes.Tie.Pv.Tail.Port Cb.Pv.Tail

variable {K : Type} [Field K]

/-- A cell hangs on the entries with its address alone. -/
theorem cellAt_congr {J : Type} [Fintype J] (Y : Lay J) (m m' : J → K) (t r c : ℕ)
    (h : ∀ j, Y.addr j = .cell t r c → m j = m' j) : Y.cellAt m t r c = Y.cellAt m' t r c := by
  unfold Lay.cellAt
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases e : Y.addr j = .cell t r c
  · rw [if_pos e, if_pos e, h j e]
  · rw [if_neg e, if_neg e]

variable {Ja Jb Jc : Type} [Fintype Ja] [Fintype Jb] [Fintype Jc] (ρ : Reading K)
  (Y : Lay (JAll Ja Jb Jc)) (tl : HTailF2)

/-- The early entries alone; the entries of the reads' message alone. -/
def onA (v : Ja → K) : JAll Ja Jb Jc → K := Sum.elim v fun _ => 0
def onB (v : Jb → K) : JAll Ja Jb Jc → K := Sum.elim (fun _ => 0) (Sum.elim v fun _ => 0)

/-- The symbol (matrix, row of symbols, column), read off the early entries. -/
def symLay (v : Ja → K) (μ i' c : ℕ) : K := Y.cellAt (onA v) (tl.gtTree.getD μ 0) i' c

/-- An entry of the vector of reads, read off the reads' message. -/
def u3Lay (v : Jb → K) (pos : ℕ) : K := Y.cellAt (onB v) (u3Of tl) 0 pos

/-- Weight j of table number n of a list of tables. -/
def phiLay (funs : Array HFun) (n j : ℕ) : K := ρ.val ((funs.getD n default).phi.getD j zeroE)

/-- The record of a statement: the public record with the statement's tables and drawn matrix. -/
def recLay (funs : Array HFun) (β : Dr (sizeOf tl).size) : HTailF2 :=
  withDraw { tl with funs := funs } β

/-- What is asked of the lay. -/
structure LayOK (N : ℕ) : Prop where
  symA : ∀ μ i' c j, μ < tl.NM → Y.addr j = .cell (tl.gtTree.getD μ 0) i' c → ∃ a, j = .inl a
  u3B : ∀ pos j, Y.addr j = .cell (u3Of tl) 0 pos → ∃ b, j = .inr (.inl b)
  bU3 : ∀ b : Jb, ∃ pos, Y.addr (.inr (.inl b)) = .cell (u3Of tl) 0 pos ∧ pos < N ∧
    Named (sizeOf tl) pos

/-- The tables have the public record's matrices, lengths and first entries. -/
def SameShapes (funs : Array HFun) : Prop :=
  (funs.toList.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) =
    tl.funs.toList.map fun Fn : HFun => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)

theorem sizeOf_recLay (funs : Array HFun) (h : SameShapes tl funs) (β : Dr (sizeOf tl).size) :
    sizeOf (recLay tl funs β) = sizeOf tl := sizeOf_funs tl funs h

theorem fits_recLay (hf : Fits tl) (funs : Array HFun) (β : Dr (sizeOf tl).size) :
    Fits (recLay tl funs β) := hf.of_same rfl rfl rfl

section
variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] (Q : Host K (sizeOf tl).size J₁ J₂)
  (ra : Q.M₁ → Ja → K) (rb : Q.U₁ → Jb → K) {U₂ : Type} (rc : U₂ → Jc → K)
  (funsAt : Q.Xe → Array HFun)

/-- The letters are read off the cells of the committed entries and the record of the statement, at
every statement and every tuple of messages. -/
theorem atT_lay {N : ℕ} (ok : LayOK Y tl N) (hsh : ∀ e, SameShapes tl (funsAt e))
    (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    (x : Q.let.X) (msg : Q.M) (u : U₂) (Z : Dig K (sizeOf tl).size) (β : Dr (sizeOf tl).size)
    (hzl : ∀ μ v i, Z.zl μ v i =
      Y.cellAt (Sum.elim (ra (Q.left msg)) (Sum.elim (rb (Q.right msg)) (rc u))) tl.ix.ZZ v
        ((tl.zzCol μ 0 0).getD 0 + i))
    (hzh : ∀ μ v i, Z.zh μ v i =
      Y.cellAt (Sum.elim (ra (Q.left msg)) (Sum.elim (rb (Q.right msg)) (rc u))) tl.ix.ZZ v
        ((tl.zzCol μ 1 0).getD 0 + i)) :
    AtT ρ (recLay tl (funsAt x.1) β) (sizeOf tl)
      (thetaQ Q (fun e => phiLay ρ (funsAt e)) (fun m => symLay Y tl (ra m))
        fun w => u3Lay Y tl (rb w))
      x msg Z β fun a r c =>
        Y.cellAt (Sum.elim (ra (Q.left msg)) (Sum.elim (rb (Q.right msg)) (rc u))) a r c where
  phi := by
    intro n Fn hn j _
    have hn' : (funsAt x.1).toList[n]? = some Fn := hn
    show phiLay ρ (funsAt x.1) n j = _
    unfold phiLay
    have e : (funsAt x.1).getD n default = Fn := by
      rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hn']
      rfl
    rw [e]
  sym := by
    intro μ i' c hμ _ _
    show symLay Y tl (ra (Q.left msg)) μ i' c = _
    refine cellAt_congr Y _ _ _ _ _ fun j hj => ?_
    obtain ⟨a, rfl⟩ := ok.symA μ i' c j hμ hj
    rfl
  u3 := by
    intro y _ d _
    show u3Lay Y tl (rb (Q.right msg)) _ = _
    refine cellAt_congr Y _ _ _ _ _ fun j hj => ?_
    obtain ⟨b, rfl⟩ := ok.u3B _ j hj
    rfl
  zl := hzl
  zh := hzh
  th := fun μ v c =>
    th_draw { tl with funs := funsAt x.1 } (sizeOf_funs tl _ (hsh x.1)) hnm hfirst β μ v c

end

/-- The read that stands at an entry of the reads' message. -/
noncomputable def itLay {N : ℕ} (ok : LayOK Y tl N) (b : Jb) : JTab (sizeOf tl).size :=
  itU (N := N) ⟨⟨(ok.bU3 b).choose, (ok.bU3 b).choose_spec.2.1⟩, (ok.bU3 b).choose_spec.2.2⟩

/-- An entry of the reads' message is the committed read at its place. -/
theorem htab_lay {N : ℕ} (ok : LayOK Y tl N) (v : Jb → K) (b : Jb) :
    v b = tabOf (sizeOf tl) (u3Lay Y tl v) (itLay Y tl ok b).1 (itLay Y tl ok b).2.1
      (itLay Y tl ok b).2.2 := by
  have h := htab_places (N := N) (u3Lay Y tl v)
    ⟨⟨(ok.bU3 b).choose, (ok.bU3 b).choose_spec.2.1⟩, (ok.bU3 b).choose_spec.2.2⟩
  refine Eq.trans ?_ h
  show v b = Y.cellAt (onB v) (u3Of tl) 0 (ok.bU3 b).choose
  rw [Lay.cellAt_addr Y (onB v) _ _ _ (.inr (.inl b)) (ok.bU3 b).choose_spec.1]
  rfl

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.sizeOf_recLay
#print axioms OnBytes.Tie.Pv.Tail.atT_lay
#print axioms OnBytes.Tie.Pv.Tail.htab_lay
