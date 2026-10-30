-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/EmbShare.lean: the late entries that the claim on the stream that comes into the first
group of layers reads, as forms on the early entries, and what the pull-back of the ledger of that
claim says.

Cb/Pv/Lay/End/EmbCl.lean writes the claim and shows what it says on entries whose reads are true.
This file writes the late entries' forms in the names and tools of Cb/Pv/Lay/End/NormsA.lean
(LateLay, lateA, toAff) and of Cb/Pv/Lay/End/GatedShare.lean (readFm). With each late entry at the
value of its form the reads are true, so the ledger enters by its pull-back alone.

Main definitions: EmbNm (the late entries' names), embFm (their forms), embLedOf (the ledger).
Main theorems: emb_reads, embLed_iff, embClaim_last, emb_pull.

Limits. hfm and hY: the late entries' names and forms, as in Cb/Pv/Lay/End/NormsA.lean. That the
ledger is a program's is not said here.


-/
import Cb.Pv.Lay.End.GatedShare
import Cb.Pv.Lay.End.EmbCl

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay
open Inst.Model.FFSeg (Dim Cell Arr)
open Blocks (Form)

/-- The names of the late entries that the claim reads: limb l of block kh of the stream that comes
in. -/
inductive EmbNm
  | x0 (l kh : ℕ)

/-- The names in range. nb: the number of blocks of the stream. -/
def EmbIn (nb : ℕ) : EmbNm → Prop
  | .x0 l kh => l < Arr.x0.nCell ∧ kh < nb

variable {E J Nm J₂ : Type} [Field E] [Fintype J] [DecidableEq J] [Fintype J₂] [DecidableEq J₂]
  (rd : (J → E) → Cell → E)

/-- What the late entry of a name is meant to be. -/
def embFm (D : Dim) (pa : ℕ → E) (ls : ℕ) : EmbNm → Form J E
  | .x0 l kh => readFm rd D .x0 pa 0 ls l 0 kh

/-- The claim, at the names of early and late entries. -/
def embClaim (Y : LateLay Nm J₂) (ι : EmbNm → Nm) (sh : E) (mE : J) (nb gB : ℕ) (pb : ℕ → E) :
    Form (J ⊕ J₂) E :=
  cEmb sh (.inl mE) (fun l kh => .inr (Y.at' (ι (.x0 l kh)))) nb gB pb

/-- The ledger of the one claim. -/
def embLedOf (Y : LateLay Nm J₂) (ι : EmbNm → Nm) (sh : E) (mE : J) (nb gB : ℕ) (pb : ℕ → E) :
    TWhole.Ledger E (J ⊕ J₂) :=
  ledOf [embClaim Y ι sh mE nb gB pb]

omit [Fintype J₂] [DecidableEq J₂] in
/-- With each late entry at the value of its form, the reads are true. -/
theorem emb_reads
    (hrd : ∀ (a b : E) (m m' : J → E) (c : Cell),
      rd (fun j => a * m j + b * m' j) c = a * rd m c + b * rd m' c)
    (D : Dim) (Y : LateLay Nm J₂) (ι : EmbNm → Nm) (fm : Nm → TWhole.Aff E J) (nb ls : ℕ)
    (pa : ℕ → E) (m : J → E)
    (hfm : ∀ x, EmbIn nb x → fm (ι x) = toAff (embFm rd D pa ls x)) (l kh : ℕ)
    (hr : EmbIn nb (.x0 l kh)) (hY : Y.good (ι (.x0 l kh))) :
    (lateA Y fm (Y.at' (ι (.x0 l kh)))).val m = readAt D (rd m) .x0 pa 0 ls l 0 kh := by
  unfold lateA
  rw [Y.ok _ hY, hfm _ hr, toAff_val]
  exact val_readFm rd hrd D .x0 pa 0 ls l 0 kh m

/-- The ledger holds of entries y exactly if the claim is worth 0 there. -/
theorem embLed_iff (Y : LateLay Nm J₂) (ι : EmbNm → Nm) (sh : E) (mE : J) (nb gB : ℕ) (pb : ℕ → E)
    (y : J ⊕ J₂ → E) :
    TWhole.Ledger.Holds (embLedOf Y ι sh mE nb gB pb) y ↔
      Form.val y (embClaim Y ι sh mE nb gB pb) = 0 := by
  unfold embLedOf
  rw [ledOf_holds]
  exact ⟨fun h => h _ List.mem_cons_self, fun h f hf => by rw [List.mem_singleton.mp hf]; exact h⟩

/-- What the claim says on entries y whose reads are true. -/
theorem embClaim_last (D : Dim) (t : Cell → E) (Y : LateLay Nm J₂) (ι : EmbNm → Nm) (sh : E)
    (mE : J) (nb ls gB : ℕ) (pa pb : ℕ → E) (y : J ⊕ J₂ → E)
    (hT : ∀ l, l < Arr.x0.nCell → ∀ kh, kh < nb →
      y (.inr (Y.at' (ι (.x0 l kh)))) = readAt D t .x0 pa 0 ls l 0 kh)
    (h : Form.val y (embClaim Y ι sh mE nb gB pb) = 0) :
    sh - y (.inl mE) = embRhs D t nb ls gB pa pb := by
  exact emb_last (J := J ⊕ J₂) D t sh (Sum.inl mE) (fun l kh => Sum.inr (Y.at' (ι (.x0 l kh)))) nb
    ls gB pa pb y hT h

/-- If the pull-back of the ledger holds, the scalar less its mask entry is embRhs on the cells that
the early entries hold. -/
theorem emb_pull
    (hrd : ∀ (a b : E) (m m' : J → E) (c : Cell),
      rd (fun j => a * m j + b * m' j) c = a * rd m c + b * rd m' c)
    (D : Dim) (Y : LateLay Nm J₂) (ι : EmbNm → Nm) (fm : Nm → TWhole.Aff E J) (sh : E) (mE : J)
    (nb ls gB : ℕ) (pa pb : ℕ → E) (m : J → E)
    (hfm : ∀ x, EmbIn nb x → fm (ι x) = toAff (embFm rd D pa ls x))
    (hY : ∀ l, l < Arr.x0.nCell → ∀ kh, kh < nb → Y.good (ι (.x0 l kh)))
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm) (embLedOf Y ι sh mE nb gB pb)) m) :
    sh - m mE = embRhs D (rd m) nb ls gB pa pb :=
  embClaim_last D (rd m) Y ι sh mE nb ls gB pa pb (Sum.elim m fun j => (lateA Y fm j).val m)
    (fun l hl kh hkh => emb_reads rd hrd D Y ι fm nb ls pa m hfm l kh ⟨hl, hkh⟩ (hY l hl kh hkh))
    ((embLed_iff Y ι sh mE nb gB pb _).1 ((Cb.Sub.pullL_holds _ _ m).1 h))

end Cb.Pv.Lay.End.Gated
