-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/VecFlatTrack.lean: a prover message of matrices written end to end, with its tracking data.

How the matrices are written end to end: Blocks/VecFlat.lean. The tracking data of a protocol
(`Core.Track`, Blocks/StageTrack.lean) say, for each exposed entry (an entry that forms may read at
the protocol's end), which earlier entry it is, or which sent vector, row and column hold it;
`Core.Track.OK` says that this is so, and that the matrix of weights is copied. (Words of this
library: lean/GLOSSARY.md.)
A stage of a chain (`Chain`, Blocks/Stage.lean) that sends matrices m v (v : A; rows v rows of len v
entries: the logical form) states everything on the logical form: its honest message, its function φ
on the message, and where an exposed entry is: (v, i, j). This file transports this once to the
physical form (rows of M v entries): `Core.sendFlat`, `Stage.sendFlat`, `Core.trackSendFlat`,
`Core.Data.sendFlat`. Throughout, the set C of challenges is nonempty; where tracking data enter
(`Core.trackSendFlat`, its theorems and `Core.Data.sendFlat`), M v is the message length of the code
of v (hlen) and every code has a position.
 * `Core.trackSendFlat_ok` proves `Core.Track.OK`, if on the logical form an exposed entry after the
   message is an entry from before it or the entry (i, j) of a matrix v (read by `Flat.rdLog`), with
   i < rows v and j < len v, and if the matrix of weights is copied.
 * `Stage.props_sendFlat` proves `Stage.Props`, from the three steps of `Stage.props_send`
   (Blocks/StageLib.lean) stated on the logical form, if every M v is positive.
-/
import Blocks.VecFlat
import Blocks.StageLib
import Blocks.StageSide
import Blocks.StageCount
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop

namespace Flat

variable {E F : Type} [Field F] [Field E] [Algebra F E] {A : Type}
  {overF : A → Bool} {rows len : A → ℕ}

/-- The entry (i, j) of the matrix a of a logical message, in E; q = (a, i, j); 0 outside the
matrix. -/
def rdLog (m : Log E F A overF rows len) (q : A × ℕ × ℕ) : E :=
  nat (fun i => nat (fun j => (m q.1 i j).toE) q.2.2) q.2.1

private theorem nat_fin {X : Type} [Zero X] {n : ℕ} (f : Fin n → X) (j : Fin n) :
    nat f j.val = f j := by
  unfold nat
  rw [dif_pos j.2]

theorem rdLog_fin (m : Log E F A overF rows len) (a : A) (i : Fin (rows a)) (j : Fin (len a)) :
    rdLog m (a, i.val, j.val) = (m a i j).toE :=
  (nat_fin (fun i' => nat (fun j' => (m a i' j').toE) j.val) i).trans
    (nat_fin (fun j' => (m a i j').toE) j)

end Flat

section Send

variable {P E F : Type} [Field F] [Field E] [Algebra F E] {a : Sorts} {X' Z : Type} (A : Type)
  (overF : A → Bool) (rows len M : A → ℕ) (K C : Type) [Fintype C] [Nonempty C]

/-- One prover message of matrices, written end to end: the protocol. msg and φ are given on the
logical form. -/
@[reducible] def Core.sendFlat (a : Sorts) (X' Z : Type) (p₀ : K → E)
    (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') : Core P E a ⟨X', a.Y × Z, a.I⟩ :=
  Core.send a X' Z (Flat.rFlat E F A overF rows len M K C) p₀ (fun s π => Flat.flat M K C (msg s π))
    (fun o => φ (Flat.unflat o)) fx

variable [Fintype A] [DecidableEq A] (code : A → Code.Enc F) (mrow : A → ℕ) (role : A → Role)
  (q : A → ℕ) (hlen : ∀ v, (code v).msg = M v) [∀ v, Nonempty (Fin (code v).n)]

/-- Its tracking data. src says on the logical form where an exposed entry comes from: an entry from
before the message, or the entry (i, j) of the matrix v. -/
def Core.trackSendFlat (p₀ : K → E) (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (A × ℕ × ℕ)) :
    (Core.sendFlat (P := P) A overF rows len M K C a X' Z p₀ msg φ fx).Track ra rb :=
  Core.trackSend (Flat.eFlat E A overF rows len M code mrow role q hlen K C) p₀
    (fun s π => Flat.flat M K C (msg s π)) (fun o => φ (Flat.unflat o)) fx ra rb
    fun n => (src n).map _root_.id fun t : A × ℕ × ℕ => Flat.src len M t.1 t.2.1 t.2.2

variable {A overF rows len M K C code mrow role q}

/-- `Core.Track.OK`, under hlen, h (the condition h of `Stage.trackSend_ok`, stated on the logical
form), hin and hm. -/
theorem Core.trackSendFlat_ok [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] (p₀ : K → E)
    (msg : a.I → (P → E) → Flat.Log E F A overF rows len) (φ : Flat.Log E F A overF rows len → Z)
    (fx : a.X → X') (ra : Reads F E a) (rb : Reads F E ⟨X', a.Y × Z, a.I⟩)
    (src : rb.N → ra.N ⊕ (A × ℕ × ℕ))
    (h : ∀ y m n, rb.rd (y, φ m) n = Sum.elim (ra.rd y) (Flat.rdLog m) (src n))
    (hin : ∀ n t, src n = .inr t → t.2.1 < rows t.1 ∧ t.2.2 < len t.1)
    (hm : ∀ y z, rb.mat (y, z) = ra.mat y) :
    (Core.trackSendFlat (P := P) A overF rows len M K C code mrow role q hlen p₀
      msg φ fx ra rb src).OK :=
  Stage.trackSend_ok (P := P) (Flat.eFlat E A overF rows len M code mrow role q hlen K C) p₀
    (fun s π => Flat.flat M K C (msg s π)) (fun o => φ (Flat.unflat o)) fx ra rb _
    (fun y o n => by
      rw [h y (Flat.unflat o) n]
      cases hs : src n with
      | inl k => rfl
      | inr t =>
        obtain ⟨v, i, j⟩ := t
        obtain ⟨hi, hj⟩ := hin n _ hs
        show Flat.rdLog (Flat.unflat o) (v, i, j) = _
        rw [show Flat.rdLog (Flat.unflat o) (v, i, j) = (Flat.unflat o v ⟨i, hi⟩ ⟨j, hj⟩).toE
            from Flat.rdLog_fin (Flat.unflat o) v ⟨i, hi⟩ ⟨j, hj⟩]
        exact Flat.read code mrow role q hlen o v ⟨i, hi⟩ ⟨j, hj⟩) hm

/-- Under hlen: every vector of the message has the property Q, if each vector v, with ⌈rows v · len
v / M v⌉ rows, has it. -/
theorem Core.all_trackSendFlat {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop} (p₀ : K → E)
    (msg : a.I → (P → E) → Flat.Log E F A overF rows len) (φ : Flat.Log E F A overF rows len → Z)
    (fx : a.X → X') (ra : Reads F E a) (rb : Reads F E ⟨X', a.Y × Z, a.I⟩)
    (src : rb.N → ra.N ⊕ (A × ℕ × ℕ))
    (h : ∀ v, Q (code v) (Flat.nRows (rows v) (len v) (M v)) (mrow v) (role v) (q v)) :
    (Core.trackSendFlat (P := P) A overF rows len M K C code mrow role q hlen p₀ msg
      φ fx ra rb src).All Q := ⟨h, trivial⟩

/-- A sum over the vectors of the message. -/
theorem Core.sum_trackSendFlat (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ) (p₀ : K → E)
    (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (A × ℕ × ℕ)) :
    (Core.trackSendFlat (P := P) A overF rows len M K C code mrow role q hlen p₀
        msg φ fx ra rb src).sum f =
      ∑ v, f (code v) (Flat.nRows (rows v) (len v) (M v)) (mrow v) (role v) (q v) := Nat.add_zero _

variable (A overF rows len M K C code mrow role q)

/-- Its data (`Core.Data`, Blocks/StageData.lean). The enumeration of the index type of the matrices
is an argument. -/
def Core.Data.sendFlat [FinEnum E] [FinEnum K] [IdxK K] [FinEnum C] [ChalK E C] (eA : FinEnum A)
    (p₀ : K → E) (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (A × ℕ × ℕ)) :
    (Core.sendFlat (P := P) A overF rows len M K C a X' Z p₀ msg φ fx).Data
      (Core.trackSendFlat A overF rows len M K C code mrow role q hlen p₀ msg φ fx ra rb src) :=
  Core.Data.send (e := Flat.eFlat E A overF rows len M code mrow role q hlen K C) (RNum.ofEnum _ eA)
    p₀ (fun s π => Flat.flat M K C (msg s π)) (fun o => φ (Flat.unflat o)) fx ra rb
    fun n => (src n).map _root_.id fun t : A × ℕ × ℕ => Flat.src len M t.1 t.2.1 t.2.2

end Send

/-! ## The stage -/

section StageFlat

variable {P E F : Type} [Field F] [Field E] [Algebra F E] [Fintype E] [DecidableEq E] [Fintype P]
  [DecidableEq P] {a : Sorts} {X' Z : Type} (A : Type) (overF : A → Bool) (rows len M : A → ℕ)
  (K C : Type) [Fintype C] [Nonempty C]

/-- One prover message of matrices, written end to end: the stage. -/
def Stage.sendFlat (a : Sorts) (X' Z : Type) (p₀ : K → E)
    (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') :
    Stage P E a ⟨X', a.Y × Z, a.I⟩ :=
  Stage.send a X' Z (Flat.rFlat E F A overF rows len M K C) p₀
    (fun s π => Flat.flat M K C (msg s π)) (fun o => φ (Flat.unflat o)) fx

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCore_sendFlat (p₀ : K → E) (msg : a.I → (P → E) → Flat.Log E F A overF rows len)
    (φ : Flat.Log E F A overF rows len → Z) (fx : a.X → X') :
    (Stage.sendFlat A overF rows len M K C a X' Z p₀ msg φ fx).toCore =
      Core.sendFlat A overF rows len M K C a X' Z p₀ msg φ fx := rfl

variable {A overF rows len M K C}

/-- `Stage.Props` under hM, from one backward step, one forward step and validity, all three stated
on the logical form. All errors are 0, no pad is used for masking, the withheld set (`Hon.withheld`)
is empty. -/
theorem Stage.props_sendFlat (hM : ∀ v, 0 < M v) (p₀ : K → E)
    (msg : a.I → (P → E) → Flat.Log E F A overF rows len) (φ : Flat.Log E F A overF rows len → Z)
    (fx : a.X → X') {ca : Cut P E a} {cb : Cut P E ⟨X', a.Y × Z, a.I⟩}
    (hback : ∀ x y m, cb.R (fx x) (y, φ m) → ca.R x y)
    (hfwd : ∀ s π x y, ca.Hn s π x y → cb.Hn s π (fx x) (y, φ (msg s π)))
    (hV : ∀ s, ca.V s → cb.V s) :
    (Stage.sendFlat A overF rows len M K C a X' Z p₀ msg φ fx).Props ca cb :=
  Stage.props_send (Flat.rFlat E F A overF rows len M K C) p₀ (fun s π => Flat.flat M K C (msg s π))
    (fun o => φ (Flat.unflat o)) fx (fun x y o => hback x y (Flat.unflat o))
    (fun s π x y h => by
      show cb.Hn s π (fx x) (y, φ (Flat.unflat (Flat.flat M K C (msg s π))))
      rw [Flat.unflat_flat hM]
      exact hfwd s π x y h) hV

end StageFlat

end Blocks
