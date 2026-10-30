-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/VecJoinTrack.lean: a prover message of matrices in one vector, with its tracking data.

Blocks/VecJoin.lean says how the matrices are in one vector; the tracking data are a `Core.Track`
(Blocks/StageTrack.lean). (Words of this library: lean/GLOSSARY.md.)
This file is the counterpart of Blocks/VecFlatTrack.lean. A stage of a chain (`Chain`,
Blocks/Stage.lean) that sends matrices m v (v : A; rows v rows of len v entries, all over one field:
the logical form) states everything on the logical form: its honest message, its function φ, and
where an exposed entry is: (v, i, j). Here this is transported once to the one vector (rows of M
entries): `Core.sendJoin`, `Stage.sendJoin`, `Core.trackSendJoin`. L says where the matrices are in
it (`Join.Lay`); ord is a list of indices v : A. Throughout, the set C of challenges is nonempty;
where tracking data enter (`Core.trackSendJoin`, its theorems and `Core.Data.sendJoin`), M is the
message length of the code (hlen) and the code has a position.
 * `Stage.props_sendJoin` proves `Stage.Props`, from the three steps of `Stage.props_send` stated on
   the logical form, for M > 0, under `Join.Lay.OK`, if ord lists every v.
 * `Core.trackSendJoin_ok` proves `Core.Track.OK`, under `Join.Lay.OK`, if on the logical form an
   exposed entry after the message is an entry from before it or the entry (i, j) of a matrix v
   (read by `Flat.rdLog`), with i < rows v and j < len v, and if the matrix of weights is copied.
-/
import Blocks.VecJoin
import Blocks.VecFlatTrack
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop

section Send

variable {P E F : Type} [Field F] [Field E] [Algebra F E] {a : Sorts} {X' Z : Type} {A : Type}
  (b : Bool) (rows len : A → ℕ) (L : Join.Lay A) (M : ℕ) (ord : List A) (K C : Type)
  [Fintype C] [Nonempty C]

/-- One prover message of matrices, in one vector: the protocol. msg and φ are given on the logical
form. -/
@[reducible] def Core.sendJoin (a : Sorts) (X' Z : Type) (p₀ : K → E)
    (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') : Core P E a ⟨X', a.Y × Z, a.I⟩ :=
  Core.send a X' Z (Join.rJoin E F b L M K C) p₀ (fun s π => Join.join L M K C ord (msg s π))
    (fun o => φ (Join.unjoin o)) fx

variable (code : Code.Enc F)
  (mrow : ℕ) (role : Role) (q : ℕ) (hlen : code.msg = M) [Nonempty (Fin code.n)]

/-- Its tracking data. src says on the logical form where an exposed entry comes from: an entry from
before the message, or the entry (i, j) of the matrix v. -/
def Core.trackSendJoin (p₀ : K → E) (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (A × ℕ × ℕ)) :
    (Core.sendJoin (P := P) b rows len L M ord K C a X' Z p₀ msg φ fx).Track ra rb :=
  Core.trackSend (Join.eJoin E b L M code mrow role q hlen K C) p₀
    (fun s π => Join.join L M K C ord (msg s π)) (fun o => φ (Join.unjoin o)) fx ra rb
    fun n => (src n).map _root_.id fun t : A × ℕ × ℕ => Join.src L M len t.1 t.2.1 t.2.2

variable {b rows len L M ord K C code mrow role q}

/-- `Core.Track.OK`, under hlen, hL, h (the condition h of `Stage.trackSend_ok`, stated on the
logical form), hin and hm. -/
theorem Core.trackSendJoin_ok [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P]
    (hL : L.OK rows len) (p₀ : K → E) (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (A × ℕ × ℕ))
    (h : ∀ y m n, rb.rd (y, φ m) n = Sum.elim (ra.rd y) (Flat.rdLog m) (src n))
    (hin : ∀ n t, src n = .inr t → t.2.1 < rows t.1 ∧ t.2.2 < len t.1)
    (hm : ∀ y z, rb.mat (y, z) = ra.mat y) :
    (Core.trackSendJoin (P := P) b rows len L M ord K C code mrow role q hlen p₀
      msg φ fx ra rb src).OK :=
  Stage.trackSend_ok (P := P) (Join.eJoin E b L M code mrow role q hlen K C) p₀
    (fun s π => Join.join L M K C ord (msg s π)) (fun o => φ (Join.unjoin o)) fx ra rb _
    (fun y o n => by
      rw [h y (Join.unjoin o) n]
      cases hs : src n with
      | inl k => rfl
      | inr t =>
        obtain ⟨v, i, j⟩ := t
        obtain ⟨hi, hj⟩ := hin n _ hs
        show Flat.rdLog (Join.unjoin o) (v, i, j) = _
        rw [show Flat.rdLog (Join.unjoin o) (v, i, j) =
              (Join.unjoin (rows := rows) (len := len) o v ⟨i, hi⟩ ⟨j, hj⟩).toE
            from Flat.rdLog_fin (Join.unjoin o) v ⟨i, hi⟩ ⟨j, hj⟩]
        exact Join.read code mrow role q hlen hL o v ⟨i, hi⟩ ⟨j, hj⟩) hm

/-- Under hlen: `All Q` holds for the message if Q holds of its one vector: code, ⌈L.tot / M⌉ rows,
mrow, role, q. -/
theorem Core.all_trackSendJoin {Q : Code.Enc F → ℕ → ℕ → Role → ℕ → Prop} (p₀ : K → E)
    (msg : a.I → (P → E) → Join.Log E F b rows len) (φ : Join.Log E F b rows len → Z)
    (fx : a.X → X') (ra : Reads F E a) (rb : Reads F E ⟨X', a.Y × Z, a.I⟩)
    (src : rb.N → ra.N ⊕ (A × ℕ × ℕ)) (h : Q code (Flat.nRows 1 L.tot M) mrow role q) :
    (Core.trackSendJoin (P := P) b rows len L M ord K C code mrow role q hlen p₀ msg
      φ fx ra rb src).All Q :=
  ⟨fun _ => h, trivial⟩

/-- Under hlen: a sum over the vectors of the message has one term. -/
theorem Core.sum_trackSendJoin (f : Code.Enc F → ℕ → ℕ → Role → ℕ → ℕ) (p₀ : K → E)
    (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (A × ℕ × ℕ)) :
    (Core.trackSendJoin (P := P) b rows len L M ord K C code mrow role q hlen p₀
        msg φ fx ra rb src).sum f =
      f code (Flat.nRows 1 L.tot M) mrow role q := by
  show (∑ _v : Unit, f code (Flat.nRows 1 L.tot M) mrow role q) + 0 = _
  simp

variable (b rows len L M ord K C code mrow role q)

/-- Its data (Blocks/StageData.lean): there is one vector, so no enumeration of the index type of
the matrices is asked. -/
def Core.Data.sendJoin [FinEnum E] [FinEnum K] [IdxK K] [FinEnum C] [ChalK E C]
    (p₀ : K → E) (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') (ra : Reads F E a)
    (rb : Reads F E ⟨X', a.Y × Z, a.I⟩) (src : rb.N → ra.N ⊕ (A × ℕ × ℕ)) :
    (Core.sendJoin (P := P) b rows len L M ord K C a X' Z p₀ msg φ fx).Data
      (Core.trackSendJoin b rows len L M ord K C code mrow role q hlen p₀ msg φ fx ra rb src) :=
  Core.Data.send (e := Join.eJoin E b L M code mrow role q hlen K C)
    (Join.nJoin E b L M code mrow role q hlen K C) p₀ (fun s π => Join.join L M K C ord (msg s π))
    (fun o => φ (Join.unjoin o)) fx ra rb
    fun n => (src n).map _root_.id fun t : A × ℕ × ℕ => Join.src L M len t.1 t.2.1 t.2.2

end Send

/-! ## The stage -/

section StageJoin

variable {P E F : Type} [Field F] [Field E] [Algebra F E] [Fintype E] [DecidableEq E] [Fintype P]
  [DecidableEq P] {a : Sorts} {X' Z : Type} {A : Type} (b : Bool) (rows len : A → ℕ)
  (L : Join.Lay A) (M : ℕ) (ord : List A) (K C : Type) [Fintype C] [Nonempty C]

/-- One prover message of matrices, in one vector: the stage. -/
def Stage.sendJoin (a : Sorts) (X' Z : Type) (p₀ : K → E)
    (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') :
    Stage P E a ⟨X', a.Y × Z, a.I⟩ :=
  Stage.send a X' Z (Join.rJoin E F b L M K C) p₀ (fun s π => Join.join L M K C ord (msg s π))
    (fun o => φ (Join.unjoin o)) fx

omit [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq P] in
theorem Stage.toCore_sendJoin (p₀ : K → E) (msg : a.I → (P → E) → Join.Log E F b rows len)
    (φ : Join.Log E F b rows len → Z) (fx : a.X → X') :
    (Stage.sendJoin b rows len L M ord K C a X' Z p₀ msg φ fx).toCore =
      Core.sendJoin b rows len L M ord K C a X' Z p₀ msg φ fx := rfl

variable {b rows len L M ord K C}

/-- `Stage.Props` under hM, hL, hall, from one backward step, one forward step and validity, all
three stated on the logical form. All errors are 0, no pad is used for masking, the withheld set
(`Hon.withheld`) is empty. -/
theorem Stage.props_sendJoin (hM : 0 < M) (hL : L.OK rows len) (hall : ∀ v, v ∈ ord) (p₀ : K → E)
    (msg : a.I → (P → E) → Join.Log E F b rows len) (φ : Join.Log E F b rows len → Z)
    (fx : a.X → X') {ca : Cut P E a} {cb : Cut P E ⟨X', a.Y × Z, a.I⟩}
    (hback : ∀ x y m, cb.R (fx x) (y, φ m) → ca.R x y)
    (hfwd : ∀ s π x y, ca.Hn s π x y → cb.Hn s π (fx x) (y, φ (msg s π)))
    (hV : ∀ s, ca.V s → cb.V s) :
    (Stage.sendJoin b rows len L M ord K C a X' Z p₀ msg φ fx).Props ca cb :=
  Stage.props_send (Join.rJoin E F b L M K C) p₀ (fun s π => Join.join L M K C ord (msg s π))
    (fun o => φ (Join.unjoin o)) fx (fun x y o => hback x y (Join.unjoin o))
    (fun s π x y h => by
      show cb.Hn s π (fx x) (y, φ (Join.unjoin (Join.join L M K C ord (msg s π))))
      rw [Join.unjoin_join hM hL hall]
      exact hfwd s π x y h) hV

end StageJoin

end Blocks

