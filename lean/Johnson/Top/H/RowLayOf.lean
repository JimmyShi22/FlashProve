-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/RowLayOf.lean: what the step from a sub-proof's closing draw into the round before a
proximity test owes (`RowLayRide.OK`, Johnson/Top/H/RowSeamRide.lean), by algebra, where all that is
open is a list of linear claims on entries of the group's members.

Definitions, statements and proofs. The round's open rows are forms on the message of the group.
Here each row is its own state: the state is the vector of coefficients. The step lays: the
sub-proof's one form as one row; and a ledger of further open claims, which hangs on the statement,
as at most nB rows (a row that says 0 = 0 at each place left over). Each claim's coefficients are
carried along an embedding of its entries into the entries of the group's message.

Main names:
  `sizeRows S G e keep nB Z L`: the size (`batSizeOf`, Cb/Pv/BatOf/Size.lean) with nB + 1 such rows.
  `rowAt`, `layRows`: the rows; how a statement is laid.
  `idf_holds`: such a row holds if and only if the form does.
  `rowLay_ok_of`: `RowLayRide.OK` at: the joint in front is "R0, and the ledger `led p` holds of the
    entries mu m". Premises: the one form's entries and the ledger's entries are entries of the
    group's message (`hmsg`, `hμ`); the ledger has at most nB claims; the joint behind gives R0
    (`hon`, `hrest`).

Limits: a row reads the group's members alone: a claim that reads an entry of another message is not
covered: it must come out of the joint behind (`hrest`). A claim that is no linear claim on entries
is not covered. Nothing on the programs' rows.
-/
import Johnson.Top.H.RowSeamRide
import Cb.Pv.BatOf.Size
import Cb.Pv.Tail.DigBatch
import Cb.Pv.Att.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.RowsOf
open KObj Iop Prob Hiop Cb IOR TWhole Cb.Pv.Att Cb.Pv.Tail Cb.Pv.BatOf VerifiableInference.OnPublicFiles

variable {E : Type} [Field E] [Fintype E]

omit [Fintype E] in
/-- A row that is its own state holds if and only if the form does. -/
theorem idf_holds {J : Type} [Fintype J] (f : Form E J) (v : J → E) :
    (Slf.idf : Slf E (J → E) J).Holds (f.tg, f.co) v ↔ f.Holds v := by
  unfold Slf.Holds Slf.idf Form.Holds Form.gap
  exact sub_eq_zero.symm

variable (S : Sig E) {Pl : Type} [Fintype Pl] (G : GrpD Pl S) (e : ℕ) (keep : S.O → Bool) (nB : ℕ)
  (Z : Evader E ((G.toGrp e).Row (Fin nB ⊕ Unit))) (L : ℕ)

/-- The size with nB + 1 rows that are their own states. -/
abbrev sizeRows : Cb.Pv.Bat.Size E :=
  batSizeOf S G e keep (Fin nB ⊕ Unit) (fun _ => (G.toGrp e).C.J → E) (fun _ => Slf.idf) Z L

variable [DecidableEq (G.toGrp e).C.J] {P J Jg St₀ : Type} [Fintype J] [Fintype Jg]
  (ι : J → (G.toGrp e).C.J) (ιg : Jg → (G.toGrp e).C.J) (led : P → Ledger E Jg)
  (st : (P × E) × Form E J → St₀)

/-- The rows: the further open claims, then the one form. -/
def rowAt (x : (P × E) × Form E J) : Fin nB ⊕ Unit → Form E (G.toGrp e).C.J
  | .inl i => pushF ιg ((led x.1.1).getD i.1 ⟨fun _ => 0, 0⟩)
  | .inr _ => pushF ι x.2

/-- How a statement behind the closing draw is laid. -/
def layRows : RowLay (sizeRows S G e keep nB Z L) P J St₀ := fun x =>
  ((fun b => (rowAt S G e nB ι ιg led x b).tg, fun b => (rowAt S G e nB ι ιg led x b).co), st x)

variable (F : ExtSpec) {Kc X0 Wp : Type} {E₀ : ExtSpec}
  (R0 : Rels Kc X0 (E₀.prod F) (S.Msg × Wp)) (pr : P → X0) (mu : S.Msg → Jg → E)
  (msg : S.Msg → J → E)
  (A₀ : Rels Kc St₀ E₀
    (((sizeRows S G e keep nB Z L).S.sub (sizeRows S G e keep nB Z L).kp).Msg × Wp))

/-- What the step owes, by algebra. -/
theorem rowLay_ok_of (hmsg : ∀ m j, msg m j = (G.toGrp e).msg m (ι j))
    (hμ : ∀ m j, mu m j = (G.toGrp e).msg m (ιg j)) (hlen : ∀ p, (led p).length ≤ nB)
    (hon : ∀ x (y : (E₀.prod F).Str), R0.on (pr x.1.1, y) → A₀.on (st x, y.1))
    (hrest : ∀ x (y : (E₀.prod F).Str) (w : S.Msg × Wp), R0.on (pr x.1.1, y) →
      A₀.relR (st x, y.1)
        ((sizeRows S G e keep nB Z L).S.res (T := OMsg.Msg) (sizeRows S G e keep nB Z L).kp w.1,
          w.2) → R0.relR (pr x.1.1, y) w) :
    RowLayRide.OK (sizeRows S G e keep nB Z L) F
      (jt R0 pr fun p m => Ledger.Holds (led p) (mu m)) msg A₀
      (layRows S G e keep nB Z L ι ιg led st) where
  on := fun x y h => hon x y h
  form := fun x m hA => by
    have h1 := (pushF_holds ι x.2 _).1 ((idf_holds _ _).1 (hA (.inr ())))
    have e1 : (fun j => (G.toGrp e).msg m (ι j)) = msg m := funext fun j => (hmsg m j).symm
    rw [e1] at h1
    exact h1
  ride := fun x y w ho hA hr => ⟨hrest x y w ho hr, fun f hf => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
    have h0 := hA (.inl ⟨i, lt_of_lt_of_le hi (hlen _)⟩)
    have h1 := (pushF_holds ιg _ _).1 ((idf_holds _ _).1 h0)
    have e1 : (fun j => (G.toGrp e).msg w.1 (ιg j)) = mu w.1 := funext fun j => (hμ w.1 j).symm
    rw [e1, List.getD_eq_getElem _ _ hi] at h1
    exact h1⟩

end VerifiableInference.OnPublicFiles.RowsOf

#print axioms VerifiableInference.OnPublicFiles.RowsOf.idf_holds
#print axioms VerifiableInference.OnPublicFiles.RowsOf.rowLay_ok_of
