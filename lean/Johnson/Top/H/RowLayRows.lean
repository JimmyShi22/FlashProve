-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/RowLayRows.lean: what the step from a sub-proof's closing draw into the round before a
proximity test owes (`RowLayRide.OK`, Johnson/Top/H/RowSeamRide.lean), by algebra, where what is
open beside the sub-proof's one form is a family of rows in the library's own form: targets and
coefficient vectors.

Definitions, statements and proofs. Johnson/Top/H/RowLayOf.lean does the same for a ledger of at
most nB claims. The library gives what a code switch leaves open as a family of rows over any names,
each row its own state, on all entries of the messages that are left (`Cb.ldLoc_after_rows`,
Cb/Req1/LdSegAfterRows.lean). Here such a family is laid as it is; and a family of rows on one set
of entries is carried to another set along a map that need be right only where a coefficient is not
0.

Main names:
  `all_push`: rows with coefficient vectors co b on the entries I, and the same carried along κ : I
    → I' (`pushTo`, Cb/Req1/LdSegAfterRows.lean): they hold together of v and v', if v n = v' (κ n)
    wherever some co b n is not 0.
  `sizeRowsB S G e keep Bx Z L`: the size with the rows Bx and one more, each its own state.
  `layRowsB`: how a statement is laid: the family `rows p`, and the one form as the last row.
  `rowLay_ok_rows`: `RowLayRide.OK` at: the joint in front is "R0, and Gc p m". Premises: the one
    form's entries are entries of the group's message (`hmsg`); the rows give Gc (`hG`); the joint
    behind gives R0 (`hon`, `hrest`).

Limits: a row reads the group's members alone. Nothing on the programs' rows.
-/
import Johnson.Top.H.RowLayOf
import Cb.Req1.LdSegAfterRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.RowsOf
open KObj Iop Prob Hiop Cb IOR TWhole Cb.Pv.Att Cb.Pv.Tail Cb.Pv.BatOf VerifiableInference.OnPublicFiles

variable {E : Type} [Field E] [Fintype E]

omit [Fintype E] in
/-- Rows carried along a map of the entries hold together with the rows themselves. -/
theorem all_push {B I I' : Type} [Fintype I] [Fintype I'] (κ : I → I') (tg : B → E)
    (co : B → I → E) (v : I → E) (v' : I' → E) (h : ∀ b n, co b n ≠ 0 → v n = v' (κ n)) :
    Slf.All (fun _ : B => (Slf.idf : Slf E (I' → E) I')) (tg, fun b => pushTo κ (co b)) v' ↔
      Slf.All (fun _ : B => (Slf.idf : Slf E (I → E) I)) (tg, co) v := by
  refine forall_congr' fun b => ?_
  unfold Slf.Holds Slf.idf
  show (∑ j, pushTo κ (co b) j * v' j = tg b) ↔ (∑ j, co b j * v j = tg b)
  rw [pushTo_sum]
  have e : ∑ i, co b i * v' (κ i) = ∑ i, co b i * v i := Finset.sum_congr rfl fun i _ => by
    by_cases hz : co b i = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [h b i hz]
  rw [e]

variable (S : Sig E) {Pl : Type} [Fintype Pl] (G : GrpD Pl S) (e : ℕ) (keep : S.O → Bool)
  (Bx : Type) [Fintype Bx] (Z : Evader E ((G.toGrp e).Row (Bx ⊕ Unit))) (L : ℕ)

/-- The size with the rows Bx and one more, each its own state. -/
abbrev sizeRowsB : Cb.Pv.Bat.Size E :=
  batSizeOf S G e keep (Bx ⊕ Unit) (fun _ => (G.toGrp e).C.J → E) (fun _ => Slf.idf) Z L

variable [DecidableEq (G.toGrp e).C.J] {P J St₀ : Type} [Fintype J] (ι : J → (G.toGrp e).C.J)
  (rows : P → (Bx → E) × (Bx → (G.toGrp e).C.J → E)) (st : (P × E) × Form E J → St₀)

/-- How a statement behind the closing draw is laid. -/
def layRowsB : RowLay (sizeRowsB S G e keep Bx Z L) P J St₀ := fun x =>
  ((Sum.elim (rows x.1.1).1 fun _ => (pushF ι x.2).tg,
    fun b => Sum.casesOn (motive := fun _ => (G.toGrp e).C.J → E) b (rows x.1.1).2
      fun _ => (pushF ι x.2).co), st x)

variable (F : ExtSpec) {Kc X0 Wp : Type} {E₀ : ExtSpec}
  (R0 : Rels Kc X0 (E₀.prod F) (S.Msg × Wp)) (pr : P → X0) (Gc : P → S.Msg → Prop)
  (msg : S.Msg → J → E)
  (A₀ : Rels Kc St₀ E₀
    (((sizeRowsB S G e keep Bx Z L).S.sub (sizeRowsB S G e keep Bx Z L).kp).Msg × Wp))

/-- What the step owes, by algebra. -/
theorem rowLay_ok_rows (hmsg : ∀ m j, msg m j = (G.toGrp e).msg m (ι j))
    (hG : ∀ p m, Slf.All (fun _ : Bx => (Slf.idf : Slf E _ (G.toGrp e).C.J)) (rows p)
      ((G.toGrp e).msg m) → Gc p m)
    (hon : ∀ x (y : (E₀.prod F).Str), R0.on (pr x.1.1, y) → A₀.on (st x, y.1))
    (hrest : ∀ x (y : (E₀.prod F).Str) (w : S.Msg × Wp), R0.on (pr x.1.1, y) →
      A₀.relR (st x, y.1)
        ((sizeRowsB S G e keep Bx Z L).S.res (T := OMsg.Msg) (sizeRowsB S G e keep Bx Z L).kp w.1,
          w.2) → R0.relR (pr x.1.1, y) w) :
    RowLayRide.OK (sizeRowsB S G e keep Bx Z L) F (jt R0 pr Gc) msg A₀
      (layRowsB S G e keep Bx Z L ι rows st) where
  on := fun x y h => hon x y h
  form := fun x m hA => by
    have h1 := (pushF_holds ι x.2 _).1 ((idf_holds _ _).1 (hA (.inr ())))
    have e1 : (fun j => (G.toGrp e).msg m (ι j)) = msg m := funext fun j => (hmsg m j).symm
    rw [e1] at h1
    exact h1
  ride := fun x y w ho hA hr => ⟨hrest x y w ho hr, hG x.1.1 w.1 fun b => hA (.inl b)⟩

end VerifiableInference.OnPublicFiles.RowsOf

#print axioms VerifiableInference.OnPublicFiles.RowsOf.all_push
#print axioms VerifiableInference.OnPublicFiles.RowsOf.rowLay_ok_rows
