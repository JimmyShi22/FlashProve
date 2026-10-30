-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/AfterLay.lean: what the code switch in front of a link has left open (`LdLocD.After`,
Cb/Req1/LdSegKit.lean), laid as rows of the link's own closing: the rows give it back.

Definitions, statements and proofs. The library shows that `After` is a family of rows on all
entries of the messages behind the switch (`Cb.ldLoc_after_rows`, Cb/Req1/LdSegAfterRows.lean, under
`D.Lin`). Here these rows are carried to the entries of the message of the link's closing group.

Main names:
  `pushTo_supp`, `rowsOf_supp`: a coefficient of such a row is 0 but at an entry that the open
    word's message or randomness is read from.
  `afterRows D pJ pQ φ xφ κ x`: the rows of `After` at x, carried along κ from the entries behind
    the switch to the entries of a group's message.
  `after_of_rows`: if these rows hold of the group's message at m, then `After x (mD m)` holds: for
    a reading mD of the messages behind the switch off the link's messages, where the entries that
    the open word is read from are entries of the group's message (`hJ`, `hQ`).
  `lin_loc`: `D.Lin` at the locations of a closing's second half (`LdCloseD.loc`,
    Cb/Req1/LdSegFit.lean): the claim is a form by definition; premises: the folded code's laws; the
    cut reads entries of the fresh messages.
  `rowLay_ok_after`: `RowLayRide.OK` (Johnson/Top/H/RowLayRows.lean) at the joint "R0, and After".

Limits: by algebra alone. That the fresh messages of the switch are members of the link's closing
group is the premise `hJ`, `hQ`. Further open claims beside `After` are not in `rowLay_ok_after`.
-/
import Johnson.Top.H.RowLayRows
import Cb.Req1.LdSegFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.RowsOf
open KObj Iop Prob Hiop Cb IOR TWhole Cb.Pv.Att Cb.Pv.Tail Cb.Pv.BatOf VerifiableInference.OnPublicFiles

/-- A carried coefficient is 0 off the map's range. -/
theorem pushTo_supp {E I J : Type} [AddCommMonoid E] [Fintype I] (p : I → J) (c : I → E) (n : J)
    (h : pushTo p c n ≠ 0) : ∃ i, p i = n := by
  classical
  by_contra hn
  refine h (Finset.sum_eq_zero fun i _ => if_neg fun hi => hn ⟨i, hi⟩)

variable {E Kd : Type} [Field E] [Fintype E] (D : LdLocD E Kd) {Xφ : Type}
  (pJ : D.C.J → D.S.Ent) (pQ : D.C.Q → D.S.Ent) (φ : Slf E Xφ D.C.J) (xφ : D.Xc → E × Xφ)

/-- A coefficient of a row of `After` is 0 but where the open word is read from. -/
theorem rowsOf_supp (x : (D.Xc × D.hd.Smp) × D.Lc) (b : D.RowN) (n : D.S.Ent)
    (h : (D.rowsOf pJ pQ φ xφ x).2 b n ≠ 0) : (∃ j, pJ j = n) ∨ ∃ q, pQ q = n := by
  rcases b with _ | ks | iα
  · exact .inl (pushTo_supp pJ _ n h)
  · obtain ⟨j, hj⟩ := pushTo_supp (fun j => pJ (D.hd.sJ ks.1 j)) _ n h
    exact .inl ⟨_, hj⟩
  · by_cases h1 : pushTo pJ (fun j => D.C.row (x.2.1 iα.1) iα.2 (.inl j)) n = 0
    · refine .inr (pushTo_supp pQ (fun q => D.C.row (x.2.1 iα.1) iα.2 (.inr q)) n fun h2 => h ?_)
      show pushTo pJ (fun j => D.C.row (x.2.1 iα.1) iα.2 (.inl j)) n +
        pushTo pQ (fun q => D.C.row (x.2.1 iα.1) iα.2 (.inr q)) n = 0
      rw [h1, h2, add_zero]
    · exact .inl (pushTo_supp pJ _ n h1)

variable {I' : Type} [Fintype I'] (κ : D.S.Ent → I')

/-- The rows of `After`, carried to other entries. -/
noncomputable def afterRows (x : (D.Xc × D.hd.Smp) × D.Lc) : (D.RowN → E) × (D.RowN → I' → E) :=
  ((D.rowsOf pJ pQ φ xφ x).1, fun b => pushTo κ ((D.rowsOf pJ pQ φ xφ x).2 b))

/-- The carried rows give `After` back. -/
theorem after_of_rows (hL : D.Lin pJ pQ φ xφ) (x : (D.Xc × D.hd.Smp) × D.Lc) (u : D.S.Msg)
    (v' : I' → E) (hJ : ∀ j, D.S.ents u (pJ j) = v' (κ (pJ j)))
    (hQ : ∀ q, D.S.ents u (pQ q) = v' (κ (pQ q)))
    (h : Slf.All (fun _ : D.RowN => (Slf.idf : Slf E (I' → E) I'))
      (afterRows D pJ pQ φ xφ κ x) v') : D.After x u :=
  (ldLoc_after_rows E Kd D Xφ pJ pQ φ xφ hL x u).2
    ((all_push κ _ _ (D.S.ents u) v' fun b n hn => by
      rcases rowsOf_supp D pJ pQ φ xφ x b n hn with ⟨j, rfl⟩ | ⟨q, rfl⟩
      · exact hJ j
      · exact hQ q).1 h)

/-- `D.Lin` at the locations of a closing's second half. -/
theorem lin_loc {Kc : Type} (Dd : LdFoldD E Kc) (Q : LdCloseD Dd) (nJ : Dd.Cf.J → Q.N.Ent)
    (nQ : Dd.Cf.Q → Q.N.Ent) (hC : Dd.Cf.Laws)
    (hJ : ∀ u j, (Q.cutN u).1 j = Q.N.ents u (nJ j))
    (hQ : ∀ u q, (Q.cutN u).2 q = Q.N.ents u (nQ q)) :
    Q.loc.Lin (fun j => ⟨Sum.inr (nJ j).1, (nJ j).2⟩) (fun q => ⟨Sum.inr (nQ q).1, (nQ q).2⟩)
      Dd.slf id where
  cutJ := fun m j => hJ (Dd.S₂.right Q.N (T := OMsg.Msg) m) j
  cutQ := fun m q => hQ (Dd.S₂.right Q.N (T := OMsg.Msg) m) q
  form := fun _ _ => Iff.rfl
  laws := hC

section Lay
variable (S : Sig E) {Pl : Type} [Fintype Pl] (G : GrpD Pl S) (e : ℕ) (keep : S.O → Bool)
  [Fintype D.RowN] (Z : Evader E ((G.toGrp e).Row (D.RowN ⊕ Unit))) (L : ℕ)
  [DecidableEq (G.toGrp e).C.J] {P J St₀ : Type} [Fintype J] (ι : J → (G.toGrp e).C.J)
  (κg : D.S.Ent → (G.toGrp e).C.J) (xo : P → (D.Xc × D.hd.Smp) × D.Lc) (mD : S.Msg → D.S.Msg)
  (st : (P × E) × Form E J → St₀) (F : ExtSpec) {Kc X0 Wp : Type} {E₀ : ExtSpec}
  (R0 : Rels Kc X0 (E₀.prod F) (S.Msg × Wp)) (pr : P → X0) (msg : S.Msg → J → E)
  (A₀ : Rels Kc St₀ E₀
    (((sizeRowsB S G e keep D.RowN Z L).S.sub (sizeRowsB S G e keep D.RowN Z L).kp).Msg × Wp))

/-- What the step into the closing owes, where what is open beside the one form is what the code
switch in front has left. -/
theorem rowLay_ok_after (hL : D.Lin pJ pQ φ xφ)
    (hmsg : ∀ m j, msg m j = (G.toGrp e).msg m (ι j))
    (hJ : ∀ m j, D.S.ents (mD m) (pJ j) = (G.toGrp e).msg m (κg (pJ j)))
    (hQ : ∀ m q, D.S.ents (mD m) (pQ q) = (G.toGrp e).msg m (κg (pQ q)))
    (hon : ∀ x (y : (E₀.prod F).Str), R0.on (pr x.1.1, y) → A₀.on (st x, y.1))
    (hrest : ∀ x (y : (E₀.prod F).Str) (w : S.Msg × Wp), R0.on (pr x.1.1, y) →
      A₀.relR (st x, y.1)
        ((sizeRowsB S G e keep D.RowN Z L).S.res (T := OMsg.Msg)
          (sizeRowsB S G e keep D.RowN Z L).kp w.1, w.2) → R0.relR (pr x.1.1, y) w) :
    RowLayRide.OK (sizeRowsB S G e keep D.RowN Z L) F
      (jt R0 pr fun p m => D.After (xo p) (mD m)) msg A₀
      (layRowsB S G e keep D.RowN Z L ι (fun p => afterRows D pJ pQ φ xφ κg (xo p)) st) :=
  rowLay_ok_rows S G e keep D.RowN Z L ι _ st F R0 pr _ msg A₀ hmsg
    (fun p m h => after_of_rows D pJ pQ φ xφ κg hL (xo p) (mD m) _ (hJ m) (hQ m) h) hon hrest

end Lay

end VerifiableInference.OnPublicFiles.RowsOf

#print axioms VerifiableInference.OnPublicFiles.RowsOf.rowsOf_supp
#print axioms VerifiableInference.OnPublicFiles.RowsOf.after_of_rows
#print axioms VerifiableInference.OnPublicFiles.RowsOf.lin_loc
#print axioms VerifiableInference.OnPublicFiles.RowsOf.rowLay_ok_after
