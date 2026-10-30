-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Yes.lean: SMALL LAWS FOR THE ASSEMBLY OF K12's LAW IN THE PLAIN FORM.
Statements and proofs.

  `like_lo`: a stretch whose data are written rounds (`Like`) is `lo.map mk` (Written.lean).
  `yes_step`: where a piece without rounds put behind puts out b: the stage's tests passed; the
    block's step went on to b's record on the transcript's own rounds and the stage's own columns;
    no column is left over.
  `bears_le`, `errList_errW`: from `Bears` to the library's order on errors.
  `ofFn_getD`, `colW_woIn`: a column of the right width, read back off `woIn`, is itself.
  `PCol`: "col is the column at x of the tree that the declared opening o names, as wide as
    declared, x inside the declared depth".
A tool.
-/
import Johnson.Desc.K12.Coin.Sheet
import Johnson.Desc.K12.Coin.Inside
import Johnson.Desc.K12.Coin.Written
import Johnson.Desc.K12.Coin.Src

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open H2K.Pub (WR)

theorem like_lo (dt : List RDT) (l : List WR) (h : List.Forall₂ Like dt l) :
    ∃ lo : List (PQ.RD × List ℕ), dt = lo.map mk ∧ lo.map (·.1) = l.map WR.rd := by
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons d w dt l hd _ ih =>
    obtain ⟨lo, h1, h2⟩ := ih
    refine ⟨(w.rd, d.opens) :: lo, ?_, ?_⟩
    · obtain ⟨⟨e, k, it, tr, op⟩, st⟩ := d
      obtain ⟨a1, a2, a3, a4, a5⟩ := hd
      dsimp only at a1 a2 a3 a4 a5
      subst a1 a2 a3 a4 a5
      rw [h1]
      rfl
    · rw [List.map_cons, List.map_cons, h2]

section
variable {S Cl W : Type} {C : PQ.CK} {F : Frame}

theorem yes_step (p : Piece C F S Cl W) (h0 : p.back = []) (a : S × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (b : S × F.E.Str) (hb : p.ior.red.out a τ = some b) :
    sTests C p.stage a.2 τ = true ∧
      ∃ k, p.b.step F.ft a.1 (rvT C p.ds τ) (sView C p.stage a.2 τ).opened = .ok (b.1, k) ∧
        (sView C p.stage a.2 τ).opened.drop k = [] := by
  obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hs' : (if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none) =
      some s' := hs
  split at hs'
  · rename_i ht
    refine ⟨ht, ?_⟩
    have hc := (chainOne _ _ _ _ _ _).1 (toOptionOk hs')
    obtain ⟨_, s₁, k, hst, he⟩ := (foldOne _ _ _ _ _ _).1 hc
    have e₁ : s' = s₁ := congrArg Prod.fst he
    have e₂ : ([] : List Fmt.RoundView) = (rvT C p.ds τ ++ p.back).drop p.b.rounds.length :=
      congrArg (fun x => x.2.1) he
    have e₃ : ([] : List OpenedColumn) = (sView C p.stage a.2 τ).opened.drop k :=
      congrArg (fun x => x.2.2) he
    have e₄ : (rvT C p.ds τ ++ p.back).take p.b.rounds.length = rvT C p.ds τ := by
      rw [List.take_of_length_le (List.drop_eq_nil_iff.1 e₂.symm), h0, List.append_nil]
    have hst' : p.b.step F.ft a.1 ((rvT C p.ds τ ++ p.back).take p.b.rounds.length)
        (sView C p.stage a.2 τ).opened = .ok (s₁, k) := hst
    rw [e₄, ← e₁] at hst'
    exact ⟨k, hst', e₃.symm⟩
  · cases hs'

end

theorem bears_le : ∀ (s : Shape) (ε ε' : Err s), Bears ε ε' → Err.le ε ε'
  | [], _, _, _ => trivial
  | _ :: s, (_, ε), (_, ε'), h => by
    cases h with
    | cons h1 h2 => exact ⟨h1, bears_le s ε ε' h2⟩

theorem errList_errW (C : PQ.CK) : ∀ (lo : List (PQ.RD × List ℕ))
    (ε : Err (PQ.uL C (lo.map (·.1)))), errList _ (errW C lo ε) = errList _ ε
  | [], _ => rfl
  | _ :: lo, (e, ε) => congrArg (e :: ·) (errList_errW C lo ε)

theorem ofFn_getD (col : List UInt64) (w : ℕ) (h : col.length = w) :
    List.ofFn (fun k : Fin w => col.getD k.val 0) = col := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD]

theorem colW_woIn (F : Frame) (y : F.E.Str) (j a w x : ℕ) (col : List UInt64) (hx : x < 2 ^ a)
    (hc : colIn F y j x = col) (hl : col.length = w) :
    colW (woIn F y j a w).1 (woIn F y j a w).2 x = col := by
  unfold colW
  rw [dif_pos (show x < PQ.posN (woIn F y j a w).1.tree from hx)]
  show List.ofFn (fun k : Fin w => (colIn F y j x).getD k.val 0) = col
  rw [hc]
  exact ofFn_getD col w hl

/-- "col is the column at x of the tree that the declared opening o names, as wide as declared; x
lies inside the declared depth." -/
def PCol (C : PQ.CK) (St : StageD) (y : St.Ei.Str) (τ : Iop.Tr (uLT C St.ds))
    (num : Fmt.TreeSource → ℕ) (o : ToldO) (x : ℕ) (col : List UInt64) : Prop :=
  sCol C St y τ (.tree (num o.2) x) = some col ∧ col.length = o.1.W ∧ x < 2 ^ o.1.a

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.like_lo
#print axioms VerifiableInference.Desc.K12.Coin.yes_step
#print axioms VerifiableInference.Desc.K12.Coin.colW_woIn
