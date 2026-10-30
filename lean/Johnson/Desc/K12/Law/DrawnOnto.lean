-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.DrawOnto
import Johnson.Desc.K12.Law.FitWritten
/-
Johnson/Desc/K12/Law/DrawnOnto.lean: WHICH RECORDS OF WHAT A ROUND DREW COME FROM HASH BLOCKS: every Fmt.Drawn that fits its entry (DrawnIs) is, its sealed digest apart, (ckP .two).dr of some blocks. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  Canon x       the three words of an element of the extension field are below the field's size
  DrawnIs e k D as many positions as the entry says, each below 2 ^ logN · as many matrix entries, each -1, 0 or 1 · the elements stand one to one beside the entry's draws of elements (Fmt.dsElems e k: so their number and their order are the format's), each canonical, and not 0 where the draw must not be 0. (FitsDrawn, Johnson/Desc/K12/Law/FitWritten.lean, says that every written round's draws meet these but «canonical»; here is the converse.)
  vals_onto     by recursion on a list of draws: elements, positions and matrix entries that fit the list are collect ∘ outAll of some typed values
  drawnOf_onto  DrawnIs e k D ⇒ ∃ v : Ch .two e k, drawnOf .two e k v has D's elements, positions and matrix entries
  drawn_of_blocks  e.logN ≤ 64 · DrawnIs e k D ⇒ ∃ u : (ckP .two).Ch e k, { (ckP .two).dr e k u with digest := none } = { D with digest := none }
WHAT IT DOES NOT SAY: anything of the sealed digest (a kind is shown its rounds without it) · that the blocks are a hash function's answers: they are any blocks: the statement lives in the oracle model.
EVERY THEOREM OF THIS FILE IS PROVED OUTRIGHT: nothing is left open and nothing is laid down by decree; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.Onto
open Run H2K.Fit

def Canon (x : Fmt.Ext) : Prop :=
  x.1.toNat < Fmt.Fld.two.p ∧ x.2.1.toNat < Fmt.Fld.two.p ∧ x.2.2.toNat < Fmt.Fld.two.p

structure DrawnIs (e : Fmt.Entry) (k : Fmt.Kind) (D : Fmt.Drawn) : Prop where
  poss : D.poss.length = e.poss
  below : ∀ x ∈ D.poss, x < 2 ^ e.logN
  trits : D.trits.length = e.trits
  signs : ∀ t ∈ D.trits, t = -1 ∨ t = 0 ∨ t = 1
  elems : List.Forall₂ (fun d x => Canon x ∧ (d = Fmt.Draw.elemNZ → x ≠ ((0, 0, 0) : Fmt.Ext)))
    (Fmt.dsElems e k) D.elems

theorem toU_mk (w : UInt64) (h : w.toNat < Fmt.Fld.two.p) : toU (f := .two) ⟨w.toNat, h⟩ = w := by
  unfold toU
  exact UInt64.ofNat_toNat

def evOf (x : Fmt.Ext) (h : Canon x) : EV .two :=
  (⟨x.1.toNat, h.1⟩, ⟨x.2.1.toNat, h.2.1⟩, ⟨x.2.2.toNat, h.2.2⟩)

theorem toU3_evOf (x : Fmt.Ext) (h : Canon x) : toU3 (evOf x h) = x := by
  obtain ⟨a, b, c⟩ := x
  show (toU (f := .two) ⟨a.toNat, h.1⟩, toU (f := .two) ⟨b.toNat, h.2.1⟩,
    toU (f := .two) ⟨c.toNat, h.2.2⟩) = (a, b, c)
  rw [toU_mk, toU_mk, toU_mk]

theorem evOf_ne (x : Fmt.Ext) (h : Canon x) (hx : x ≠ (0, 0, 0)) :
    evOf x h ≠ (zF .two, zF .two, zF .two) := by
  intro he
  apply hx
  rw [← toU3_evOf x h, he]
  rfl

def pre (t : Int) : Bool × Bool :=
  if t = 0 then (false, false) else if t = 1 then (true, false) else (true, true)

theorem trit_pre (t : Int) (h : t = -1 ∨ t = 0 ∨ t = 1) : trit (pre t) = t := by
  rcases h with rfl | rfl | rfl <;> rfl

theorem trits_onto (n : ℕ) (l : List Int) (hl : l.length = n)
    (hs : ∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1) :
    ∃ b : Fin n → Bool × Bool, (List.ofFn fun j => trit (b j)) = l := by
  subst hl
  refine ⟨fun j => pre (l.get j), ?_⟩
  have : (fun j : Fin l.length => trit (pre (l.get j))) = l.get :=
    funext fun j => trit_pre _ (hs _ (List.get_mem l j))
  rw [this, List.ofFn_get]

/-- Elements, positions and matrix entries that fit a list of draws are the values of some typed
tuple. -/
theorem vals_onto : ∀ (ds : List Fmt.Draw) (E : List Fmt.Ext) (P : List ℕ) (T : List Int),
    List.Forall₂ (fun d x => Canon x ∧ (d = Fmt.Draw.elemNZ → x ≠ ((0, 0, 0) : Fmt.Ext)))
      (ds.filter isE) E →
    List.Forall₂ (fun d x => ∀ k, d = Fmt.Draw.pos k → x < 2 ^ k) (ds.filter isP) P →
    T.length = (ds.map tritN).sum → (∀ t ∈ T, t = -1 ∨ t = 0 ∨ t = 1) →
    ∃ v : Vals .two ds, (Fmt.collect (outAll .two ds v)).elems = E ∧
      (Fmt.collect (outAll .two ds v)).poss = P ∧ (Fmt.collect (outAll .two ds v)).trits = T
  | [], E, P, T, hE, hP, hT, _ => by
    cases hE
    cases hP
    obtain rfl := List.length_eq_zero_iff.1 hT
    exact ⟨(), rfl, rfl, rfl⟩
  | .elem :: ds, E, P, T, hE, hP, hT, hs => by
    cases hE with
    | cons hx hE' =>
      obtain ⟨v, a, b, c⟩ := vals_onto ds _ P T hE' hP (by simpa [tritN] using hT) hs
      exact ⟨(evOf _ hx.1, v), by
        show toU3 (evOf _ hx.1) :: _ = _
        rw [toU3_evOf, a], b, c⟩
  | .elemNZ :: ds, E, P, T, hE, hP, hT, hs => by
    cases hE with
    | cons hx hE' =>
      obtain ⟨v, a, b, c⟩ := vals_onto ds _ P T hE' hP (by simpa [tritN] using hT) hs
      exact ⟨(⟨evOf _ hx.1, evOf_ne _ hx.1 (hx.2 rfl)⟩, v), by
        show toU3 (evOf _ hx.1) :: _ = _
        rw [toU3_evOf, a], b, c⟩
  | .pos k :: ds, E, P, T, hE, hP, hT, hs => by
    cases hP with
    | cons hx hP' =>
      obtain ⟨v, a, b, c⟩ := vals_onto ds E _ T hE hP' (by simpa [tritN] using hT) hs
      exact ⟨(⟨_, hx k rfl⟩, v), a, by
        show _ :: _ = _
        rw [b], c⟩
  | .trits n :: ds, E, P, T, hE, hP, hT, hs => by
    have hT' : T.length = n + (ds.map tritN).sum := by simpa [tritN] using hT
    obtain ⟨bb, hb⟩ := trits_onto n (T.take n) (by rw [List.length_take]; omega)
      fun t ht => hs t (List.mem_of_mem_take ht)
    obtain ⟨v, a, b, c⟩ := vals_onto ds E P (T.drop n) hE hP (by rw [List.length_drop]; omega)
      fun t ht => hs t (List.mem_of_mem_drop ht)
    exact ⟨(bb, v), a, b, by
      show (List.ofFn fun j => trit (bb j)) ++ _ = _
      rw [hb, c, List.take_append_drop]⟩
  | .sealed :: ds, E, P, T, hE, hP, hT, hs => by
    obtain ⟨v, a, b, c⟩ := vals_onto ds E P T hE hP (by simpa [tritN] using hT) hs
    exact ⟨(fun _ => 0, v), a, b, c⟩

theorem forall₂_of_all {α β : Type} (R : α → β → Prop) : ∀ (l : List α) (m : List β),
    l.length = m.length → (∀ a ∈ l, ∀ b ∈ m, R a b) → List.Forall₂ R l m
  | [], [], _, _ => List.Forall₂.nil
  | a :: l, b :: m, h, hR =>
    List.Forall₂.cons (hR a List.mem_cons_self b List.mem_cons_self)
      (forall₂_of_all R l m (Nat.succ.inj h) fun a' ha b' hb =>
        hR a' (List.mem_cons_of_mem _ ha) b' (List.mem_cons_of_mem _ hb))
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h


theorem drawnOf_onto (e : Fmt.Entry) (k : Fmt.Kind) (D : Fmt.Drawn) (h : DrawnIs e k D) :
    ∃ v : Ch .two e k, (drawnOf .two e k v).elems = D.elems ∧
      (drawnOf .two e k v).poss = D.poss ∧ (drawnOf .two e k v).trits = D.trits := by
  refine vals_onto (Fmt.dsOf e k) D.elems D.poss D.trits ?_ ?_ ?_ h.signs
  · rw [dsOf_isE]
    exact h.elems
  · refine forall₂_of_all _ _ _ (by rw [dsOf_isP, h.poss]) fun d hd x hx k' hk => ?_
    subst hk
    rw [dsOf_pos e k k' (List.mem_of_mem_filter hd)]
    exact h.below x hx
  · rw [dsOf_trits, h.trits]


theorem drawn_of_blocks (e : Fmt.Entry) (k : Fmt.Kind) (D : Fmt.Drawn) (hl : e.logN ≤ 64)
    (h : DrawnIs e k D) :
    ∃ u : (ckP .two).Ch e k,
      { (ckP .two).dr e k u with digest := none } = { D with digest := none } := by
  obtain ⟨v, a, b, c⟩ := drawnOf_onto e k D h
  obtain ⟨u, hu⟩ := dr_onto .two e k hl v
  refine ⟨u, ?_⟩
  rw [hu]
  show (⟨(drawnOf .two e k v).elems, (drawnOf .two e k v).poss, (drawnOf .two e k v).trits,
    none⟩ : Fmt.Drawn) = _
  rw [a, b, c]

end H2K.Onto

#print axioms H2K.Onto.drawnOf_onto
#print axioms H2K.Onto.drawn_of_blocks
