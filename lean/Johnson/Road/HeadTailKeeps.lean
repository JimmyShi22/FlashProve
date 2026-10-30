-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadTailKeeps.lean: the routine that adds the claims of the smallness test keeps the
state's shape.

Johnson/Road/HeadWalk.lean shows that six routines of the output head's check start from states with
one coefficient for each slot and with one number of columns for each array. For the last of the six
it asks that the routine which runs before it, objectsF in OnBytes/Model/Tail.lean, keeps that
shape. This file shows that it does.

How. The routine changes the state in four ways: it adds claims of forms, it adds claims of forms
with long runs of entries (t2Lin, OnBytes/Model/Trees.lean), it marks owed claims as added, and,
where it forms the claim that a sumcheck leaves (pscRow, which adds no claim), it puts the
coefficients of the hiding polynomial under their slots. OnBytes/Model/TreesLaws.lean has what is
needed of the second; the files beside this one have the others. The rest is a walk through the
routine and through the five routines of OnBytes/Model/Tail.lean that it calls.

Main theorems: keeps_t2Lin; keeps_linJoin9, keeps_linBits9, keeps_linTie, keeps_linRead,
keeps_weightsF; keeps_objectsF; objectsF_keeps (the same in the words of
Johnson/Road/HeadWalk.lean).

What is not claimed. Nothing on which claims the routine adds, on their values, on its tests, or on
what the smallness test shows. Every theorem begins "if the routine succeeds": none says that it
does. The program does not import this file.
-/
import Johnson.Road.HeadRunParts
import OnBytes.Model.TreesLaws

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd.Parts

open OnBytes.Model (Fork SubM Reading)

/-- A claim of a form with runs keeps the state's shape. -/
instance keeps_t2Lin (a : Model.Aff) (runs : Array Model.Run2) : KeepsS (Model.t2Lin a runs) :=
  ⟨fun F C u G D hs h => by
    obtain ⟨_, _, _, _, _, h5, h6⟩ :=
      Model.t2Lin_total Reading.gl Walk.world0 a runs F G C D hs h
    exact ⟨h5, fun t => by rw [colsOf_frame, colsOf_frame, h6]⟩⟩

/-- Marking an owed claim as added keeps the state's shape. -/
instance keeps_paid (i : ℕ) : KeepsS (SubM.paid i) := ⟨Walk.keeps_paid i⟩

/-- Reading the number of claims added so far keeps the state's shape. -/
instance keeps_claims : KeepsS SubM.claims := by
  unfold SubM.claims
  infer_instance

/-- The routine that adds the lookup's claims on mask entries keeps the state's shape. -/
instance keeps_objects (g : Model.Forest.Heard) : KeepsS (Model.Forest.objects g) :=
  ⟨Walk.keeps_objects g⟩

/-- Marking the lookup's claim on the key vectors as added keeps the state's shape. -/
instance keeps_joinAdded (g : Model.Forest.Heard) : KeepsS (Model.Forest.joinAdded g) := by
  unfold Model.Forest.joinAdded
  infer_instance

/-- Marking the lookup's three claims on the planes as added keeps the state's shape. -/
instance keeps_planesAdded (g : Model.Forest.Heard) : KeepsS (Model.Forest.planesAdded g) := by
  unfold Model.Forest.planesAdded
  infer_instance

/-- The lookup's test on the places of the padding keeps the state's shape. -/
instance keeps_paddingLaid (g : Model.Forest.Heard) (laid : Array ℕ) :
    KeepsS (Model.Forest.paddingLaid g laid) := by
  unfold Model.Forest.paddingLaid
  infer_instance

/-- A loop over an array, with the fact on its steps given by hand. -/
theorem kfa {γ σ : Type} {l : Array γ} {s : σ} {f : γ → σ → SubM (ForInStep σ)}
    (hf : ∀ x s, KeepsS (f x s)) : KeepsS (forIn l s f) := by
  rw [← Array.forIn_toList]
  exact kfl hf

/-- The two last steps of a loop's body. -/
theorem kpp {α β : Type} (a : α) (b : β) :
    KeepsS ((pure a : SubM α) >>= fun _ => (pure b : SubM β)) :=
  kb (keeps_pure _) fun _ => keeps_pure _

/-- The tie of one matrix. -/
instance keeps_linTie (tl : Model.HTailF2) (mu : ℕ) : KeepsS (tl.linTie mu) := by
  unfold Model.HTailF2.linTie
  dsimp only
  exact kb (keeps_get _) fun _ => kb (keeps_get _) fun _ => kb (keeps_ask _) fun _ =>
    kb (keeps_get _) fun _ => kb (keeps_get _) fun _ => keeps_t2Lin _ _

/-- One read. -/
instance keeps_linRead (tl : Model.HTailF2) (Fn : Model.HFun) (sg laid : ℕ) (sums : E) :
    KeepsS (tl.linRead Fn sg laid sums) := by
  unfold Model.HTailF2.linRead
  dsimp only
  refine kb (keeps_get _) fun _ => kb (keeps_ask _) fun _ => kb (keeps_ask _) fun _ =>
    kb (keeps_liftM _) fun _ => kb (keeps_get _) fun ⟨_, _⟩ => ?_
  exact kb (keeps_liftM _) fun _ => kb (keeps_get _) fun _ => kb (keeps_get _) fun _ =>
    keeps_t2Lin _ _

/-- The powers of the batching element and the sums over the matrix's columns. -/
instance keeps_weightsF (tl : Model.HTailF2) : KeepsS tl.weightsF := by
  unfold Model.HTailF2.weightsF
  exact kb (keeps_ask _) fun _ => keeps_get _

/-- The three claims on the planes. -/
instance keeps_linBits9 (tl : Model.HTailF2) : KeepsS tl.linBits9 := by
  unfold Model.HTailF2.linBits9
  dsimp only
  refine kb (keeps_get _) fun g => kb (keeps_pscRow _ _ _) fun ⟨_, _⟩ => ?_
  exact kb (keeps_t2Lin _ _) fun _ => kb (keeps_t2Lin _ _) fun _ => kb (keeps_t2Lin _ _) fun _ =>
    kb (keeps_planesAdded _) fun _ => keeps_pure _

/-- The claim on the key vectors. -/
instance keeps_linJoin9 (tl : Model.HTailF2) : KeepsS tl.linJoin9 := by
  unfold Model.HTailF2.linJoin9
  dsimp only
  refine kb (keeps_get _) fun g => kb (keeps_liftM _) fun _ =>
    kb (kfl fun q r => ?_) fun ⟨_, _, _, _, _⟩ => ?_
  · refine kb (kfa fun p r2 => ?_) fun ⟨_, _, _, _⟩ => kpp _ _
    refine kb (keeps_liftM _) fun _ => ki ?_ ?_
    · refine kb (keeps_pure _) fun _ => kb (kfl fun rr r3 => ?_) fun _ => kpp _ _
      exact kb (keeps_get _) fun _ => kpp _ _
    · refine kb (keeps_pure _) fun _ => kb (kfl fun rr r3 => ?_) fun _ => kpp _ _
      exact kb (keeps_get _) fun _ => kpp _ _
  · refine kb (kfl fun y r => kpp _ _) fun _ => ?_
    exact kb (keeps_liftM _) fun _ => kb (keeps_paddingLaid _ _) fun _ =>
      kb keeps_claims fun _ => kb (keeps_t2Lin _ _) fun _ => kb (keeps_joinAdded _) fun _ =>
        keeps_pure _

/-- The routine that adds the claims of the smallness test keeps the state's shape. -/
instance keeps_objectsF (tl : Model.HTailF2) (funs : Array Model.HFun) :
    KeepsS (tl.objectsF funs) := by
  unfold Model.HTailF2.objectsF
  dsimp only
  refine kb (keeps_liftM _) fun _ => kb (keeps_liftM _) fun _ => kb (keeps_ask _) fun _ =>
    kb (keeps_liftM _) fun _ => kb (keeps_get _) fun g => kb keeps_claims fun _ =>
    kb (keeps_objects _) fun _ => kb keeps_claims fun _ => kb (keeps_liftM _) fun _ =>
    kb keeps_claims fun _ => kb (keeps_linJoin9 _) fun tl1 => kb (keeps_linBits9 _) fun tl2 =>
    kb keeps_claims fun _ => kb (keeps_liftM _) fun _ => kb (keeps_weightsF _) fun tl3 =>
    kb (keeps_ask _) fun _ => kb (kfl fun mu r => ?_) fun ⟨_, _⟩ => ?_
  · exact kb keeps_claims fun _ => kb (keeps_linTie _ _) fun _ => kpp _ _
  · refine kb (kfl fun mu r => ?_) fun ⟨_, _⟩ => ?_
    · refine kb (kfl fun un r2 => ?_) fun ⟨_, _⟩ => kpp _ _
      refine kb (kfa fun Fn r3 => ki ?_ ?_) fun ⟨_, _⟩ => kpp _ _
      · refine kb (keeps_liftM _) fun _ => kb (keeps_liftM _) fun _ =>
          kb (kfl fun sg r4 => ?_) fun ⟨_, _⟩ => kpp _ _
        exact kb (keeps_get _) fun _ => kb (keeps_linRead _ _ _ _ _) fun _ => kpp _ _
      · exact kpp _ _
    · exact kb (keeps_liftM _) fun _ => kb (keeps_liftM _) fun _ => kb (keeps_get _) fun _ =>
        kb (keeps_get _) fun _ => kb (keeps_ask _) fun _ => kb (keeps_liftM _) fun _ =>
        kb (keeps_liftM _) fun _ => kb (keeps_liftM _) fun _ => kb (keeps_ask _) fun _ =>
        keeps_pure _

/-- The same in the words of Johnson/Road/HeadWalk.lean: the hypothesis of walk_states on the
routine of the smallness test holds. -/
theorem objectsF_keeps (tl : Model.HTailF2) (funs : Array Model.HFun) :
    Walk.Keeps (tl.objectsF funs) := (keeps_objectsF tl funs).keep

#print axioms keeps_t2Lin
#print axioms keeps_linJoin9
#print axioms keeps_linBits9
#print axioms keeps_linRead
#print axioms keeps_objectsF
#print axioms objectsF_keeps

end OnBytes.Road.Hd.Parts
