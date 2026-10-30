-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/TieThreeFour.lean: FOUR OF THE SIX DEBTS t3 | t4 THAT ARE LEFT OF THE
TIES OF A LINK's THREE PIECES AT THE TABLE (`TieRestR`, LinkTiedR.lean), AT THE COMPOSED MEANING
(`mgAll 𝔇 Mg₀`, Johnson/Desc/Sound/MgAll.lean) AND AT THE LAW's LETTERS AS THEY ARE CHOSEN: the
reader of the witness `rdC` (ClampPin.lean), the context `ctxPins` (PinsBack.lean), own := the
plan's group of the segment, the public sentence Rw := the composed meaning's own test `𝔇.rw m`.
t3: what the row opens, with what it reads, gives the kind's own relation behind; t4: the kind's own
relation in front gives what the row closes, with what it reads. Over
Johnson/Desc/Sound/Clamp/FormsClamp.lean (the sentences «the one sum is 0», in their two forms, at
`rdC` are the composed meaning's own at `seatTab`, under `InsideAt`). Definitions and theorems, each
ending in the field's own type.

What is said.
  `after_moves`, `after_at`: the function «what follows the batching» in the law's letters and in
    the composed meaning's is the link's own `runBehind`. `rwAt 𝔇 m`: the public sentence.
    `outs_mem`, `ctx_mem`: an item that a row opens, or reads, is among what `outsQ` names.
    `t3_batch`: **t3 at the batching's piece.** `t3_behind`, `t4_behind`: **both at the piece of the
    frame's sub-protocol behind it.** `t4_eq`: **t4 at the one equation's piece.**

Limits. PREMISES: what the table's rows at the three places open, close and read (closed facts on
the written list: not evaluated here); 𝔇.lk m is the link; `InsideAt` at the part of each state at
which a sentence is turned, asked only inside the conditions `onTR`: SHOWN AT NO STATE (its file
says so of itself); `PinAsks` for the pins' ride backward. NOT HERE: t4 at the batching's
piece (the runs' forms and the two worths) and t3 at the one equation's (the equation's row).
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedR
import Johnson.Desc.First.Link.Law.ClampPin
import Johnson.Desc.Sound.Clamp.FormsClamp
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers pinsOf)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

/-- «What follows the batching», in the law's letters, is the link's own runBehind. -/
theorem after_moves (α : Type) (L : Link S Claim) :
    K9L.afterOf ((moves₂ (α := α) L).map (·.move)) = L.runBehind := by
  funext s
  show (L.runBehind s).bind (K9L.afterOf []) = _
  cases L.runBehind s <;> rfl

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

/-- In the composed meaning's letters too. -/
theorem after_at (m : ℕ) (L : Link S Claim) (h : 𝔇.lk m = some L) : 𝔇.after m = L.runBehind := by
  funext s
  unfold MgData.after
  rw [h]

variable {F : Frame}

/-- The public sentence: the composed meaning's own test. -/
def rwAt (m : ℕ) : S × F.E.Str → Prop := fun a => 𝔇.rw m a.1 = true

theorem outs_mem (links : List ModelPart) (pl : List Place) (k : ℕ) (i : Item)
    (h : i ∈ (rowQ links pl k).outs) : outsQ links pl k i :=
  List.mem_append_left _ (List.mem_append_left _ h)

theorem ctx_mem (links : List ModelPart) (pl : List Place) (k : ℕ) (i : Item)
    (h : i ∈ (rowQ links pl k).ctx) : outsQ links pl k i :=
  List.mem_append_left _ (List.mem_append_right _ h)

variable (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (links : List ModelPart) (pl : List Place)
  (z : P) (Rz : ℕ → S × F.E.Str → Prop) (k m : ℕ)

local notation "Mg" => mgAll 𝔇 Mg₀
local notation "rdW" => rdC (Cells := CellsQ rows cols) (Tok := Tok) 𝔇.cs 𝔇.arr 𝔇.ms
local notation "own" => 𝔇.N.group m
local notation "onK" => onTR 𝔇.N (mgAll 𝔇 Mg₀) links pl (fun s : S => (z, s)) Rz

/-- The context, off what a row reads. -/
theorem ctx_of_outs (hctx : (rowQ links pl k).ctx = pinsOf m) (b : S × F.E.Str)
    (w : Wit (CellsQ rows cols) Tok MsgT)
    (h : relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w) :
    ctxPins 𝔇.N Mg z m b w :=
  (ctxPins_iff 𝔇.N Mg z m b w).2 fun i hi => h i (ctx_mem links pl k i (by rw [hctx]; exact hi))

/-- **t3 AT THE BATCHING's PIECE.** -/
theorem t3_batch {C : CK} (α : Type) (L : Link S Claim) (hL : 𝔇.lk m = some L)
    (houts : (rowQ links pl k).outs = [.totalB m]) (hctx : (rowQ links pl k).ctx = pinsOf m)
    (hin : ∀ b, onK (k + 1) b → ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a →
      InsideAt 𝔇.cs 𝔇.ms own a)
    (pb : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) :
    ∀ a τ b w, onK k a → pb.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relTotB α L own rdW (rwAt 𝔇 m) (ctxPins 𝔇.N Mg z m) b w := by
  intro a τ b w _ _ hb h
  have h1 : totalBQ (𝔇.after m) own b.1 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) ∧ 𝔇.rw m b.1 = true :=
    h (.totalB m) (outs_mem links pl k _ (by rw [houts]; exact List.mem_singleton.2 rfl))
  refine ⟨⟨?_, h1.2⟩, ctx_of_outs 𝔇 Mg₀ links pl z k m hctx b w h⟩
  rw [after_moves α L]
  rw [after_at 𝔇 m L hL] at h1
  exact (totalBQ_clamp 𝔇.cs 𝔇.arr 𝔇.ms own L.runBehind b.1 w (hin b hb)).2 h1.1

/-- **t3 AT THE PIECE OF THE FRAME's SUB-PROTOCOL BEHIND THE BATCHING.** -/
theorem t3_behind {C : CK} (houts : (rowQ links pl k).outs = [.total m])
    (hin : ∀ b, onK (k + 1) b → ∀ a, atS.get? b.1 = some a → InsideAt 𝔇.cs 𝔇.ms own a)
    (pq : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) :
    ∀ a τ b w, onK k a → pq.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relTot own rdW (rwAt 𝔇 m) b w := by
  intro a τ b w _ _ hb h
  have h1 : totalQ own b.1 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) ∧ 𝔇.rw m b.1 = true :=
    h (.total m) (outs_mem links pl k _ (by rw [houts]; exact List.mem_singleton.2 rfl))
  exact ⟨(totalQ_clamp 𝔇.cs 𝔇.arr 𝔇.ms own b.1 w (hin b hb)).2 h1.1, h1.2⟩

/-- **t4 AT THAT PIECE.** -/
theorem t4_behind {C : CK} (α : Type) (L : Link S Claim) (hL : 𝔇.lk m = some L)
    (hins : (rowQ links pl k).ins = [.totalB m]) (hctx : (rowQ links pl k).ctx = pinsOf m)
    (hin : ∀ a, onK k a → ∀ s' x, L.runBehind a.1 = .ok s' → atS.get? s' = some x →
      InsideAt 𝔇.cs 𝔇.ms own x)
    (pq : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT)) (hext : ∀ a τ w, pq.ext a τ w = w)
    (hpin : ∀ a τ b, onK k a → pq.ior.red.out a τ = some b →
      PinAsks 𝔇.cs 𝔇.smp 𝔇.N z m pq.base a.1 b.1) :
    ∀ a τ b w, onK k a → pq.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relTotB' α L own rdW (rwAt 𝔇 m) a (pq.ext a τ w) →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (insQ links pl k) a (pq.ext a τ w) := by
  intro a τ b w ha hout _ h hR
  rw [hext] at hR ⊢
  refine relAt_ins 𝔇.N Mg links pl _ k a w ha.1.2 (fun i hi => ?_) fun i hi => ?_
  · rw [hins] at hi
    obtain rfl := List.mem_singleton.1 hi
    show totalBQ (𝔇.after m) own a.1 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) ∧ 𝔇.rw m a.1 = true
    rw [after_at 𝔇 m L hL]
    have h1 := hR.1
    rw [after_moves α L] at h1
    exact ⟨(totalBQ_clamp 𝔇.cs 𝔇.arr 𝔇.ms own L.runBehind a.1 w (hin a ha)).1 h1, hR.2⟩
  · rw [hctx] at hi
    exact (ctxPins_iff 𝔇.N Mg z m a w).1
      (hc_at 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms 𝔇.N Mg (mgAll_pin 𝔇 Mg₀) z m pq (onK k) hpin a τ b w
        ha hout (ctx_of_outs 𝔇 Mg₀ links pl z k m hctx b w h)) i hi

/-- **t4 AT THE ONE EQUATION's PIECE.** -/
theorem t4_eq {C : CK} (hins : (rowQ links pl k).ins = [.total m])
    (hctx : (rowQ links pl k).ctx = [])
    (hin : ∀ a, onK k a → ∀ x, atS.get? a.1 = some x → InsideAt 𝔇.cs 𝔇.ms own x)
    (pe : Piece C F S Claim (Wit (CellsQ rows cols) Tok MsgT))
    (hext : ∀ a τ w, pe.ext a τ w = w) :
    ∀ a τ b w, onK k a → pe.ior.red.out a τ = some b → onK (k + 1) b →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (outsQ links pl k) b w →
      relTot own rdW (rwAt 𝔇 m) a (pe.ext a τ w) →
      relAt (meansQ 𝔇.N Mg (fun s : S => (z, s))) (insQ links pl k) a (pe.ext a τ w) := by
  intro a τ b w ha _ _ _ hR
  rw [hext] at hR ⊢
  refine relAt_ins 𝔇.N Mg links pl _ k a w ha.1.2 (fun i hi => ?_) fun i hi => ?_
  · rw [hins] at hi
    obtain rfl := List.mem_singleton.1 hi
    show totalQ own a.1 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) ∧ 𝔇.rw m a.1 = true
    exact ⟨(totalQ_clamp 𝔇.cs 𝔇.arr 𝔇.ms own a.1 w (hin a ha)).1 hR.1, hR.2⟩
  · rw [hctx] at hi
    exact nomatch hi

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.after_moves
#print axioms VerifiableInference.Desc.LinkJoin.t3_batch
#print axioms VerifiableInference.Desc.LinkJoin.t3_behind
#print axioms VerifiableInference.Desc.LinkJoin.t4_behind
#print axioms VerifiableInference.Desc.LinkJoin.t4_eq
