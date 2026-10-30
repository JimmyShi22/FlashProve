-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotExchangeLayer.lean: ExchangeS AT THE LAYERS OF ROWS OF THE KEY FILE's TWO LOOKUPS, numbers 5 and 11 of the first chain
("look0.3.layer", "look1.3.layer": the table's «THE EXCHANGE»), in scope: at the thread laid₁ (E2E/KeyRest.lean) at every
filling whose reading takes two machine elements for the same where they read alike, and so at the honest prover's thread Th
(E2E/FirstHSeat.lean) AT EVERY BOOK, K, f, Q, INPUT AND LETTER Said.

  room_sourced, answers_sourced, two_sourced, looks_lof, flat_len   in scope: the public facts that the walk asks
  open_layer      the three sentences are open in front of each layer
  anew_at         at lookup l: rows l and kclaims l hold behind the layer's step
  exchangeS_layer   ExchangeS at 5, 11 of laid₁
  LotExchangeLayer, lotExchangeLayer   the same at Th

By what. What the row owes again (pinT, pin 0, pin 1): exchangeS_of_anew₁ (E2E/KeyRowsLater.lean). What it makes anew:
layer_forward (E2E/LotLayerForward.lean), at the witness that the thread has; its premises on the record in front (the table of
homes, the statement's tables, what was heard) come off the thread's own clause «the state is what the fold returns», by
rec_of_fold (E2E/LotLayerWalk.lean); the three sentences in front are the thread's own open items.

Limits. As every debt it speaks of a stand in front: none is shown; where the three sentences fail there is no stand. It moves
truth from three sentences to two: that the three hold behind the lookup's step is ExchangeS at 4 and 10. The member has no
round: no challenge is drawn at it. In scope, at the written sizes. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotLayerForward
import E2E.LotLayerWalk
import E2E.KeyRowsLater
import E2E.KeyKeepsLayer
import E2E.KeyPlacesNamed
import E2E.FirstHSeat
import Johnson.Desc.First.Look.KeyLaw.TakesFull
import Johnson.Desc.First.Look.KeyLaw.HeldFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block OpenedColumn foldBlocks claimsIn)
open VerifiableInference.Desc.K3 (lookupKind)
open VerifiableInference.Desc.K3.KeyLaw (RoomFor room_full held_full_two)
open VerifiableInference.Desc.Key (Xi FirstState Claim KItem Source LaterPlaces lookupsOf lookupSeat
  lookupPlace layer caller start₁)
open Johnson.RunOne.Sound (FK rowsOf)
open Johnson.RunOne.KeyRows1 (ReadsL)
open Johnson.RunOne.Law.LinkAtPlan (Lof layout_of_admitted)
open Johnson.RunOne.Law.LinkAtCut (fk_admitted fk_messageId)
open AtPublicFiles.KeyThread
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (six_sourced)
open AtPublicFiles.KeyBook (places_named fullFirst)
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

section
variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

theorem room_sourced (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    RoomFor Xs.Y.k.oneTime.ranges (Wf.matrixOf Xs.Y.k.oneTime.lin) Xs.Y.k.oneTime.codes
      Xs.Y.k.oneTime.indexMasks.shape := by
  have h6 := six_sourced hs scope
  rw [(h6.ranges : Xs.Y.k.oneTime.ranges = keyFull.ranges.x),
    (h6.lin : Xs.Y.k.oneTime.lin = keyFull.once.shape),
    (h6.codes : Xs.Y.k.oneTime.codes = keyFull.codes),
    (h6.indexMasks : Xs.Y.k.oneTime.indexMasks = keyFull.once.input)]
  exact room_full

theorem answers_full : keyFull.ranges.x.message.shape.answers ≠ 0 := by decide +kernel

theorem answers_sourced (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    Xs.Y.k.oneTime.ranges.message.shape.answers ≠ 0 := by
  rw [((six_sourced hs scope).ranges : Xs.Y.k.oneTime.ranges = keyFull.ranges.x)]
  exact answers_full

theorem two_sourced (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    Xs.Y.k.oneTime.ranges.lookups.length = 2 := by
  rw [((six_sourced hs scope).ranges : Xs.Y.k.oneTime.ranges = keyFull.ranges.x)]
  exact held_full_two

/-- The two lookups' public records, by the plan's lookups. -/
theorem looks_lof {one : Params.OneTime} (hn : one.ranges.lookups.length = 2) :
    lookupsOf one = [Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin) (Lof one 0),
      Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin) (Lof one 1)] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hn
  show one.ranges.lookups.map (Wf.lookupOf one.ranges.messageId (Wf.matrixOf one.lin)) = _
  unfold Lof
  rw [hab]
  rfl

theorem flat_len (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (FK Xs N Pl).first.blocksInOrder.length = 19 := by
  have hr := congrArg List.length (places_named scope hs.named).1
  unfold rowsOf at hr
  rw [List.length_map] at hr
  exact hr

end

/-- The three sentences are open in front of each layer. -/
theorem open_layer : ∀ l, l < 2 →
    KItem.forms l "objects" ∈ fwdOpen (start₁ 2) rowsFirst (2 + (6 * l + 3)) ∧
      KItem.worth l "planes" ∈ fwdOpen (start₁ 2) rowsFirst (2 + (6 * l + 3)) ∧
      KItem.worth l "keys" ∈ fwdOpen (start₁ 2) rowsFirst (2 + (6 * l + 3)) := by
  decide

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (L : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tb₁ : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}

/-- **At lookup l: what the layer's row makes anew holds behind its step.** -/
theorem anew_at (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hsame : L.R.same = fun a b => readE a = readE b) (l : Nat) (hl : l < 2)
    (hdec : ∀ blk, (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[2 + (6 * l + 3)]? = some blk →
      ∀ s rs gs, blk.decide s rs gs =
        (layer (one₀ Xs) Xs.set l (Wf.lookupOf (one₀ Xs).ranges.messageId
            (Wf.matrixOf (one₀ Xs).lin) (Lof (one₀ Xs) l))
          (claimsIn [caller (one₀ Xs) l (Wf.lookupOf (one₀ Xs).ranges.messageId
              (Wf.matrixOf (one₀ Xs).lin) (Lof (one₀ Xs) l)),
            lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace Xs.set l
                  (Wf.lookupOf (one₀ Xs).ranges.messageId (Wf.matrixOf (one₀ Xs).lin)
                    (Lof (one₀ Xs) l)))]
            [(1, "objects"), (1, "planes"), (1, "guests")])).decide s rs gs) :
    ∀ blk, (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).bs[2 + (6 * l + 3)]? = some blk →
      ∀ k s m E ds y cols s', Thr (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) (2 + (6 * l + 3)) k s m E →
      drawsFit blk.rounds ds = true →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Stepped blk k s m E ds y cols s' →
      (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).Items [.rows l, .kclaims l] k s' y.2 (E.add y.1) := by
  intro blk hblk k s m E ds y cols s' hT hd hS
  have hp : (FK Xs N Pl).planOk = true := hs.named.plan
  have hn := two_sourced hs scope
  have hW := fk_admitted Xs N Pl hp
  -- the record's half in front, off the clause «the state is what the fold returns»
  obtain ⟨-, -, -, -, s₀, cols₀, hbeg, -, hfold⟩ := hT.2.2.2.2.1
  have hb₀ : s₀ = (D Xs N Pl).start₁ m.st.input.x := hbeg
  subst hb₀
  have hrec := rec_of_fold (X := Xs) (N := N) (P := Pl) 0 hp (room_sourced hs scope)
    (answers_sourced hs scope) (2 + (6 * l + 3)) (by rw [hn]; omega)
    (by rw [flat_len hs scope]; omega) m.seen cols₀ s [] [] hfold
  obtain ⟨oL, kL, idxN, hInv, hH⟩ := rec_layer hrec
  -- the layer's yes
  obtain ⟨-, gs, hdc⟩ := VerifiableInference.Desc.K1.step_ok _ blk s s' _ _ _ hS.2
  rw [hdec blk hblk] at hdc
  -- the play
  have hM := hS.1
  unfold Thread.Moved at hM
  obtain ⟨⟨ll, -, hy⟩, -⟩ := hM
  obtain ⟨o1, o2, o3⟩ := open_layer l hl
  intro ds' i hi
  have f1 := hT.2.2.2.1 (ds ++ ds') (KItem.forms l "objects") o1
  have f2 := hT.2.2.2.1 (ds ++ ds') (KItem.worth l "planes") o2
  have f3 := hT.2.2.2.1 (ds ++ ds') (KItem.worth l "keys") o3
  have hF := layer_forward (X := Xs) (R := L.R) hsame hW (fk_messageId Xs N Pl hp)
    (layout_of_admitted hW) (i := l) (by rw [hn]; exact hl) hInv hH hdc _
    ((laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).strs E) ((laid₁ Xs N Pl L w₀ rc x hs₁ tb₁).strs (E.add y.1))
    _ f1 f2 f3
  rw [seat_behind (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) hT.2.1 hy, (play_mid _ _ _ _ _ hy).1,
    play_heard _ _ _ _ _ hy, List.append_assoc]
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hF.1
  · obtain rfl := List.mem_singleton.1 hi
    exact hF.2

/-- **ExchangeS at the two layers.** -/
theorem exchangeS_layer (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hG : ReadsL L.base.h₁) (hsame : L.R.same = fun a b => readE a = readE b)
    (S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) : ∀ b ∈ [5, 11],
    ExchangeS (laid₁ Xs N Pl L w₀ rc x hs₁ tb₁) S₁ b := by
  have hlk := looks_lof (two_sourced hs scope)
  intro b hb
  refine exchangeS_of_anew₁ Xs N Pl L w₀ rc x hs scope hG S₁ b
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢; omega) ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact fun blk hblk k s m E ds y cols s' hT =>
      anew_at Xs N Pl L w₀ rc x hs scope hsame 0 (by decide)
        (fun blk hblk s rs gs => dec_layer0 _ _ _ _ _ _ _ hlk blk hblk s rs gs) blk hblk k s m E ds
        y cols s' hT.1
  · exact fun blk hblk k s m E ds y cols s' hT =>
      anew_at Xs N Pl L w₀ rc x hs scope hsame 1 (by decide)
        (fun blk hblk s rs gs => dec_layer1 _ _ _ _ _ _ _ hlk blk hblk s rs gs) blk hblk k s m E ds
        y cols s' hT.1

end

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi)

/-- **The lot: ExchangeS at 5 and 11 of the honest prover's first thread.** -/
def LotExchangeLayer : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true →
    ∀ (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop), ∀ b ∈ [5, 11],
      ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b

theorem lotExchangeLayer : LotExchangeLayer Xs N Pl K f Q w₀ rc x := fun hs scope Said =>
  exchangeS_layer Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hs scope
    (Johnson.RunOne.KeyRows1.readsL_h₁ (baseH (one₀ Xs)) fun _ _ _ _ => rfl) rfl Said

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.room_sourced
#print axioms AtPublicFiles.FirstH.Lots.answers_sourced
#print axioms AtPublicFiles.FirstH.Lots.two_sourced
#print axioms AtPublicFiles.FirstH.Lots.looks_lof
#print axioms AtPublicFiles.FirstH.Lots.flat_len
#print axioms AtPublicFiles.FirstH.Lots.open_layer
#print axioms AtPublicFiles.FirstH.Lots.anew_at
#print axioms AtPublicFiles.FirstH.Lots.exchangeS_layer
#print axioms AtPublicFiles.FirstH.Lots.lotExchangeLayer
