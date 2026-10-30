-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/GroupsFull.lean: THE COPY's FILE AT ITS WRITTEN LETTERS, THE FULL SIZE: THE
GROUPS THAT Block.step DEALS THE PROXIMITY TEST's STAGES, READ BY THE FRAME's LOOK-UP (lookV,
Johnson/Prover/Link/ChainDefs.lean) AT THE STRATEGY linkNext, ARE bodyAll's OWN GROUPS. A
definition, statements and proofs.

  seatsB        a closed test, with code: along the stages the plan's lists, the rounds at which the
                switches send and the stages' depths are those of written rows
  seats_of_B    that test and the look-up at each written row give Seats (BodyGroups.lean)
  fr_seatsB     the test at the full size, by the kernel's evaluation: the body begins at round 6
  frOwn_small, fr_rounds41   the five own trees' numbers are below 2 ^ 16, their rounds below 41; 41
                rounds
  look_full     under each own tree's number the look-up finds the column that stands in linkAll's
                list at the round that sends that tree
  groups_full   so groups_body's equation (BodyGroups.lean) at these letters: A MEMBER OF Looked

fr_seatsB, frOwn_small and fr_rounds41 stand under "set_option maxRecDepth 100000 in", as the
library's own closed facts at these letters do (Johnson/Desc/K15/TypedV.lean): a limit of
elaboration is raised; the kernel checks the term.

By: groups_body, looked_of_tr (BodyGroups.lean); fr_dealt, fr_lists, fr_depths, fr_hk, fr_seatOf,
fr_seatTree (ChainSeats.lean); look_tree (LinkLook.lean); linkAll_tr (LinkCausal.lean);
linkNext_wide (LinkAtFull.lean); length_drawnSL (LinkFrameView.lean).

Limits. The full size alone. Nothing on what a stage decides. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.BodyGroups
import Johnson.Prover.Link.ChainSeats
import Johnson.Prover.Link.LinkAtFull
import Johnson.Prover.Link.LinkFrameView

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12 Desc.K15
open VerifiableInference.Desc.Plain.One (readG)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open OnBytes.Flat (dsFull)
open _root_.Run (ckP)
open _root_.Run.PQ (SgX)
open TypedOracleCompiler.Run.PQ (drawnSL uL)
open _root_.Iop (twoExternalStrings Rho)

/-- **A closed test, with code**: along the stages: the next of the plan's lists names ONE tree;
that tree's number, the round at which the switch into the next stage sends ("SEND seed": the place
b + (1 + kk) where the stage cur begins at b) and the next stage's depth are those of the next of
the written rows (number, round, depth, width). A row's width and the named tree's are not read. -/
def seatsB : ℕ → Fmt.M1.Stage → List Fmt.M1.Stage → List (List Told) → List (ℕ × ℕ × ℕ × ℕ) → Bool
  | _, _, [], _, _ => true
  | b, cur, next :: rest, [o'] :: Ls', q :: own =>
    (o'.1.tree - 0 == q.1) && (o'.1.a == next.C.a) && (q.2.2.1 == next.C.a) &&
      (q.2.1 == b + (1 + ((sgOf cur).h + (sgOf cur).g))) &&
      seatsB (b + (((sgOf cur).h + (sgOf cur).g) + 3)) next rest Ls' own
  | _, _, _ :: _, _, _ => false

/-- The closed test and the look-up at each written row give Seats. -/
theorem seats_of_B (L : ℕ → ℕ → Option (List UInt64)) (TR : List (ℕ → List UInt64)) :
    ∀ (b : ℕ) (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Ls : List (List Told))
      (own : List (ℕ × ℕ × ℕ × ℕ)), seatsB b cur rest Ls own = true →
      (∀ q ∈ own, ∀ x, x < 2 ^ q.2.2.1 → L q.1 x = some ((TR[q.2.1]?).getD (fun _ => []) x)) →
      Seats L TR b cur rest Ls
  | _, _, [], _, _, _, _ => trivial
  | b, cur, next :: rest, [o'] :: Ls', q :: own, h, hL => by
    simp only [seatsB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    refine ⟨o', Ls', rfl, h2, fun x hx => ?_,
      seats_of_B L TR _ next rest Ls' own h5 fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')⟩
    rw [h1, ← h4]
    exact hL q List.mem_cons_self x (by rw [h3]; exact hx)
  | _, _, _ :: _, [], _, h, _ => by simp [seatsB] at h
  | _, _, _ :: _, [] :: _, _, h, _ => by simp [seatsB] at h
  | _, _, _ :: _, (_ :: _ :: _) :: _, _, h, _ => by simp [seatsB] at h
  | _, _, _ :: _, [_] :: _, [], h, _ => by simp [seatsB] at h

set_option maxRecDepth 100000 in
/-- The closed test at the full size. -/
theorem fr_seatsB (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of frP).nums.stages = first :: rest) :
    seatsB 6 first rest (listsOf (p12Of frP).nums).tail frOwn.tail = true := by
  have h : (match (p12Of frP).nums.stages with
    | f :: r => seatsB 6 f r (listsOf (p12Of frP).nums).tail frOwn.tail
    | [] => false) = true := by decide +kernel
  rw [hs] at h
  exact h

set_option maxRecDepth 100000 in
theorem frOwn_small : ∀ q ∈ frOwn, q.1 < 2 ^ 16 ∧ q.2.1 < 41 := by decide +kernel

set_option maxRecDepth 100000 in
theorem fr_rounds41 : dsFull.length = 41 := by decide +kernel

/-- **At the written letters, the full size: the look-up under each own tree's number.** -/
theorem look_full (t : ℕ) (X : LIn frS) (C : LCoins) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (ρ : Rho (uL (ckP .two) dsFull)) (q : ℕ × ℕ × ℕ × ℕ) (hq : q ∈ frOwn) (x : ℕ)
    (hx : x < 2 ^ q.2.2.1) :
    lookV dsFull frS.P.T.a (linkNext frP frS t X C) y (drawnSL (ckP .two) dsFull ρ) q.1 x =
      some ((((linkAll frP frS t X C (drawsOf (drawnSL (ckP .two) dsFull ρ))).tr[q.2.1]?).getD
        fun _ => []) x) := by
  obtain ⟨d, hd, ht⟩ := fr_seatTree q hq
  exact look_tree frP frS t X C dsFull frS.P.T.a y _ q.1 q.2.1 x d _ (frOwn_small q hq).1
    (fr_seatOf q hq) hd ht hx (by rw [length_drawnSL, fr_rounds41]; exact (frOwn_small q hq).2)
    (linkNext_wide t X C q.2.1 0 d _ hd ht _ x)

/-- **At the written letters, the full size: the groups that the stages are dealt.** -/
theorem groups_full (t : ℕ) (X : LIn frS) (C : LCoins) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (ρ : Rho (uL (ckP .two) dsFull)) (first : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : (p12Of frP).nums.stages = first :: rest) :
    (groupsOf 0 (((laidOf (p12Of frP)).drop 1).map (·.1))
        ((bodyAll (p12Of frP) C.body rest 0 first ((laidOf (p12Of frP)).drop 1) 6
          (lT frP frS t X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
          (lPS frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
          (lCol frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
          (drawsOf (drawnSL (ckP .two) dsFull ρ))).rs.map (·.drawn))).map
      (readG (lookV dsFull frS.P.T.a (linkNext frP frS t X C) y (drawnSL (ckP .two) dsFull ρ))) =
    (bodyAll (p12Of frP) C.body rest 0 first ((laidOf (p12Of frP)).drop 1) 6
      (lT frP frS t X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (lPS frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (lCol frP frS X C (drawsOf (drawnSL (ckP .two) dsFull ρ)))
      (drawsOf (drawnSL (ckP .two) dsFull ρ))).gs := by
  have hTR := linkAll_tr frP frS t X C (drawsOf (drawnSL (ckP .two) dsFull ρ)) first rest hs
  have e : listsOf (p12Of frP).nums =
      [((⟨24, 645, false, 0⟩ : Fmt.Shape), Fmt.TreeSource.own 0)] ::
        (listsOf (p12Of frP).nums).tail := by
    rw [fr_lists]
    rfl
  have ha : first.C.a = 24 := by
    have := fr_depths
    rw [hs] at this
    exact (List.cons.inj this).1
  have hD := fr_dealt first rest hs
  refine groups_body _ (p12Of frP) C.body _ rest 0 first _ 6 _ _ _ _ hD
    (fun s hm => fr_hk s (by rw [hs]; exact hm)) ?_
  rw [e]
  refine looked_of_tr _ (p12Of frP) C.body _
    (linkAll frP frS t X C (drawsOf (drawnSL (ckP .two) dsFull ρ))).tr rest 0 first _ 6 _ _ _ 6 _ _
    (fun i => ?_) ha.symm (fun x hx => ?_)
    (seats_of_B _ _ 6 first rest _ _ (fr_seatsB first rest hs) fun q hq x hx =>
      look_full t X C y ρ q (List.mem_of_mem_tail hq) x hx)
  · rw [hTR, List.getElem?_append_right (by simp)]
    simp
  · have := look_full t X C y ρ (0, 1, 24, 645) (by simp [frOwn]) x (by rw [ha] at hx; exact hx)
    rw [hTR] at this
    exact this

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.seats_of_B
#print axioms Johnson.Prover.Link.fr_seatsB
#print axioms Johnson.Prover.Link.frOwn_small
#print axioms Johnson.Prover.Link.fr_rounds41
#print axioms Johnson.Prover.Link.look_full
#print axioms Johnson.Prover.Link.groups_full
