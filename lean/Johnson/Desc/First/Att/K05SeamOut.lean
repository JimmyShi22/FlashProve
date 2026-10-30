-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SeamOut.lean: what a yes of ANY piece of the rule of composition holds
(Johnson/Desc/Sound/ChainRule.lean: Piece, Piece.ior), for a stretch of any number of written
rounds. General in the block: no kind occurs here.

Main names:
  `chainAt_single`: a chain of one block: its yes is the block's yes as a step on all the rounds
    and all the columns that the view shows.
  `piece_out_step`: where a piece behind whose stretch no round is put puts out: the stretch's
    tests of work passed; the block said yes as a step on the view of the written transcript; the
    oracles behind are the stage's.
  `collect_okE`, `rvT_okE`: every element that the view of a written transcript shows as drawn has
    its three words below the prime: by the type of a written round's typed values.
  `roundsFit_noDigest`: the fit does not read the sealed digest.
  `SameBelow`, `piece_same_below`: what a piece leaves of the oracles in front: the stored table,
    and every column of a tree whose number is below the piece's base, read through the frame's own
    list (posL).

Limits. Laws on the frame: they hold of every block, also of one that says yes to all or no to all:
they claim nothing of what a block decides. `roundsFit_noDigest` is a twin of `noDigest_fit`
(Johnson/Desc/First/Tape/TapeFits.lean), typed here so that that file's imports are not drawn in.
K8's `chainAt_one` and `piece_out` (Johnson/Desc/First/K8/LawPiece.lean)
are the case of one round.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.ShownRounds
import Johnson.Desc.Sound.StageCut
import OnBytes.Slice.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block OpenedColumn chainAt foldBlocks roundsFit drawsMarkedNonzeroHaveNonzeroWords noDigest)
open VerifiableInference.Desc.Sound (Frame Piece foldRun stg sLeft_at sCol_eq)
open _root_.Run (ckP)
open _root_.Run.PQ (CK)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- A chain of one block: its yes is the block's yes as a step, on all the rounds and all the
columns. -/
theorem chainAt_single (name : String) (ft : Nat) (b : Block S Cl) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (h : chainAt name ft [b] s ⟨rs, cols⟩ = .ok s') :
    ∃ k, b.step ft s rs cols = .ok (s', k) := by
  unfold chainAt at h
  rw [if_neg (by simp)] at h
  cases hf : foldBlocks ft [b] s rs cols with
  | error e =>
    simp only [hf] at h
    cases h
  | ok x =>
    obtain ⟨t, rr, cc⟩ := x
    simp only [hf] at h
    cases rr with
    | cons _ _ => cases h
    | nil =>
      cases cc with
      | cons _ _ => cases h
      | nil =>
        obtain rfl : t = s' := Except.ok.inj h
        simp only [foldBlocks] at hf
        split at hf
        · cases hf
        · split at hf
          · cases hf
          · rename_i hl s1 k hs
            have e := Except.ok.inj hf
            have e1 : s1 = t := congrArg Prod.fst e
            have e2 : (rs.splitAt b.rounds.length).2 = [] := congrArg (fun x => x.2.1) e
            rw [List.splitAt_eq] at e2 hs
            have e3 : rs.take b.rounds.length = rs :=
              List.take_of_length_le (List.drop_eq_nil_iff.1 e2)
            simp only [e3] at hs
            exact ⟨k, e1 ▸ hs⟩

/-- **Where a piece puts out.** -/
theorem piece_out_step (P : Piece C F S Cl W) (hb : P.back = []) (a b : S × F.E.Str)
    (τ : Iop.Tr (uLT C P.ds)) (h : P.ior.red.out a τ = some b) :
    passT C P.ds (rhoT C P.ds τ) = true ∧
      (∃ cols k, P.b.step F.ft a.1 (rvT C P.ds τ) cols = .ok (b.1, k)) ∧
      b.2 = P.ior.imp a.2 τ := by
  have h' : (P.ior.out a.1 a.2 τ).map (fun xo => (xo, P.ior.imp a.2 τ)) = some b := h
  cases ho : P.ior.out a.1 a.2 τ with
  | none => rw [ho] at h'; cases h'
  | some st =>
    rw [ho] at h'
    obtain rfl : (st, P.ior.imp a.2 τ) = b := Option.some.inj h'
    have ho' : (if sTests C P.stage a.2 τ then P.run a.1 (sView C P.stage a.2 τ) else none) =
        some st := ho
    by_cases ht : sTests C P.stage a.2 τ = true
    · rw [if_pos ht] at ho'
      have hp : passT C P.ds (rhoT C P.ds τ) = true := by
        simp only [sTests, Bool.and_eq_true] at ht
        exact ht.1.1
      have hr : (chainAt P.b.name F.ft [P.b] a.1
          ⟨rvT C P.ds τ ++ P.back, (sView C P.stage a.2 τ).opened⟩).toOption = some st := ho'
      rw [hb, List.append_nil] at hr
      cases hc : chainAt P.b.name F.ft [P.b] a.1
          ⟨rvT C P.ds τ, (sView C P.stage a.2 τ).opened⟩ with
      | error x => rw [hc] at hr; cases hr
      | ok s1 =>
        rw [hc] at hr
        obtain rfl : s1 = st := Option.some.inj hr
        obtain ⟨k, hk⟩ := chainAt_single _ _ _ _ _ _ _ hc
        exact ⟨hp, ⟨_, k, hk⟩, rfl⟩
    · rw [if_neg ht] at ho'
      cases ho'

/-- The elements in the format's record of typed values have their words below the prime. -/
theorem collect_okE : ∀ (ds : List Fmt.Draw) (v : _root_.Run.Vals .two ds),
    ∀ x ∈ (Fmt.collect (_root_.Run.outAll .two ds v)).elems, Fmt.Fld.two.okE x = true
  | [], _, _, h => by cases h
  | .elem :: ds, v, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact OnBytes.Slice.okE_toU3 v.1
    · exact collect_okE ds v.2 x h
  | .elemNZ :: ds, v, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact OnBytes.Slice.okE_toU3 v.1.1
    · exact collect_okE ds v.2 x h
  | .pos _ :: ds, v, x, h => collect_okE ds v.2 x h
  | .trits _ :: ds, v, x, h => collect_okE ds v.2 x h
  | .sealed :: ds, v, x, h => collect_okE ds v.2 x h

/-- **Every element that the view of a written transcript shows as drawn is below the prime.** -/
theorem rvSL_okE : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD)
    (τ : Iop.Tr (TypedOracleCompiler.Run.PQ.uL (ckP .two) ds)),
    ∀ r ∈ TypedOracleCompiler.Run.PQ.rvSL (ckP .two) ds τ, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true
  | [], _, _, h, _, _ => by cases h
  | d :: ds, (_, c, τ), r, h, x, hx => by
    rcases List.mem_cons.1 h with rfl | h
    · exact collect_okE _ _ x hx
    · exact rvSL_okE ds τ r h x hx

theorem rvT_okE (ds : List RDT) (τ : Iop.Tr (uLT (ckP .two) ds)) :
    ∀ r ∈ rvT (ckP .two) ds τ, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true :=
  rvSL_okE (toRDs ds) τ

/-- The fit does not read the sealed digest. -/
theorem roundsFit_noDigest : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView),
    roundsFit ds (rs.map noDigest) = roundsFit ds rs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | d :: ds, r :: rs => by
    simp only [List.map_cons, roundsFit, drawsMarkedNonzeroHaveNonzeroWords, noDigest, roundsFit_noDigest ds rs]

/-- The oracles y' hold what y holds: of the stored table; and of every tree whose number is below
base, read through the frame's own list. -/
def SameBelow (F : Frame) (base : ℕ) (y y' : F.E.Str) : Prop :=
  y'.1 = y.1 ∧ ∀ j x, j < base → (posL F.all j x).map y'.2 = (posL F.all j x).map y.2

/-- **What a piece leaves of the oracles in front.** -/
theorem piece_same_below (P : Piece C F S Cl W) (a b : S × F.E.Str) (τ : Iop.Tr (uLT C P.ds))
    (h : P.ior.red.out a τ = some b) : SameBelow F P.base a.2 b.2 := by
  have h' : (P.ior.out a.1 a.2 τ).map (fun xo => (xo, P.ior.imp a.2 τ)) = some b := h
  cases ho : P.ior.out a.1 a.2 τ with
  | none => rw [ho] at h'; cases h'
  | some st =>
    rw [ho] at h'
    obtain rfl : (st, P.ior.imp a.2 τ) = b := Option.some.inj h'
    refine ⟨rfl, fun j x hj => ?_⟩
    cases hp : posL F.all j x with
    | none => rfl
    | some q =>
      show some (sLeft C (stg F P.base P.ds) a.2 τ q) = some (a.2.2 q)
      rw [sLeft_at C F P.ds P.base a.2 τ j x q hp, sCol_eq, if_pos hj, hp]
      rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.chainAt_single
#print axioms VerifiableInference.Desc.First.Att.P.piece_out_step
#print axioms VerifiableInference.Desc.First.Att.P.rvT_okE
#print axioms VerifiableInference.Desc.First.Att.P.roundsFit_noDigest
#print axioms VerifiableInference.Desc.First.Att.P.piece_same_below
