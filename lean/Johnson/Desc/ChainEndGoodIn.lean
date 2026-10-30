-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ChainEndGoodIn.lean: what the rule of composition for one chain asks of each block
(Piece.GoodIn, Johnson/Desc/Sound/GoodIn.lean), for the chain's last block: at any errors, so also
at errors that are all 0. Theorems.

  single_decide      a chain's decision over one block that says yes rests on a yes of that block's
                     decide, at the same record.
  toOption_some      a value read off a yes.
  Piece.out_of_decide   NO KIND NAMED: where a piece's reduction puts out a statement, its oracles
                     are those that the stretch leaves, and its record is one that the block's
                     decide returns at the record in front.
  goodIn_of_sure     NO KIND NAMED: a piece that meets, at every transcript, what the prover must
                     lose towards has GoodIn at any errors.
  end_goodIn         **the end**: a piece whose block says yes just where the clauses ask hold, and
                     hands the record on: from (on, R) to (on', R'), where on and the clauses give
                     on' at the same record with the oracles left, and a witness behind gives one in
                     front.
  chainEnd_goodIn    the same at the text of the chain's end itself, with the promise "on, and every
                     clause holds" and one relation in front and behind.
What is not claimed. THE ORACLES THAT THE STRETCH LEAVES ARE NOT SHOWN TO BE THE ORACLES IN FRONT:
the two premises speak of the oracles left. A block that refuses all has GoodIn too: it is the other
half of the end's law, that it says yes wherever its clauses hold, that such a block fails
(Johnson/Desc/ChainEndExact.lean). Nothing on an end that is lifted. Nothing on soundness of the
protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.Sound.GoodIn
import Johnson.Desc.ChainEndExact
import Johnson.Desc.FoldKeeps
import Iop.Compose

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- A chain's decision over one block rests on that block's decide. -/
theorem single_decide (name : String) (ft : Nat) (b : Block S Cl) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft [b] s v = .ok s') : ∃ rs gs, b.decide s rs gs = .ok s' := by
  have hf := Keeps.chainAt_fold name ft [b] s s' v h
  simp only [foldBlocks] at hf
  split at hf
  · cases hf
  · split at hf
    · cases hf
    · rename_i t k hs
      simp only [Except.ok.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, -, -⟩ := hf
      obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft b s _ _ _ k hs
      exact ⟨rs', gs', hd⟩

/-- A value read off a yes. -/
theorem toOption_some {α : Type} {x : Except String α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => cases h
  | ok y => cases h; rfl

/-- What a piece's reduction puts out: the oracles left; a record that the block's decide
returns. -/
theorem Piece.out_of_decide (p : Piece C F S Cl W) (a : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (b : S × F.E.Str) (h : p.ior.red.out a τ = some b) :
    b.2 = p.ior.imp a.2 τ ∧ ∃ rs gs, p.b.decide a.1 rs gs = .ok b.1 := by
  obtain ⟨s, y⟩ := a
  have h' : (if sTests C p.stage y τ = true then p.run s (sView C p.stage y τ) else none).map
      (fun xo => (xo, p.ior.imp y τ)) = some b := h
  split at h'
  · cases hr : p.run s (sView C p.stage y τ) with
    | none => rw [hr] at h'; cases h'
    | some xo =>
      rw [hr] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      subst h'
      exact ⟨rfl, single_decide _ _ _ _ _ _ (toOption_some hr)⟩
  · cases h'

/-- A piece that meets at every transcript what the prover must lose towards. -/
theorem goodIn_of_sure (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop)
    (h : ∀ a τ b, on a → p.ior.red.out a τ = some b → on' b ∧ ∀ w, R' b w → R a (p.ext a τ w)) :
    p.GoodIn on on' R R' :=
  fun a ha => Doomed.of_forall _ _ fun τ b hb => h a τ b ha hb

/-- **The end has GoodIn, at any errors.** -/
theorem end_goodIn (p : Piece C F S Cl W) (ask : S → ChainEnd.Clauses)
    (he : ChainEnd.Exact ask p.b) (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (h1 : ∀ a τ, on a → (∀ c ∈ ask a.1, c.2 = true) → on' (a.1, p.ior.imp a.2 τ))
    (h2 : ∀ a τ w, on a → (∀ c ∈ ask a.1, c.2 = true) → R' (a.1, p.ior.imp a.2 τ) w →
      R a (p.ext a τ w)) : p.GoodIn on on' R R' := by
  refine goodIn_of_sure p on on' R R' fun a τ b ha hb => ?_
  obtain ⟨hy, rs, gs, hd⟩ := p.out_of_decide a τ b hb
  obtain ⟨hs, hc⟩ := (he a.1 rs gs b.1).1 hd
  have hb' : b = (a.1, p.ior.imp a.2 τ) := Prod.ext hs hy
  subst hb'
  exact ⟨h1 a τ ha hc, fun w hw => h2 a τ w ha hc hw⟩

/-- The same at the text of the chain's end, with the extractor the identity: the promise behind is
"on at the oracles left, and every clause holds". -/
theorem chainEnd_goodIn (chain piece : Nat) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (ask : S → ChainEnd.Clauses) (base : ℕ) (ds : List RDT) (back : List Fmt.RoundView)
    (err : Err (uLT C ds)) (on : S × F.E.Str → Prop) (R : S × F.E.Str → W → Prop)
    (hon : ∀ a τ, on a → on (a.1, (⟨ChainEnd.chainEnd chain piece sealed inFront ask, base, ds,
      back, fun _ _ w => w, err⟩ : Piece C F S Cl W).ior.imp a.2 τ))
    (hR : ∀ a τ w, on a → R (a.1, (⟨ChainEnd.chainEnd chain piece sealed inFront ask, base, ds,
      back, fun _ _ w => w, err⟩ : Piece C F S Cl W).ior.imp a.2 τ) w → R a w) :
    (⟨ChainEnd.chainEnd chain piece sealed inFront ask, base, ds, back, fun _ _ w => w, err⟩ :
      Piece C F S Cl W).GoodIn on (fun b => on b ∧ ∀ c ∈ ask b.1, c.2 = true) R R :=
  end_goodIn _ ask (ChainEnd.chainEnd_exact chain piece sealed inFront ask) _ _ _ _
    (fun a τ ha hc => ⟨hon a τ ha, hc⟩) (fun a τ w ha _ hw => hR a τ w ha hw)

end VerifiableInference.Desc.Sound
