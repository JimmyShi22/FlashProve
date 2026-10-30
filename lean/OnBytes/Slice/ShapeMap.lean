-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ShapeMap.lean: round-by-round soundness and small errors pass along a map of shapes in
which one new round may stand over two old ones.

Beside OnBytes/Slice/Carry.lean. That file carries round-by-round soundness between two given
protocols whose shapes have THE SAME NUMBER OF ROUNDS, along maps of messages that may depend on all
that was sent before, with a map of verifier's messages that may be undefined and many-to-one, and
with other statements and external strings (`sound_carry`). It says of itself that there is no such
thing between shapes of different lengths. This file is for that case: a protocol in which the
prover sends in ONE round what another protocol's prover sends in TWO. Its maps are plainer than
`Carry`'s (they do not look at the past; the verifier's messages are in bijection; statements,
external strings and language are the same), so the counts pass unchanged. Where no new round stands
over two old ones `sound` says nothing that `sound_carry` does not say at one message to one: by a
reading; no file of this library states that tie. (The partners of `doomed` and `below` in
OnBytes/Slice/Carry.lean are `Carry.doomed` and `below_mulErr`; no tie is stated for them either.)

All is over the library's `Shape`, `Round`, `Tr`, `Err`, `Doomed`, `InteractiveOracleProof` alone. Both protocols are
given. A round's count is the number of verifier's messages that may let a prover that has lost
escape; "the prover has lost towards a goal" is `Doomed` (Iop/Rbr.lean).
 - `RMap r' r`: a map of rounds from the NEW round to the OLD: every new prover's message is read as
   an old one; the verifier's messages are in bijection;
 - `RMap2 r' r1 r2`: ONE new round over TWO old ones: a new prover's message is read as a message of
   each; the first old round's verifier's message is taken at a value u; the new round's verifier's
   messages are in bijection with the second's;
 - `SMap s' s`: a map of shapes: the two kinds of step, one after the other; `SMap.refl`,
   `SMap.app`; `SMap.Flat`: no new round stands over two old ones;
 - `back M`: a transcript of the new shape, read as one of the old; `back_app`, `fst_back`,
   `snd_back`: part by part;
 - `fwd M`: the old counts as counts of the new shape: the same numbers; of two old rounds under one
   new round the second's; `FirstZero M ε`: there the first's is 0; `firstZero_of_flat`,
   `firstZero_app`, `firstZero_app_flat`;
 - `doomed`: under `FirstZero M ε`: if the old prover has lost towards a goal with the counts ε, the
   new prover has lost towards that goal of the transcript read back, with the counts `fwd M ε`;
 - `sound`: under `FirstZero M ε`: round-by-round soundness with the counts ε passes from the old
   protocol Q to the new protocol Q', for the same language, with the counts `fwd M ε`, if whatever
   Q' accepts Q accepts when read back;
 - `below`: counts that are at most a share c of their rounds' verifier's messages stay so;
   `sound_below`: both at once, from counts that meet `FirstZero`.

Of the prover's messages only a map from new to old is asked, no way back: a prover of the new
protocol is a prover of the old one that plays the images. Where one new round stands over two old
ones, the new prover fixes both messages at once, without a verifier's message between them; the
first old round's verifier's message is never drawn, and is taken at u. Nothing is asked of how many
values it has, only that its count is 0: then the old prover has lost at EVERY value of it, so at u.

Main definitions: `RMap`, `RMap2`, `SMap`, `SMap.refl`, `SMap.app`, `SMap.Flat`, `back`, `fwd`,
`FirstZero`, `errSnd`.
Main theorems: `back_refl`, `back_app`, `fst_back`, `snd_back`, `fwd_app`, `firstZero_app`,
`firstZero_refl`, `flat_refl`, `flat_app`, `firstZero_of_flat`, `firstZero_app_flat`, `none_of_cnt`,
`doomed`, `below`, `sound`, `sound_below`.

Not claimed. No protocol is named and no map is given. The hypothesis of `sound` (what Q' accepts, Q
accepts when read back) is the work at each use; it can hang on u. NOT CARRIED: that the decision
depends on the oracles only at the positions read (`InteractiveOracleProof.IsLocal`): it would want maps of positions
and symbols; completeness and zero knowledge (`Honest`): they would want a way back; nothing on
batch protocols, annotations or statements fixed late (`SndB`, `JDoomed`, `LateSound`); nothing on
how many positions are read. More than two old rounds under one new round: by no constructor.
Nothing on a compiler, a wiring, an encoding or bytes.

Terms: lean/GLOSSARY.md.

-/
import Prob.Count
import Iop.InteractiveOracleProof

set_option autoImplicit false

namespace OnBytes.Slice.ShapeMap
open Iop Prob
open scoped ENNReal

/-- A map of rounds, from the new round r' to the old round r: every prover's message of the new
round is read as one of the old; the verifier's messages are in bijection. -/
structure RMap (r' r : Round) where
  /-- a new prover's message, read as an old one -/
  msg  : r'.Msg → r.Msg
  /-- the verifier's messages -/
  chal : r'.Chal ≃ r.Chal

/-- The identity. -/
def RMap.refl (r : Round) : RMap r r := ⟨id, Equiv.refl _⟩

/-- A map from ONE new round r' to TWO old rounds r1, r2: a new prover's message is read as a
message of each; u is the value at which the first old round's verifier's message is taken; the new
round's verifier's messages are in bijection with the second's. -/
structure RMap2 (r' r1 r2 : Round) where
  /-- a new prover's message, read as one of the first old round -/
  msg1 : r'.Msg → r1.Msg
  /-- the first old round's verifier's message -/
  u    : r1.Chal
  /-- a new prover's message, read as one of the second old round -/
  msg2 : r'.Msg → r2.Msg
  /-- the verifier's messages of the new round and of the second old round -/
  chal : r'.Chal ≃ r2.Chal

/-- A map of shapes, from the new shape to the old: round by round, or one new round over two old
ones. -/
inductive SMap : Shape → Shape → Type 1
  | nil : SMap [] []
  | one {r' r : Round} {s' s : Shape} (f : RMap r' r) (M : SMap s' s) : SMap (r' :: s') (r :: s)
  | two {r' r1 r2 : Round} {s' s : Shape} (f : RMap2 r' r1 r2) (M : SMap s' s) :
      SMap (r' :: s') (r1 :: r2 :: s)

/-- The identity. -/
def SMap.refl : (s : Shape) → SMap s s
  | [] => .nil
  | r :: s => .one (RMap.refl r) (SMap.refl s)

/-- Two maps, one after the other. -/
def SMap.app : {s' s t' t : Shape} → SMap s' s → SMap t' t → SMap (s' ++ t') (s ++ t)
  | _, _, _, _, .nil, N => N
  | _, _, _, _, .one f M, N => .one f (SMap.app M N)
  | _, _, _, _, .two f M, N => .two f (SMap.app M N)

/-- A transcript of the new shape, read as one of the old. -/
def back : {s' s : Shape} → SMap s' s → Tr s' → Tr s
  | _, _, .nil, _ => ()
  | _, _, .one f M, (m, c, τ) => (f.msg m, f.chal c, back M τ)
  | _, _, .two f M, (m, c, τ) => (f.msg1 m, f.u, f.msg2 m, f.chal c, back M τ)

/-- The old counts as counts of the new shape: the same numbers; of two old rounds under one new
round the second's. -/
def fwd : {s' s : Shape} → SMap s' s → Err s → Err s'
  | _, _, .nil, _ => ()
  | _, _, .one _ M, (e, ε) => (e, fwd M ε)
  | _, _, .two _ M, (_, e, ε) => (e, fwd M ε)

/-- Where one new round stands over two old ones, the first old round's count is 0. -/
def FirstZero : {s' s : Shape} → SMap s' s → Err s → Prop
  | _, _, .nil, _ => True
  | _, _, .one _ M, (_, ε) => FirstZero M ε
  | _, _, .two _ M, (e, _, ε) => e = 0 ∧ FirstZero M ε

/-- Read back along the identity, a transcript is itself. -/
theorem back_refl : ∀ (s : Shape) (τ : Tr s), back (SMap.refl s) τ = τ
  | [], () => rfl
  | _ :: s, (m, c, τ) => by
      show (m, c, back (SMap.refl s) τ) = (m, c, τ)
      rw [back_refl s τ]

/-- Reading back goes part by part. -/
theorem back_app : ∀ {s' s t' t : Shape} (M : SMap s' s) (N : SMap t' t) (a : Tr s') (b : Tr t'),
    back (M.app N) (Tr.app a b) = Tr.app (back M a) (back N b)
  | _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, .one f M, N, (m, c, a), b =>
      congrArg (fun x => (f.msg m, f.chal c, x)) (back_app M N a b)
  | _, _, _, _, .two f M, N, (m, c, a), b =>
      congrArg (fun x => (f.msg1 m, f.u, f.msg2 m, f.chal c, x)) (back_app M N a b)

/-- The first part of a transcript read back. -/
theorem fst_back {s' s t' t : Shape} (M : SMap s' s) (N : SMap t' t) (τ : Tr (s' ++ t')) :
    Tr.fst (back (M.app N) τ) = back M (Tr.fst τ) := by
  conv_lhs => rw [← Tr.app_fst_snd τ, back_app]
  exact Tr.fst_app _ _

/-- The second part of a transcript read back. -/
theorem snd_back {s' s t' t : Shape} (M : SMap s' s) (N : SMap t' t) (τ : Tr (s' ++ t')) :
    Tr.snd (s := s) (back (M.app N) τ) = back N (Tr.snd (s := s') τ) := by
  conv_lhs => rw [← Tr.app_fst_snd τ, back_app]
  exact Tr.snd_app _ _

/-- The counts go part by part. -/
theorem fwd_app : ∀ {s' s t' t : Shape} (M : SMap s' s) (N : SMap t' t) (ε : Err s) (δ : Err t),
    fwd (M.app N) (Err.app ε δ) = Err.app (fwd M ε) (fwd N δ)
  | _, _, _, _, .nil, _, _, _ => rfl
  | _, _, _, _, .one _ M, N, (e, ε), δ => congrArg (Prod.mk e) (fwd_app M N ε δ)
  | _, _, _, _, .two _ M, N, (_, e, ε), δ => congrArg (Prod.mk e) (fwd_app M N ε δ)

/-- The condition on the counts goes part by part, for counts that are given in parts. -/
theorem firstZero_app : ∀ {s' s t' t : Shape} (M : SMap s' s) (N : SMap t' t) (ε : Err s)
    (δ : Err t),
    FirstZero M ε → FirstZero N δ → FirstZero (M.app N) (Err.app ε δ)
  | _, _, _, _, .nil, _, _, _, _, h => h
  | _, _, _, _, .one _ M, N, (_, ε), δ, h1, h2 => firstZero_app M N ε δ h1 h2
  | _, _, _, _, .two _ M, N, (_, _, ε), δ, h1, h2 => ⟨h1.1, firstZero_app M N ε δ h1.2 h2⟩

/-- The identity asks nothing of the counts. -/
theorem firstZero_refl : ∀ (s : Shape) (ε : Err s), FirstZero (SMap.refl s) ε
  | [], _ => trivial
  | _ :: s, (_, ε) => firstZero_refl s ε

/-- No new round stands over two old ones. -/
def SMap.Flat : {s' s : Shape} → SMap s' s → Prop
  | _, _, .nil => True
  | _, _, .one _ M => M.Flat
  | _, _, .two _ _ => False

/-- The identity has no new round over two old ones. -/
theorem flat_refl : ∀ s : Shape, (SMap.refl s).Flat
  | [] => trivial
  | _ :: s => flat_refl s

/-- Nor have two such maps, one after the other. -/
theorem flat_app : ∀ {s' s t' t : Shape} (M : SMap s' s) (N : SMap t' t),
    M.Flat → N.Flat → (M.app N).Flat
  | _, _, _, _, .nil, _, _, h => h
  | _, _, _, _, .one _ M, N, h1, h2 => flat_app M N h1 h2
  | _, _, _, _, .two _ _, _, h1, _ => h1.elim

/-- Where no new round stands over two old ones, nothing is asked of the counts. -/
theorem firstZero_of_flat : ∀ {s' s : Shape} (M : SMap s' s), M.Flat → ∀ ε : Err s, FirstZero M ε
  | _, _, .nil, _, _ => trivial
  | _, _, .one _ M, h, (_, ε) => firstZero_of_flat M h ε
  | _, _, .two _ _, h, _ => h.elim

/-- The counts of the second part of a shape. -/
def errSnd : {s t : Shape} → Err (s ++ t) → Err t
  | [], _, ε => ε
  | _ :: s, _, (_, ε) => errSnd (s := s) ε

/-- Behind a part in which no new round stands over two old ones, the condition on the counts is
that of the rest. For counts that are not given in parts. -/
theorem firstZero_app_flat : ∀ {s' s t' t : Shape} (M : SMap s' s) (N : SMap t' t), M.Flat →
    ∀ ε : Err (s ++ t), FirstZero (M.app N) ε ↔ FirstZero N (errSnd (s := s) ε)
  | _, _, _, _, .nil, _, _, _ => Iff.rfl
  | _, _, _, _, .one _ M, N, h, (_, ε) => firstZero_app_flat M N h ε
  | _, _, _, _, .two _ _, _, h, _ => h.elim

/-- A count that is at most 0 leaves nothing. -/
theorem none_of_cnt {α : Type} [Fintype α] {P : α → Prop} (h : cnt P ≤ 0) (a : α) : ¬ P a :=
  fun ha => by
    haveI : Nonempty {x : α // P x} := ⟨⟨a, ha⟩⟩
    have hp : 0 < Nat.card {x : α // P x} := Nat.card_pos
    exact absurd (show Nat.card {x : α // P x} ≤ 0 from h) (Nat.not_le.2 hp)

/-- If the old prover has lost towards `bad`, the new prover has lost towards "`bad` of the
transcript read back", with the counts `fwd`, if the first of two old rounds under one new round
has the count 0. -/
theorem doomed : ∀ {s' s : Shape} (M : SMap s' s) (ε : Err s) (bad : Tr s → Prop),
    FirstZero M ε → Doomed s ε bad → Doomed s' (fwd M ε) (fun τ => bad (back M τ))
  | _, _, .nil, _, _, _, h => h
  | _, _, .one f M, (_, ε), bad, hz, h => fun m => by
      have h1 := h (f.msg m)
      rw [← cnt_equiv f.chal] at h1
      exact le_trans (cnt_mono fun c hc hd =>
        hc (doomed M ε (fun τ => bad (f.msg m, f.chal c, τ)) hz hd)) h1
  | _, _, .two f M, (e, _, ε), bad, hz, h => fun m => by
      have h0 : cnt (fun c : _ => ¬ Doomed _ _ (fun τ => bad (f.msg1 m, c, τ))) ≤ 0 :=
        hz.1 ▸ h (f.msg1 m)
      have h1 := (Classical.not_not.1 (none_of_cnt h0 f.u)) (f.msg2 m)
      rw [← cnt_equiv f.chal] at h1
      exact le_trans (cnt_mono fun c hc hd =>
        hc (doomed M ε (fun τ => bad (f.msg1 m, f.u, f.msg2 m, f.chal c, τ)) hz.2 hd)) h1

/-- Small errors stay small: every count is at most the share c of its round's verifier's
messages. -/
theorem below : ∀ {s' s : Shape} (M : SMap s' s) (ε : Err s) (c : ℝ≥0∞),
    Err.Below ε c → Err.Below (fwd M ε) c
  | _, _, .nil, _, _, _ => trivial
  | _, _, .one f M, (_, ε), c, h =>
      ⟨by rw [Fintype.card_congr f.chal]; exact h.1, below M ε c h.2⟩
  | _, _, .two f M, (_, _, ε), c, h =>
      ⟨by rw [Fintype.card_congr f.chal]; exact h.2.1, below M ε c h.2.2⟩

variable {X : Type} {E : ExtSpec}

/-- Round-by-round soundness passes from the old protocol Q to the new protocol Q', for the
same language on the same instances and external strings, with the counts `fwd`: if whatever Q'
accepts, Q accepts when read back, and the first of two old rounds under one new round has the count
0. Both protocols are given. -/
theorem sound (Q' Q : InteractiveOracleProof X E) (M : SMap Q'.shape Q.shape)
    (hacc : ∀ x y τ, Q'.accept x y τ = true → Q.accept x y (back M τ) = true)
    (L : X → E.Str → Prop) (ε : Err Q.shape) (hz : FirstZero M ε) (h : Q.Sound L ε) :
    Q'.Sound L (fwd M ε) :=
  fun x y hL => Doomed.mono _ _ (fun τ hτ => by
    cases ha : Q'.accept x y τ with
    | false => rfl
    | true => rw [hacc x y τ ha] at hτ; cases hτ) (doomed M ε _ hz (h x y hL))

/-- Soundness and small errors at once. This is said under the hypotheses that stand in the
statement itself, which this comment does not list; it is no claim that they hold. -/
theorem sound_below (Q' Q : InteractiveOracleProof X E) (M : SMap Q'.shape Q.shape)
    (hacc : ∀ x y τ, Q'.accept x y τ = true → Q.accept x y (back M τ) = true)
    (L : X → E.Str → Prop) (c : ℝ≥0∞)
    (h : ∃ ε : Err Q.shape, FirstZero M ε ∧ Q.Sound L ε ∧ Err.Below ε c) :
    ∃ ε' : Err Q'.shape, Q'.Sound L ε' ∧ Err.Below ε' c := by
  obtain ⟨ε, hz, hs, hb⟩ := h
  exact ⟨fwd M ε, sound Q' Q M hacc L ε hz hs, below M ε c hb⟩

end OnBytes.Slice.ShapeMap
