-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Sub/Joint.lean: the joint for a sub-proof: how a ledger of claims stands between two blocks of a
typed chain, and how any block with `TWhole.KnowAt` becomes a block that appends claims to a ledger.

Definitions, statements and their proofs.
In a sub-proof no block tests an equation. Each algebraic check becomes a claim: a linear form on
the entries of the committed messages, with a public target (`TWhole.Form`, `TWhole.Ledger`,
Cb/G6/Led.lean). Between two blocks stand: public data, the open claims, and the ledger. At
the end one challenge batches the ledger into one form (`TWhole.batch_knowAt`).
A block is proved by itself, between joints A and B on its own statements, without a ledger. What B
says beyond a remainder B₀ is given as claims `cl x'`, read off the block's output statement. This
file puts the ledger beside the block.

Main names:
  `ledJ A msg n`: the joint: A of the statement's first part (public data and whatever claims are
    open), and every claim of the ledger holds of the entries. ITS CONDITION (`on`): A's, and the
    ledger has at most n claims: that number is what the batching challenge's error reads.
  `R.led cl`: R beside a ledger that is handed on, with the claims `cl x'` appended behind. Its
    rounds are R's.
  `keepX_knowAt`: R beside any carried part Z: a relation Q and a condition P on Z ride along.
  `led_knowAt`: from `KnowAt R A B idW ε`, "at most c claims are appended", "B's condition gives
    B₀'s" and "B₀ and the appended claims give B": `KnowAt (R.led cl) (ledJ A msg n) (ledJ B₀ msg (n
    + c))`, with the same errors. THE FOUR FIELDS: `point` and `isLocal` are R's; `onOut`: R's, and
    the count n + c; `know`: R's, the old ledger being a part of the new one.
  `led_start`: a chain starts at the empty ledger. `led_close`: where nothing is left open, the
    joint gives `ledIn` (Cb/G6/Led.lean), in front of the batching challenge.
  `led_batch`: a chain's end and the batching challenge in a row.

Limits: nothing on an honest prover or on zero knowledge: each statement is true of a verifier that
rejects everything. `led_close` and `led_batch` ask that what is left beside the ledger (B₀) holds
of every statement and witness, and the joint behind them forgets it: a rider that says something
does not pass them. The entries J are those of messages that
are fixed before the chain's first round: a message that is sent inside the chain is not treated
here.
Terms: lean/GLOSSARY.md.
-/
import Cb.G6.Led
import Cb.Ld.LdSigLiftProofs

set_option autoImplicit false

namespace Cb.Sub
open Iop Prob Hiop TWhole IOR

/-- The extractor that hands the further witness back. -/
@[reducible] def idW {M Xi Wp : Type} {Ei : ExtSpec} {s : Shape} :
    M → Xi × Ei.Str → Tr s → Wp → Wp := fun _ _ _ wp => wp

/-- A joint beside a carried part Z: the relation Q and the condition P of the carried part. -/
def withZ {K X Z W : Type} {Ex : ExtSpec} (A : Rels K X Ex W) (Q : Z → W → Prop) (P : Z → Prop) :
    Rels K (X × Z) Ex W :=
  ⟨fun x y w => A.rel x.1 y w ∧ Q x.2 w, fun a w => A.relR (a.1.1, a.2) w ∧ Q a.1.2 w,
    fun a => A.on (a.1.1, a.2) ∧ P a.1.2, A.core⟩

/-- A block beside a carried part. -/
theorem keepX_knowAt {K M X X' Z Wp : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (M × Wp)} {B : Rels K X' Eo (M × Wp)} {ε : Err R.shape}
    (Q : Z → M × Wp → Prop) (P : Z → Prop) (h : KnowAt R A B idW ε) :
    KnowAt (R.keepX Z) (withZ A Q P) (withZ B Q P) idW ε where
  point := h.point
  isLocal := isLocal_keepX h.isLocal Z
  onOut := fun a τ b ha hb => by
    obtain ⟨h1, h2⟩ := keepX_red_out R Z a τ b hb
    exact ⟨h.onOut (a.1.1, a.2) τ (b.1.1, b.2) ha.1 h2, h1 ▸ ha.2⟩
  know := fun m a ha =>
    Doomed.mono _ _ (fun τ hτ b w hb hw => by
      obtain ⟨h1, h2⟩ := keepX_red_out R Z a τ b hb
      exact ⟨hτ (b.1.1, b.2) w h2 hw.1, h1 ▸ hw.2⟩) (h.know m (a.1.1, a.2) ha.1)

variable {E J : Type} [Field E] [Fintype J]

/-- THE JOINT FOR A SUB-PROOF: A of the public data and the open claim; every claim of the ledger
holds; on the statements whose ledger has at most n claims. -/
def ledJ {K X M Wp : Type} {Ex : ExtSpec} (A : Rels K X Ex (M × Wp)) (msg : M → J → E) (n : ℕ) :
    Rels K (X × Ledger E J) Ex (M × Wp) :=
  withZ A (fun L w => L.Holds (msg w.1)) fun L => L.length ≤ n

/-- R beside a ledger, with the claims read off R's output statement appended. -/
noncomputable def _root_.Iop.IOR.led {X X' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo)
    (cl : X' → Ledger E J) : IOR (X × Ledger E J) Ei (X' × Ledger E J) Eo :=
  (R.keepX (Ledger E J)).post (fun b => some (b.1, b.2 ++ cl b.1)) (ExtMap.id Eo)

omit [Fintype J] in
theorem holds_append [Fintype J] (L L' : Ledger E J) (m : J → E) :
    (L ++ L').Holds m ↔ L.Holds m ∧ L'.Holds m := by
  unfold Ledger.Holds
  simp only [List.mem_append]
  exact ⟨fun h => ⟨fun f hf => h f (Or.inl hf), fun f hf => h f (Or.inr hf)⟩,
    fun h f hf => hf.elim (h.1 f) (h.2 f)⟩

/-- A BLOCK BECOMES A BLOCK THAT APPENDS CLAIMS. -/
theorem led_knowAt {K M X X' Wp : Type} {Ei Eo : ExtSpec} {R : IOR X Ei X' Eo}
    {A : Rels K X Ei (M × Wp)} {B B₀ : Rels K X' Eo (M × Wp)} {ε : Err R.shape}
    (msg : M → J → E) (cl : X' → Ledger E J) (n c : ℕ) (h : KnowAt R A B idW ε)
    (hc : ∀ x', (cl x').length ≤ c) (ho : ∀ b, B.on b → B₀.on b)
    (hB : ∀ x' y w, B.on (x', y) → B₀.relR (x', y) w → (cl x').Holds (msg w.1) →
      B.relR (x', y) w) :
    KnowAt (R.led cl) (ledJ A msg n) (ledJ B₀ msg (n + c)) idW ε :=
  knowAt_postMap (B := ledJ B msg n) (B' := ledJ B₀ msg (n + c))
    (fun b : X' × Ledger E J => (b.1, b.2 ++ cl b.1))
    (keepX_knowAt (fun (L : Ledger E J) (w : M × Wp) => L.Holds (msg w.1))
      (fun L : Ledger E J => L.length ≤ n) h)
    (fun x y (hx : B.on (x.1, y) ∧ x.2.length ≤ n) =>
      (⟨ho _ hx.1, by
        rw [List.length_append]
        exact Nat.add_le_add hx.2 (hc x.1)⟩ : B₀.on (x.1, y) ∧ (x.2 ++ cl x.1).length ≤ n + c))
    fun x y w (hx : B.on (x.1, y) ∧ x.2.length ≤ n)
        (hw : B₀.relR (x.1, y) w ∧ (x.2 ++ cl x.1).Holds (msg w.1)) =>
      (⟨hB x.1 y w hx.1 hw.1 ((holds_append x.2 (cl x.1) (msg w.1)).1 hw.2).2,
        ((holds_append x.2 (cl x.1) (msg w.1)).1 hw.2).1⟩ :
        B.relR (x.1, y) w ∧ x.2.Holds (msg w.1))

/-- A chain starts at the empty ledger. -/
theorem led_start {K M X X' Wp : Type} {Ei Eo : ExtSpec}
    {R : IOR (X × Ledger E J) Ei X' Eo} {A : Rels K X Ei (M × Wp)} {B : Rels K X' Eo (M × Wp)}
    {ε : Err R.shape} (msg : M → J → E) (n : ℕ) (h : KnowAt R (ledJ A msg n) B idW ε) :
    KnowAt (R.pre (fun x => some (x, ([] : Ledger E J))) (ExtMap.id Ei)) A B idW ε :=
  knowAt_preMap (A' := A) (A := ledJ A msg n) (fun x : X => (x, ([] : Ledger E J)))
    (fun x y hx => (⟨hx, Nat.zero_le n⟩ : A.on (x, y) ∧ ([] : Ledger E J).length ≤ n))
    (fun x y w _ (hw : A.relR (x, y) w ∧ Ledger.Holds ([] : Ledger E J) (msg w.1)) => hw.1) h

/-- Where nothing is left open, the joint gives "every claim of the ledger holds". -/
theorem led_close {K M X X' Wp : Type} {Ei Eo : ExtSpec} {R : IOR X Ei (X' × Ledger E J) Eo}
    {A : Rels K X Ei (M × Wp)} {B₀ : Rels K X' Eo (M × Wp)} {ε : Err R.shape} (msg : M → J → E)
    (n : ℕ) (h : KnowAt R A (ledJ B₀ msg n) idW ε) (h0 : ∀ b w, B₀.relR b w) :
    KnowAt R A (ledIn (P := X') Eo n msg B₀.core) idW ε :=
  knowAt_mono h (fun _ ha => ha) (fun _ _ _ hw => hw) (fun _ w _ hw => ⟨h0 _ w, hw⟩) fun _ hb =>
  hb.2

/-- A chain's end and the batching challenge in a row: from A to "the one form holds". -/
theorem led_batch [Fintype E] {K M X X' Wp : Type} {Ei Eo : ExtSpec}
    {R : IOR X Ei (X' × Ledger E J) Eo} {A : Rels K X Ei (M × Wp)} {B₀ : Rels K X' Eo (M × Wp)}
    {ε : Err R.shape} (msg : M → J → E) (n : ℕ) (h : KnowAt R A (ledJ B₀ msg n) idW ε)
    (h0 : ∀ b w, B₀.relR b w) :
    KnowAt (R.seq (IOR.draw E (ledNx (J := J) (P := X')) Eo)) A (ledOut Eo msg B₀.core) idW
      (Err.app ε (Nums.draw K E (ledNx (J := J) (P := X')) Eo (n - 1)).err) :=
  knowAt_seq (led_close msg n h h0) (batch_knowAt Eo n msg B₀.core)

end Cb.Sub
