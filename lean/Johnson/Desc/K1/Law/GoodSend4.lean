-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSend4.lean: two premises of the law of a sending in the form of the rule of
composition (send_goodIn, GoodSend3.lean), paid: what it asks of the first written round's draws
holds where that round has the place's own entry of the seeds; and a sending with a block without a
round laid behind it is a sending still, where that block leaves the statement's messages.

Main names: seeds_one (under the one Boolean a place has one seed); seed_draws; send_goodIn_entry
(the law with the entry in the place of the five facts, and without the premise of one seed);
LeavesMsgs, isSend_andThen.

What is not claimed. One answer a message, and so one seed. That a written round of a plan has the
place's entry is a premise. Which block without a round stands at which place is not said.
Nothing on soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.First (S)

theorem foldl_max_le : ∀ (l : List OracleShape) (a b : Nat), a ≤ b → (∀ s ∈ l, s.answers ≤ b) →
    l.foldl (fun a s => max a s.answers) a ≤ b
  | [], _, _, ha, _ => ha
  | x :: l, _, b, ha, h =>
    foldl_max_le l _ b (Nat.max_le.2 ⟨ha, h x List.mem_cons_self⟩)
      fun s hs => h s (List.mem_cons_of_mem _ hs)

/-- **Under the one Boolean a place has one seed.** -/
theorem seeds_one (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) : P.seeds = 1 := by
  have hidx : ∀ s ∈ P.tuple, ∃ k : Fin (shapesOf P).length, sampledAt P k ∧ shapeAt P k = s := by
    intro s hs
    obtain ⟨hm, h0⟩ := List.mem_filter.1 hs
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hm
    exact ⟨⟨i, hi⟩, (bne_iff_ne.1 h0 : (shapesOf P)[i].answers ≠ 0), rfl⟩
  have hle : P.seeds ≤ 1 := foldl_max_le _ _ _ (Nat.zero_le _) fun s hs => by
    obtain ⟨k, hk, rfl⟩ := hidx s hs
    exact Nat.le_of_eq (cond_tie P rad hC k hk).one
  have hB := (cond_parts P rad hC).1
  simp only [planOkOwn, planOk, Bool.and_eq_true] at hB
  cases ht : P.tuple with
  | nil =>
    have := hB.1.2
    rw [ht] at this
    cases this
  | cons s l =>
    obtain ⟨k, hk, _⟩ := hidx s (by rw [ht]; exact List.mem_cons_self)
    have := one_le_seeds P k hk
    omega

/-- **The draws of the place's own entry of the seeds**, at one seed. -/
theorem seed_draws (P : Par) (h1 : P.seeds = 1) (d : RDT) (he : d.entry = seedEntry P)
    (hk : d.kind = .seeds) :
    PlainDraws (Fmt.dsOf d.entry d.kind) ∧ nE (Fmt.dsOf d.entry d.kind) = P.coordinates + 1 ∧
      nP (Fmt.dsOf d.entry d.kind) = 0 ∧ IsNZ (Fmt.dsOf d.entry d.kind) P.coordinates ∧
      d.entry.logN ≤ 64 := by
  have hE : (seedEntry P).drawE = P.coordinates + 1 := by
    show P.seeds * (P.coordinates + 1) = _
    rw [h1, Nat.one_mul]
  have hN : (seedEntry P).drawNZ = 1 := h1
  rw [he, hk]
  refine ⟨plain_dsOf _ _ rfl (by decide), ?_, nP_dsOf _ _, ?_, Nat.zero_le _⟩
  · rw [nE_dsOf_seed _ hN (by rw [hE]; exact Nat.succ_pos _), hE]
  · have := isNZ_dsOf_seed (seedEntry P) hN
    rw [hE] at this
    exact this

variable {T Cl W : Type} {F : Frame}

/-- **The law of a sending**, with the place's own entry at the first written round. -/
theorem send_goodIn_entry (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true)
    (b : Block T Cl) (stOf : T → Statement) (hS : IsSend P stOf b) (base : Nat)
    (d₁ d₂ : RDT) (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e : Nat)
    (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.imp y τ) =
      fIn y τ.1)
    (On On' : T × F.E.Str → Prop) (R R' : T × F.E.Str → W → Prop)
    (hkeep : ∀ a τ x, On a →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x → On' x)
    (hback : ∀ a τ x w, On a →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      R' x w → R a w) :
    (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).GoodIn On
      (fun x => On' x ∧ ∀ k, sampledAt P k →
        Sealed P.codes (shapeAt P k) (rad k.val) (fOf x.2 k) (stOf x.1)
          ((stOf x.1).oracles.size - (shapesOf P).length + k.val)) R R' := by
  have h1 := seeds_one P rad hC
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws P h1 d₁ he₁ hk₁
  exact send_goodIn P rad hC h1 b stOf hS base d₁ d₂ a1 a2 a3 a4 a5 e he fOf fIn hf On On' R R'
    hkeep hback

/-- A block's yes leaves the statement's messages: their number, shapes, marks and sample rows. -/
def LeavesMsgs (stOf : T → Statement) (q : Block T Cl) : Prop :=
  ∀ s s' rs gs, q.decide s rs gs = .ok s' → SameMsgs (stOf s) (stOf s')

/-- **A sending with such a block laid behind it is a sending.** -/
theorem isSend_andThen (P : Par) (stOf : T → Statement) (name : String) (p q : Block T Cl)
    (hp : IsSend P stOf p) (hlen : p.rounds.length = 2) (hq : LeavesMsgs stOf q) :
    IsSend P stOf (p.andThen name q) := by
  intro s s' r₁ r₂ gs h
  have h' : (p.decide s ([r₁, r₂].take p.rounds.length) (gs.take p.openings)).bind (fun s₁ =>
      q.decide s₁ ([r₁, r₂].drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  rw [hlen] at h'
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  obtain ⟨L, d, d', owed, ids, hyes, hsame, hsize⟩ := hp s s₁ r₁ r₂ _ h1
  have hk := hq _ _ _ _ h2
  exact ⟨L, d, d', owed, ids, hyes, hsame.trans hk, (size_of_same hk).trans hsize⟩

end VerifiableInference.Desc.K1
