-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SmpHeldAt.lean: "a held sample stays", for every block that leaves the codes and
the sampled messages (SmpStay, SmpStay.lean): the sample of a message THAT BEARS THE MARK, read off
the statement, is held behind such a block as it is held in front. With groundKeeps_smpStay that is
every block whose decision is shown to keep each relation that the ground's plain functions keep.

Main names:
  smpS         the sample read off the statement (smpAt, GoodSendForms.lean), where the message
               bears the mark "sampled"; nothing else.
  smpS_some    what it is to hold one.
  smpS_held    it is held along SmpStay.
  smpS_of_seedIs   it is there where the rows are the kind's one row at a seed.
  held_block, held_piece   past a block, and past a piece that holds the block.
  send_gives_onS   the law of a sending whose block goes on, inside a fence, as one lost game, with
               this reading of the sample.
Why the mark is read. The admitting of a sample overwrites the rows of a message that is not yet
sampled; it refuses one that is. So what stays for certain is the sample of a marked message.

What is not claimed. Which blocks leave the sampled messages: that is shown block by block (for a
block made of the ground's plain functions: groundKeeps_smpStay). One answer a message. Nothing on
soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendOn
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.Ground (By)

/-- The sample of a message that bears the mark. -/
noncomputable def smpS (cs : Codes) (s : OracleShape) (e : Nat) (St : Statement) (o : Nat) :
    Option (portOmZ cs s e).Smp :=
  (St.oracles[o]?).bind fun x => if x.sampled = true then smpAt cs s e St o else none

theorem smpS_some (cs : Codes) (s : OracleShape) (e : Nat) (St : Statement) (o : Nat)
    (z : (portOmZ cs s e).Smp) : smpS cs s e St o = some z ↔
      ∃ x : OnBytes.Oracle, St.oracles[o]? = some x ∧ x.sampled = true ∧
        smpAt cs s e St o = some z := by
  constructor
  · intro h
    unfold smpS at h
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.1 h
    by_cases hs : x.sampled = true
    · rw [if_pos hs] at h
      exact ⟨x, hx, hs, h⟩
    · rw [if_neg hs] at h
      cases h
  · rintro ⟨x, hx, hs, h⟩
    unfold smpS
    exact Option.bind_eq_some_iff.2 ⟨x, hx, by rw [if_pos hs]; exact h⟩

/-- The sample rows of a marked message are as they were. -/
theorem rows_stay {A B : Statement} (h : SmpStay A B) (o : Nat) (x : OnBytes.Oracle)
    (hx : A.oracles[o]? = some x) (hs : x.sampled = true) :
    (B.oracles[o]?).map (fun y : OnBytes.Oracle => y.sampleRows) =
      (A.oracles[o]?).map fun y : OnBytes.Oracle => y.sampleRows := by
  obtain ⟨x', hx', _, _, e⟩ := h.2 o x hx hs
  rw [hx, hx']
  exact congrArg some e

theorem smpAt_stay (cs : Codes) (s : OracleShape) (e : Nat) {A B : Statement} (h : SmpStay A B)
    (o : Nat) (x : OnBytes.Oracle) (hx : A.oracles[o]? = some x) (hs : x.sampled = true) :
    smpAt cs s e B o = smpAt cs s e A o := by
  have e1 : formsAt cs s B o = formsAt cs s A o := by
    rw [formsAt_rows, formsAt_rows, rows_stay h o x hx hs]
  have e2 : ansAt B o = ansAt A o := by
    rw [ansAt_rows, ansAt_rows, rows_stay h o x hx hs]
  unfold smpAt
  simp only [e1, e2]

/-- **A held sample stays.** -/
theorem smpS_held (cs : Codes) (s : OracleShape) (e : Nat) {A B : Statement} (h : SmpStay A B)
    (o : Nat) (z : (portOmZ cs s e).Smp) (hz : smpS cs s e A o = some z) :
    smpS cs s e B o = some z := by
  obtain ⟨x, hx, hs, h1⟩ := (smpS_some cs s e A o z).1 hz
  obtain ⟨x', hx', _, hs', _⟩ := h.2 o x hx hs
  exact (smpS_some cs s e B o z).2 ⟨x', hx', hs', by rw [smpAt_stay cs s e h o x hx hs]; exact h1⟩

/-- **It is there where the rows are the kind's.** -/
theorem smpS_of_seedIs (cs : Codes) (s : OracleShape) (e : Nat) (St : Statement) (o : Nat)
    (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (y : GE) (hT : Tie cs s) (h : SeedIs cs s St o ρ y) :
    ∃ z, smpS cs s e St o = some z ∧ (portOmZ cs s e).Z.val z.1 = (portOmZ cs s e).Z.val ρ ∧
      z.2 = fun _ => y := by
  obtain ⟨z, h1, h2, h3⟩ := smpAt_of cs s e St o ρ y hT h
  obtain ⟨_, x, _, _, _, hx, _, hsm, _⟩ := h
  exact ⟨z, (smpS_some cs s e St o z).2 ⟨x, hx, hsm, h1⟩, h2, h3⟩

variable {T Cl W : Type} {F : Frame}

/-- **Past a block that leaves the sampled messages.** -/
theorem held_block (stOf : T → Statement) (b : Block T Cl) (hb : Decides (By SmpStay stOf) b)
    (cs : Codes) (s : OracleShape) (e : Nat) (t t' : T) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide t rs gs = .ok t') (o : Nat)
    (z : (portOmZ cs s e).Smp) (hz : smpS cs s e (stOf t) o = some z) :
    smpS cs s e (stOf t') o = some z :=
  smpS_held cs s e (hb t rs gs t' h) o z hz

/-- **Past a piece that holds such a block**: where the piece says yes, a sample that the record in
front holds, the record behind holds. -/
theorem held_piece {C : Run.PQ.CK} (p : Piece C F T Cl W) (stOf : T → Statement)
    (hb : Decides (By SmpStay stOf) p.b) (a x : T × F.E.Str) (τ : Tr (uLT C p.ds))
    (hx : p.ior.red.out a τ = some x) (cs : Codes) (s : OracleShape) (e : Nat) (o : Nat)
    (z : (portOmZ cs s e).Smp) (hz : smpS cs s e (stOf a.1) o = some z) :
    smpS cs s e (stOf x.1) o = some z := by
  obtain ⟨_, gs, hdec⟩ := Desc.K14.Law.piece_yes p a τ x hx
  exact held_block stOf p.b hb cs s e _ _ _ gs hdec o z hz

/-- **The law of a sending inside a fence as one lost game, with the marked message's sample.** -/
theorem send_gives_onS (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) (b : Block T Cl)
    (stOf : T → Statement) (first : T → Nat) (Fn : T → Prop) (hS : IsSendOn P stOf first Fn b)
    (base : Nat) (d₁ : RDT) (ds : List RDT) (back : List Fmt.RoundView) (he₁ : d₁.entry = seedEntry P)
    (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ,
      fOf ((openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.imp y τ) =
        fIn y τ.1) (a : T × F.E.Str) (ha : Fn a.1) :
    Doomed (uLT (ckP .two) (d₁ :: ds))
      (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).err fun τ =>
        ∀ x, (openPiece (W := W) (F := F) b base d₁ ds back P.coordinates e).ior.red.out a τ =
            some x →
          ∀ k, sampledAt P k → ∃ z,
            smpS P.codes (shapeAt P k) (rad k.val) (stOf x.1) (first x.1 + k.val) = some z ∧
            ¬ (portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (fOf x.2 k) z.1 := by
  have g := send_goodIn_on (W := W) (F := F) P rad hC b stOf first Fn hS base d₁ ds back he₁ hk₁ e
    he fOf fIn hf (fun x => Fn x.1) (fun _ => True) (fun _ h => h) (fun _ _ => True)
    (fun _ _ => True) (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
  refine Doomed.mono _ _ (fun τ hτ x hx k hk => ?_) (g a ha)
  obtain ⟨ρ, y, hs, hc⟩ := (hτ x hx).1.2 k hk
  obtain ⟨z, h1, h2, _⟩ := smpS_of_seedIs _ _ (rad k.val) _ _ ρ y (cond_tie P rad hC k hk) hs
  exact ⟨z, h1, fun hcl => hc ((clash_val _ _ z.1 ρ h2).1 hcl)⟩

/-- A try: a message without the mark holds no sample, whatever rows it bears. -/
theorem smpS_unmarked (cs : Codes) (s : OracleShape) (e : Nat) (St : Statement) (o : Nat)
    (x : OnBytes.Oracle) (hx : St.oracles[o]? = some x) (hs : x.sampled = false) :
    smpS cs s e St o = none := by
  unfold smpS
  rw [hx, Option.bind_some, if_neg (by rw [hs]; exact Bool.false_ne_true)]

end VerifiableInference.Desc.K1
