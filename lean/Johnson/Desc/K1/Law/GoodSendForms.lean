-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GoodSendForms.lean: the sample of an oracle message read off the statement: the
first sample row that the statement holds of the message, read as a linear form on the library's
typed message, and its target; where the rows are the kind's one row at a seed, that form is the
library's row at the seed. With it the law of a sending, as the row that is owed for a block that
sends sampled members, stands without a letter for the reading of the sample.

Main names:
  formRow      a plain row, read as a linear form on the entries of the library's message.
  formsAt, ansAt   the form and the target of the first sample row of message number o.
  forms_of_seedIs  where the rows are the kind's one row at the seed ρ: the form is the library's
               matrix at ρ, and the target is the answer.
  smpAt        a sample: some seed whose matrix is that form, by choice, with the target.
  smpAt_of     it is there where the rows are the kind's, and its seed has the seed's sample map.
  send_gives_smpAt   the law.

What is not claimed. One answer a message. On entries of the tables that are no entry of the message
the form reads nothing. The other premises are send_goodIn_entry's (GoodSend4.lean). Nothing on
soundness of a protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSendSmp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)

/-- A plain row, read as a linear form on the entries of the library's message of the shape. -/
def formRow (cs : Codes) (s : OracleShape) (o : Nat) (r : OnBytes.Row) :
    (portCode cs s).J → GE := fun j =>
  match (j : (Fin s.mainRows × Fin (pMain cs s).ell) ⊕ (Fin s.maskRows × Fin (pMask cs s).ell)) with
  | .inl x => coefAt r o .main (x.1.val + 2 ^ k1 s * x.2.val)
  | .inr x => coefAt r o .mask (x.1.val + 2 ^ k2 s * x.2.val)

/-- The first sample row of message number o, as a linear form. -/
def formsAt (cs : Codes) (s : OracleShape) (St : Statement) (o : Nat) :
    Option (Unit → (portCode cs s).J → GE) :=
  (St.oracles[o]?).bind fun x => (x.sampleRows[0]?).map fun r _ => formRow cs s o r

/-- Its target. -/
def ansAt (St : Statement) (o : Nat) : Option (Unit → GE) :=
  (St.oracles[o]?).bind fun x => (x.sampleRows[0]?).map fun r _ => readE r.target

/-- **Where the rows are the kind's one row at a seed, the form is the library's matrix there.** -/
theorem forms_of_seedIs (cs : Codes) (s : OracleShape) (e : Nat) (St : Statement) (o : Nat)
    (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (y : GE) (hT : Tie cs s) (h : SeedIs cs s St o ρ y) :
    formsAt cs s St o = some ((portOmZ cs s e).Z.mat ρ) ∧ ansAt St o = some fun _ => y := by
  obtain ⟨_, x, z, β, t, hx, _, _, hr, hread, ht⟩ := h
  constructor
  · unfold formsAt
    rw [hx, Option.bind_some, hr]
    show some _ = _
    congr 1
    funext u j
    cases u
    cases j with
    | inl a => exact coef_port_main hT e o z β t ρ hread a
    | inr a => exact coef_port_mask hT e o z β t ρ hread a
  · unfold ansAt
    rw [hx, Option.bind_some, hr]
    show some _ = _
    congr 1
    funext _
    exact ht

open Classical in
/-- **A sample, read off the statement**: some seed whose matrix is the form, with the target. -/
noncomputable def smpAt (cs : Codes) (s : OracleShape) (e : Nat) (St : Statement) (o : Nat) :
    Option (portOmZ cs s e).Smp :=
  if h : ∃ ρ, formsAt cs s St o = some ((portOmZ cs s e).Z.mat ρ) then
    (ansAt St o).map fun v => (h.choose, v)
  else none

/-- **It is there where the rows are the kind's.** -/
theorem smpAt_of (cs : Codes) (s : OracleShape) (e : Nat) (St : Statement) (o : Nat)
    (ρ : (Fin (bitsZ cs s) → GE) × GEˣ) (y : GE) (hT : Tie cs s) (h : SeedIs cs s St o ρ y) :
    ∃ z, smpAt cs s e St o = some z ∧ (portOmZ cs s e).Z.val z.1 = (portOmZ cs s e).Z.val ρ ∧
      z.2 = fun _ => y := by
  obtain ⟨h1, h2⟩ := forms_of_seedIs cs s e St o ρ y hT h
  have g : ∃ ρ', formsAt cs s St o = some ((portOmZ cs s e).Z.mat ρ') := ⟨ρ, h1⟩
  refine ⟨(g.choose, fun _ => y), ?_, ?_, rfl⟩
  · unfold smpAt
    rw [dif_pos g, h2]
    rfl
  · have hm : (portOmZ cs s e).Z.mat g.choose = (portOmZ cs s e).Z.mat ρ :=
      Option.some.inj (g.choose_spec.symm.trans h1)
    funext u a
    unfold Sample.val
    rw [hm]

variable {T Cl W : Type} {F : Frame}

/-- **The law of a sending, with the sample read off the statement.** -/
theorem send_gives_smpAt (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true) (b : Block T Cl)
    (stOf : T → Statement) (hS : IsSend P stOf b) (base : Nat) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.imp y τ) =
      fIn y τ.1)
    (On On' : T × F.E.Str → Prop)
    (hkeep : ∀ a τ x, On a →
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
      On' x) :
    ∀ a, On a → Doomed (uLT (ckP .two) [d₁, d₂])
      (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).err fun τ =>
        ∀ x, (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x →
          On' x ∧ ∀ k, sampledAt P k → ∃ z,
            smpAt P.codes (shapeAt P k) (rad k.val) (stOf x.1)
              ((stOf x.1).oracles.size - (shapesOf P).length + k.val) = some z ∧
            ¬ (portOmZ P.codes (shapeAt P k) (rad k.val)).Clash (fOf x.2 k) z.1 :=
  send_gives_smp P rad hC b stOf hS base d₁ d₂ he₁ hk₁ e he fOf fIn hf On On' hkeep
    (fun t k => smpAt P.codes (shapeAt P k) (rad k.val) (stOf t)
      ((stOf t).oracles.size - (shapesOf P).length + k.val))
    fun t k hk ρ y h => by
      obtain ⟨z, h1, h2, _⟩ := smpAt_of _ _ (rad k.val) _ _ ρ y (cond_tie P rad hC k hk) h
      exact ⟨z, h1, h2⟩

/-- A try: at a statement without the message no sample is read. -/
theorem smpAt_none (cs : Codes) (s : OracleShape) (e : Nat) (St : Statement) (o : Nat)
    (h : St.oracles[o]? = none) : smpAt cs s e St o = none := by
  unfold smpAt
  split
  · rename_i g
    obtain ⟨_, hg⟩ := g
    simp [formsAt, h] at hg
  · rfl

end VerifiableInference.Desc.K1
