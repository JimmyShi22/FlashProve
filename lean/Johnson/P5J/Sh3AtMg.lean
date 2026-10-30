-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/Sh3AtMg.lean: THE FIELD SH₃ OF `tables_fit` AT THE TOWER's LETTERS, FOR FIVE NAMED
PREMISES. One structure, one definition, one theorem, two examples.

Why. `VerifiableInference.Desc.Last.sh₃_field` (Johnson/Desc/Last/ShapeDoorField.lean) has the text
of the field SH₃ of `TablesFitR` (Johnson/P5J/TopTablesR.lean) at the seated description's types.
It is general in the shared table's promise's meaning, the last table's book-keeping, the pieces
and the numbers.
Here it is called at the letters at which `AtMg.Three` and `AtMg.ThreeLeft` ask the field.

  `AtMg.Sh3Prem h 𝔇₀ 𝔏 R Pw V X`: that theorem's own five premises, at these letters (below).
  `AtMg.Sh3Owed h 𝔇₀ 𝔏`: some R, Pw, V and X meet the five together.
  **`AtMg.sh3_field`**: h.Sh3Owed 𝔇₀ 𝔏 gives the field SH₃, in its own text, at the tower's letters.
    General in the second hash function, in 𝔇₀ and in 𝔏.
  The five:
    H : `DoorStays` of the first table's numbers, meaning and lists, at a place Pw and own seats V.
    hR: inside the first table's last promise, under h.rc, without a failure mark: `FourFacts V` of
      the first chain's last state.
    hD, hX: where 𝔏.Pm's test at the shared chain's last border accepts, the shared chain's text at
      the door holds (`doorSharedB`), and a test X accepts.
    hPL: where `fillZ`'s book-keeping accepts at border 0 and X accepts, 𝔏.PLm's accepts at
      border 0.
  That theorem's hZ and hg are paid here: hZ by the head (h.laid.pub), hg by rfl.
  The two examples lay it into `h.Three 𝔇₀ 𝔏` and into `h.ThreeLeft 𝔇₀ 𝔏`: that it fits is Lean's
    word.

Who could pay hPL. Where 𝔏.PLm is the last table's meant book-keeping, hPL is, by reading,
`shape0_at_layers` (Johnson/LTPileR/DoorAtPlm.lean).
It is not called here.
Limits. It swaps the field for five premises and four letters (R, Pw, V, X).
That one choice of these meets all five together, at any 𝔏, is not shown here; the payer's own head
says the same of V, Pm, PLm and Rc.
That the conclusion's two fences are met anywhere (the shared table's promise at its last border;
the last chain's start accepts) is not shown either.
No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.ThreeLeft
import Johnson.Desc.Last.ShapeDoorField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ

open VerifierAndGoals.AtTheName
open VerifiableInference.Desc (Chain KindName)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  (h : AtMg o Z D r Zp Np cF) {nR : ℕ}
  (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
  (𝔏 : Free numsFull D (F0T o Zp Np cF) At.Tok)

set_option quotPrecheck false in
/-- The first chain's state as the table reads it. -/
local notation "GT" => (fun a : (F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁ =>
  ((a.1, (fun s => s) a.2) : (F0T o Zp Np cF).XiPub × TS))

set_option quotPrecheck false in
/-- The three rows of pieces. -/
local notation "TW" => (piecesAt (ckP .two) (F0T o Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂
  𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd)

set_option quotPrecheck false in
/-- The shared table's numbers, tied to the first table's. -/
local notation "NT" => tiedNumbers (At.N Zp cF) 𝔏.Ns

set_option quotPrecheck false in
/-- The shared table's meaning, tied to the first table's. -/
local notation "MT" => tiedMeaning GT (h.mq 𝔇₀) 𝔏.MgS

set_option quotPrecheck false in
/-- The two later tables' own condition. -/
local notation "OC" => ocR GT (At.N Zp cF) (h.mq 𝔇₀) fullLinks At.ps h.rc

/-- **What `sh₃_field` asks, at the tower's letters**, for a list of rounds R, a place Pw, own seats
V and a test X on the shared chain's last state. -/
structure AtMg.Sh3Prem (R : List Fmt.DeclaredRound) (Pw : VerifiableInference.Desc.K13.Where)
    (V : OwnSeats) (X : _root_.Desc.K14.St → Bool) : Prop where
  /-- what the door still asks of the first table's meaning and lists: seven closed facts -/
  H : DoorStays (At.N Zp cF) (h.mq 𝔇₀) fullLinks At.ps Pw V
  /-- inside the first table's last promise, under h.rc, without a failure mark: the four facts -/
  hR : ∀ q y, ocEnd GT (At.N Zp cF) (h.mq 𝔇₀) fullLinks At.ps q y → h.rc q →
    (GT q).2.failed = none → FourFacts V (GT q).2
  /-- where 𝔏.Pm's test at the shared chain's last border accepts, its text at the door holds -/
  hD : ∀ d, 𝔏.Pm.shape (1 + (TW).l₂.length) d = true → doorSharedB (ProofFile.pAt Zp) d = true
  /-- and X accepts -/
  hX : ∀ d, 𝔏.Pm.shape (1 + (TW).l₂.length) d = true → X d = true
  /-- where `fillZ`'s book-keeping and X accept, 𝔏.PLm's book-keeping accepts, at border 0 -/
  hPL : ∀ q e s, (fillZ (ProofFile.pAt Zp) R fun q => (GT q).2).shape 0 q e s = true → X e = true →
    𝔏.PLm.shape 0 q e s = true

/-- Some R, Pw, V and X meet the five together. -/
def AtMg.Sh3Owed : Prop := ∃ R Pw V X, h.Sh3Prem 𝔇₀ 𝔏 R Pw V X

/-- **The field SH₃ at the tower's letters.** -/
theorem AtMg.sh3_field (S : h.Sh3Owed 𝔇₀ 𝔏) :
    ∀ (b : (((F0T o Zp Np cF).XiPub × (F0T o Zp Np cF).S₁) × (F0T o Zp Np cF).S₂) ×
        (EAll (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))).Str) (s : (F0T o Zp Np cF).S₃),
      onQ₂ NT 𝔏.Pm OC 𝔏.split (TW).p₂ (TW).l₂ (1 + (TW).l₂.length) b →
      ((F0T o Zp Np cF).start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s →
      𝔏.PLm.shape 0 (b.1.1.1, b.1.1.2) b.1.2 s = true := by
  obtain ⟨R, Pw, V, X, S⟩ := S
  exact sh₃_field o Z.pol Z.lay Z.KL Zp h.laid.pub Np cF R GT (fun _ _ => rfl) TW NT 𝔏.Pm 𝔏.PLm
    𝔏.split (At.N Zp cF) (h.mq 𝔇₀) fullLinks At.ps Pw V S.H h.rc S.hR X S.hD S.hX S.hPL

/-- It is the field SH₃ of `h.Three`'s own tables_fit. -/
example (S : h.Sh3Owed 𝔇₀ 𝔏) (W : h.Three 𝔇₀ 𝔏) : h.Three 𝔇₀ 𝔏 :=
  ThreeF.mk W.head_cuts W.reply_leaves { W.tables_fit with SH₃ := h.sh3_field 𝔇₀ 𝔏 S }

/-- It is the field SH₃ of `h.ThreeLeft`'s own tables_left. -/
example (S : h.Sh3Owed 𝔇₀ 𝔏) (W : h.ThreeLeft 𝔇₀ 𝔏) : h.ThreeLeft 𝔇₀ 𝔏 :=
  ThreeLeftF.mk W.head_cuts { W.tables_left with SH₃ := h.sh3_field 𝔇₀ 𝔏 S }

end P5J

#print axioms P5J.AtMg.sh3_field
