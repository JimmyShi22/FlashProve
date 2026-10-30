-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameAtAll.lean:
FrameOwed9 (FramePaid9.lean) AT THE CLOSED CONSTANT: Dm := dmOf h, the structure of the
composed meaning's parameters under the one head AtMgA (Johnson/P5J/MgAtAll.lean): four of its eight
fields hold there outright.

  dmOf              the term for that structure (AtMgA.𝔇, h.𝔇), under a name in plain letters

  meant_whole       three parameters of dmOf h are the meant terms (MeantAt,
                    Johnson/Top/H0/Walk/FrameReadKeptAt.lean): the reader of OOD samples by the
                    listed seats; a decoder that reads no state; a request read off the public part
  frameOwed9_atAll  FrameOwed9 (dmOf h) Zp T Kn Z.lay from the four fields that are left: low,
                    fence, carryElseLaid, carryElseClear. PAID THERE: carryIs (by definition),
                    headIs (FrameHeadOpen.lean's headOpen_of_req, the parameter being the output
                    head's own term by definition), kept (readKept_meant), d1 (d1Fits_at)

Limits. The head AtMgA is not shown to be meetable here. T is a letter. No soundness statement.

-/
import Johnson.P1L20R.FramePaid9
import Johnson.Top.H0.Walk.FrameReadKeptAt
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Caller (carryAtZ rest)
open Johnson.Desc.First.Walk (layFront)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Part 5's structure of the composed meaning's parameters under its head, by a name in plain
letters. -/
noncomputable abbrev dmOf (h : AtMgA o Z D₀ r Zp Np cF x) := h.𝔇

/-- **Three parameters of the constant are the meant terms.** -/
theorem meant_whole (h : AtMgA o Z D₀ r Zp Np cF x) :
    MeantAt (dmOf h) (P5J.At.seats Zp)
      (fun p => (Meaning.backReq (P5J.At.reqB p)).getD P5J.At.d₀) :=
  ⟨rfl, P5J.At.noRec_decT o Zp Np cF (P5J.At.EAt Z) h.plan.shape, fun _ => rfl⟩

variable {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {C : CK} {D : WholeD}
  {all : List LeftT} {X₁ X₂ : Type}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp A B (fun s => s) (ProofFile.startS Zp) c)
    X₁ X₂ (Wit (CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull)) P5J.At.Tok
      MsgT)}
  {Kn : ℕ → ProofFile.InstPub × S → Strs → Prop}

/-- **FrameOwed9 at the constant**, from the four fields that are left. -/
theorem frameOwed9_atAll (h : AtMgA o Z D₀ r Zp Np cF x)
    (low : ∀ k, k ∈ our51 → ∀ q, (T.p₁ :: T.l₁)[k]? = some q → LowAt (dmOf h).N (openL9 k) q.base)
    (fence : ∀ k, k ∈ our51 → ∀ q, (T.p₁ :: T.l₁)[k]? = some q → ∀ m,
      openP9 (k + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands = .link → ∀ p s y,
      InAt9 (dmOf h) Kn k (p, s) y → CarryFence Zp m q.base (rest s))
    (carryElseLaid : ∀ l, l < 25 → ∀ q, (T.p₁ :: T.l₁)[14 * l + 1]? = some q → ∀ m,
      openP9 (14 * l + 1 + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands ≠ .link →
      GoesBack (StepRel (Yes (layFront l)) q.base (InAt9 (dmOf h) Kn (14 * l + 1)))
        ((dmOf h).cr1 m))
    (carryElseClear : ∀ l, l < 25 → ∀ fs f,
      Johnson.Desc.First.Walk.Seat.framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs →
      fs[l]? = some f → ∀ q, (T.p₁ :: T.l₁)[clearIx l]? = some q → ∀ m,
      openP9 (clearIx l + 1) (.carry m) → (ProofFile.pAtK2 Zp m).stands ≠ .link →
      GoesBack (StepRel (Yes f.clear) q.base (InAt9 (dmOf h) Kn (clearIx l))) ((dmOf h).cr1 m)) :
    FrameOwed9 (dmOf h) Zp T Kn Z.lay where
  carryIs := rfl
  headIs := fun Op hOp R hreq => headOpen_of_req (dmOf h) _ _ _ _ _ _ _ _ _ _ _ rfl Op hOp R hreq
  kept := fun _ _ q _ => readKept_meant (meant_whole h) q.base
  low := low
  d1 := d1Fits_at Zp
  fence := fence
  carryElseLaid := carryElseLaid
  carryElseClear := carryElseClear

end

end P1L20

#print axioms P1L20.meant_whole
#print axioms P1L20.frameOwed9_atAll
