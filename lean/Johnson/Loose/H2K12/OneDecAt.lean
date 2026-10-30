-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.P5J.MgAtAll
import Johnson.Desc.K14.Law.SharedConstByMake
import Johnson.Desc.K14.Law.SharedConstOpenAt
/-
Johnson/Loose/H2K12/OneDecAt.lean: `Sh.OneDec`
(SharedConstByMake.lean) AT THE LAID MEANING: the first table's meaning `P5J.mgAtAll h`
(MgAtAll.lean) decodes the committed table by the shared chain's own guarded decoder at the shared
chain's first state. A definition, two statements with proofs meant to be by unfolding alone.

What for. `Sh.hdec_by_make`, `Sh.hPW_by_make` (SharedConstByMake.lean) pay the premises hdec and hPW
in front of `Sh.on_zero_at_seat` and `Sh.rel_end_of_zero` from `Sh.OneDec`.
Main names.
  `heldAt Zs Z N hs`: the letter held of the shared table's open letters, laid as `heldFull`
    (Johnson/Desc/Sound/DataAlong.lean) at the arguments at which `P5J.dtK`
    (Johnson/P5J/AtTerm.lean) has it: the seat's parameters, 0, the coding `P5J.At.EAt Zs`.
  `oneDec_at`: at every head h : P5J.AtMgA o Zs D r Z N cF x and every filling of the other open
    letters: `Sh.OneDec` at `planAt Z N (seatF o Z N B' cF)`, at `openAt₀` with held := `heldAt` and
    Mg₁ := `P5J.mgAtAll h`, and at start₂ := (P5J.F0T o Z N cF).start₂.
  `start₂_one`: the two spellings of the IOP as written in Lean (P5J.F0T, seatF) have one start₂.
Why it should hold. `mgAll_decodes`, `mgAll_pinW` (Johnson/Desc/Sound/MgAll.lean): the two fields
are `decodesOf`, `pinWOf` of the structure's decT, by rfl; that decT is `P5J.At.decT … := dtK E o Zp
Np cF hs 0` (Johnson/P5J/LettersAll.lean, LettersAt.lean); `dtK := decShared ‹the seat's parameters›
err 2852142980 (rankLib …) (heldFull …) (F0T …).start₂`; `Sh.rank A := rankLib A.Q.par.S.fold`;
`planAt`'s Q is `p14Of Z.p.chains (beforePointOf N)`.




(Where this and lean/THEOREM.md differ, the page holds.)
What it is not. NO EXAMPLE: no head h is shown. It says nothing on whether the decoder returns. It
pays no law and closes no row.
No soundness and no level is claimed. Nothing on
hiding. No sorry, no axiom of this library's; what each theorem rests on is printed at the end.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K12
open OnBytes OnBytes.Flat OnBytes.Maker
open OnBytes.Slice (GE)
open P5J (CellsM)
open VerifiableInference.OnPublicFiles (ppAtFiles)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (Numbers ModelPart)
open VerifiableInference.Desc.Sound
open Desc.K14 (p14Of beforePointOf)
open Desc.K14.Law (fullShapeB full_index heldFull)
open Desc.K14.Law.Sh (OneDec openAt₀ seatF planAt)

/-- The shared table's letter held, as the first table's decoder has it. -/
def heldAt (Zs : VerifierAndGoals.PublicFiles) (Z : ProofFile.Pub) (N : H2U.Places4)
    (hs : fullShapeB (p14Of Z.p.chains (beforePointOf N)).par.S = true) :=
  heldFull (p14Of Z.p.chains (beforePointOf N)).par 0
    (p14Of Z.p.chains (beforePointOf N)).par.S.fold.index.saltBytes
    (full_index (p14Of Z.p.chains (beforePointOf N)).par.S hs) OnBytes.Flat.numsFull
    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)

variable {o : ProofFile.SecondHashFunctionArgument} {Zs : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Z : ProofFile.Pub}
  {N : H2U.Places4} {cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The first table's decoder is made of the shared chain's, at the laid meaning.** -/
theorem oneDec_at (h : P5J.AtMgA o Zs D r Z N cF x) (B' : ProofFile.SecondSeat)
    (c₀ : P5J.CellsM OnBytes.Flat.numsFull)
    (matC : P5J.CellsM OnBytes.Flat.numsFull → Nat → Nat → OnBytes.Slice.GE)
    (N₁ : VerifiableInference.Desc.First.Numbers) (links : List VerifiableInference.Desc.First.ModelPart)
    (smp₁ : ProofFile.InstPub × VerifiableInference.Desc.First.S →
      (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf (planAt Z N (seatF o Z N B' cF)).Q.codes s.l).om i).Smp)
    (ms₁ : List VerifiableInference.Desc.Sound.Mem) :
    OneDec (planAt Z N (seatF o Z N B' cF))
      (openAt₀ o Z N B' cF c₀ matC (heldAt Zs Z N h.plan.shape)
        ⟨N₁, links, P5J.mgAtAll h, smp₁, ms₁⟩)
      (P5J.F0T o Z N cF).start₂ :=
  ⟨rfl, rfl⟩

/-- The two spellings of the IOP as written in Lean start the shared chain alike. -/
theorem start₂_one (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : Chain VerifiableInference.Desc.First.S ProofFile.Cl) :
    (P5J.F0T o Z N cF).start₂ = (seatF o Z N B' cF).start₂ := rfl

end H2K12

#print axioms H2K12.oneDec_at
#print axioms H2K12.start₂_one
