-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SizesDigits.lean: THE DECISION OF THE SEATED LOOKUP ON THE DIGITS KEEPS
THE LEDGER's SIZES; so `SizesS` walks the whole stretch, and WalkDigits.lean's three ends
`later_sized_back`, `later_sized_layers`, `later_sized_head` stand without their premise h3.
Theorems: joins of other files' lemmas.
  `sizes_behind_digits`: **a yes of `K3.theStated`'s value at the digits' address, its test on the
    plan passed: where a ledger is open behind, one was open in front, with the same four sizes**
    (`SizesS`, SizesStretch.lean). How: `theStated_yes_digits` cuts the yes into a yes of
    `K3.block`'s decision and the step without a round behind it; `decide_sameLen`
    (Johnson/Top/H/Keep/PadSizes.lean) has the four equations at the first; `quietAt_sizesS`
    (SizesStretch.lean) has the second.
  `k3_sizesS`: that, as `WalkKeeps`' field k3. `sizesS_walk`: **`WalkKeeps SizesS`, with no
    premise.**
  `laterSized_back`, `laterSized_layers`, `laterSized_head`: **where the state in front of the
    batching holds a ledger with its sizes: ONE state s reached at the earlier border (14 l + 6; 28
    g + 5; 343), whose ledger F has its sizes, with the later ledger a later state of F, and R s
    s'**, for any R that walks.
PREMISES. The scope (hS, hR, `IM.Open`); hp: every sub-protocol of the first chain passes its test
on the plan; "reached"; hB: the ledger in front of the batching is open and has its sizes.
Limits. hp and hB are shown of nothing here. On the decisions alone. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.WalkDigits
import Johnson.Top.H.Keep.PadSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.OnPublicFiles (theStated_yes_digits decide_exact decide_sameLen seatDigits_keeps)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **THE SEATED LOOKUP ON THE DIGITS KEEPS THE LEDGER's SIZES.** -/
theorem sizes_behind_digits {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (i : ℕ) (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) : Decides SizesS B := by
  intro s rs gs c hd
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  obtain ⟨F, x, hF, e, L⟩ :=
    decide_sameLen (K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  obtain ⟨_, _, _, hn, -, -⟩ :=
    decide_exact (K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  have hsome : ((K3.seatDigits claim).fork s).isSome = true := by
    rw [hF]
    rfl
  have hy : s'.fork? = some x.2 := by
    rw [e]
    exact seatDigits_keeps claim _ _ _ hsome hn
  have q1 : SizesS s s' := fun G' hG' => by
    obtain rfl : x.2 = G' := Option.some.inj (hy.symm.trans hG')
    exact ⟨F, hF, L⟩
  rcases hstep with rfl | ⟨f, hf, hfs⟩
  · exact q1
  · exact SizesS.trans _ _ _ q1 (quietAt_sizesS X i f hf s' c hfs)

/-- `WalkKeeps`' field k3 at `SizesS`. -/
theorem k3_sizesS (claim : Aff → ProofFile.Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block S ProofFile.Cl) (i : ℕ) (h : K3.theStated claim readers X codes shape a = some B)
    (hOk : B.planOk = true) (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) :
    Decides SizesS B := sizes_behind_digits claim readers X codes shape a B i h hOk hi hpc

/-- **`SizesS` WALKS.** -/
theorem sizesS_walk : WalkKeeps SizesS := sizesS_walks k3_sizesS

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S} {R : S → S → Prop}

/-- **ONE STATE: ITS LEDGER HAS ITS SIZES, THE LATER LEDGER IS A LATER STATE OF IT, AND R.** -/
theorem laterSized_back (K : WalkKeeps R)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 24) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s'))
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ s F F', Reach 0 c.blocksInOrder start (14 * l + 6) (z, s) ∧ s.fork? = some F ∧ Sized F ∧
      s'.fork? = some F' ∧ PscRun.Later F F' ∧ R s s' :=
  later_sized_back K k3_sizesS hS hR O hp hl h hB

theorem laterSized_layers (K : WalkKeeps R)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s'))
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ s F F', Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ s.fork? = some F ∧ Sized F ∧
      s'.fork? = some F' ∧ PscRun.Later F F' ∧ R s s' :=
  later_sized_layers K k3_sizesS hS hR O hp hg h hB

theorem laterSized_head (K : WalkKeeps R)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ s F F', Reach 0 c.blocksInOrder start 343 (z, s) ∧ s.fork? = some F ∧ Sized F ∧
      s'.fork? = some F' ∧ PscRun.Later F F' ∧ R s s' :=
  later_sized_head K k3_sizesS hS hR O hp h hB

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.sizes_behind_digits
#print axioms VerifiableInference.Desc.LinkJoin.k3_sizesS
#print axioms VerifiableInference.Desc.LinkJoin.sizesS_walk
#print axioms VerifiableInference.Desc.LinkJoin.laterSized_back
#print axioms VerifiableInference.Desc.LinkJoin.laterSized_layers
#print axioms VerifiableInference.Desc.LinkJoin.laterSized_head
