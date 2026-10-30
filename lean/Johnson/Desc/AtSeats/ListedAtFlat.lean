-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/ListedAtFlat.lean: THE FIELD "listed" OF `PlanAt`
(Johnson/Desc/K1/Law/NewAtSending.lean: the stretch's trees are listed in the frame) AT ANY
SENDING OF THE PROOF FILE's FIRST CHAIN, AT THE DATA's OWN TWO ROUNDS: NO PREMISE BEYOND WHAT THE
TIES HAVE IN HAND (the scope; the four on the pieces' row; the fit of the chain). Statements with
their proofs: calls. WHY. The payers of the premises hNew at number 356 and number 2 asked
`PlanAt` whole, though no piece is named in their binder. A piece stands at every number of the
row: so its own "listed" (`listed_at_cut`,
Johnson/Desc/K1/Law/PlanAtData.lean) can be had. `piece_at_flat`: where the flat list has a
  sub-protocol at number k, the row of pieces has a piece there. `listed_at_flat`: so "listed" at
  the base and the two rounds that the cut gives that piece (`letters_at_flat'`,
  Johnson/Desc/K1/Law/LettersAtFifty.lean). `listed_at_W`, `listed_at_G`: at number 356 (W's
  commitment) and at number 2 (the first segment's opening).
What is not claimed. The premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.LettersAtFifty
import Johnson.Desc.K1.Law.PlanAtData
import Johnson.Desc.K1.Law.HWOf
import Johnson.IMR.FirstUnder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {a : ℕ} {R₁ R₂ R₃ : Rounds} {e₁ : List (List ByteArray × ByteArray)} {all : List LeftT}
  {X₁ X₂ W : Type}
  {T : ThreeAt (ckP .two) (dataOf a R₁ R₂ R₃) all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ W}
  {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
  {rest₁ : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two)
    (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) (ProofFile.InstPub × S) W ds}
  {r : Fmt.RoundView}

/-- Where the flat list has a sub-protocol, the row has a piece. -/
theorem piece_at_flat (hT : OfDesc _ T)
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁) (k : ℕ)
    (e : Block S Cl) (hflat : c.blocksInOrder[k]? = some e) : ∃ q, (T.p₁ :: T.l₁)[k]? = some q := by
  have hB := cutBlocks _ _ _ _ _ rest₁ [r] l₁ b₁ 0 0 (dataOf a R₁ R₂ R₃).ds₁
  rw [← hC] at hB
  have hb : b₁ :: l₁ = (c.blocksInOrder.map below).map (Block.lift Prod.snd fun t s => (t.1, s)) :=
    hB.symm.trans hT.b₁
  have h2 := congrArg (fun l => l[k]?) (hB.trans hb)
  simp only [List.getElem?_map, hflat, Option.map_some] at h2
  exact (Option.map_eq_some_iff.1 h2).imp fun q h => h.1

/-- **"listed", at any sending of the first chain.** -/
theorem listed_at_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hT : OfDesc _ T)
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁) (dep : ℕ → Option ℕ)
    (hFit : ChainFit (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) dep 0
      b₁ l₁ (dataOf a R₁ R₂ R₃).ds₁ [r]) (k : ℕ) (hk : k < 357) (e : Block S Cl)
    (hflat : c.blocksInOrder[k]? = some e) (Q : Par) (hrd : e.rounds = rounds Q) (d₁ d₂ : RDT)
    (hds : ((dataOf a R₁ R₂ R₃).ds₁.drop (inFront c k)).take 2 = [d₁, d₂]) :
    ListedAt (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁)
      (nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront c k))) [d₁, d₂] := by
  obtain ⟨d₁', d₂', _, _, hds', hL⟩ := letters_at_flat' hS hR O hT hC hWr k hk e hflat Q hrd
  obtain ⟨q, hq⟩ := piece_at_flat hT hC k e hflat
  have hl := listed_at_cut rest₁ [r] dep l₁ b₁ 0 0 _ hFit q
    (by rw [← hC]; exact List.mem_of_getElem? hq)
  have e1 := hL q hq e
  have eb : q.base = nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront c k)) :=
    congrArg Sound.Piece.base e1
  have ed : q.ds = [d₁', d₂'] := congrArg Sound.Piece.ds e1
  rw [eb, ed, ← hds', hds] at hl
  exact hl

/-- **At W's commitment.** -/
theorem listed_at_W (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hT : OfDesc _ T)
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁) (dep : ℕ → Option ℕ)
    (hFit : ChainFit (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) dep 0
      b₁ l₁ (dataOf a R₁ R₂ R₃).ds₁ [r]) (d₁ d₂ : RDT)
    (hds : ((dataOf a R₁ R₂ R₃).ds₁.drop (inFront c 356)).take 2 = [d₁, d₂]) :
    ListedAt (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁)
      (nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront c 356))) [d₁, d₂] := by
  obtain ⟨_, e, msg, hflat, _, _, hu⟩ := K13.Law.k13_sits_flat hS hR O
  exact listed_at_flat hS hR O hT hC hWr dep hFit 356 (by omega) e hflat (parWZ Z msg) hu.1 d₁ d₂
    hds

/-- **At the first segment's opening.** -/
theorem listed_at_G (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hT : OfDesc _ T)
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁) (dep : ℕ → Option ℕ)
    (hFit : ChainFit (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁) dep 0
      b₁ l₁ (dataOf a R₁ R₂ R₃).ds₁ [r]) (d₁ d₂ : RDT)
    (hds : ((dataOf a R₁ R₂ R₃).ds₁.drop (inFront c 2)).take 2 = [d₁, d₂]) :
    ListedAt (Sound.frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁)
      (nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront c 2))) [d₁, d₂] := by
  obtain ⟨e, nm, X, hflat, _, hu⟩ := IM.first_under hS hR O
  exact listed_at_flat hS hR O hT hC hWr dep hFit 2 (by omega) e hflat
    (firstPar Bs.G₀.first (gpOf Z))
    (hu.1.trans (by first | rfl | (unfold openingZero; simp; done))) d₁ d₂ hds

end

end VerifiableInference.Desc.K1
