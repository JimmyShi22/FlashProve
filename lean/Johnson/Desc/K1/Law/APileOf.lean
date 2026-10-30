-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.ReaderAtLater
import Johnson.Desc.K13.Law.ReaderFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker Desc.Plain
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Item Pub Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (MsgT Sending Mem linksFull)
open VerifiableInference.Desc.K13.Law (openAt MgK13 PlanK13 reader_four pileMasksItem seatsItem)
open OnBytes.Model.Stages (LinkH)

/-- The block at (l, d) is one of the two later blocks. -/
theorem later_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : ∃ own, Later (blkL Z G l d X arrs) own := by
  cases d with
  | true => exact ⟨_, .digits G.first (gpOf Z) l _ arrs⟩
  | false => exact ⟨_, .reads Z G l X _ arrs⟩

/-- It declares two rounds. -/
theorem rounds_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : (blkL Z G l d X arrs).rounds.length = 2 := by
  cases d with
  | true => rfl
  | false => exact rounds_k1Reads Z G l X _ arrs

/-- **THE TOP's ARM aPile, AS A CALL.** -/
theorem aPile_of {Xi Cells Tok : Type} {nR : ℕ} {P : K13.Where} {N : Numbers}
    {Mg : Meaning ProofFile.InstPub (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : ProofFile.InstPub × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid}
    (hMg : MgK13 P N Mg cs sh ly rest arr mat G smp ms decT M L)
    (hPl : PlanK13 ProofFile.InstPub N cs ms M L) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (d : Bool)
    (hkIn : pileMasksItem ∈
      (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [])
    (hsIn : seatsItem ∈
      (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [])
    (hI : Item.pinI ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d))
    (base : ℕ) (X : LinkH) (arrs : Option (List ℕ)) (x x' : ProofFile.InstPub × S) (y y' : Strs)
    (w : Desc.Wit Cells Tok MsgT) (hY : YesOf (blkL Z G₀ l d X arrs) x x')
    (hIn : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x y)
    (_hK : KeptBelow base y y') (hw : Mg.pile x' y' w) : Mg.pile x y w := by
  obtain ⟨-, rs, gs, hfit, hd⟩ := hY
  obtain ⟨own, hB⟩ := later_blkL Z G₀ l d X arrs
  -- two rounds
  have hlen : rs.length = 2 := (Keeps.fit_length _ _ hfit).trans (rounds_blkL Z G₀ l d X arrs)
  obtain ⟨r₁, r₂, rfl⟩ : ∃ r₁ r₂, rs = [r₁, r₂] := by
    match rs, hlen with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  -- what the promise in front holds
  obtain ⟨hon, hm⟩ := hIn
  unfold First.onAt at hon
  obtain ⟨-, hrest⟩ := hon
  rcases hrest with hx | ⟨h1, -, -, -⟩
  · exact absurd hm hx
  simp only [Bool.and_eq_true] at h1
  obtain ⟨⟨-, c5⟩, c6⟩ := h1
  unfold First.pubHeld at c5
  rw [List.all_eq_true] at c5
  have hQ : ∀ q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [],
      Mg.pub q x = true := fun q hq => c5 q (List.mem_append_left _ hq)
  have hit : Mg.pub .indexThere x = true := by
    refine c5 _ (List.mem_append_right _ ?_)
    unfold First.pubOfItems
    rw [List.mem_flatMap]
    exact ⟨.pinI, hI, by simp⟩
  obtain ⟨hOn, hlt, hsz, htree⟩ := reader_four _ hMg hPl hkIn hsIn x _ hQ hit c6
  exact (hMg.ours.pile x y w).2
    (pileBack_book hB arr mat x x' w _ _ gs hd hOn hlt hsz htree ((hMg.ours.pile x' y' w).1 hw))

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.later_blkL
#print axioms VerifiableInference.Desc.K1.rounds_blkL
#print axioms VerifiableInference.Desc.K1.aPile_of
