-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ToldAtD.lean: THE BINDER hTold OF
k01_fifty_atBase, TO ITS LETTER, WITH THE PREMISE ON THE THREE LISTS OF ROUNDS TURNED INTO ONE ON
THE DATA. Where the three lists are bound by "there are" (at the laying over the three chains' cap),
nothing says which lists they are; what is in hand there is a sentence on the data.

  hTold_atD        the end of hTold_at [not in this library];
                   in the place of eR (the three lists are the written ones):
                   eD: THE FIRST CHAIN's LIST OF ROUNDS' DATA IS THE WRITTEN LISTS' (all that the
                   proof spends of the lists on the data's side); ht, hT: AT THE WRITTEN LISTS: two
                   closed facts. hWr and hRoots stay at R₁.

The proof is that of hTold_at [not in this library], but for the data's half:
dataHalf_of (Johnson/Desc/AtSeats/DataHalfWritten.lean) at
letters, laid at the written lists behind eD: so that the written lists are never unfolded.
What is not claimed. Any of the premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.LettersAtFifty
import Johnson.Desc.K1.Law.TellsAtFifty
import Johnson.Desc.AtSeats.DataHalfWritten
import Johnson.Desc.AtSeats.DeclHalfOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Johnson.G Desc.Plain
open OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open k1Ix)

theorem hTold_atD {Xi : Type} {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {e₁ : List (List ByteArray × ByteArray)} (G : FileDescription Xi)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hRoots : ∀ r ∈ R₁, r.1.items.countP (· == .root) = r.1.entry.roots)
    (eD : (dataOf aN R₁ R₂ R₃).ds₁ =
      (dataOf aN dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).ds₁)
    (eG : ∀ j, G.oracleAt j = F.oracleAt j)
    (ht : 83 ≤ Three.rootsIn dryProofFull.1)
    (hT : nTrees (dataOf aN dryProofFull.1 dryProofFull.2.1 dryProofFull.2.2).ds₁ ≤ 83)
    (h4 : ∀ l, l < 25 → ∀ d : Bool, ∀ n, n < (layOf (parL Z Bs.G₀ l d)).shapes.size →
      HashBuild.laidFull[nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c (noL l d))) + n]? =
        some (((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).logN,
          ((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).mainWidth +
            ((layOf (parL Z Bs.G₀ l d)).shapes.getD n {}).maskWidth)) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ d₁ d₂ : RDT, d₁.entry = seedEntry (parL Z Bs.G₀ l d) →
      d₁.kind = .seeds →
      ((dataOf aN R₁ R₂ R₃).ds₁.drop (inFront c (noL l d))).take 2 = [d₁, d₂] →
      ∀ n sh, treeShT [d₁, d₂] n = some sh → ∀ o,
      G.oracleAt (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c (noL l d))) + n) = some o →
      o.logLength = sh.a ∧ o.words = sh.W := by
  intro l hl d d₁ d₂ _ _ e n sh h o ho
  -- what the place declares
  obtain ⟨decl, hdecl, hD⟩ : ∃ decl, (toldBy c.blocksInOrder)[noL l d]? = some decl ∧
      Declares decl (layOf (parL Z Bs.G₀ l d)) (parL Z Bs.G₀ l d).sent.size
        (tenantOf (parL Z Bs.G₀ l d)) := by
    cases d with
    | true => exact tells_digits hS hR O (fun b hb => (hOk b hb).1) l hl
    | false => exact tells_reads hS hR O (fun b hb => (hOk b hb).1) l hl
  -- the room behind the place
  obtain ⟨x, X, arrs, hflat, hu⟩ := k01_flat hS hR O l hl d
  obtain ⟨e7, hflat7, _, hu7⟩ := K13.Law.k13_sits_flat357 hS hR O
  have hk : noL l d < 357 := by
    have : k1Ix l d ≤ 6 := by unfold k1Ix; split <;> split <;> omega
    show 14 * l + k1Ix l d + 2 < 357
    omega
  have hroom := K13.Law.room_of_later c.blocksInOrder (noL l d) 357 x e7 hflat hflat7 hk
    (by rw [hu7.1]; exact Nat.zero_lt_one)
  have hx2 : x.rounds.length = 2 := by
    rw [hu.1]
    show (blkL Z Bs.G₀ l d X arrs).rounds.length = 2
    rw [rounds_blk]
    rfl
  have hsh : ∀ b ∈ c.blocksInOrder, b.shaped = true := fun b hb => (hOk b hb).2
  have hin : inFront c (noL l d + 1) = inFront c (noL l d) + 2 := by
    unfold inFront
    rw [List.take_add_one, hflat]
    simp [hx2]
  have hr0 : _root_.Desc.K14.Law.roundsIn (c.blocksInOrder.take (noL l d)) = inFront c (noL l d) := rfl
  have hr1 : _root_.Desc.K14.Law.roundsIn (c.blocksInOrder.take (noL l d + 1)) =
      inFront c (noL l d + 1) := rfl
  have b1 : nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c (noL l d))) =
      First.treesTold (toldBy c.blocksInOrder) (noL l d) :=
    nTrees_front aN R₁ R₂ R₃ c.blocksInOrder hWr hRoots hsh (noL l d) (by omega)
  have b2 : nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c (noL l d) + 2)) =
      First.treesTold (toldBy c.blocksInOrder) (noL l d + 1) := by
    rw [← hin]
    exact nTrees_front aN R₁ R₂ R₃ c.blocksInOrder hWr hRoots hsh (noL l d + 1) (by omega)
  have tt : First.treesTold (toldBy c.blocksInOrder) (noL l d + 1) =
      First.treesTold (toldBy c.blocksInOrder) (noL l d) + decl.length := by
    unfold First.treesTold
    rw [List.take_add_one, hdecl]
    simp
  -- the three
  have hDa : HashBuild.DataHalf (dataOf aN R₁ R₂ R₃).ds₁ (inFront c (noL l d))
      (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c (noL l d)))) := by
    have key : ∀ W₁ W₂ W₃ : Rounds,
        (∀ r sent i sh, (Three.rdOf (Three.Whole.of W₁ W₂ W₃).opens (Three.rootsIn W₁)
          (Three.rootsIn W₂) 0 0 0 r sent).trees[i]? = some sh → sent + i < 83 →
          HashBuild.laidFull[sent + i]? = some (sh.a, sh.W)) →
        nTrees (dataOf aN W₁ W₂ W₃).ds₁ ≤ 83 →
        HashBuild.DataHalf (dataOf aN W₁ W₂ W₃).ds₁ (inFront c (noL l d))
          (nTrees ((dataOf aN W₁ W₂ W₃).ds₁.take (inFront c (noL l d)))) :=
      fun W₁ W₂ W₃ H hT' => HashBuild.dataHalf_of W₁ W₂ W₃ H hT' (inFront c (noL l d))
    rw [eD]
    exact key _ _ _ (fun r sent i sh h hi => HashBuild.trees_of_round _ _ ht r sent i sh h hi) hT
  have hC : HashBuild.CountTie (dataOf aN R₁ R₂ R₃).ds₁ (inFront c (noL l d)) decl.length :=
    HashBuild.countTie_of (s := First.treesTold (toldBy c.blocksInOrder) (noL l d)) b1 (b2.trans tt)
  obtain rfl : F = _ := O.desc
  have hG : HashBuild.DeclHalf
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (nTrees ((dataOf aN R₁ R₂ R₃).ds₁.take (inFront c (noL l d)))) decl.length :=
    HashBuild.declHalf_of
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (noL l d) decl hdecl _ b1
      (fun τ => (((layOf (parL Z Bs.G₀ l d)).shapes.getD τ {}).logN,
        ((layOf (parL Z Bs.G₀ l d)).shapes.getD τ {}).mainWidth +
          ((layOf (parL Z Bs.G₀ l d)).shapes.getD τ {}).maskWidth))
      (fun τ Oo hO => by
        obtain ⟨a, b, _⟩ := hD.shape τ Oo hO
        rw [a, b])
      (fun n hn => h4 l hl d n (by rw [← hD.trees]; exact hn))
  rw [eG] at ho
  exact HashBuild.told_of_halves hDa hG hC d₁ d₂ e n sh h o ho

end VerifiableInference.Desc.K1
