-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/FrontOfReach.lean: THE SMALLNESS TEST: THE NAMED PREMISE
`AllFrontAtStand` (Johnson/Desc/ProofFile/Honest/K8/ValuesJoin.lean: at every stand of the batching
the state in front shows its data, its ledger, what the lookup heard, `AllFront`'s seventeen and a
member of the link's list for each array) FROM A SMALLER ONE, WHERE THE THREAD's BLOCKS ARE THE
FIRST CHAIN's OWN, IN THE GOALS' SCOPE. Why it goes: a stand holds the thread and "what is said";
from these another house's law reaches the library's "reached"; at a reached state eleven of the
seventeen are shown whole and two in part. A joining; none of the library's goals.

  `reach_at_stand`   a stand · the border lies within the thread's blocks · the thread begins at
                   start z alone · stored words lie below the prime ⊢ the state in front is reached
                   by the thread's own blocks, at the border's number
  `LeftOverAtStand`   THE NAMED PREMISE THAT STAYS: at every stand the state in front shows tl, F,
                   funs and what the lookup heard, `FrontLeftOver`'s eight
                   (Johnson/Desc/K8/Honest/AllFrontAtBatch.lean), and a member of the link's list
                   for each array
  **`allFrontAtStand_of`**   the scope · the files read · an opening of the description · the
                   description's test on its plan · l < 25 · the built segment number l · SIX TIES
                   OF THE THREAD TO THE CHAIN: its first number is 0 · its blocks are the chain's ·
                   its border is 14 l + 9, or 347 at the head's segment · the border lies within
                   its blocks · at all coins and middles it begins at the description's own first
                   state alone · stored words lie below the prime · LeftOverAtStand ⊢
                   AllFrontAtStand
By: `reach_below` (Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean) · the
library's `reach_raw` (Johnson/Top/H0/Walk/Reach.lean) · `allFront_at_batch`.
Limits. AN IMPLICATION STILL: `LeftOverAtStand` and the six ties ARE PAID BY NOBODY HERE AND SHOWN
OF NO THREAD. The fifth tie asks more than is spent: it is asked at all coins and middles and spent
at a stand's alone. PAYERS IN SIGHT, NOT CALLED: the first two ties are the third and fourth clauses
of another house's premise on its first thread (`Sits.one`,
Johnson/Desc/ProofFile/Honest/Thread/File.lean), where the chain is the description's first. NO
MEMBER: that the premises can hold together is not shown; where there is no stand all is idle. IN
SCOPE ALONE: the full size's 25 segments; the first chain. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.ValuesJoin
import Johnson.Desc.K8.Honest.AllFrontAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K9 (BatStand)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

section
variable {Lk : Link S Claim} {p : Desc.K9.Where}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}

/-- A stand's state in front is reached by the thread's own blocks. -/
theorem reach_at_stand {Q : Type} (start : Q → S) (q : Q) {κ : Coins Bk} {s : S} {m : Mid W X}
    {En : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List Desc.OpenedColumn} {s' : S}
    {x : E} {z : S × Desc.K9.Part × List Claim} {G : Fork}
    (hS : BatStand Lk p T b κ s m En ds y cols s' x z G) (hb : b ≤ T.bs.length)
    (h0 : ∀ s₀, T.begun κ m.st.input (m.st.heard.take T.front) s₀ → s₀ = start q)
    (hst : ∀ w i x u, T.stored w i x = some u → ∀ a ∈ u, a < fieldPrimeWord) :
    Reach T.ft T.bs start b (q, s) :=
  reach_raw (reach_below T start q hb h0 hst hS.thr)

variable (Lk p T b) in
/-- **The named premise that stays.** -/
def LeftOverAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ∃ (tl : HTailF2) (F : Fork) (funs : Array HFun) (g : Forest.Heard), s.tl? = some tl ∧
      s.fork? = some F ∧ s.funs? = some funs ∧ tl.heard = some g ∧ FrontLeftOver tl F g ∧
      ∀ a0, Desc.K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **WHERE THE THREAD's BLOCKS ARE THE FIRST CHAIN's OWN.** -/
theorem allFrontAtStand_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl)
    (hft : T.ft = 0) (hbs : T.bs = c.blocksInOrder) (hb : b = 14 * l + (if l = 24 then 11 else 9))
    (hlen : b ≤ T.bs.length)
    (h0 : ∀ (κ : Coins Bk) (m : Mid W X), ∃ q : ProofFile.InstPub,
      ∀ s₀, T.begun κ m.st.input (m.st.heard.take T.front) s₀ → s₀ = ProofFile.startS Z q)
    (hst : ∀ w i x u, T.stored w i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hL : LeftOverAtStand Lk p T b) : AllFrontAtStand Lk p T b := by
  intro κ s m En ds y cols s' x z G hSt
  obtain ⟨tl, Fk, funs, g, ht, hF, hf, hg, L, hT⟩ := hL κ s m En ds y cols s' x z G hSt
  obtain ⟨q, hq⟩ := h0 κ m
  have r := reach_at_stand (ProofFile.startS Z) q hSt hlen hq hst
  rw [hft, hbs, hb] at r
  obtain ⟨nbW, Wn, D⟩ := allFront_at_batch hS hR O hOk hl e3 r ht hF L
  exact ⟨tl, Fk, funs, g, nbW, Wn, ht, hF, hf, hg, D, hT⟩

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.reach_at_stand
#print axioms ProofFile.Honest.K8.allFrontAtStand_of
