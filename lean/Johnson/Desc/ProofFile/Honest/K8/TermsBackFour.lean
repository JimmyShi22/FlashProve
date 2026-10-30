-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/TermsBackFour.lean: THE SMALLNESS TEST: THE SENTENCE `TermsBack` OF
THE ITEM "totalB" (Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean, another house's file) AT THE
LIBRARY's TERM `tmFour` (Johnson/Desc/First/Link/Law/LinkRestAtSort2.lean): at a stand of the
batching every coefficient of the four terms, at what is fixed in front and the witness's data in
front, is 0: UNDER SIX NAMED PREMISES. A joining of Johnson/Desc/K8/Honest/FourFacts.lean (the
algebra, from one bundle of facts) with Johnson/Desc/ProofFile/Honest/K8/RunAtStand.lean (the run's
own yes, fetched out of the gatherer's). None of the library's goals.

  `LaterRun Lk`   a named premise: each run that the order names hands on "a ledger is open and is
                   later than U", at every U that has its sizes
  `LaterDraw p`   a named premise: the draw's yes lays that sentence at the ledger in front
  **`termsBack_vals`**   SealLaw … → K8At Lk k pW → LaterRun Lk → LaterDraw p → (Ok gives the
                   snapshot's sizes) → (AT A STAND, Ok and Front give FourFacts) → TermsBack … (fun
                   n q y => numbered n (vals4 π (ent4 π) q y)) Front
  **`termsBack_four`**   the same at π := pi8: TermsBack … tmFour Front
Limits. AN IMPLICATION: IT MOVES THE DEBT AND PAYS NONE: OF ITS SIX PREMISES NONE IS PAID HERE.
WHERE THE DEBT THEN LIES: `FourFacts` IS HEAVY, AND IT IS NOT SHOWN THAT AN HONEST STAND MEETS IT:
it is asked at a stand, with the stand in hand: so what comes off the thread (that the lookup's
heard structure stands) can be laid there, and what comes off the open items' meanings through the
free letter Front; its three ties of the letters to the data's cells and mask row are not shown.
"Ok gives the snapshot's sizes" is a sentence on the other house's letter Ok. `LaterRun`:
Johnson/Desc/ProofFile/Honest/K8/LaterRunAt.lean pays it at each sort but for the sort's ties and
the lookups' entries. `LaterDraw`: paid at every place p, with no premise: `laterDraw_at`
(Honest/K9/LaterDrawAt.lean).
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.RunAtStand
import Johnson.Desc.ProofFile.Honest.K8.CountsFrontSeal
import Johnson.Desc.K8.Honest.FourFacts
import Johnson.Desc.First.Link.Law.LinkRestAtSort2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.First.K8.Honest (parts_of FourFacts vals4_of_facts)
open VerifiableInference.Desc.K9L (Pub9 Bound GE8 vals4 numbered_zero fixed9 pubOf)
open VerifiableInference.Desc.LinkJoin (ent4 HasFork tmFour pi8)
open ProofFile.Honest.K9 (BatStand TermsBack SealLaw drawnOne)

/-- Each run that the order names hands on "a ledger is open and is later than U". -/
def LaterRun (Lk : Link S Claim) : Prop :=
  ∀ U : Fork, OnBytes.PscRun.Sized U → ∀ o ∈ Lk.order, ∀ run, LinkJoin.At Lk o run →
    ∀ n e c e₁, run n e = .ok (c, e₁) →
      HasFork (fun G => OnBytes.PscRun.Later U G) e → HasFork (fun G => OnBytes.PscRun.Later U G) e₁

/-- The draw's yes lays that sentence at the ledger in front. -/
def LaterDraw (p : Desc.K9.Where) : Prop :=
  ∀ (s : S) (a : Desc.K9.Part) (x : E) (t₁ : S), Desc.K9.atS.get? s = some a →
    (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      HasFork (fun G => OnBytes.PscRun.Later a.F G) t₁

section
variable {α : Type} {sub : First.ModelPart} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option Pub9 → Prop} {nU : Array ℕ} {u : HTailF2}
  {π : α → Option HTailF2 × Option (Array HFun)}
  {tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound GE8 → List (ℕ × GE8)}
  {lenOf : ℕ × String → α × Option Pub9 → ℕ}
  {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : Nat)
  (own : List (ℕ × ℕ)) (rdW : T.Wt → ℕ × ℕ → Sound.MsgQ)

/-- **The four values' terms, at a stand.** -/
theorem termsBack_vals (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) {k : Desc.K9.SegSort}
    {pW : K8.ParW} (hK : K8At Lk k pW) (hLR : LaterRun Lk) (hLD : LaterDraw p)
    (hSz : ∀ q v, Ok q → q.2 = some v → OnBytes.PscRun.Sized v.F) (Front : S → T.Wt → Prop)
    (hFacts : ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
      ∀ a v, Desc.K9.atS.get? s = some a → Ok (fixed9 φ s) → Front s v →
        FourFacts u π (fixed9 φ s) (Sound.dataQ own a (rdW v))) :
    TermsBack Lk p φ Ok T b own rdW (fun n q y => K9L.numbered n (vals4 π (ent4 π) q y))
      Front := by
  intro κ s m En ds y cols s' x z G hS a v ha hOk hFr n
  refine (numbered_zero _ n).2 ?_
  have h2 : (fixed9 φ s).2 = some (pubOf a) := by
    show (Desc.K9.atS.get? s).map pubOf = _
    rw [ha]
    rfl
  have hsz : OnBytes.PscRun.Sized a.F := hSz _ _ hOk h2
  obtain ⟨e, front, q8, tl', F1, cls, ⟨hI1, hI2⟩, hq, he⟩ := run_at_stand hK hS
    (fun e => K9L.numOf u e = K9L.numOf u s ∧
      HasFork (fun G => OnBytes.PscRun.Later a.F G) e)
    (fun t₁ h => ⟨numDraw p u s x t₁ h, hLD s a x t₁ ha h⟩)
    fun o ho run hr n e c e₁ hz hI =>
      ⟨(A.numRun o ho run hr n e c e₁ hz).trans hI.1, hLR a.F hsz o ho run hr n e c e₁ hz hI.2⟩
  obtain ⟨ht, -, hf⟩ := parts_of hq
  have e1 : e.tl?.map (blank u) = s.tl?.map (blank u) := congrArg (·.1) hI1
  have h1 : (π (fixed9 φ s).1).1 = some (blank u q8.tl) := by
    show (π (φ s)).1 = _
    rw [A.reads s]
    show s.tl?.map (blank u) = _
    rw [← e1, ht]
    rfl
  obtain ⟨G', hG', hL⟩ := hI2
  obtain rfl : G' = q8.F := Option.some.inj (hG'.symm.trans hf)
  exact vals4_of_facts π u (fixed9 φ s) (Sound.dataQ own a (rdW v)) he h1 h2 hsz hL
    (hFacts κ s m En ds y cols s' x z G hS a v ha hOk hFr)

end

section
variable {β : Type} {sub : First.ModelPart} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
  {φ : S → PhiAll.Phi β} {Ok : PhiAll.Phi β × Option Pub9 → Prop} {nU : Array ℕ} {u : HTailF2}
  {tmOf : ℕ × String → ℕ → PhiAll.Phi β × Option Pub9 → Bound GE8 → List (ℕ × GE8)}
  {lenOf : ℕ × String → PhiAll.Phi β × Option Pub9 → ℕ}
  {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : Nat)
  (own : List (ℕ × ℕ)) (rdW : T.Wt → ℕ × ℕ → Sound.MsgQ)

/-- **`TermsBack` at the library's own term.** -/
theorem termsBack_four (A : SealLaw sub l Lk p φ Ok nU u pi8 tmOf lenOf) {k : Desc.K9.SegSort}
    {pW : K8.ParW} (hK : K8At Lk k pW) (hLR : LaterRun Lk) (hLD : LaterDraw p)
    (hSz : ∀ q v, Ok q → q.2 = some v → OnBytes.PscRun.Sized v.F) (Front : S → T.Wt → Prop)
    (hFacts : ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
      ∀ a v, Desc.K9.atS.get? s = some a → Ok (fixed9 φ s) → Front s v →
        FourFacts u pi8 (fixed9 φ s) (Sound.dataQ own a (rdW v))) :
    TermsBack Lk p φ Ok T b own rdW tmFour Front :=
  termsBack_vals T b own rdW A hK hLR hLD hSz Front hFacts

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.termsBack_vals
#print axioms ProofFile.Honest.K8.termsBack_four
