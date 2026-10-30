-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/ValuesJoin.lean: THE SMALLNESS TEST: THE NAMED PREMISE
`ValuesAtStand` (Johnson/Desc/ProofFile/Honest/K8/LeftFront.lean: at a stand of the batching, at the
state at which the tests behind it are called: three readings and seven tests on what the runs and
the adding have laid) FROM SENTENCES ON THE STATE IN FRONT OF THE BATCHING ALONE, AT A LINK OF EACH
OF THE THREE SORTS. A joining of `allHeld_at_layers`, `allHeld_at_att`, `allHeld_at_head`
(Johnson/Desc/ProofFile/Honest/K8/AllAtSorts.lean) to another house's stand (`BatStand`, `LsLaid`,
Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean). None of the library's goals.

  `valuesLeft_iff`   `ValuesLeft` is `AllHeld` (Johnson/Desc/K8/Honest/LeftAtLink.lean), sign for
                   sign
  `valuesLeft_slot`   the laying of the kept slots leaves it: none of its ten conjuncts reads them
  `yes_at_stand`   a stand holds a yes of the batching block itself, from the state in front to the
                   state behind, at the drawn element's three words (the other house's
                   `batch_join`, Johnson/Desc/ProofFile/Honest/K9/BatYes.lean)
  `valuesLeft_of_held`   pointwise: the state behind shows tl' and G with AllHeld tl' G · the state
                   at which the tests are called has that ledger and that data with the kept slots
                   laid ⊢ ValuesLeft at its data and ledger
  `valuesAtStand_of_held`   so: AllHeld behind every stand ⊢ ValuesAtStand
  `AllFrontAtStand`   THE NAMED PREMISE THAT STAYS: at every stand the state in front shows tl, F,
                   funs, what the lookup heard, `AllFront`'s seventeen, and a member of the link's
                   list for each array
  **`valuesAtStand_layers`**, **`valuesAtStand_att`**, **`valuesAtStand_head`**   the sort's ties ·
                   the lookups' runs' ties · the sort's order · AllFrontAtStand · at every stand
                   what the sort's lemmas ask of the state in front ⊢ ValuesAtStand
Of `ValuesAtStand`'s own premises four are not spent: that the link's tests say yes · that the share
is silent · that the state at which the tests are called goes on from what is fixed in front
(`K9L.Fx9`) · that one coefficient stands there for each slot (`K9L.good9`). So what is shown is
stronger than the name asks.
Limits. AN IMPLICATION STILL: THE DEBT IS MOVED TO THE STATE IN FRONT, NOT PAID: `AllFrontAtStand`,
the ties and the sort's asks are paid by nobody HERE, and as wholes are shown of no state; three of
AllFront's seventeen are the verifier's own tests at the data in front. PAYERS IN SIGHT, NOT CALLED:
Johnson/P1K8R/ (LookAtBatch · LookAtBatchAll · HeardAtBatch · MergeAtBatch · LeftAtBatch ·
NamedAtBatch · HeadDigitsAtBatch · ThirdTie · BehindAtRch · DrawAtBatch) shows many of their fields
of every state that the chain's own blocks reach in front of a batching; that a stand's state in
front is such a state is another house's to show. NO MEMBER: that the premises can hold together is
not shown. `FrontAtStand`, the other half of the cut in LeftFront.lean, is not touched here. No
prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.LeftFront
import Johnson.Desc.ProofFile.Honest.K8.AllAtSorts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9L (Pub9)
open ProofFile.Honest.K9 (BatStand LsLaid drawnOne batch_join)
open _root_.P1K8

/-- The two sentences are one. -/
theorem valuesLeft_iff (tl : HTailF2) (F : Fork) : ValuesLeft tl F ↔ AllHeld tl F := Iff.rfl

/-- The laying of the kept slots leaves it. -/
theorem valuesLeft_slot (tl : HTailF2) (F : Fork) (v : Array E) :
    ValuesLeft { tl with lsTail := v } F ↔ ValuesLeft tl F := Iff.rfl

/-- Pointwise. -/
theorem valuesLeft_of_held {s' z₂ : S} {tl' tl : HTailF2} {G F : Fork}
    (hget : tlForkP.get? s' = some (tl', G)) (hA : AllHeld tl' G) (hf : z₂.fork? = s'.fork?)
    (hL : LsLaid s' z₂) (hz : z₂.tl? = some tl) (hzF : z₂.fork? = some F) : ValuesLeft tl F := by
  obtain ⟨F₀, tl₀, h1, h2, h3⟩ := hL
  obtain ⟨e1, e2⟩ := (tlFork_iff s' tl' G).1 hget
  obtain rfl : tl₀ = tl' := Option.some.inj (h2.symm.trans e1)
  obtain rfl : F₀ = G := Option.some.inj (h1.symm.trans e2)
  obtain rfl : F = F₀ := Option.some.inj (hzF.symm.trans (hf.trans h1))
  obtain rfl := Option.some.inj (hz.symm.trans h3)
  exact (valuesLeft_slot _ _ _).2 ((valuesLeft_iff _ _).2 hA)

section
variable {α : Type} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option Pub9 → Prop} {nU : Array ℕ}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}

/-- A stand holds a yes of the batching block itself. -/
theorem yes_at_stand {κ : Coins Bk} {s : S} {m : Mid W X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid W X} {cols : List Desc.OpenedColumn} {s' : S} {x : E}
    {z : S × Desc.K9.Part × List Claim} {G : Fork}
    (hS : BatStand Lk p T b κ s m En ds y cols s' x z G) :
    (Desc.K9.batch Desc.K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide s
      [⟨[], drawnOne x⟩] [] = .ok s' := by
  rw [hS.bat.state]
  exact batch_join p _ s x z G hS.bat.gathered hS.bat.added

/-- So: `AllHeld` behind every stand gives the named premise. -/
theorem valuesAtStand_of_held
    (h : ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
      ∃ (tl' : HTailF2) (G' : Fork), tlForkP.get? s' = some (tl', G') ∧ AllHeld tl' G') :
    ValuesAtStand Lk p φ Ok nU T b := by
  intro κ s m En ds y cols s' x z G hS _ _ z₂ _ _ hf hL tl F hz hzF
  obtain ⟨tl', G', hget, hA⟩ := h κ s m En ds y cols s' x z G hS
  exact valuesLeft_of_held hget hA hf hL hz hzF

variable (Lk p T b) in
/-- **The named premise that stays**: at the state in front of the batching. -/
def AllFrontAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    ∃ (tl : HTailF2) (F : Fork) (funs : Array HFun) (g : Forest.Heard) (nbW : Nat)
      (Wn : List Want), s.tl? = some tl ∧ s.fork? = some F ∧ s.funs? = some funs ∧
      tl.heard = some g ∧ AllFront tl F g nbW Wn ∧
      ∀ a0, Desc.K9.atS.get? s = some a0 → a0.L.list.nt.size = F.trees.size

/-- **AT A LAYERS' LINK.** -/
theorem valuesAtStand_layers (p4 : OnBytes.Desc.First.K4.Par)
    (ties : LinkJoin.LayersTies Lk p4 nU)
    (tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (hord : Lk.order = First.orderOf .layers) (hFront : AllFrontAtStand Lk p T b)
    (hs : ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
      ∀ tl, s.tl? = some tl → LayAsks p4 ((tl.ix.U.getD 2 none).getD 0) s) :
    ValuesAtStand Lk p φ Ok nU T b :=
  valuesAtStand_of_held fun κ s m En ds y cols s' x z G hS => by
    obtain ⟨tl, F, funs, g, nbW, Wn, ht, hF, hf, hg, D, hT⟩ :=
      hFront κ s m En ds y cols s' x z G hS
    exact allHeld_at_layers Lk p4 nU ties tC tD hord p
      (fun u rs =>
        (Desc.K9.batch Desc.K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide u rs [])
      s s' tl F funs (fun _ _ h => h) ht hF hf g hg nbW Wn D hT
      (hs κ s m En ds y cols s' x z G hS tl ht) (drawnOne x) (yes_at_stand hS)

/-- **AT AN ATTENTION LINK.** -/
theorem valuesAtStand_att (A : Attention.Plan) (ties : LinkJoin.AttTies Lk (Att.P.parCOf A) nU)
    (tC : ∀ run, LinkJoin.At Lk (1, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At Lk (6, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At Lk (2, "join") run → LinkJoin.Under run
      (Desc.K9.joinCalls (Att.P.keysOfK (Att.P.seatCO (Att.P.parCOf A)) (Att.P.parCOf A))))
    (tP : ∀ run, LinkJoin.At Lk (1, "planes") run → ∃ lm, LinkJoin.Under run
      (Desc.K9.planesCalls lm (Att.P.readersOfK (Att.P.seatCO (Att.P.parCOf A)) (Att.P.parCOf A))))
    (hord : Lk.order = First.orderOf .attention) (hFront : AllFrontAtStand Lk p T b)
    (hs : ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
      ∀ tl, s.tl? = some tl → AttAsks s ∧ tl.ix.U.getD 2 none = some A.iU3 ∧
        ∃ a : AttOwn, s.here = .att a ∧ Att.P.U3At A (Att.P.plannedK A) a.F) :
    ValuesAtStand Lk p φ Ok nU T b :=
  valuesAtStand_of_held fun κ s m En ds y cols s' x z G hS => by
    obtain ⟨tl, F, funs, g, nbW, Wn, ht, hF, hf, hg, D, hT⟩ :=
      hFront κ s m En ds y cols s' x z G hS
    obtain ⟨h1, h2, a, ha, hU⟩ := hs κ s m En ds y cols s' x z G hS tl ht
    exact allHeld_at_att Lk A nU ties tC tD tJ tP hord p
      (fun u rs =>
        (Desc.K9.batch Desc.K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide u rs [])
      s s' tl F funs (fun _ _ h => h) ht hF hf g hg nbW Wn D hT h1 a ha hU h2 (drawnOne x)
      (yes_at_stand hS)

/-- **AT THE HEAD's LINK.** -/
theorem valuesAtStand_head (h : Model.Head.Shape) (iU3 l piece : Nat) (p6 : Kinds.Head.Par)
    (ties : LinkJoin.HeadTies Lk h iU3 l piece p6 nU)
    (tC : ∀ run, LinkJoin.At Lk (2, "objects") run → LinkJoin.Under run Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At Lk (7, "objects") run → LinkJoin.Under run Desc.K9.objectsDigits)
    (tP : ∀ run, LinkJoin.At Lk (2, "planes") run → ∃ lm, LinkJoin.Under run
      (Desc.K9.planesCalls lm (Kinds.Head.callerReaders (Kinds.Head.planesAt iU3))))
    (hord : Lk.order = First.orderOf .head) (hFront : AllFrontAtStand Lk p T b)
    (hs : ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
      ∀ tl, s.tl? = some tl → HeadWants h iU3 p6 s ∧ tl.ix.U.getD 2 none = some iU3) :
    ValuesAtStand Lk p φ Ok nU T b :=
  valuesAtStand_of_held fun κ s m En ds y cols s' x z G hS => by
    obtain ⟨tl, F, funs, g, nbW, Wn, ht, hF, hf, hg, D, hT⟩ :=
      hFront κ s m En ds y cols s' x z G hS
    obtain ⟨h1, h2⟩ := hs κ s m En ds y cols s' x z G hS tl ht
    exact allHeld_at_head Lk h iU3 l piece p6 nU ties tC tD tP hord p
      (fun u rs =>
        (Desc.K9.batch Desc.K9.atS p (claimsInBy Lk.each Lk.hear Lk.order)).decide u rs [])
      s s' tl F funs (fun _ _ h => h) ht hF hf g hg nbW Wn D hT h1 h2 (drawnOne x)
      (yes_at_stand hS)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.valuesLeft_iff
#print axioms ProofFile.Honest.K8.valuesLeft_slot
#print axioms ProofFile.Honest.K8.valuesLeft_of_held
#print axioms ProofFile.Honest.K8.yes_at_stand
#print axioms ProofFile.Honest.K8.valuesAtStand_of_held
#print axioms ProofFile.Honest.K8.valuesAtStand_layers
#print axioms ProofFile.Honest.K8.valuesAtStand_att
#print axioms ProofFile.Honest.K8.valuesAtStand_head
