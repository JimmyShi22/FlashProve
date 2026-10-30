-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SharesIs.lean: CONDITIONAL: K4's shares of a thread's debt
`Exchange`, said in the threads' own form at one item: `ExchangeAt` (Honest/Thread/Shares.lean) and
`ExchangeAtS` (Honest/Thread/SharesS.lean). Statements with their proofs: two by unfolding, the
others calls of Law/Worth.lean, Law/Wo.lean and Law/Table.lean.

Not shown here. THAT A FORM IS WORTH 0, OR THAT THE PENDING ROW HOLDS, ANYWHERE: `K4Worths` and
`K4WoHolds` are hypotheses. That the hypotheses can hold together: no example is known. Nothing on
soundness, on completeness or on any other property.
WHAT THIS FILE's IMPORTS REACH, by a program's walk of import lines that stops, unopened, at every
module under Johnson/Goal/, Johnson/D/ or ThirdParty/ and at the names RecCompile.Honest…, Both… and
PassH…: 28 modules whose names hold RecCompile; none under Johnson/Goal/ or ThirdParty/; none under
Johnson/D/, none of the three names.

  `shareAt_thr`, `shareAt_said`: `ShareAt` (Law/Table.lean) at a list of one item is `ExchangeAt`
      where At is the thread's sentence, and `ExchangeAtS` where At is the pair: by unfolding.
  `k4_exchangeAtS_own`: the share at K4's own item, under K4Table, K4Sits, K4Front and K4Worths.
  `k4_exchangeAt_planes`, `k4_exchangeAt_join`: the shares at the two items for which a layers'
      segment lists no run, under K4Table alone.
  `k4_exchangeAtS_wo`: the share at the pending row's item, under K4WoTable and K4WoHolds.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Worth
import Johnson.Desc.ProofFile.Honest.K4.Law.Wo
import Johnson.Desc.ProofFile.Honest.Thread.SharesS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Link Claim First.S)
open VerifiableInference.Desc.K9 (LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated)
open VerifiableInference.Desc.First.FillP1 (PileWit PubData)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

section
variable {S Cl : Type} (T : Thread Bk S Cl V W X Pb)

/-- A share at one item, at the thread's sentence, is the threads' own form. -/
theorem shareAt_thr (b : Nat) (i : T.ι) : ShareAt T (Thr T b) b [i] ↔ ExchangeAt T b i := Iff.rfl

/-- A share at one item, at the pair, is the threads' own form. -/
theorem shareAt_said (Said : Nat → Coins Bk → Mid W X → Prop) (b : Nat) (i : T.ι) :
    ShareAt T (ThrS T Said b) b [i] ↔ ExchangeAtS T Said b i := Iff.rfl

end

section
variable {T : Thread Bk First.S Claim V W X Pb} {b : Nat} {M : First.S → Bound GQ → Road.Mats GQ}
  {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated} {own : List (Nat × Nat)}
  {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par} {iOwn iPl iJo : T.ι} {rest : List T.ι}

/-- **`ExchangeAtS` AT K4's OWN ITEM.** CONDITIONAL: on the table's parameters, the seat, the eight
clauses and the worths, each at the pair of the thread's sentence and what has been said. -/
theorem k4_exchangeAtS_own (Said : Nat → Coins Bk → Mid W X → Prop)
    (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf) (hSit : K4Sits T b p)
    (hF : K4Front T (ThrS T Said b) b M Hh l St own rdOf tl p)
    (hW : K4Worths T (ThrS T Said b) b M own rdOf tl p) : ExchangeAtS T Said b iOwn :=
  k4_own_share_of_worths Tb hSit hF hW

/-- `ExchangeAt` at the first of the two items without a run. CONDITIONAL: on the table's
parameters. -/
theorem k4_exchangeAt_planes (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf) :
    ExchangeAt T b iPl := by
  intro blk _ k s m E ds y cols s' _ _ _ ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  exact Tb.planes _ _ _ _

/-- `ExchangeAt` at the second. CONDITIONAL: on the table's parameters. -/
theorem k4_exchangeAt_join (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf) :
    ExchangeAt T b iJo := by
  intro blk _ k s m E ds y cols s' _ _ _ ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  exact Tb.join _ _ _ _

variable {iWo : T.ι} {nR kC : Nat} {d : PubData} {rw : T.P × First.S → T.Wt → PileWit nR kC}
  {m : Nat}

/-- **`ExchangeAtS` AT THE PENDING ROW's ITEM.** CONDITIONAL: on the table's parameters and on the
row's holding, at the pair. -/
theorem k4_exchangeAtS_wo (Said : Nat → Coins Bk → Mid W X → Prop) (Tb : K4WoTable T iWo d rw m)
    (hW : K4WoHolds T (ThrS T Said b) b d rw m) : ExchangeAtS T Said b iWo :=
  k4_wo_share Tb hW

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.shareAt_thr
#print axioms ProofFile.Honest.K4.shareAt_said
#print axioms ProofFile.Honest.K4.k4_exchangeAtS_own
#print axioms ProofFile.Honest.K4.k4_exchangeAt_planes
#print axioms ProofFile.Honest.K4.k4_exchangeAt_join
#print axioms ProofFile.Honest.K4.k4_exchangeAtS_wo
