-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/Kept.lean: CONDITIONAL: K4's share of a thread's debt
`Exchange` (Honest/Thread/Pays.lean) at the item "the forms of K4's own runs are worth 0", from the
member's own step. Definitions of hypotheses, and statements with their proofs.

Not shown here. THAT THE FORMS ARE WORTH 0 ANYWHERE: `K4Values` is a hypothesis. That the hypotheses
can hold together: no example is known. At a thread that holds at no run the share holds emptily.
Nothing on soundness, on completeness or on any other property.
No property is claimed.

  `K4FrontAt … s s' v`   what `kept_forms` (Johnson/Road/K4/KeptForms.lean) asks beside what an
      accepting decision leaves, the values and the table's parameters: EIGHT CLAUSES, each named in
      the definition's text. s: the state in front of the member; s': behind it; v: the witness.
  `K4Front T At b …`   that at every state behind the member's step and every continuation. At:
      which stands in front are meant, as in `K4Values` (Law/Table.lean).
  `k4_own_share`: K4's SHARE AT ITS OWN ITEM (`ShareAt T At b [iOwn]`), under K4Table, K4Sits,
      K4Front and K4Values, at every At.

ONE p THROUGHOUT: the parameters of the member as the chain seats it: there the lookup states its
own claims (p.k3Runs = true): K4FrontAt's clause runs asks it, with front and back, which read the
runs of claims at p.

Who is meant to prove each, GENERAL IN THE THREAD: nobody has. AT THE LIBRARY's OWN PARAMETERS OF
THE FIRST CHAIN's THREAD (`lettersHead`; the full size and the format's second hash function alone) EACH
OF K4Front's EIGHT CLAUSES IS THE END OF A THEOREM SINCE, each under the hypotheses that its own
statement names (h and the member's laying throughout):
  * asks · names · reads: `asks_head` · `names_head` · `reads_head` (Law/FrontHead.lean).
  * test: `test_head` (Law/W/TestHead.lean), under Behind at the same member.
  * front · back · runs: inside `k4Front_head` (Law/W/ExchangeParts.lean).
  * stated: `stated_head` (Law/StatedHead.lean), AT ONE LIST OF NAMES, P5J.At.names3 Zp m.
K4Sits (Law/Sits.lean): `k4Sits_head` (Law/SeatedHead.lean). K4Values stays a hypothesis here; four
statements end in it, each from other hypotheses: `values_of_worths` (Law/Worth.lean),
`values_of_opens` (Law/W/Values.lean), `values_of_slots` (Law/W/ValuesOfPlan.lean),
`values_of_right` (Law/W/SlotsOfStand.lean).

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Table
import Johnson.Desc.ProofFile.Honest.K4.Law.Sits
import Johnson.Road.K4.KeptForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4 (StatedAt readsArrayB kept_atS kept_forms)
open OnBytes.Road.K4.InT (StatesAt)
open VerifiableInference.Desc (Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles statesOfLink readersOfLink formsInT)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated second dataQ)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **What the join behind an accepting decision asks beside that decision, the values and the
table's parameters.** A hypothesis's form. Nothing is claimed by the definition. -/
structure K4FrontAt {Wt : Type} (M : First.S → Bound GQ → Road.Mats GQ) (Hh : LinkHoles)
    (l : Link First.S Claim) (St : Stated) (own : List (Nat × Nat)) (rd : Wt → Nat × Nat → MsgQ)
    (tl : HTailF2) (p : Par) (s s' : First.S) (v : Wt) : Prop where
  /-- tests on the state in front, and the plan's public test -/
  asks : ∃ (P₀ : Layer.Pub) (o₀ : Own), KeptAsks p s s' P₀ o₀
  /-- the lookup's promise on the names of its pad -/
  names : ∀ a fo, s.here = .lay a → a.fo = some fo → _root_.Fo.Tp.PadNames fo a.F
  /-- the reads' array is there behind the step -/
  reads : readsArrayB p.hp s' = true
  /-- at the state behind, the link's two runs do what the kind's sub-protocol's do -/
  front : StatesAt (statesOfLink l) 2 p "front" s'
  back : StatesAt (statesOfLink l) 2 p "back" s'
  /-- the lookup states its own claims -/
  runs : p.k3Runs = true
  /-- at the reads' array the stated function's cells are the true entries -/
  stated : ∀ A' o c, segAt? s' = some A' → s'.own? = some o → A'.L.arrayOf[o.v.iU3]? = some c →
    second s' c = true → StatedAt St M s' tl o c (p.hp.nU.getD 2 0) (dataQ own A' (rd v))
  /-- the table's public test at both runs -/
  test : ∀ q ∈ [(2, "front"), (2, "back")], formsInT (readersOfLink Hh l) own q.1 q.2 s' = true

/-- That at every state behind the member's step, at every continuation. A hypothesis's form.
Nothing is claimed by the definition. -/
def K4Front (T : Thread Bk First.S Claim V W X Pb)
    (At : Coins Bk → First.S → Mid W X → Env → Prop) (b : Nat)
    (M : First.S → Bound GQ → Road.Mats GQ) (Hh : LinkHoles) (l : Link First.S Claim) (St : Stated)
    (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds',
    K4FrontAt M Hh l St own rdOf tl p s s' (T.wit k y.2.st.input (y.2.st.heard ++ ds'))

/-- **K4's SHARE OF `Exchange` AT ITS OWN ITEM, FROM THE MEMBER's OWN STEP.** CONDITIONAL: on the
table's parameters, the seat, the eight clauses and the values. -/
theorem k4_own_share {T : Thread Bk First.S Claim V W X Pb} {b : Nat} {iOwn iPl iJo : T.ι}
    {rest : List T.ι} {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated}
    {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
    (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf)
    {At : Coins Bk → First.S → Mid W X → Env → Prop} {M : First.S → Bound GQ → Road.Mats GQ}
    {tl : HTailF2} {p : Par} (hSit : K4Sits T b p) (hF : K4Front T At b M Hh l St own rdOf tl p)
    (hV : K4Values T At b M own rdOf tl p) : ShareAt T At b [iOwn] := by
  intro blk hblk k s m E ds y cols s' hA hd hS ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  have F := hF blk hblk k s m E ds y cols s' hA hd hS ds'
  obtain ⟨_, _, A⟩ := F.asks
  exact Tb.own _ _ _ _ (kept_forms M Hh l own rdOf _ (kept_atS hdec) A F.names F.reads F.front
    F.back F.runs F.stated F.test (hV blk hblk k s m E ds y cols s' hA hd hS ds'))

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_own_share
