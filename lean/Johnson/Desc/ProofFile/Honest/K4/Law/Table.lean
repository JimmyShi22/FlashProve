-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/Table.lean: the hypotheses on a thread's table of joints at the
member of the layers' own rounds (kind K4), the hypothesis on values, and how shares of the debt
`Exchange` (Honest/Thread/Pays.lean), item by item, make the debt. Definitions of hypotheses, and
small statements with their proofs.

Not shown here. THAT THE FORMS ARE WORTH 0 ANYWHERE: `K4Values` is a hypothesis; Law/Worth.lean
brings it down to the worths group by group, which are hypotheses there. That the hypotheses can
hold together: no example is known. Nothing on soundness, on completeness or on any other property.

In this folder a "parameter" is a free variable or a field of a thread; T is a variable throughout.

  `K4Table T b iOwn iPl iJo rest Hh l St own rdOf`   the items are parameters of type T.ι.
      * owes: the thread's forward row behind border b owes iOwn, iPl, iJo and the items of rest;
      * own: the table's sentence `formsTQ` (Johnson/Desc/Sound/FormsQ.lean) at K4's two runs, at
        the readers of the link l with the filling Hh of their two holes, the stated function St,
        the seats own and the witness's tables rdOf, GIVES the thread's sentence at iOwn;
      * planes, join: the thread's sentences at iPl and iJo hold outright (at a layers' segment the
        table lists no run for them).
  `K4Values T At b M own rdOf tl p`   THE VALUES: `FormsT` (Johnson/Desc/Plain/K04Plain.lean) at the
      table's data, at every state behind the member's step and every continuation of the
      challenges. At: which stands in front are meant: a parameter, so that one text serves
      `Exchange` (At := Thr T b) and `ExchangeS` (At := ThrS T Said b, Honest/Thread/PaysS.lean).
      THE FOUR TIES OF Law/Script.lean ARE BOUND AT Thr T b: a statement from them to K4Values at
      another At wants «At k s m E → Thr T b k s m E» as a hypothesis by name.
      M is meant as fun _ D => matsOfData tl names D, the right side of `K4CellsTie`
      (Law/Script.lean).
  `items_nil`, `items_cons`, `items_append`: `Thread.Items` of a list, from its members.
  `k4_idle`: the shares at iPl and iJo, under K4Table.
  `ShareAt T At b O`: the sentence of `Exchange` with the list O in the stead of the row's.
  `share_mono`, `share_cons`, `share_append`: a share at more stands serves at fewer; shares at one
      At join as their lists do.
  `exchange_of_shares`, `exchangeS_of_shares`: under K4Table, the share at iOwn and the share at
      rest give `Exchange T b`, and `ExchangeS T Said b`.

Who is meant to prove each. K4Table: whoever lays the thread; at the library's own parameters it is
proved in Law/TableAt.lean. K4Values: the writers of K4's honest side, with the writers of the
lookup's for three forms of the run "front" (the lookup's own claim on its leaves, and two on its
planes). The share at rest (the pending row's item `wo`, and the four items that the row reads and
owes again): `wo`: K4's writers; nothing is typed for it. The four: whoever proves each item.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Script
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Road.K4.ItemOfForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Road.K4 (semQ)
open VerifiableInference.Desc (Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles readersOfLink)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ formsTQ)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **The table's parameters at K4's member.** A hypothesis's form. Nothing is claimed by the
definition. -/
structure K4Table (T : Thread Bk First.S Claim V W X Pb) (b : Nat) (iOwn iPl iJo : T.ι)
    (rest : List T.ι) (Hh : LinkHoles) (l : Link First.S Claim) (St : Stated)
    (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) : Prop where
  /-- what the thread's forward row owes behind the member -/
  owes : (T.row b).owes = iOwn :: iPl :: iJo :: rest
  /-- the table's sentence at K4's two runs gives the thread's at K4's own item -/
  own : ∀ w (a : T.P × First.S) y v,
    (∀ q ∈ [(2, "front"), (2, "back")],
      formsTQ (readersOfLink Hh l) St own q.1 q.2 a.2 (rdOf v)) → T.means w iOwn a y v
  /-- the two items for which a layers' segment lists no run hold outright -/
  planes : ∀ w a y v, T.means w iPl a y v
  join : ∀ w a y v, T.means w iJo a y v

/-- **THE VALUES**: FormsT at the table's data, at every state behind the member's step, at every
continuation. A hypothesis's form. Nothing is claimed by the definition. -/
def K4Values (T : Thread Bk First.S Claim V W X Pb)
    (At : Coins Bk → First.S → Mid W X → Env → Prop) (b : Nat)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A →
    FormsT seatS (semQ tl M s' fun v => dataQ own A (rdOf v)) (frontRun p) formsBack s'
      (T.wit k y.2.st.input (y.2.st.heard ++ ds'))

section
variable {S Cl : Type} (T : Thread Bk S Cl V W X Pb)

/-- No item: nothing is asked. -/
theorem items_nil (k : Coins Bk) (s : S) (m : Mid W X) (E : Env) : T.Items [] k s m E :=
  fun _ _ hi => absurd hi (List.not_mem_nil)

/-- The items of a list, from the first and the others. -/
theorem items_cons {i : T.ι} {O : List T.ι} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    (h : T.Items [i] k s m E) (h' : T.Items O k s m E) : T.Items (i :: O) k s m E := by
  intro ds j hj
  rcases List.mem_cons.1 hj with rfl | hj
  · exact h ds _ (List.mem_singleton.2 rfl)
  · exact h' ds j hj

/-- The items of two lists in a row. -/
theorem items_append {O O' : List T.ι} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    (h : T.Items O k s m E) (h' : T.Items O' k s m E) : T.Items (O ++ O') k s m E := by
  intro ds j hj
  rcases List.mem_append.1 hj with hj | hj
  · exact h ds j hj
  · exact h' ds j hj

/-- **A share of `Exchange`**: its sentence with the list O in the stead of what the row owes, at
the stands in front that At names. A definition: nothing is claimed by it. -/
def ShareAt (At : Coins Bk → S → Mid W X → Env → Prop) (b : Nat) (O : List T.ι) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Items O k s' y.2 (E.add y.1)

/-- A share at more stands in front serves at fewer. -/
theorem share_mono {At At' : Coins Bk → S → Mid W X → Env → Prop} {b : Nat} {O : List T.ι}
    (hA : ∀ k s m E, At' k s m E → At k s m E) (h : ShareAt T At b O) : ShareAt T At' b O :=
  fun blk hblk k s m E ds y cols s' hA' => h blk hblk k s m E ds y cols s' (hA k s m E hA')

/-- The share at a list, from the shares at its first item and at the others. -/
theorem share_cons {At : Coins Bk → S → Mid W X → Env → Prop} {b : Nat} {i : T.ι} {O : List T.ι}
    (h : ShareAt T At b [i]) (h' : ShareAt T At b O) : ShareAt T At b (i :: O) :=
  fun blk hblk k s m E ds y cols s' hA hd hS =>
    items_cons T (h blk hblk k s m E ds y cols s' hA hd hS)
      (h' blk hblk k s m E ds y cols s' hA hd hS)

/-- The share at two lists in a row. -/
theorem share_append {At : Coins Bk → S → Mid W X → Env → Prop} {b : Nat} {O O' : List T.ι}
    (h : ShareAt T At b O) (h' : ShareAt T At b O') : ShareAt T At b (O ++ O') :=
  fun blk hblk k s m E ds y cols s' hA hd hS =>
    items_append T (h blk hblk k s m E ds y cols s' hA hd hS)
      (h' blk hblk k s m E ds y cols s' hA hd hS)

end

section
variable {T : Thread Bk First.S Claim V W X Pb} {b : Nat} {iOwn iPl iJo : T.ι} {rest : List T.ι}
  {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated} {own : List (Nat × Nat)}
  {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- The shares at the two items for which a layers' segment lists no run. CONDITIONAL: on the
table's parameters. -/
theorem k4_idle (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf) (k : Coins Bk)
    (s' : First.S) (m : Mid W X) (E : Env) : T.Items [iPl, iJo] k s' m E := by
  intro ds' i hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact Tb.planes _ _ _ _
  · obtain rfl := List.mem_singleton.1 hi
    exact Tb.join _ _ _ _

/-- The row's whole debt at the stands that At names, from the share at K4's own item and the share
at the others. CONDITIONAL: on the table's parameters. -/
theorem share_of_shares (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf)
    {At : Coins Bk → First.S → Mid W X → Env → Prop} (hO : ShareAt T At b [iOwn])
    (hR : ShareAt T At b rest) : ShareAt T At b (T.row b).owes := by
  intro blk hblk k s m E ds y cols s' hA hd hS
  rw [Tb.owes]
  exact items_cons T (hO blk hblk k s m E ds y cols s' hA hd hS)
    (items_append T (O := [iPl, iJo]) (k4_idle Tb k s' y.2 (E.add y.1))
      (hR blk hblk k s m E ds y cols s' hA hd hS))

/-- **`Exchange T b` from the shares.** CONDITIONAL: on the table's parameters. -/
theorem exchange_of_shares (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf)
    (hO : ShareAt T (Thr T b) b [iOwn]) (hR : ShareAt T (Thr T b) b rest) : Exchange T b :=
  share_of_shares Tb hO hR

/-- **`ExchangeS T Said b` from the shares.** CONDITIONAL: on the table's parameters. -/
theorem exchangeS_of_shares (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf)
    (Said : Nat → Coins Bk → Mid W X → Prop) (hO : ShareAt T (ThrS T Said b) b [iOwn])
    (hR : ShareAt T (ThrS T Said b) b rest) : ExchangeS T Said b :=
  share_of_shares Tb hO hR

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.items_nil
#print axioms ProofFile.Honest.K4.items_cons
#print axioms ProofFile.Honest.K4.items_append
#print axioms ProofFile.Honest.K4.share_mono
#print axioms ProofFile.Honest.K4.share_cons
#print axioms ProofFile.Honest.K4.share_append
#print axioms ProofFile.Honest.K4.k4_idle
#print axioms ProofFile.Honest.K4.share_of_shares
#print axioms ProofFile.Honest.K4.exchange_of_shares
#print axioms ProofFile.Honest.K4.exchangeS_of_shares
