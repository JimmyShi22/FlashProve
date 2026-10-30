-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/HeardWhole.lean: the honest side of the sub-protocol "the output
head's own rounds": what the verifier's state holds as heard at the head, with the point on the
positions, the two batching elements and the four sumchecks' variables' challenges laid, as a
function of the sub-protocol's own challenges; and that the maker of the head's tables of reads asks
no more of it. Definitions with code, three theorems, and tests.

Why. Behind the sub-protocol's rounds the prover sends the vector of reads: sums of committed cells
under weights. The weights are those of the head's tables (`tables`,
Johnson/Desc/K8/ReadsQuiet.lean), which are made of what was heard at the head. An honest sender is
handed no state of the verifier's; it is handed the challenges. Honest/K6/Heard.lean lays the last
sumcheck's challenges alone, for the claim on the weights. Here those of all four are laid.

  `headSumR`        the challenges of the variables of the sumcheck that is part number i
  `headHearingOf`   the sub-protocol's hearing, of its own challenges: the challenges listed below
                    are laid; every value that was sent, and each sumcheck's own data, are blank
  `headHeardWhole`  what the verifier's text lays into its state of such a hearing: its own
                    `heardOf` (Johnson/Stored/HeadSeat.lean)
  `headHeardWholeAt`   the same of a chain's challenges and the number of rounds in front; it
                    refuses where fewer are heard than the sub-protocol has rounds
  `tables_nine`     **two structures of what was heard that agree in nine fields get one answer of
                    the maker of tables**
  `tables_fields`   **of what the lookup left, four fields are enough**
  `tables_heardOf`  **so two hearings that agree in five challenge fields, at two lookups' data
                    that agree in five fields, get one answer: of the sub-protocol's own rounds the
                    maker reads no value that was sent**

Which rounds are read, inside the sub-protocol, from 0. f i: the number of rounds in front of part i
(`headInFront`).
  pV           round 0: all its elements, in the order of drawing
  gam          round 1
  squares.r    rounds f 2 + 1 + j, j < lPd + lt; the element of the round that ends it (`down`):
               round f 3
  om           round f 4
  products.r   rounds f 5 + 1 + j, j < lt
  normed.r     rounds f 6 + 1 + j, j < lt
  logits.r     rounds f 7 + 1 + j, j < lt + lPd
A sumcheck's first round draws an element that is no coordinate, so its variables' rounds begin one
behind. NOT LAID: the four elements of these first rounds, and the four of the rounds in the further
variable: the verifier's text keeps them in each sumcheck's own data, with values that were sent.

The list that is handed in. own: the challenges of the sub-protocol's own rounds, from its first
round on: what `heardJust` (Honest/ForKinds.lean) yields at the number of the chain's rounds in
front of the sub-protocol and the number of its rounds.

The maker of tables reads at most nine fields: PV, wpl.r, tV.r, tN.r, tH.r (of the five challenge
fields above), g1 (what the lookup on the head's calls left, handed through whole), Zl (cut off
g1.zx), qN and qH (both laid as 0 by `heardOf`). Of g1 it reads at most zk, zb0, zb1 and shape.
Whether these, and zx, hang on a value that was sent in the lookup's rounds is the lookup's to say.

Limits. In `headHeardWhole` a round that the list does not hold, or that draws nothing, counts as 0,
and nothing refuses. Of round 0 all elements are read; of every other round the first alone. In
`headHeardWhole` every field that `heardOf` makes of a sent value, of a slot's number or of a
sumcheck's own data (sW, sPv; sL, sR, row in wpl; sCl, sEnd, p, rowU in tV, tN, tH) is made of
blanks and means nothing. g1 is an argument: that it is what the lookup's hearing leaves is the
lookup's matter. THAT THESE VALUES ARE THOSE OF THE VERIFIER'S STATE BEHIND A SESSION'S ROUNDS IS
NOT SHOWN HERE: Honest/K6/HeardTie.lean (`heardOf_tie`: fourteen fields; `tables_tie`) and
Honest/K6/HeardAtYes.lean (`tables_at_yes`: five fields and the maker's answer) state it,
CONDITIONALLY and field by field: where the hearing returns from a well laid ledger; at the state
behind an accepting step of the member from such a ledger. (Beside these the first file's two ask
that the lookup's point on the positions has lt coordinates, the second's the member's form and two
premises on its address and its guard.)
Honest/K6/HeardWholeToy.lean tries it at
one small size.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Heard
import Johnson.Desc.K8.ReadsQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open OnBytes (E)
open VerifiableInference.Desc.Kinds (Point Head.Par Head.Request)

/-- The challenges of the n variables of the sumcheck that is part number i, in the order of the
rounds. own: the sub-protocol's own challenges, from its first round on. -/
def headSumR (p : Head.Par) (i n : Nat) (own : List Fmt.Drawn) : Point :=
  ((List.range n).map fun j => elemOf own (headInFront p i + 1 + j)).toArray

/-- **The sub-protocol's hearing, of its own challenges**: the point on the positions, the two
batching elements, the four sumchecks' variables' challenges and the element of the round that ends
the first are laid; every value that was sent, and each sumcheck's own data, are blank. -/
def headHearingOf (p : Head.Par) (own : List Fmt.Drawn) :
    VerifiableInference.Desc.Kinds.Head.HeardAll :=
  ({ pV := headPV own, W := #[], gam := headGam own, rhoI := #[]
     squares := { r := headSumR p 2 (headLPd p + headLt p) own
                  down := elemOf own (headInFront p 3) }
     P := #[], om := headOm p own, products := { r := headSumR p 5 (headLt p) own } },
   { normed := { r := headSumR p 6 (headLt p) own } },
   { logits := { r := headSumR p 7 (headLt p + headLPd p) own } })

/-- **What was heard at the head, of the sub-protocol's own challenges**: the verifier's own
function on that hearing. g1: what the lookup on the head's calls left; it is handed through. -/
def headHeardWhole (p : Head.Par) (request : Head.Request) (y : Nat)
    (g1 : OnBytes.Model.Forest.Heard) (own : List Fmt.Drawn) : OnBytes.Model.Head.Heard :=
  let _ := p.sizes
  let _ := request
  let _ : VerifiableInference.Desc.Kinds.Head.Token := ⟨y⟩
  VerifiableInference.Desc.Kinds.Head.heardOf g1 (headHearingOf p own)

/-- The same of a chain's challenges from its first round on, and the number of its rounds in front
of the sub-protocol. It refuses where fewer challenges are heard from there on than the sub-protocol
has rounds, as `heardJust` (Honest/ForKinds.lean) does. -/
def headHeardWholeAt (p : Head.Par) (request : Head.Request) (y : Nat)
    (g1 : OnBytes.Model.Forest.Heard) (base : Nat) (heard : List Fmt.Drawn) :
    Except String OnBytes.Model.Head.Heard :=
  let own := (heard.drop base).take (headInFront p 8)
  if own.length == headInFront p 8 then .ok (headHeardWhole p request y g1 own)
  else .error "fewer challenges have been heard than the output head's own rounds draw"

/-- **THE MAKER OF THE HEAD's TABLES READS AT MOST NINE FIELDS OF WHAT WAS HEARD**: where two agree
in these, it gives one answer. -/
theorem tables_nine (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (hp : OnBytes.Model.Head.HPlanH2) (cov : OnBytes.Model.Head.Covered)
    {x x' : OnBytes.Model.Head.Heard}
    (e1 : x.PV = x'.PV) (e2 : x.wpl.r = x'.wpl.r) (e3 : x.tV.r = x'.tV.r) (e4 : x.tN.r = x'.tN.r)
    (e5 : x.tH.r = x'.tH.r) (e6 : x.g1 = x'.g1) (e7 : x.Zl = x'.Zl) (e8 : x.qN = x'.qN)
    (e9 : x.qH = x'.qH) :
    VerifiableInference.Desc.K8.ReadsQuiet.tables h L hp cov x =
      VerifiableInference.Desc.K8.ReadsQuiet.tables h L hp cov x' := by
  unfold VerifiableInference.Desc.K8.ReadsQuiet.tables
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]

/-- **OF WHAT THE LOOKUP LEFT, THE MAKER READS AT MOST FOUR FIELDS**: the calls' key points, the two
points of the planes, and the shape. -/
theorem tables_fields (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (hp : OnBytes.Model.Head.HPlanH2) (cov : OnBytes.Model.Head.Covered)
    {x x' : OnBytes.Model.Head.Heard}
    (e1 : x.PV = x'.PV) (e2 : x.wpl.r = x'.wpl.r) (e3 : x.tV.r = x'.tV.r) (e4 : x.tN.r = x'.tN.r)
    (e5 : x.tH.r = x'.tH.r) (k1 : x.g1.zk = x'.g1.zk) (k2 : x.g1.zb0 = x'.g1.zb0)
    (k3 : x.g1.zb1 = x'.g1.zb1) (k4 : x.g1.shape = x'.g1.shape) (e7 : x.Zl = x'.Zl)
    (e8 : x.qN = x'.qN) (e9 : x.qH = x'.qH) :
    VerifiableInference.Desc.K8.ReadsQuiet.tables h L hp cov x =
      VerifiableInference.Desc.K8.ReadsQuiet.tables h L hp cov x' := by
  have z1 : ∀ q, OnBytes.Model.Head.zjOf L x.g1 q = OnBytes.Model.Head.zjOf L x'.g1 q := by
    intro q
    unfold OnBytes.Model.Head.zjOf
    rw [k1]
  have z2 : ∀ q, OnBytes.Model.Head.ztOf h L x.g1 q = OnBytes.Model.Head.ztOf h L x'.g1 q := by
    intro q
    unfold OnBytes.Model.Head.ztOf
    rw [k1]
  have z3 : ∀ e, VerifiableInference.Desc.Own.planeWeights x.g1 h.lmbH e =
      VerifiableInference.Desc.Own.planeWeights x'.g1 h.lmbH e := by
    intro e
    unfold VerifiableInference.Desc.Own.planeWeights
    rw [k2, k3, k4]
  unfold VerifiableInference.Desc.K8.ReadsQuiet.tables
  simp only [e1, e2, e3, e4, e5, e7, e8, e9, z1, z2, z3]

/-- **OF THE SUB-PROTOCOL's OWN ROUNDS THE MAKER OF THE HEAD's TABLES READS NO VALUE THAT WAS
SENT**: two hearings that agree in the point on the positions and in the four sumchecks' challenges
get one answer, at two lookups' data that agree in the lookup's point, the calls' key points, the
two points of the planes and the shape. It asks more than the maker reads: e5 asks the whole of
logits.r and k0 the whole of g1.zx, where the proof spends the first lt coordinates of the one and
the last ls + lt of the other; and the classes of the request and the token stand there only because
`heardOf` is typed with them: the maker reads neither win nor rs. -/
theorem tables_heardOf [VerifiableInference.Desc.Kinds.Head.Sizes] [Head.Request]
    [VerifiableInference.Desc.Kinds.Head.Token]
    (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (hp : OnBytes.Model.Head.HPlanH2) (cov : OnBytes.Model.Head.Covered)
    (g1 g1' : OnBytes.Model.Forest.Heard) (H H' : VerifiableInference.Desc.Kinds.Head.HeardAll)
    (e1 : H.1.pV = H'.1.pV) (e2 : H.1.squares.r = H'.1.squares.r)
    (e3 : H.1.products.r = H'.1.products.r) (e4 : H.2.1.normed.r = H'.2.1.normed.r)
    (e5 : H.2.2.logits.r = H'.2.2.logits.r) (k0 : g1.zx = g1'.zx) (k1 : g1.zk = g1'.zk)
    (k2 : g1.zb0 = g1'.zb0) (k3 : g1.zb1 = g1'.zb1) (k4 : g1.shape = g1'.shape) :
    VerifiableInference.Desc.K8.ReadsQuiet.tables h L hp cov
        (VerifiableInference.Desc.Kinds.Head.heardOf g1 H) =
      VerifiableInference.Desc.K8.ReadsQuiet.tables h L hp cov
        (VerifiableInference.Desc.Kinds.Head.heardOf g1' H') :=
  tables_fields h L hp cov e1 e2 e3 e4
    (congrArg (fun r : Point => r.extract 0 VerifiableInference.Desc.Kinds.Norm.lt) e5) k1 k2 k3 k4
    (congrArg (fun z : Array E => z.extract
      (z.size - (VerifiableInference.Desc.Kinds.Norm.ls + VerifiableInference.Desc.Kinds.Norm.lt))
      z.size) k0) rfl rfl

#print axioms tables_nine
#print axioms tables_fields
#print axioms tables_heardOf

/-! ## Tests at small made-up numbers

The public numbers and the list of Honest/K6/Heard.lean's tests: four positions, six features;
round number i draws i + 100 (and 7, which only round 0's reader takes). The parts have 1, 1, 8, 1,
1, 5, 5, 8 rounds. -/

/-- The structure at the made-up list, without a request and a lookup. -/
def headWholeToy : OnBytes.Model.Head.Heard :=
  headHeardWhole headHeardToyPar ⟨fun _ => 0, 0, 0⟩ 0 headNoLookup (headHeardToyList 30)

#guard headWholeToy.PV == #[100, 7].map headHeardToyE
#guard headWholeToy.wpl.r == #[103, 104, 105, 106, 107].map headHeardToyE
#guard headWholeToy.wpl.tau == headHeardToyE 110
#guard headWholeToy.tV.r == #[113, 114].map headHeardToyE
#guard headWholeToy.tN.r == #[118, 119].map headHeardToyE
#guard headWholeToy.tH.r == #[123, 124].map headHeardToyE
#guard headWholeToy.rs == #[127, 126, 125].map headHeardToyE
#guard headWholeToy.gp.extract 0 2 == #[1, 101].map headHeardToyE
#guard headWholeToy.omV.extract 0 2 == #[1, 111].map headHeardToyE
#guard (headWholeToy.qN, headWholeToy.qH) == (0, 0)
-- where both lay a field, this file and Heard.lean agree; with rounds in front
#guard
  match headHeardWholeAt headHeardToyPar ⟨fun i => i + 40, 1, 4⟩ 3 headNoLookup 5
    (headHeardToyList 40) with
  | .ok a =>
    let b := headHeardOf headHeardToyPar ⟨fun i => i + 40, 1, 4⟩ 3 headNoLookup 5
      (headHeardToyList 40)
    a.tH.r == b.tH.r && a.rs == b.rs && a.win == b.win && a.tH.r == #[128, 129].map headHeardToyE
  | .error _ => false
-- just enough rounds are heard: an answer; one fewer: a refusal
#guard (headHeardWholeAt headHeardToyPar ⟨fun _ => 0, 0, 0⟩ 0 headNoLookup 5
  (headHeardToyList 35)).toOption.isSome
#guard (headHeardWholeAt headHeardToyPar ⟨fun _ => 0, 0, 0⟩ 0 headNoLookup 5
  (headHeardToyList 34)).toOption.isNone

end ProofFile.Honest.K6
