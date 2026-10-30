-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SpentReadersAtHead.lean: FIVE FUNCTIONS OF THE LIBRARY THAT TAKE THE PUBLIC
PART Z OR THE GROUND G WHOLE (`K1.linkNumbers`, `P1K2.pureLetters`, `ProofFile.k8ParW`, `K11.parOf`,
`P1K2.prepOf`; in Johnson/Desc/ProofFile/Lot/: K1.lean, K2.lean, K8.lean, K11.lean, K2OfPlan.lean):
WHAT THEY READ OF Z AND G; AND, UNDER THE HYPOTHESIS `P5J.AtMg`, WHAT IS LEFT OF THAT: the ground's
fields W and built, and, for prepOf, the public record Zp.p.X. General congruences; six short second
texts on the table of steps and the entries, each tied to the library's text; the proofs under the
hypothesis combine these with LinkNumbersAtHead.lean, BackNumbersAtHead.lean and
K1NumbersAtHead.lean. Nothing is evaluated.

Words. `P5J.AtMg` (Johnson/P5J/AtMg.lean) is the library's hypothesis at the full size; the library
calls it "the head". Below: the hypothesis. An opening is a value of `IM.Open`
(Johnson/IMR/SeatOpen.lean). The public record is a `Verify.Public`: Zp.p.X, which at an opening is
the ground's W (`IM.Open.W`).

Purpose. A table of steps on shapes, one for each of the 358 blocks in the first chain's blocksInOrder list,
is to be evaluated at closed terms. It is not in the library yet, so nothing about what it reads is
claimed here. It uses what these five functions return: to evaluate it, what they return at the
public part and ground of given public files must be written in the public record and in written
values.

How. (1) linkNumbers, k8Asks and k8NU read of G its W; pureLetters and K11.parAt read its built too:
by unfolding. prepareAt reads of the first chain's parameters the codes and the shape alone. (2) Of
Z, k8Msgs and sentAt? read the table of steps and, of the declared rounds, the entries' roots:
`roundsBeforeC?`, `rootsC`, `k8MsgsC`, `sentAtC?` are their texts on these two lists, with laws
"second text = the library's". `k8ParWC`, `parAtC`: k8ParW's and K11.parAt's texts with the one
thing that reads Z as an argument; tied by rfl. (3) Under the hypothesis the table of steps and the
entries are the written ones (`cuts_at_head`, `entries_at_head`, LinkNumbersAtHead.lean); the sizes
are the written ones (`sized_in_scope`, Johnson/Goal/Numbers/KeyInScope.lean); the state before the
first segment is the first record (`start?_first`, Johnson/Desc/First/EPubAtStart.lean); at an
opening the ground's W and first are the public part's (`IM.Open.W`, `IM.Open.first`).

Main names.
* General: `linkNumbers_congr`, `nums_congr`, `pureLetters_congr`, `k8Asks_congr`, `k8NU_congr`,
  `prepareAt_congr`, `k8ParWC_congr`, `parAtC_congr`; `roundsBefore?_eq`, `roots_entries`,
  `k8Msgs_eq`, `sentAt?_eq`, `k8ParW_eq`, `parOf_eq`.
* Under the hypothesis: `k8Msgs_at_head`, `sentAt?_at_head`, `s₀_record`. **`k8ParW_at_head`**:
  ProofFile.k8ParW Zp G X l = k8ParWC (k8MsgsC cutWritten esW) G' X l where G.W = G'.W.
  **`parOf_at_head`**: the like for K11.parOf, where G.built = G'.built too. **`prepOf_at_head`**
  (at an opening): P1K2.prepOf Zp Bs.G₀ = P1K2.prepareAt at the written sizes, Zp.p.X, the
  placeholder qFull, the written codes, shape and number of samples.

Limits. SECOND TEXTS: six short ones: each is tied to the library's text by a theorem here: a change
of that text that breaks the equation stops the build. qFull IS A PLACEHOLDER, NO VALUE THAT ANY
FILE GIVES (Johnson/Desc/K1/Law/QFull.lean: its fields given, layout, identifiers and more are empty
fillings): prepOf_at_head holds all the same, because prepareAt reads of that argument the codes and
the shape alone (`prepareAt_congr`). UNDER THE HYPOTHESIS. That the hypothesis can be met is shown
only for `P5J.AtMgA`, which extends AtMg, at the hash OnBytes.secondHashFunction and at two named sets of public
files (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean; `headMember_zGap`,
AtFullSide/Top/HeadMemberAtGap.lean); by the first file's own words the example's weights are
synthetic. Closed terms, not numerals: what k8MsgsC and sentAtC? return at the written lists is not
evaluated. What the ground's built is, is not said here. `rootsC` here is a count; the library has
another `rootsC`, a test, in another namespace (Johnson.Unfolds.rootsC,
Johnson/Unfolds/TreesAt.lean). Only the full-size parameters are covered. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.LinkNumbersAtHead
import Johnson.AtFull.Shape.K1NumbersAtHead
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.Desc.ProofFile.Lot.K11
import Johnson.Desc.ProofFile.Lot.K2
import Johnson.Goal.Numbers.KeyInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain Block FileDescription)
open VerifiableInference.Desc.First (S Cut)
open VerifiableInference.Desc.K1 (qFull linkNumbers)
open VerifiableInference.PlanWritten (proofSizedFull sized_in_scope sized_of_made)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Desc.Lots (esW)
open Johnson.G (codesFull2)
open OnBytes.Maker (WholeD)
open P5J (AtMg)

/-! ## 1 What hangs on the ground's W and built alone. General -/

section
variable {G G' : ProofFile.Ground}

/-- K1.linkNumbers reads of the ground its field W alone. -/
theorem linkNumbers_congr (hW : G.W = G'.W) (X : Stages.LinkH) :
    linkNumbers G X = linkNumbers G' X := by
  unfold linkNumbers
  rw [hW]

/-- So a link's numbers, looked up by the link's number, depend on the ground's built and W alone.
-/
theorem nums_congr (hB : G.built = G'.built) (hW : G.W = G'.W) (l : Nat) :
    (G.built[l]?).bind (linkNumbers G) = (G'.built[l]?).bind (linkNumbers G') := by
  rw [hB, funext (linkNumbers_congr hW)]

/-- P1K2.pureLetters reads of the ground its built and its W alone. -/
theorem pureLetters_congr (hB : G.built = G'.built) (hW : G.W = G'.W) (l : Nat) :
    P1K2.pureLetters G l = P1K2.pureLetters G' l := by
  unfold P1K2.pureLetters
  rw [hB, hW]

/-- ProofFile.k8Asks reads of the ground its W alone. -/
theorem k8Asks_congr (hW : G.W = G'.W) (X : Stages.LinkH) : ProofFile.k8Asks G X = ProofFile.k8Asks G' X := by
  unfold ProofFile.k8Asks
  rw [hW]

/-- ProofFile.k8NU reads of the ground its W alone. -/
theorem k8NU_congr (hW : G.W = G'.W) (X : Stages.LinkH) : ProofFile.k8NU G X = ProofFile.k8NU G' X := by
  unfold ProofFile.k8NU
  rw [hW]

end

/-- K2's preparing reads of the first chain's parameters the codes and the shape alone. General. -/
theorem prepareAt_congr {q q' : Params.First} (hc : q.codes = q'.codes) (hs : q.shape = q'.shape)
    (z : Params.ProofSized) (W : Verify.Public) (c₀ : Codes) (s₀ : Params.ReqShape) (n₀ : Nat) :
    P1K2.prepareAt z W q c₀ s₀ n₀ = P1K2.prepareAt z W q' c₀ s₀ n₀ := by
  unfold P1K2.prepareAt P1K2.tied
  rw [hc, hs]

/-! ## 2 What takes Z whole and reads its table of steps and its declared rounds' entries -/

/-- ProofFile.Pub.roundsBefore?'s text on the table of steps. -/
def roundsBeforeC? (cuts : List Cut) (look : String) : Option Nat :=
  if cuts.any fun c => c.look == look
  then some ((cuts.takeWhile fun c => c.look != look).foldl (fun n c => n + c.take) 0) else none

/-- The library's Pub.roundsBefore? is roundsBeforeC? at the public part's table of steps. -/
theorem roundsBefore?_eq (Z : ProofFile.Pub) (look : String) :
    Z.roundsBefore? look = roundsBeforeC? Z.cuts look := rfl

/-- The roots that the first k entries send. -/
def rootsC (es : List Fmt.Entry) (k : Nat) : Nat := (es.take k).foldl (fun a e => a + e.roots) 0

/-- The count of roots over declared rounds is rootsC over their entries. -/
theorem roots_entries (ds : List Fmt.DeclaredRound) (k : Nat) :
    (ds.take k).foldl (fun a r => a + r.entry.roots) 0 = rootsC (ds.map (·.entry)) k := by
  unfold rootsC
  rw [← List.map_take, List.foldl_map]

/-- ProofFile.k8Msgs' text on the table of steps and the entries. -/
def k8MsgsC (cuts : List Cut) (es : List Fmt.Entry) (look : String) : List Nat :=
  match cuts.find? (·.look == look), roundsBeforeC? cuts look with
  | some c, some n => (List.range (rootsC es (n + c.take) - rootsC es n)).map (· + rootsC es n)
  | _, _ => []

/-- The library's ProofFile.k8Msgs is k8MsgsC at the public part's table of steps and at its declared
rounds' entries. -/
theorem k8Msgs_eq (Z : ProofFile.Pub) (look : String) :
    ProofFile.k8Msgs Z look = k8MsgsC Z.cuts (Z.D.1.map (·.entry)) look := by
  unfold ProofFile.k8Msgs k8MsgsC
  rw [roundsBefore?_eq]
  cases Z.cuts.find? (·.look == look) <;> cases roundsBeforeC? Z.cuts look <;>
    simp only [roots_entries]

/-- K11.sentAt?'s text on the table of steps and the entries. -/
def sentAtC? (cuts : List Cut) (es : List Fmt.Entry) (look : String) : Option Nat :=
  (roundsBeforeC? cuts look).map fun k => rootsC es k

/-- The library's K11.sentAt? is sentAtC? at the same two lists. -/
theorem sentAt?_eq (Z : ProofFile.Pub) (look : String) :
    K11.sentAt? Z look = sentAtC? Z.cuts (Z.D.1.map (·.entry)) look := by
  unfold K11.sentAt? sentAtC?
  rw [roundsBefore?_eq]
  simp only [roots_entries]

/-- ProofFile.k8ParW's text with ProofFile.k8Msgs Z, the one thing in it that reads Z, as an argument. -/
def k8ParWC (msgs : String → List Nat) (G : ProofFile.Ground) (X : Stages.LinkH) (l : Nat) :
    VerifiableInference.Desc.First.K8.ParW :=
  { link := l, piece := if X.kind == 2 then 6 else 5, ks := X.tl.mats.toList.map (·.k)
    tau := X.tl.tau, ms := X.tl.mats.toList.map (·.m), asks := ProofFile.k8Asks G X
    matsIn := msgs (X.name ++ (if X.kind == 2 then ".1.call" else ".0.call"))
    readsIn := msgs (X.name ++ (if X.kind == 2 then ".4.call" else ".3.call"))
    nU := ProofFile.k8NU G X }

/-- The library's ProofFile.k8ParW is k8ParWC at ProofFile.k8Msgs Z. -/
theorem k8ParW_eq (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : Stages.LinkH) (l : Nat) :
    ProofFile.k8ParW Z G X l = k8ParWC (ProofFile.k8Msgs Z) G X l := rfl

/-- k8ParWC reads of the ground its W alone. -/
theorem k8ParWC_congr {G G' : ProofFile.Ground} (hW : G.W = G'.W) (msgs : String → List Nat)
    (X : Stages.LinkH) (l : Nat) : k8ParWC msgs G X l = k8ParWC msgs G' X l := by
  unfold k8ParWC
  rw [k8Asks_congr hW, k8NU_congr hW]

/-- K11.parAt's text with the count that it reads off Z as an argument. -/
def parAtC (sent : Nat) (G : ProofFile.Ground) : Johnson.Desc.First.ForkMerge.HeadMergeP :=
  { link := G.built.size - 1, piece := 9, lay := G.W.layers.wsLay
    work := (Params.settingOf G.W.P.frame).workOf .field .request
    sent := sent
    ncl := G.W.H.NCL, nMsg := G.W.H.nMsg, nLin := G.W.H.nLin }

/-- The library's K11.parOf is parAtC at what K11.sentAt? gives at the step "H.8.call", 0 where it
gives nothing. -/
theorem parOf_eq (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    K11.parOf Z G = parAtC ((K11.sentAt? Z "H.8.call").getD 0) G := rfl

/-- parAtC reads of the ground its built and its W alone. -/
theorem parAtC_congr {G G' : ProofFile.Ground} (hB : G.built = G'.built) (hW : G.W = G'.W) (sent : Nat) :
    parAtC sent G = parAtC sent G' := by
  unfold parAtC
  rw [hB, hW]

/-! ## 3 Under the hypothesis -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- Under the hypothesis ProofFile.k8Msgs at the public part is k8MsgsC at the two written lists. -/
theorem k8Msgs_at_head (h : AtMg o Z D r Zp Np cF) (look : String) :
    ProofFile.k8Msgs Zp look = k8MsgsC cutWritten esW look := by
  rw [k8Msgs_eq, cuts_at_head h, entries_at_head h]

/-- Under the hypothesis K11.sentAt? at the public part is sentAtC? at the two written lists. -/
theorem sentAt?_at_head (h : AtMg o Z D r Zp Np cF) (look : String) :
    K11.sentAt? Zp look = sentAtC? cutWritten esW look := by
  rw [sentAt?_eq, cuts_at_head h, entries_at_head h]

/-- **UNDER THE HYPOTHESIS K8's NUMBERS AT A LINK DEPEND ON THE GROUND's W AND ON THE LINK ALONE.**
-/
theorem k8ParW_at_head (h : AtMg o Z D r Zp Np cF) {G G' : ProofFile.Ground} (hW : G.W = G'.W)
    (X : Stages.LinkH) (l : Nat) :
    ProofFile.k8ParW Zp G X l = k8ParWC (k8MsgsC cutWritten esW) G' X l := by
  rw [k8ParW_eq, funext (k8Msgs_at_head h), k8ParWC_congr hW]

/-- **UNDER THE HYPOTHESIS THE MERGE's NUMBERS** (K11.parOf) are parAtC at the count off the written
lists, at any ground that has G's built and G's W. -/
theorem parOf_at_head (h : AtMg o Z D r Zp Np cF) {G G' : ProofFile.Ground} (hB : G.built = G'.built)
    (hW : G.W = G'.W) :
    K11.parOf Zp G = parAtC ((sentAtC? cutWritten esW "H.8.call").getD 0) G' := by
  rw [parOf_eq, sentAt?_at_head h, parAtC_congr hB hW]

/-- Under the hypothesis the state before the first segment is the first record at the public part's
own codes, shape and layout. -/
theorem s₀_record (h : AtMg o Z D r Zp Np cF) :
    Zp.s₀ = S.firstRecord Zp.first.codes Zp.first.shape Zp.first.layout :=
  VerifiableInference.Desc.First.start?_first
    (ProofFile.Law.pubBy_start (st := ProofFile.plainStarts) h.laid.pub)

section
variable {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **UNDER THE HYPOTHESIS, AT AN OPENING, WHAT K2 PREPARES** (P1K2.prepOf) is prepareAt at written
arguments, at the placeholder qFull and at the public record Zp.p.X. -/
theorem prepOf_at_head (h : AtMg o Z D r Zp Np cF)
    (O : IM.Open o Z.pol Z.lay Z.KL F Zp Bs base c A B) :
    P1K2.prepOf Zp Bs.G₀ = P1K2.prepareAt proofSizedFull Zp.p.X qFull codesFull2
      proofSizedFull.request proofSizedFull.request.answers := by
  have W4 := H2K12.written354_of_pins h.scope h.laid.pub h.pins.1 h.laid.laidPOf
  obtain ⟨-, -, f3, -, -, -⟩ := first_at_head h
  have hz := sized_in_scope h.scope h.laid.pub (sized_of_made (pinned_at_head h))
  have e1 : Zp.s₀.st.codes = codesFull2 := by rw [s₀_record h]; exact W4.codes
  have e2 : Zp.s₀.check.frame.shape = proofSizedFull.request := by rw [s₀_record h]; exact f3
  have e3 : Zp.P.samples = proofSizedFull.request.answers := by rw [par_at_head h]
  unfold P1K2.prepOf
  rw [hz, O.W, O.first, e1, e2, e3]
  exact prepareAt_congr W4.codes f3 _ _ _ _ _

end

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.linkNumbers_congr
#print axioms Johnson.AtFull.Shape.nums_congr
#print axioms Johnson.AtFull.Shape.pureLetters_congr
#print axioms Johnson.AtFull.Shape.k8Asks_congr
#print axioms Johnson.AtFull.Shape.k8NU_congr
#print axioms Johnson.AtFull.Shape.prepareAt_congr
#print axioms Johnson.AtFull.Shape.roundsBefore?_eq
#print axioms Johnson.AtFull.Shape.roots_entries
#print axioms Johnson.AtFull.Shape.k8Msgs_eq
#print axioms Johnson.AtFull.Shape.sentAt?_eq
#print axioms Johnson.AtFull.Shape.k8ParW_eq
#print axioms Johnson.AtFull.Shape.k8ParWC_congr
#print axioms Johnson.AtFull.Shape.parOf_eq
#print axioms Johnson.AtFull.Shape.parAtC_congr
#print axioms Johnson.AtFull.Shape.k8Msgs_at_head
#print axioms Johnson.AtFull.Shape.sentAt?_at_head
#print axioms Johnson.AtFull.Shape.k8ParW_at_head
#print axioms Johnson.AtFull.Shape.parOf_at_head
#print axioms Johnson.AtFull.Shape.s₀_record
#print axioms Johnson.AtFull.Shape.prepOf_at_head
