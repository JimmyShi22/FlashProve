-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/MaskSeat.lean: at the IOP as written in Lean that `ProofFile.onlineDescription` returns, in the goals'
scope, at the second hash function: the eight sub-protocols number 338
to 345 of the first chain's flat list, which stand in the output head's segment in front of the
merge of the claims on the committed table (number 346), have what
Johnson/Top/H0/MergeLaw/MaskReached.lean asks of them: so the test `maskAtB` (MaskRow.lean) accepts
at border 346, under the premises named in the Limits. One definition with code, and theorems with
their proofs.

How. Which sub-protocol stands at which number of the chain's flat list is said by
Johnson/IMR/FirstSeats.lean, K2Seat.lean, K3Seat.lean, K6Seat.lean, K1Seat.lean, K8Seat.lean,
K11Seat.lean (a maker's sub-protocol, alone, under the guards that the chain's maker lays around
it), Johnson/IMR/FlatIx.lean and Johnson/IMR/FlatScope.lean (number 14 l + i + 2 for number i in
front of the batching of segment l). An accepting step of a sub-protocol as it stands in the chain
is one of the maker's own (Johnson/IMR/SeatForm.lean: `yes_alone`; Johnson/IMR/FirstSeats.lean:
`k7_sits_yes`). What the makers' accepting steps do is said in MaskKeeps.lean and MaskMaker.lean.

Main names:
  `alone_decides`, `retype_decides`: what a maker's sub-protocol's accepting steps have, those of
    the sub-protocol as it stands in the chain have.
  `k7Block_fresh`: the sub-protocol at the segment's first place makes `HeadFresh`.
  `k2Is_opens`: WHICHEVER CASE OF `IM.K2Is` HOLDS at a segment l's place of the code switch, an
    accepting step from a state with `HeadFresh` makes `OpenedAt l`: a sub-protocol that always
    rejects never accepts; the code switch alone, whose numbers say that it stands at a segment
    other than the head's, accepts only between two segments.
  `k1Reads_stays`, `k1_head_stays`: the sending of the reads with the quiet step behind it; the two
    later sendings of the output head's segment.
  `addsAt Z G i`: how many oracle messages number i of the six behind the opening adds. With code.
    `later_count`, `addsAt_two`, `addsAt_four`, `addsAt_else`, `total_addsAt`: it is the number of
    the messages that the shape G.first.shape gives segment 24 at moment 1 (i = 2) and at moment 2
    (i = 4), and 0 else.
  `flat_at`: number 338 + i of the flat list. `mergePlace_at`: the sub-protocol number 346 stands at
    the merge's place.
  `seated_three`: THE THREE PREMISES of `maskMsgB_reached` at bs := c.blocksInOrder, k0 := 338, n := 6, l :=
    24.
  `maskAtB_seated`, `maskAtB_seated_counts`: THE TEST OF MaskRow.lean AT BORDER 346; the second with
    the six sub-protocols' messages counted by `momentCount`.

Limits. THE IDLE CASES. In two of the three cases of `IM.K2Is` that can occur at number 339 (a
sub-protocol that always rejects; the code switch alone) no step from a reached state accepts, for
every state reached at 339 has `HeadFresh`: then nothing is reached at the borders 340 to 346, and
`maskAtB_seated` and what follows it speak of no state. Which case holds is said by no file. The
like at number 342: where the public files name no arrays for the reads, or give no quiet step
behind them, that sub-protocol always rejects. No accepting step of any of the eight is exhibited
here; that the family is not empty will be shown by an evaluation of `maskMsgB` at the honest run's
state in front of the merge, which has been made nowhere yet. THE PREMISES. In the goals' scope and
at the second hash function alone (the premises of the IM files that are called); that
`ProofFile.onlineDescription` returns there is inside the premise `IM.Open`. Every member of the family Rch at
border 346 is reached over c.blocksInOrder. At that border, at unmarked states: `atFirstSeats` and
`atFirstShapes` (Johnson/Desc/K12/Door) accept, and the copy in use has the shape sh. The premises
on numbers (hm, hlt, hnum, hp, hstand, hx, hown, hRb) are on numbers that are functions of the
public files: they are not shown at all files in scope, and no example at the release's own
values is given. The shape sh, by which the left side of hnum counts, and Bs.G₀.first.shape, by
which the six sub-protocols' messages are counted, are tied by nothing here. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.MaskReached
import Johnson.IMR.FirstSeats
import Johnson.IMR.K2Seat
import Johnson.IMR.K3Seat
import Johnson.IMR.K6Seat
import Johnson.IMR.K1Seat
import Johnson.IMR.K8Seat
import Johnson.IMR.K11Seat
import Johnson.IMR.FlatScope
import Johnson.IMR.SeatKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc.Keeps (Decides Whole)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

/-! ## From a maker's sub-protocol to the one that stands in the chain -/

/-- What the accepting steps of a maker's sub-protocol have, those of the sub-protocol as it stands
in the chain, alone under the chain's guards, have. -/
theorem alone_decides {R : S → S → Prop} {b b' : Block S Cl} {name : String} {a : Place}
    (hk : a.kind ≠ KindName.K7) (la : IM.LaidAlone ProofFile.sameReply b b' name a)
    (W : Decides R b') : Decides R b :=
  fun s rs gs t h => W s rs gs t ((IM.yes_alone la hk s t rs gs).1 h).1

/-- The like where the type of a claim alone is changed. -/
theorem retype_decides {R : S → S → Prop} {x : Block S Unit} (W : Decides R x) :
    Decides R (x.retype : Block S Cl) := fun s rs gs t h => W s rs gs t h

/-! ## The makers at the first two places -/

/-- The sub-protocol at the segment's first place makes "fresh". -/
theorem k7Block_fresh (X : OnBytes.Model.Verify.Public) (l : ℕ) :
    Decides (fun _ s' => HeadFresh s') (IM.k7Block X l) :=
  h1_fresh
    (decides_guarded
      (b := { (roundlessBlock "H:1" 1 (some l) 1 (K2.headFrontQ X.H.tl) : Block S Unit) with
        place := (Kinds.Reply.blockOf X l).place })
      (fun s rs gs s' h => headFront_decides (Cl := Unit) "H:1" 1 (some l) 1 X.H.tl s rs gs s' h)
      ProofFile.sameReply fun _ => false)
    "H:1" l X.hS.V

/-- **Whichever case of `IM.K2Is` holds at segment l's place of the code switch, an accepting step
from a state with "fresh" makes "opened" at l.** -/
theorem k2Is_opens {Z : ProofFile.Pub} {G : ProofFile.Ground} {nm : String} {x : Block S Unit} {l pc : ℕ}
    (h : IM.K2Is Z G { chain := 1, link := some l, piece := pc, kind := .K2 } nm x) :
    Decides (fun s s' => HeadFresh s → OpenedAt l s') x := by
  intro s rs gs s' hy hf
  rcases h with ⟨-, hm⟩ | ⟨P, n, -, -, ⟨hn, -⟩ | ⟨l', HP, hl, hHP, rfl⟩ | ⟨l', -, rfl⟩⟩
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at hy
    cases hy
  · cases hn
  · obtain rfl : l = l' := Option.some.inj hl
    have hPl : HP.l = l := by
      unfold P1K2.pureLetters at hHP
      obtain ⟨X, -, rfl⟩ := Option.map_eq_some_iff.1 hHP
      rfl
    rw [← hPl]
    exact placeH2_makes (p := IM.k2P Z _ nm .head n) (n := nm) (P := HP) hy hf
  · exfalso
    obtain ⟨a, ha, -⟩ := hf
    have hy' : K2.decideWith _root_.Tw.K2.sendByL8
        (IM.k2P Z { chain := 1, link := some l, piece := pc, kind := .K2 } nm .link n) s rs gs =
          .ok s' := hy
    rcases K2.stands _ _ _ _ _ _ hy' with ⟨-, hb⟩ | ⟨hp, -⟩ | ⟨hp, -⟩
    · rw [ha] at hb
      cases hb
    · have hp' : K2.At.link = K2.At.head := hp
      cases hp'
    · have hp' : K2.At.link = K2.At.finish := hp
      cases hp'

/-! ## The six behind the opening -/

/-- The sending of the reads with the quiet step behind it. -/
theorem k1Reads_stays (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : OnBytes.Model.Stages.LinkH)
    (pr : ℕ) (reads : Option (List ℕ)) :
    Decides (SegStays (K1.shapesOf (K1.parLater G.first (K1.gpOf Z) l pr 1)).length)
      (IM.k1Reads Z G l X pr reads) :=
  decides_andThen (e := 0) (laterAt_stays G.first (K1.gpOf Z) l pr 1 reads)
    (q := IM.k1Quiet G l X)
    (decides_of_quiet
      (_root_.Meaning.K2.orLoud_whole fun _ hb => _root_.Meaning.K2.readsQuietAt_quiet hb)) _

/-- How many oracle messages number i of the six sub-protocols behind the opening adds. -/
def addsAt (Z : ProofFile.Pub) (G : ProofFile.Ground) : ℕ → ℕ
  | 2 => (K1.shapesOf (K1.parLater G.first (K1.gpOf Z) 24 5 1)).length
  | 4 => (K1.shapesOf (K1.parLater G.first (K1.gpOf Z) 24 7 2)).length
  | _ => 0

/-- A later sending has as many messages as the shape gives the segment at that moment. -/
theorem later_count (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ) :
    (K1.shapesOf (K1.parLater q gp link piece moment)).length =
      momentCount q.shape link moment := by
  simp [K1.shapesOf, K1.Par.sent, K1.parLater, K1.noticesAt, ReqFrame.notices, ReqFrame.atMoment,
    momentCount]

/-- Number 2 of the six: the sending at the segment's moment 1. -/
theorem addsAt_two (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    addsAt Z G 2 = momentCount G.first.shape 24 1 := later_count _ _ _ _ _

/-- Number 4 of the six: the sending at the segment's moment 2. -/
theorem addsAt_four (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    addsAt Z G 4 = momentCount G.first.shape 24 2 := later_count _ _ _ _ _

/-- The four others of the six add no message. -/
theorem addsAt_else (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    addsAt Z G 0 = 0 ∧ addsAt Z G 1 = 0 ∧ addsAt Z G 3 = 0 ∧ addsAt Z G 5 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- What the six add together. -/
theorem total_addsAt (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    total (addsAt Z G) 6 = momentCount G.first.shape 24 1 + momentCount G.first.shape 24 2 := by
  have e : total (addsAt Z G) 6 = 0 + addsAt Z G 0 + addsAt Z G 1 + addsAt Z G 2 + addsAt Z G 3 +
      addsAt Z G 4 + addsAt Z G 5 := rfl
  obtain ⟨e0, e1, e3, e5⟩ := addsAt_else Z G
  rw [e, addsAt_two, addsAt_four, e0, e1, e3, e5]
  omega

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Number 338 + i of the flat list. -/
theorem flat_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Lk : Link S Cl}
    {b : Block S Cl} {i k : ℕ} (eL : c.links[24]? = some Lk) (e : Lk.hear[i]? = some b)
    (hk : k = 338 + i) : c.blocksInOrder[k]? = some b := by
  have q := IM.hear_at_flat eL e
  rw [IM.flatIx_scope hS hR O (Nat.le_refl 24) i] at q
  rw [hk, show 338 + i = 14 * 24 + i + 2 by omega]
  exact q

/-- A later sending of the output head's segment: number i in front of the batching, i = 4 or 6. -/
theorem k1_head_stays (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {i : ℕ} (hi : i = 4 ∨ i = 6) :
    ∃ Lk b, c.links[24]? = some Lk ∧ Lk.hear[i]? = some b ∧
      Decides (SegStays (addsAt Z Bs.G₀ (i - 2))) b := by
  have hk : (kindsBeforeBatching .head (24 == 0))[i]? = some KindName.K1 := by
    rcases hi with rfl | rfl <;> (unfold kindsBeforeBatching; rfl)
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, eL, e, -, hn, harm⟩ :=
    IM.k1_later O 24 .head (IM.subs_head hS hR O.pub O.blank) i hk
      (by rcases hi with rfl | rfl <;> decide)
  refine ⟨Lk, b, eL, e, ?_⟩
  have hp := IM.numbers_pieces hn
  rcases hi with rfl | rfl
  · rcases harm with ⟨h5, la⟩ | ⟨h5, -⟩
    · obtain rfl : pr = 5 := h5.symm
      exact alone_decides (by intro k; cases k) la
        (retype_decides (k1Reads_stays Z Bs.G₀ 24 Xl 5 reads))
    · omega
  · rcases harm with ⟨h7, -⟩ | ⟨h7, la⟩
    · omega
    · obtain rfl : pd = 7 := h7.symm
      exact alone_decides (by intro k; cases k) la
        (retype_decides (laterAt_stays Bs.G₀.first (K1.gpOf Z) 24 7 2 digits))

/-- The sub-protocol number 346 of the flat list stands at the merge's place. -/
theorem mergePlace_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ b, c.blocksInOrder[346]? = some b ∧ b.place = IM.k11Place := by
  obtain ⟨Lk, b, eL, e, la, -⟩ := IM.k11_of hS hR O
  exact ⟨b, flat_at hS hR O eL e rfl, IM.alone_place la⟩

/-- **The three premises of `maskMsgB_reached` at the chain's flat list**: number 338 makes "fresh",
number 339 makes "opened" at 24 of it, and number 340 + i, i below 6, leaves what the test reads and
adds `addsAt Z Bs.G₀ i` messages. -/
theorem seated_three (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    (∃ b1, c.blocksInOrder[338]? = some b1 ∧ Decides (fun _ s' => HeadFresh s') b1) ∧
      (∃ b2, c.blocksInOrder[338 + 1]? = some b2 ∧
        Decides (fun s s' => HeadFresh s → OpenedAt 24 s') b2) ∧
      ∀ i, i < 6 → ∃ b, c.blocksInOrder[338 + 2 + i]? = some b ∧
        Decides (SegStays (addsAt Z Bs.G₀ i)) b := by
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · obtain ⟨Lk, b, eL, e, hj, -⟩ := IM.k7_sits hS hR O
    exact ⟨b, flat_at hS hR O eL e rfl, fun s rs gs t h =>
      k7Block_fresh Bs.G₀.W 24 s _ _ t (IM.k7_sits_yes hS hR O hj h).1⟩
  · obtain ⟨Lk, b, x, eL, e, -, la, his⟩ := IM.k2_head_of hS hR O
    exact ⟨b, flat_at hS hR O eL e rfl,
      alone_decides (by intro k; cases k) la (retype_decides (k2Is_opens his))⟩
  · obtain rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
      omega
    · obtain ⟨Lk, b, b', eL, e, k3, la⟩ := IM.k3_of hS hR O 24 (by decide) false
      have e' : Lk.hear[2]? = some b := e
      exact ⟨b, flat_at hS hR O eL e' rfl,
        alone_decides (by intro k; cases k) la (theStated_stays _ _ _ _ _ _ k3)⟩
    · obtain ⟨Lk, b, b', ms, eL, e, -, k6, la, -⟩ := IM.k6_of hS hR O
      exact ⟨b, flat_at hS hR O eL e rfl,
        alone_decides (by intro k; cases k) la (seatedClaims_stays k6)⟩
    · obtain ⟨Lk, b, eL, e, hd⟩ := k1_head_stays hS hR O (Or.inl rfl)
      exact ⟨b, flat_at hS hR O eL e rfl, hd⟩
    · obtain ⟨Lk, b, Xl, eL, e, -, la, -⟩ := IM.k8_of_head hS hR O
      exact ⟨b, flat_at hS hR O eL e rfl,
        alone_decides (by intro k; cases k) la (k8Whole_stays _)⟩
    · obtain ⟨Lk, b, eL, e, hd⟩ := k1_head_stays hS hR O (Or.inr rfl)
      exact ⟨b, flat_at hS hR O eL e rfl, hd⟩
    · obtain ⟨Lk, b, b', eL, e, k3, la⟩ := IM.k3_of hS hR O 24 (by decide) true
      have e' : Lk.hear[7]? = some b := e
      exact ⟨b, flat_at hS hR O eL e' rfl,
        alone_decides (by intro k; cases k) la (theStated_stays _ _ _ _ _ _ k3)⟩

/-- **`maskAtB` accepts at border 346 of the chain**, at every statement that meets the table's
condition there, lies in the family Rch and bears no mark: `maskAtB_reached` with its three premises
on the sub-protocols had from `seated_three`. -/
theorem maskAtB_seated (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pp W : Type}
    {Fr : Sound.Frame} {ft : ℕ} {start : Pp → S} (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (own : List (ℕ × ℕ))
    (x : ℕ × ℕ) (R O' : ℕ) (L : K12.Door.Laid) (M : List OracleShape) (p : Place) (sub : ModelPart)
    (sh : ReqShape) (m : ℕ) (hRch : ∀ a, Rch 346 a → Reach ft c.blocksInOrder start 346 a.1)
    (hm : maskNoOf sh 24 = some m) (hlt : m < firstCount sh 24)
    (hnum : O' + (firstCount sh 24 + 1) + total (addsAt Z Bs.G₀) 6 = Nn.msgsAt (some p) + m)
    (hp : ps[346]? = some p) (hstand : standAt links p = .link sub)
    (hx : L.places[O']? = some x) (hown : x ∈ own)
    (hRb : (M[O']?).map (fun y => ceilLog2 y.maskRows) = some R)
    (hseats : ∀ a, Rch 346 a → a.1.2.failed = none → K12.Door.atFirstSeats L a.1.2 = true)
    (hshapes : ∀ a, Rch 346 a → a.1.2.failed = none → K12.Door.atFirstShapes M a.1.2 = true)
    (hlive : ∀ a, Rch 346 a → a.1.2.failed = none → a.1.2.live.frame.shape = sh) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → a.1.failed = none → maskAtB own x R a.1 = true := by
  obtain ⟨⟨b1, h1, hb1⟩, ⟨b2, h2, hb2⟩, hk⟩ := seated_three hS hR O
  exact maskAtB_reached (bs := c.blocksInOrder) (start := start) (ft := ft) Rch Nn Mg links ps own x R O'
    338 6 24 L M p sub (addsAt Z Bs.G₀) sh m hRch h1 hb1 h2 hb2 hk hm hlt hnum hp hstand hx hown
    hRb hseats hshapes hlive

/-- The same, with the six sub-protocols' messages counted by `momentCount`. -/
theorem maskAtB_seated_counts (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pp W : Type}
    {Fr : Sound.Frame} {ft : ℕ} {start : Pp → S} (Rch : ℕ → (Pp × S) × Fr.E.Str → Prop)
    (Nn : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (own : List (ℕ × ℕ))
    (x : ℕ × ℕ) (R O' : ℕ) (L : K12.Door.Laid) (M : List OracleShape) (p : Place) (sub : ModelPart)
    (sh : ReqShape) (m : ℕ) (hRch : ∀ a, Rch 346 a → Reach ft c.blocksInOrder start 346 a.1)
    (hm : maskNoOf sh 24 = some m) (hlt : m < firstCount sh 24)
    (hnum : O' + (firstCount sh 24 + 1) +
      (momentCount Bs.G₀.first.shape 24 1 + momentCount Bs.G₀.first.shape 24 2) =
        Nn.msgsAt (some p) + m)
    (hp : ps[346]? = some p) (hstand : standAt links p = .link sub)
    (hx : L.places[O']? = some x) (hown : x ∈ own)
    (hRb : (M[O']?).map (fun y => ceilLog2 y.maskRows) = some R)
    (hseats : ∀ a, Rch 346 a → a.1.2.failed = none → K12.Door.atFirstSeats L a.1.2 = true)
    (hshapes : ∀ a, Rch 346 a → a.1.2.failed = none → K12.Door.atFirstShapes M a.1.2 = true)
    (hlive : ∀ a, Rch 346 a → a.1.2.failed = none → a.1.2.live.frame.shape = sh) :
    ∀ (z : Pp) (a : S × Fr.E.Str), Sound.onQ Nn Mg links ps (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → a.1.failed = none → maskAtB own x R a.1 = true :=
  maskAtB_seated hS hR O Rch Nn Mg links ps own x R O' L M p sub sh m hRch hm hlt
    (by rw [total_addsAt]; exact hnum) hp hstand hx hown hRb hseats hshapes hlive

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.alone_decides
#print axioms VerifiableInference.Desc.First.MergeLaw.retype_decides
#print axioms VerifiableInference.Desc.First.MergeLaw.k7Block_fresh
#print axioms VerifiableInference.Desc.First.MergeLaw.k2Is_opens
#print axioms VerifiableInference.Desc.First.MergeLaw.k1Reads_stays
#print axioms VerifiableInference.Desc.First.MergeLaw.later_count
#print axioms VerifiableInference.Desc.First.MergeLaw.addsAt_two
#print axioms VerifiableInference.Desc.First.MergeLaw.addsAt_four
#print axioms VerifiableInference.Desc.First.MergeLaw.addsAt_else
#print axioms VerifiableInference.Desc.First.MergeLaw.total_addsAt
#print axioms VerifiableInference.Desc.First.MergeLaw.mergePlace_at
#print axioms VerifiableInference.Desc.First.MergeLaw.maskAtB_seated_counts
#print axioms VerifiableInference.Desc.First.MergeLaw.flat_at
#print axioms VerifiableInference.Desc.First.MergeLaw.k1_head_stays
#print axioms VerifiableInference.Desc.First.MergeLaw.seated_three
#print axioms VerifiableInference.Desc.First.MergeLaw.maskAtB_seated
