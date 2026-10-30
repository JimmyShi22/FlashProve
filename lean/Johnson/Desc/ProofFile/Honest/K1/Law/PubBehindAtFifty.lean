-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/PubBehindAtFifty.lean: the kind K1's fifty later sendings
(every link's reads and digits), under the library's head: if the table's six tests hold at the
state in front, they hold at the next border behind an accepting step, under further premises at the
state in front (no mark; the open link's frame's group and shape; at link 24's reads, that the state
is reached) and one on the tests base beneath. Beside the step no premise speaks of the state
behind.

What this file proves. Let h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x (the library's head,
Johnson/P5J/MgAtAll.lean), l < 25, d a Boolean (false: the reads; true: the digits), blk whatever
stands at the number noL l d in the first chain's flat list, and s, s' the states in front of and
behind an accepting step of blk (IM.Yes).
  - xk_later_head: the six tests IM.XK (Johnson/IMR/HandsDef.lean) at the numbers P5J.At.N Zp cF,
    the written lists IM.linksW and IM.placesW and the further test EW h.𝔇.pubD base z
    (Johnson/LPFK9R/SharesAtE.lean: every public item that is open or tied at the border passes
    pubAll) go from border noL l d at s to border noL l d + 1 at s'. Its premises beside the step
    and the six in front: no mark at s (h0); the open link's frame's group and shape at s (hgs); at
    link 24's reads alone, that s is reached at number 342 of the flat list (hreach); and hbase:
    where base passes a name at one state it passes it at every state.
  - pub_later_head: the further test alone, at the written list linksFull, from the further test and
    the test on the book in front, the frame's shape there, hreach and hbase.
  - pub_later_all: the same for any structure of parameters Dm, with TablesOk at the state in front
    for hreach, under the goals' scope, the reader's return and the opening (hS, hR, O), and from
    named premises on the plan and on public parameters.
  - readers_later_all, found_later_all: the two premises of the library's lemmas on the sort
    formsIn: what a run's reader answers in front it answers behind (ReadersStay); each array of the
    link's second sending is found behind under a new number (SecondFound).
  - Two facts on the written lists, by evaluation in Lean's kernel, with no premise; the second
    shows that the first one's test can fail.
No thread, no prover and no file's bytes occur. No definition. Statements and proofs.

How it fits. xk_later_six_W (Johnson/Desc/ProofFile/Honest/K1/Law/FiftyAtHead.lean) gives the six
tests behind from the six in front and the further test at the state behind. That last premise is
proved here. Every item behind stood in front, or is tied or made at the place (the field pubs of
the table's row: rowL_reads_full, rowL_digits_full, Johnson/Desc/K1/Law/RowLFull.lean). What stood
in front: ride_later_all (Johnson/Desc/ProofFile/Honest/K1/Law/RideAtFifty.lean), and for formsIn
and formsInT pub_formsIn_later_plan and pub_formsInT_later
(Johnson/Desc/K1/Law/PubAtLaterIndex.lean). What is tied, at the reads: formsIn, by tied_reads_full
(Johnson/Desc/K1/Law/FormsAtFifty.lean) and pub_formsIn_new_later
(Johnson/Desc/K1/Law/GoAtLaterForms.lean). What is made, at the reads: sentIs1_later_all. No mark
behind: mark_later_head, inside xk_later_six_W.

Proofs that this file follows: hRd_any (Johnson/Desc/K1/Law/ReadersHeadReads.lean) and hRd_of_runs
(Johnson/Desc/K1/Law/ReadersByRun.lean) in readers_later_all; secondFound_reads
(Johnson/Desc/K1/Law/HpubPointwise.lean) in found_later_all; inAt_book
(Johnson/Desc/K1/Law/PubAtLaterCall.lean) for the book's two equations. Each is typed anew with its
premise InAt (the whole promise in front, with the files' strings) replaced by what its proof takes
from it. runsFit_all is runsFit_mw (Johnson/Desc/K1/Law/ReadersByRun.lean) with moreAll in the place
of its table.

Lemmas used beside these: fwd_all (Johnson/Desc/K1/Law/ReadersHeadReads.lean), runsFit_of
(Johnson/Desc/K1/Law/ReadersByRun.lean), secondFound_of (Johnson/Desc/K1/Law/HpubPointwise.lean),
sentIs_k1Reads (Johnson/Desc/K1/Law/SentIsAtReads.lean); under the head k01_flat
(Johnson/Desc/K1/Law/LettersAtFifty.lean), planK1_head
(Johnson/Desc/ProofFile/Honest/K1/Law/FiftyAtHead.lean) with hinj_of, trees_of, msgs_of and hP_of
(Johnson/Desc/K1/Law/CallsC.lean), sides_later_head
(Johnson/Desc/ProofFile/Honest/K1/Law/RideAtFifty.lean), hlk_atAll
(Johnson/Desc/K1/Law/LinksQuietAtAll.lean), sortB_iff (Johnson/Desc/AtSeats/SortAtOpen.lean),
hAt_scope (Johnson/Desc/K1/Law/TestsInScope.lean), no_tables_342
(Johnson/Desc/AtSeats/TablesAtHead.lean) with tablesOk_of_no
(Johnson/Desc/K1/Law/TablesWalkHead.lean).

Names (namespace ProofFile.Honest.K1).
  runsFit_all, runsFit_all_fails   the kernel's two; for them the recursion depth is raised in this
    file (maxRecDepth 1000000, as in the file whose test it is).
  readers_later_all, found_later_all, pub_later_all, pub_later_head, xk_later_head   as above.

Limits, the weightiest first.
  1. This file shows no value of the head h, and no state at which the premises of xk_later_head
    hold. That blk accepts anywhere is not shown here.
  2. hgs and hreach are premises at the state in front. This file does not prove them.
  3. hbase holds at the library's closed meaning beneath, vacuously (hbase_mgBase,
    Johnson/Desc/ProofFile/Honest/K1/Law/RideAtFifty.lean, with that file's limit 2).
  4. At the further test EW, which has no "in order". At P1K2.EQ (Johnson/P1K2R/TieTwo.lean) "in
    order" at the state behind is wanted beside it; this file does not prove that.
  5. The samples' test is not touched here: it stands in
    Johnson/Desc/ProofFile/Honest/K1/Law/HeldAtFifty.lean.
  6. At the written list linksFull and the table moreAll. Nothing on the first segment's opening
    (number 2) or on W's sending (number 356).
  7. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.RideAtFifty
import Johnson.Desc.ProofFile.Honest.K1.Law.FiftyAtHead
import Johnson.Desc.K1.Law.ReadersHeadReads
import Johnson.Desc.K1.Law.HpubPointwise
import Johnson.Desc.K1.Law.GoAtLaterForms
import Johnson.Desc.K1.Law.FormsAtFifty
import Johnson.Desc.K1.Law.LinksQuietAtAll
import Johnson.Desc.AtSeats.TablesAtHead
import Johnson.LPFK9R.SharesAtE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place FileDescription)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf pubAll ePubAt)
open VerifiableInference.Desc.First.Look (HeardNoneAll)
open VerifiableInference.Desc.Sound (linksFull moreAll MgData runsAt)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K1
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open IM (k1Ix)
open Johnson.Desc.First.Walk.Tied (Reach)

/-! ## 1 Two facts on the written lists at moreAll, by evaluation in Lean's kernel -/

/-- At all fifty: each formsIn or formsInT in front of the place is the link's own, and each run
that it stands for is on the written list runsL. -/
theorem runsFit_all : ((List.range 25).all fun l => [false, true].all fun d =>
    runsFitB moreAll l d (runsL l d)) = true := by
  decide +kernel

/-- **The test can fail**: at link 3's digits, with link 4's list. -/
theorem runsFit_all_fails : runsFitB moreAll 3 true (runsL 4 true) = false := by
  decide +kernel

/-! ## 2 The two arms on forms -/

section
variable {Xi Pp Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi Pp Tok rows cols nR XV) (base : First.Pub → Pp × S → Bool)
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base₀ : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **What a run's reader answers in front of an accept it answers behind**, at every formsIn or
formsInT in front; and the item is the link's own. hT: the invariant TablesOk at x, asked at link
24's reads alone. -/
theorem readers_later_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX : headLink XV = 24)
    (hXW : XV.hS = Bs.G₀.W.hS ∧ XV.HLy = Bs.G₀.W.HLy ∧ XV.H = Bs.G₀.W.H) (l : ℕ) (hl : l < 25)
    (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (x x' : Pp × S)
    (hY : YesOf (blkL Z Bs.G₀ l d X arrs) x x')
    (hT : l = 24 → d = false → TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H x.2) (m j : ℕ)
    (r : String)
    (hq : First.Pub.formsIn m j r ∈
      (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨
      First.Pub.formsInT m j r ∈
      (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) :
    m = l ∧ ReadersStay Dm.pubD m j r x.2 x'.2 := by
  obtain ⟨rfl, hsub⟩ := runsFit_of (List.all_eq_true.1
    (List.all_eq_true.1 runsFit_all l (List.mem_range.2 hl)) d (by cases d <;> simp)) m j r hq
  refine ⟨rfl, fun p hp => ?_⟩
  have hp' : p ∈ runsAt linksFull m j r := by
    have e : Dm.pubD.runs = runsAt linksFull := show runsAt Dm.links = runsAt linksFull by rw [hDlk]
    rw [e] at hp
    exact hp
  show Fwd (K9.readersAt Dm.lk XV (headLink XV) m) p.1 p.2 x.2 x'.2
  cases e : Dm.lk m with
  | none =>
    rw [K9.readersAt_none _ _ _ _ e]
    intro R hR'
    cases hR'
  | some lk =>
    rw [K9.readersAt_some _ _ _ _ lk e]
    rw [hlk m hl] at e
    exact fwd_all hS hR O hX hXW m hl d X arrs lk e x x' hY hT p (hsub p hp')

/-- **Each array of the link's second sending is found behind an accept of the reads, under a new
number**, if all items in front pass and the open link's frame has the plan's shape, under the test
hAt on the plan. -/
theorem found_later_all (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) (X : LinkH)
    (arrs : Option (List ℕ)) (x x' : Pp × S) (hY : YesOf (blkL Z G l false X arrs) x x')
    (hF : ∀ q ∈
      (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)),
      pubAll Dm.pubD base q x = true)
    (hshape : ∀ Lk, x.2.link? = some Lk → Lk.check.frame.shape = Dm.shape)
    (hAt : secondAtB Dm.shape l (Dm.pubD.dS.own l).size (parL Z G l false).sent.size = true) :
    SecondFound (idsOf (parL Z G l false) x.2.st.oracles.size).toList x.2 x'.2 := by
  obtain ⟨_, rs, gs, hfit, hd⟩ := hY
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  obtain ⟨r₁, r₂, e⟩ := List.length_eq_two.1 hlen
  rw [e] at hd
  have h0 := hF _ (open_of (List.all_eq_true.1 sentIn_all l (List.mem_range.2 hl)))
  rw [First.pubAll_more_sentIs] at h0
  have h1 := sentIs_k1Reads Z G l X _ arrs x.2 x'.2 r₁ r₂ gs hd Dm.pubD.dS l h0
  exact secondFound_of h0 h1 hshape (by rw [idsOf_size]; exact hAt)

/-! ## 3 Every item behind -/

/-- **If every public item in front passes, every public item behind an accept passes.** Under the
test on the book, the frame's shape and (at link 24's reads) TablesOk at x, and under named premises
on base, on the plan and on public parameters. -/
theorem pub_later_all
    (hbase : ∀ m n (x x' : Pp × S), base (.more (some m) n) x = true →
      base (.more (some m) n) x' = true)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX : headLink XV = 24)
    (hXW : XV.hS = Bs.G₀.W.hS ∧ XV.HLy = Bs.G₀.W.HLy ∧ XV.H = Bs.G₀.W.H)
    (hW : HeardNoneAll Bs.G₀.W) (hSo : sortB XV = true)
    (hOwn1 : own1B Dm.shape Dm.N Dm.links Z Bs.G₀ = true) (l : ℕ) (hl : l < 25) (d : Bool)
    (hAt : secondAtB Dm.shape l (Dm.pubD.dS.own l).size (parL Z Bs.G₀ l false).sent.size = true)
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      Dm.N.groupAt m' = Dm.N.groupAt l → m' = l)
    (trees : Dm.N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      Dm.N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z Bs.G₀ l d)).shapes.size)
    (msgs : Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z Bs.G₀ l d).sent.size)
    (hP : laterSeatsB Dm.N (parL Z Bs.G₀ l d) l (momL d)
      (Dm.N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (X : LinkH) (arrs : Option (List ℕ)) (x x' : Pp × S)
    (hY : YesOf (blkL Z Bs.G₀ l d X arrs) x x')
    (hT : l = 24 → d = false → TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H x.2)
    (hshape : ∀ Lk, x.2.link? = some Lk → Lk.check.frame.shape = Dm.shape)
    (hbk : First.bookAt Dm.N (flatPlacesOf linksFull true)[noL l d]? x.2 = true)
    (hF : ∀ q ∈ (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
      pubAll Dm.pubD base q x = true) :
    ∀ q ∈ (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      pubAll Dm.pubD base q x' = true := by
  intro q hq'
  have hY' := hY
  obtain ⟨_, rs, gs, hfit, hd⟩ := hY'
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  have hbk' := hbk
  unfold First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  have ht : momL d < 3 := by cases d <;> decide
  have hSd := laterSend_blkL Z Bs.G₀ l d X arrs
  have hpubs : q ∈
      (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨
      q ∈ tiedL moreAll l d := by
    cases d with
    | true => exact (rowL_digits_full Dm.N moreAll l hl _ _ hinj trees msgs).pubs q hq'
    | false => exact (rowL_reads_full Dm.N moreAll l hl _ _ hinj trees msgs).pubs q hq'
  rcases hpubs with hq | hq
  · by_cases hn : ∀ m j r, q ≠ .formsIn m j r ∧ q ≠ .formsInT m j r
    · exact ride_later_all Dm base hbase Z Bs.G₀ hW hSo l hl d X arrs x x' hY hF q hq hq' hn
    · have h0 := hF q hq
      cases q with
      | formsIn m j r =>
        obtain ⟨rfl, hRd⟩ := readers_later_all Dm hS hR O hDlk hlk hX hXW l hl d X arrs x x' hY hT
          m j r (Or.inl hq)
        exact pub_formsIn_later_plan hSd Dm.pubD base x x' _ gs hlen hd m j r hRd (momL d) _ ht
          hbk'.1.2 hbk'.1.1 hP h0
      | formsInT m j r =>
        obtain ⟨rfl, hRd⟩ := readers_later_all Dm hS hR O hDlk hlk hX hXW l hl d X arrs x x' hY hT
          m j r (Or.inr hq)
        exact pub_formsInT_later hSd Dm.pubD base x x' _ gs hlen hd m j r hRd h0
      | _ => exact (hn fun m j r => ⟨nofun, nofun⟩).elim
  · cases d with
    | true =>
      have e := eq_of_beq (List.all_eq_true.1 made_digits_all l (List.mem_range.2 hl))
      have hq2 : q ∈ [] ++
          madeAt moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2) := hq
      rw [e] at hq2
      cases hq2
    | false =>
      have hq2 : q ∈ tiedAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) ++
          madeAt moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) := hq
      rcases List.mem_append.1 hq2 with hq3 | hq3
      · obtain ⟨j, r, rfl, ho⟩ := tied_reads_full l hl q hq3
        have hin : First.Pub.formsInT l j r ∈
          (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
          First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)) :=
          List.mem_append_right _ ho
        obtain ⟨-, hRd⟩ := readers_later_all Dm hS hR O hDlk hlk hX hXW l hl false X arrs x x' hY
          hT l j r (Or.inr hin)
        exact pub_formsIn_new_later hSd Dm.pubD base x x' _ gs hlen hd hbk'.1.2 l j r hRd 1 _
          (by decide) hbk'.1.1 hP
          (found_later_all Dm base Z Bs.G₀ l hl X arrs x x' hY hF hshape hAt) (hF _ hin)
      · rw [eq_of_beq (List.all_eq_true.1 made_reads_all l (List.mem_range.2 hl))] at hq3
        obtain rfl : q = .more (some l) "frame.sentIs1" := List.mem_singleton.1 hq3
        exact sentIs1_later_all Dm base Z Bs.G₀ hOwn1 l hl X arrs x x' hY hF hbk

end

/-! ## 4 Under the library's head: the six tests, with no premise at the state behind -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The further test behind an accepting step of what stands at the place's number**, under the
head: from the further test and the test on the book in front, the frame's shape there, and (at link
24's reads) that the state is reached. Under hbase. -/
theorem pub_later_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (d : Bool) {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[noL l d]? = some blk)
    (base : First.Pub → ProofFile.InstPub × S → Bool)
    (hbase : ∀ m n (x x' : ProofFile.InstPub × S), base (.more (some m) n) x = true →
      base (.more (some m) n) x' = true)
    (z : ProofFile.InstPub) (ft : ℕ) {s s' : S}
    (hshape : ∀ L, s.link? = some L → L.check.frame.shape = h.𝔇.shape)
    (hreach : l = 24 → d = false → Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (341 + 1) (z, s))
    (hy : IM.Yes ft blk s s')
    (hbk : First.bookAt h.𝔇.N (flatPlacesOf linksFull true)[noL l d]? s = true)
    (hF : ePubAt (pubAll h.𝔇.pubD base) moreAll linksFull (flatPlacesOf linksFull true) (noL l d)
      (z, s) = true) :
    ePubAt (pubAll h.𝔇.pubD base) moreAll linksFull (flatPlacesOf linksFull true) (noL l d + 1)
      (z, s') = true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨e, X, arrs, he, hu⟩ := K1.k01_flat h.scope h.reads O l hl d
  obtain rfl : e = blk := Option.some.inj (he.symm.trans hb)
  have H := planK1_head h O
  obtain ⟨hW, hSo, hOwn1⟩ := sides_later_head h O
  have hs := K1.hs_atAll h O (K1.pin1_atAll h)
  have eW : Bs.G₀.W = P5J.At.X Zp := O.W
  refine List.all_eq_true.2 (pub_later_all h.𝔇 base hbase h.scope h.reads O (K1.hDlk_atAll h)
    (K1.hlk_atAll h) ((sortB_iff _).1 hSo) (by rw [eW]; exact ⟨rfl, rfl, rfl⟩) hW hSo hOwn1 l hl d
    (hAt_scope h.𝔇 (K1.hDsh_atAll h O (K1.pin1_atAll h)) Zp Bs.G₀ hs l hl) (K1.hinj_of H l hl d)
    (K1.trees_of H l hl d) (K1.msgs_of H l hl d) (K1.hP_of H hs l hl d) X arrs (z, s) (z, s')
    (K1.yesOf_of_yes hu hy z)
    (fun h1 h2 => tablesOk_of_no _ _ _ _ (no_tables_342 h.scope h.reads O (z, s) (hreach h1 h2)))
    hshape hbk (List.all_eq_true.1 hF))

/-- **The six tests at the next border, behind an accepting step of what stands at the place's
number**, under the head: from the six in front, no mark there, the open link's frame's group and
shape there, and (at link 24's reads) that the state is reached. Under hbase. Beside the step no
premise speaks of the state behind. -/
theorem xk_later_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (d : Bool) {blk : Block S ProofFile.Cl} (hb : cF.blocksInOrder[noL l d]? = some blk)
    (base : First.Pub → ProofFile.InstPub × S → Bool)
    (hbase : ∀ m n (x x' : ProofFile.InstPub × S), base (.more (some m) n) x = true →
      base (.more (some m) n) x' = true)
    (z : ProofFile.InstPub) (ft : ℕ) {s s' : S}
    (hgs : ∀ L, s.link? = some L → L.check.frame.group = h.𝔇.N.groupAt l ∧
      L.check.frame.shape = (Sound.d13 h.𝔇).shape)
    (hreach : l = 24 → d = false → Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (341 + 1) (z, s))
    (hy : IM.Yes ft blk s s') (h0 : s.failed = none)
    (hx : IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (LPFK9.HandsAt.EW h.𝔇.pubD base z) (noL l d)
      s = true) :
    IM.XK (P5J.At.N Zp cF) IM.linksW IM.placesW (LPFK9.HandsAt.EW h.𝔇.pubD base z) (noL l d + 1)
      s' = true := by
  have eE : LPFK9.HandsAt.EW h.𝔇.pubD base z = fun k t =>
      ePubAt (pubAll h.𝔇.pubD base) moreAll linksFull (flatPlacesOf linksFull true) k (z, t) := by
    funext k t
    unfold LPFK9.HandsAt.EW
    rw [IM.placesW_full, IM.linksW_full]
  refine xk_later_six_W h hl d hb _ ft (fun _ L hL => by rw [← head_N_is h]; exact (hgs L hL).1) hy
    h0 hx ?_
  have hp := IM.xk_parts hx
  rw [IM.placesW_full, ← head_N_is h] at hp
  rw [eE] at hp ⊢
  exact pub_later_head h hl d hb base hbase z ft (fun L hL => (hgs L hL).2) hreach hy hp.2.2.2.1
    hp.2.2.2.2

end ProofFile.Honest.K1
