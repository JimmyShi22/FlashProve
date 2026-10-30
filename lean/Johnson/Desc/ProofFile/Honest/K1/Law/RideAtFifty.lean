-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RideAtFifty.lean: the kind K1's fifty later sendings (every
link's reads and digits): if every public item in front passes its test, then behind an accept of
the sub-protocol every item that was open or tied in front and still is passes too, but for the two
sorts on forms; so does the one name that is made at the reads, if the test on the book holds in
front too. Under side premises on base and on public parameters.

What this file proves. The tests are pubAll Dm.pubD base (Johnson/Desc/First/PubAll.lean), for any
structure of parameters Dm and any tests base beneath; the lists of items are the written ones at
the table of extra public tests moreAll (Johnson/Desc/Sound/MoreAll.lean) and the written list of
links linksFull. l < 25; d is a Boolean (false: the reads; true: the digits); x and x' are the
states in front of and behind an accept of the lot's own sub-protocol blkL (YesOf).
  - ride_later_all: under three side premises (hbase: where base passes a name at one state it
    passes it at every state; hW: HeardNoneAll of the ground's public parameters; hX: the test sortB
    on Dm's), if every item in front passes at x, then an item that stands in front and behind, and
    is neither formsIn nor formsInT, passes at x'.
  - sentIs1_later_all: at the reads, under the test own1B on the plan (hOwn1), if every item in
    front passes at x and the test on the book holds there, the name "frame.sentIs1" of the link
    passes at x'.
  - heard_later_all: at the reads, under hW, if every item in front passes at x, nothing is heard at
    the digits' seat at x'.
  - Seven facts on the written lists, by evaluation in Lean's kernel, with no premise. One of them
    shows that the test on the classes can fail (rest_all_fails).
  - sides_later_head, hbase_mgBase: the side premises hW, hX and hOwn1 under the library's head
    (P5J.AtMgA, Johnson/P5J/MgAtAll.lean) and its opening; hbase at the library's closed meaning
    beneath, mgBase.
Every premise stands at x, on base or on public parameters; of the state behind they say YesOf
alone.
No thread, no prover and no file's bytes occur. No definition. Statements and proofs.

Proofs that this file follows: hPub_of (Johnson/Desc/K1/Law/PubAtLaterCall.lean), hrest_point
(Johnson/Desc/K1/Law/RestAtPlus13.lean), heardNone_at_reads_of
(Johnson/Desc/K1/Law/HeardAtReads.lean), sentIs1_made (Johnson/Desc/K1/Law/HpubAtPlus13.lean),
k5_pub_kept and k5_names_else (Johnson/Desc/K1/Law/K5AtLater.lean), hSort_of
(Johnson/Desc/K1/Law/SortAtFifty.lean). Each is typed anew at pubAll Dm.pubD base and moreAll. The
first four have the premise InAt (the whole promise in front, with the files' strings): it is
replaced by what the proof takes from it, the public tests in front and the test on the book; a
caller that has a state and its tests alone has no InAt. The other three stand at meanings built
with plus13, or at such a meaning's table (mwMore). The kernel's facts are the same files' tests
with moreAll in the place of their table.

Lemmas used: pub_keeper_later (Johnson/Desc/K1/Law/PubAtLaterKeeper.lean), pub_indexIs_later and
pub_indexThere_later (Johnson/Desc/K1/Law/PubAtLaterIndex.lean), pub_look_later and laterLook_blkL
(Johnson/Desc/K1/Law/LookAtLater.lean), pub_hasRow_later (Johnson/Desc/K1/Law/HasRowAtPubAll.lean),
laterK5_blkL (Johnson/Desc/K1/Law/K5AtLater.lean), laterHeard_k1Reads
(Johnson/Desc/K1/Law/HeardAtReads.lean), sentIs_k1Reads_plan
(Johnson/Desc/K1/Law/SentIsAtReads.lean), rest_of and keepsRow_blkL
(Johnson/Desc/K1/Law/RestAtPlus13.lean), keepsKeeper_blkL and laterSend_blkL
(Johnson/Desc/K1/Law/CallsG.lean); for the side premises heardNoneAll_of_public
(Johnson/Desc/First/Look/HeardNone.lean), sortB_open (Johnson/Desc/AtSeats/SortAtOpen.lean),
hOwn1_scope (Johnson/Desc/K1/Law/TestsInScope.lean).

Names (namespace ProofFile.Honest.K1).
  rest_all, rest_all_fails, lookPieces_all, freshIn_all, sentIn_all, made_reads_all, made_digits_all
    the kernel's seven; for them the recursion depth is raised in this file (maxRecDepth 1000000, as
    in the files whose tests they are). made_reads_all and made_digits_all are used by nothing here:
    they are for the step to all items behind (limit 1).
  hSort_all, k5_else_all   two helpers: the lookups' items in front are of the sorts that
    pub_look_later pays; at a link that is no attention link the two names of K5 fall to base.
  heard_later_all, ride_later_all, sentIs1_later_all, hbase_mgBase, sides_later_head   as above.

Limits, the weightiest first.
  1. It ends in none of the table's six tests (IM.XK), and by itself it does not prove the premise
    h6 of xk_later_six_head (Johnson/Desc/ProofFile/Honest/K1/Law/FiftyAtHead.lean): the sort
    formsIn, which rides at the digits and is new at the reads, is left out, and so is the step from
    these items to all items behind. Both stand in
    Johnson/Desc/ProofFile/Honest/K1/Law/PubBehindAtFifty.lean.
  2. hbase_mgBase holds vacuously: mgBase's public test is false everywhere. So at that base the arm
    of ride_later_all that falls to base is never entered: were a name of K5 in front at a link that
    is no attention link, its test would fail at x. This file does not show at which links these
    names stand in front.
  3. This file shows no state at which every item in front passes, and no value of the head. That
    the sub-protocol accepts anywhere is not shown here.
  4. At the written list linksFull and the table moreAll. Nothing on the first segment's opening
    (number 2) or on W's sending (number 356).
  5. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.RestAtPlus13
import Johnson.Desc.K1.Law.SortAtFifty
import Johnson.Desc.K1.Law.HeardAtReads
import Johnson.Desc.K1.Law.K5AtLater
import Johnson.Desc.K1.Law.HpubAtPlus13
import Johnson.Desc.K1.Law.CallsG
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.K1.Law.TestsInScope
import Johnson.Desc.K1.Law.PinsAtHead
import Johnson.Desc.AtSeats.SortAtOpen
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf pubAll pubAll_else)
open VerifiableInference.Desc.First.Look (HeardNoneAll heardNoneAll_of_public k3SortAt)
open VerifiableInference.Desc.First.FillSent (sentIsB secondNos base1At)
open VerifiableInference.Desc.Sound (linksFull moreAll MgData mgBase)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K1
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open H2K5.Door (k5Item)
open _root_.Desc.K14.Law (seatZ secondAt)
open IM (k1Ix)

/-! ## 1 Seven facts on the written lists at moreAll, by evaluation in Lean's kernel -/

/-- **At all fifty: what stands in front and behind, and is none of the seven sorts of sevenItem, is
of four classes**: the link's lookups' three sorts, leftOn, hasRow, the link's two names of K5. -/
theorem rest_all : ((List.range 25).all fun l => [false, true].all fun d =>
    restB moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)
      (fun q => lookAt l q || leftOnItem q || hasRowItem q || k5At l q)) = true := by
  decide +kernel

/-- **The test can fail**: without the class of K5's two names, at link 3's digits. -/
theorem rest_all_fails :
    restB moreAll linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      (fun q => lookAt 3 q || leftOnItem q || hasRowItem q) = false := by
  decide +kernel

/-- At all fifty: the link's lookups' items in front stand at the pieces that lookIsB names. -/
theorem lookPieces_all : ((List.range 25).all fun l => [false, true].all fun d =>
    lookPiecesB moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) l
      (lookIsB l)) = true := by
  decide +kernel

/-- In front of every link's reads the link's linkFresh stands. -/
theorem freshIn_all : ((List.range 25).all fun l =>
    openB moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)
      (.linkFresh l)) = true := by
  decide +kernel

/-- In front of every link's reads the link's name "frame.sentIs" stands. -/
theorem sentIn_all : ((List.range 25).all fun l =>
    openB moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)
      (.more (some l) "frame.sentIs")) = true := by
  decide +kernel

/-- At every link's reads the table makes one name: the link's "frame.sentIs1". -/
theorem made_reads_all : ((List.range 25).all fun l =>
    madeAt moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2) ==
      [.more (some l) "frame.sentIs1"]) = true := by
  decide +kernel

/-- At every link's digits the table makes no name. -/
theorem made_digits_all : ((List.range 25).all fun l =>
    madeAt moreAll linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l true + 2) == []) =
      true := by
  decide +kernel

/-! ## 2 The sorts that ride, and the one made name -/

section
variable {Xi Pp Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi Pp Tok rows cols nR XV) (base : First.Pub → Pp × S → Bool)

/-- The lookups' items that are open in front of a later sending are of the sorts that
pub_look_later pays. -/
theorem hSort_all (hX : sortB XV = true) : ∀ l, l < 25 → ∀ d : Bool, ∀ q, lookAt l q = true →
    q ∈ (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
    lookPaid Dm.pubD (dgsL d) q = true := by
  intro l hl d q hq hmem
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 lookPieces_all l
    (List.mem_range.2 hl)) d (by cases d <;> simp)) q hmem
  rw [hq] at h1
  have h2 : lookIsB l q = true := h1
  have h3 := List.all_eq_true.1 hX l (List.mem_range.2 hl)
  rw [Bool.and_eq_true, beq_iff_eq] at h3
  cases q with
  | linkFresh m => rfl
  | lookIn m pc =>
    have hq' : (m == l) = true := hq
    have h2' : (pc == pD l) = true := h2
    rw [eq_of_beq hq', eq_of_beq h2']
    exact h3.2
  | lookOut m pc =>
    have hq' : (m == l) = true := hq
    have h2' : (pc == pC l) = true := h2
    rw [eq_of_beq hq', eq_of_beq h2']
    show (k3SortAt XV l (pC l)).any (dgsL d) = true
    rw [h3.1]
    cases d <;> rfl
  | _ => cases hq

/-- **Behind an accept of the reads' sub-protocol nothing is heard at the digits' seat.** -/
theorem heard_later_all (Z : ProofFile.Pub) (G : ProofFile.Ground) (hW : HeardNoneAll G.W) (l : ℕ)
    (hl : l < 25) (X : LinkH) (arrs : Option (List ℕ)) (x x' : Pp × S)
    (hY : YesOf (blkL Z G l false X arrs) x x')
    (hF : ∀ q ∈
      (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)),
      pubAll Dm.pubD base q x = true) : HeardNone x'.2 := by
  have h0 := hF _ (open_of (List.all_eq_true.1 freshIn_all l (List.mem_range.2 hl)))
  rw [First.pubAll_linkFresh] at h0
  obtain ⟨_, rs, gs, hfit, hd⟩ := hY
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  exact laterHeard_k1Reads Z G hW l X _ arrs Dm.pubD.d3 l x.2 x'.2 _ gs hlen hd h0

/-- At a link that is no attention link the two names fall to the tests beneath. -/
theorem k5_else_all (m : ℕ) (n : String) (hn : n = "K5.okAt" ∨ n = "K5.plain")
    (hatt : Dm.pubD.d5.isAtt m = false) (a : Pp × S) :
    pubAll Dm.pubD base (.more (some m) n) a = base (.more (some m) n) a := by
  have h5 : k5Item Dm.pubD.d5 (.more (some m) n) = false := by
    show (Dm.pubD.d5.isAtt m && _) = false
    rw [hatt]
    rfl
  have hl : First.FillBare.leftItem Dm.pubD.links (.more (some m) n) = false := by
    show (_ && (n == "K4.rowsBare" || n == "K4.lookLeft")) = false
    rcases hn with rfl | rfl <;> exact Bool.and_eq_false_iff.2 (Or.inr rfl)
  have hs : First.FillSent.sentItem (.more (some m) n) = false := by
    rcases hn with rfl | rfl <;> rfl
  have hs1 : First.FillSent.sent1Item (.more (some m) n) = false := by
    rcases hn with rfl | rfl <;> rfl
  exact pubAll_else Dm.pubD _ (.more (some m) n) rfl rfl rfl rfl rfl rfl h5 hs hs1 hl rfl a

/-- **If every public item in front passes, every one that is open or tied in front and behind, but
for the two sorts on forms, passes behind an accept.** Under hbase, hW and hX. -/
theorem ride_later_all
    (hbase : ∀ m n (x x' : Pp × S), base (.more (some m) n) x = true →
      base (.more (some m) n) x' = true)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) (hW : HeardNoneAll G.W) (hX : sortB XV = true) (l : ℕ)
    (hl : l < 25) (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (x x' : Pp × S)
    (hY : YesOf (blkL Z G l d X arrs) x x')
    (hF : ∀ q ∈ (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
      pubAll Dm.pubD base q x = true)
    (q : First.Pub)
    (hq : q ∈ (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)))
    (hq' : q ∈
      (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)))
    (hn : ∀ m j r, q ≠ .formsIn m j r ∧ q ≠ .formsInT m j r) :
    pubAll Dm.pubD base q x' = true := by
  have h0 := hF q hq
  have hY' := hY
  obtain ⟨_, rs, gs, hfit, hd⟩ := hY'
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  have rest : sevenItem q = false → pubAll Dm.pubD base q x' = true := by
    intro h7
    have hc := rest_of (List.all_eq_true.1
      (List.all_eq_true.1 rest_all l (List.mem_range.2 hl)) d (by cases d <;> simp)) hq hq' h7
    simp only [Bool.or_eq_true] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · have hH : hhL d x'.2 := by
        cases d with
        | true => trivial
        | false => exact heard_later_all Dm base Z G hW l hl X arrs x x' hY hF
      exact pub_look_later (laterLook_blkL Z G l d X arrs) Dm.pubD _ x x' _ gs hlen hd hH q
        (hSort_all Dm hX l hl d q hc hq) h0
    · cases q with
      | leftOn m => rfl
      | _ => cases hc
    · cases q with
      | hasRow m =>
        exact pub_hasRow_later (keepsRow_blkL Z G l d X arrs) _ _ m x x' _ gs hd h0
      | _ => cases hc
    · have hK := laterK5_blkL Z G l d X arrs x.2 x'.2 _ gs hlen hd
      cases q with
      | more sg n =>
        cases sg with
        | none => cases hc
        | some m =>
          have hq2 : (m == l && (n == "K5.okAt" || n == "K5.plain")) = true := hc
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hq2
          obtain ⟨-, hnm⟩ := hq2
          cases hatt : Dm.pubD.d5.isAtt m with
          | true =>
            rcases hnm with rfl | rfl
            · rw [First.pubAll_more_okAt _ _ m hatt] at h0 ⊢
              simp only [hK.1]
              exact h0
            · rw [First.pubAll_more_plain _ _ m hatt] at h0 ⊢
              simp only [hK.2]
              exact h0
          | false =>
            rw [k5_else_all Dm base m n hnm hatt] at h0 ⊢
            exact hbase m n x x' h0
      | _ => cases hc
  cases q with
  | ledger m =>
    exact pub_keeper_later (keepsKeeper_blkL Z G l d X arrs) Dm.pubD base _ rfl x x' hY h0
  | freeAbove m =>
    exact pub_keeper_later (keepsKeeper_blkL Z G l d X arrs) Dm.pubD base _ rfl x x' hY h0
  | unheard =>
    exact pub_keeper_later (keepsKeeper_blkL Z G l d X arrs) Dm.pubD base _ rfl x x' hY h0
  | indexIs =>
    exact pub_indexIs_later (laterSend_blkL Z G l d X arrs) Dm.pubD base x x' _ gs hlen hd h0
  | indexThere =>
    exact pub_indexThere_later (laterSend_blkL Z G l d X arrs) Dm.pubD base x x' _ gs hlen hd h0
  | formsIn m j r => exact absurd rfl (hn m j r).1
  | formsInT m j r => exact absurd rfl (hn m j r).2
  | _ => exact rest rfl

/-- **The one name that is made at the reads passes its test behind an accept**, if all items in
front pass and the test on the book holds, under hOwn1. -/
theorem sentIs1_later_all (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (hOwn1 : own1B Dm.shape Dm.N Dm.links Z G = true) (l : ℕ) (hl : l < 25) (X : LinkH)
    (arrs : Option (List ℕ)) (x x' : Pp × S) (hY : YesOf (blkL Z G l false X arrs) x x')
    (hF : ∀ q ∈
      (First.pubSets moreAll linksFull (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)),
      pubAll Dm.pubD base q x = true)
    (hbk : First.bookAt Dm.N (flatPlacesOf linksFull true)[noL l false]? x.2 = true) :
    pubAll Dm.pubD base (.more (some l) "frame.sentIs1") x' = true := by
  obtain ⟨_, rs, gs, hfit, hd⟩ := hY
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  obtain ⟨r₁, r₂, e⟩ := List.length_eq_two.1 hlen
  rw [e] at hd
  have h0 := hF _ (open_of (List.all_eq_true.1 sentIn_all l (List.mem_range.2 hl)))
  rw [First.pubAll_more_sentIs] at h0
  rw [First.pubAll_more_sentIs1]
  have h1 := sentIs_k1Reads_plan Z G l X _ arrs x.2 x'.2 r₁ r₂ gs hd Dm.pubD.dS l Dm.N _ hbk h0
  have ho : Dm.pubD.dS1.own l = (ownPlus Dm.pubD.dS l (idsOf (parL Z G l false)
      (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l false]?))).own l := by
    show Dm.pubD.dS.own l ++ secondNos Dm.shape (base1At Dm.N Dm.links
      (flatPlacesOf Dm.links true)) l = (if l = l then Dm.pubD.dS.own l ++ idsOf (parL Z G l false)
        (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l false]?) else Dm.pubD.dS.own l)
    rw [if_pos rfl]
    exact congrArg _ (eq_of_beq (List.all_eq_true.1 hOwn1 l (List.mem_range.2 hl)))
  rw [sentIs_congr (ownPlus Dm.pubD.dS l (idsOf (parL Z G l false)
    (Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l false]?))) Dm.pubD.dS1 l x'.2 rfl ho rfl]
  exact h1

end

/-! ## 3 The side premises -/

/-- ride_later_all's premise on the tests beneath, at the library's closed meaning beneath: its
public test is false everywhere, so the premise holds vacuously. -/
theorem hbase_mgBase {Pp W : Type} (m : ℕ) (n : String) (x x' : Pp × S)
    (h : (mgBase : First.Meaning Pp W).pub (.more (some m) n) x = true) :
    (mgBase : First.Meaning Pp W).pub (.more (some m) n) x' = true :=
  h

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The three side premises under the head and its opening**: hW, hX, hOwn1. -/
theorem sides_later_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    HeardNoneAll Bs.G₀.W ∧ sortB (P5J.At.X Zp) = true ∧
      own1B h.𝔇.shape h.𝔇.N h.𝔇.links Zp Bs.G₀ = true :=
  ⟨heardNoneAll_of_public O.public, sortB_open h.scope h.reads O,
    hOwn1_scope h.𝔇 (hDsh_atAll h O (pin1_atAll h)) (hDlk_atAll h) Zp Bs.G₀
      (hs_atAll h O (pin1_atAll h))⟩

end ProofFile.Honest.K1
