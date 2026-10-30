-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/CoinsTieOfFacts.lean: kind K13, the members' batching: UNDER EIGHT
FACTS ON THE VERIFIER's STATE WHEREVER THE THREAD STANDS AT THE BORDER b, THREE ON THE READER AND
TWO PUBLIC LISTS, AND EIGHT NAMED PREMISES ON THE SCRIPT, THE THREAD, THE SENDER's TEXT AND THE BOOK
(they are not shown here; at the library's letters and the written Script of the first chain the tie
stands under the head and the maker's return alone: `k13_coinsTie_at_firstScript`,
AtFullSide/K13/FiveAt355AtFirstScript.lean; that the thread stands anywhere is shown neither here
nor there): THE KIND's TIE `CoinsTie` (ExchangeAtM3.lean of this folder): where the verifier's
taking of 2 kCol + 1 mask entries and the book's lending return, what the reader reads under these
entries are the values that the book lends the kind's row, read into the reader's field. One
statement with its proof; no definition. General in the thread's letters, the border, the message's
number and the number k₀ of takes in front.

Main name: `coinsTie_of_facts`.

THE PREMISES, EACH WITH WHOSE IT IS TO SHOW.
  hrd the reader's mask entries are `rwBook`'s (Johnson/Desc/K13/Law/ReaderByBook.lean): the
      caller's: by unfolding at the library's reader
  hsh, hq public lists: the message number im has the shape sh and the pair q: the caller's: closed
      facts
  hSt EIGHT FACTS ON THE STATE UNDER THE THREAD: whoever shows the thread's facts at the border: the
      index masks' message has the number im; five public tests (those of
      `OnBytes.Road.K4.Rec.mask_entry_at`); the message's ledger is that of k₀ takes (`LedgerAt`,
      Johnson/Desc/K13/Law/LedgerWithin.lean); free is the shape's count of free entries at the
      state's codes
  hO THE SCRIPT's: `OwnMsgs` (Honest/Thread/ScriptLots.lean) at the message's number in the witness,
      arr q.1 q.2, at the SENDER's text txt
  hV THE THREAD's: where it stands the input is one that Vd admits and at least N challenges are
      heard
  hTxt THE SENDER's: at an input that Vd admits and at least N challenges: its text at row ν % R,
      place ν / R is its own row's entry ν at its own coins, for ν below free
  h2 `SenderLaysOwn` (Honest/Law/Rule/TiesOwn.lean): that row's entry ν is the sender's value number
      base + ν. IT IS THE CALLED LEMMA's FORM, KEPT FOR THE CALL, AND NO DEBT BY ITSELF: at rowOf cs
      ν := (coinsE cs).getD (base + ν) zeroE it holds by unfolding; hTxt and h2 together say one
      sentence on the sender's text. So laid, for a sending of kind K1's: CoinsTieOfK1.lean of this
      folder
  ho THE BOOK's: `OwnIs` (there)
  hin THE SENDER's: base + ν lies inside its part's count
  hS THE BOOK's: the test `oneStretch` (Honest/BookStretch.lean) on the book's entries for the
      kind's row answers: one stretch of the sender's, from base + k₀ on, 2 kCol + 1 long
  hfree closed numbers: k₀ + (2 kCol + 1) ≤ free: the caller's

How. `coinsTie_iff_spent` (TiesToCommonForms.lean of this folder): `CoinsTie` is the common form `MaskTie` at
all that the row's parts spend. `maskTieOn_whole_free` (Honest/Law/Rule/TiesFree.lean) gives that
form from the sender's sentence, the book's two, the reader's and the ledger's. The reader's
sentence (`ReaderReads`) is shown here, by `reader_mask_own` (ReaderMaskScript.lean of this folder)
at every ν below free. The ledger's is met by rfl at the constant k₀: its work is done by
`takeMasksP_numbers` (Johnson/Desc/K13/Honest/TakenList.lean): under `LedgerAt` the entries taken
are those of the takes k₀, k₀ + 1, …. That the stretch lies inside what the look hands at the
sender's address follows from ho, hin and hfree. That the row spends 2 kCol + 1 values: `k13_ownRun`
(CoinsThere.lean of this folder).

Limits. NOT IN FRONT OF A LAW OVER COINS: a rule of use, told whole in the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean ("A limit on the coins"). THE GROUND HERE. `CoinsTie`, and
those premises that name a run's coins k, tie what the reader reads of the Script's witness to that
run's coins: the rule's first kind; no made term and no lemma lifts the bar: it is flat. The
premises on the Script, the book and the hidden input that name no coin are of its second kind: a
statement on how what is sent or shown is distributed may lean on this file only if it names them in
its own text as premises; it may not discharge, hide or assume them in silence. The premises on
public numbers tie nothing. (If the library at hand does not hold that file, the ground told here
stands by itself.) BY LETTER, at `coinsTie_of_facts`: a run's coins are named in hSt, hV, hO, hTxt
and ho; no run's coins are named in hS (the book's entries), in h2 (the sender's row, at every value
of one part's coins) and in hrd (the reader); hsh, hq, hin and hfree are on public lists and
numbers. CONDITIONAL ON ALL OF THESE: none is shown here of any thread, Script or book, nor all
together of any; where the thread stands nowhere, where the book's lending errs or where the
verifier's taking does not return, the tie holds for nothing. THREE TIES OF COUNTS ARE PREMISES
HERE, AND NO LAW JOINS THEM: (1) in hS: the start of the book's entry is the SUM of the sender's own
base and the ledger's k₀: three counts of three texts; (2) in hO: the number at which the sender's
text is laid into the Script is arr q.1 q.2; (3) sh, its rows and free, which are read off the
verifier's list M and the state's codes, are the sender's own shape and codes. "Coin" is the frame's
word for a value that the book hands out: no entry is said to be fresh or masked. This file's
imports reach Johnson/Goal/ by ExchangeAtM3.lean, where `CoinsTie` is defined, on two roads: by
FromThreadAt.lean, for its use at the library's own parameters, whose hypothesis (`P5J.AtMgA`) is
stated over the goals' description; and by FromStep.lean, through the library's list of the first
chain's places (Johnson/IMR/FirstSeats.lean). No definition stands here.

What is not claimed. That any premise holds. It is none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.TiesToCommonForms
import Johnson.Desc.ProofFile.Honest.K13.CoinsThere
import Johnson.Desc.ProofFile.Honest.K13.ReaderMaskScript
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open OnBytes.Slice (GE)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K12.Door (msgShapesB bookInOrderB seatsCarriedB placesBelowB
  msgShape_at)
open VerifiableInference.Desc.K13 (Where St)
open VerifiableInference.Desc.K13.Law (Wit ρg dOf rwBook LedgerAt)
open VerifiableInference.Desc.K13.Honest (takeMasksP_numbers)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Letters OwnMsgs)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok : Type}

/-- **`CoinsTie` FROM THE FACTS ON THE STATE, THE SENDER's TEXT AND THE BOOK.** CONDITIONAL: on
every premise named; whose each is to show: the head. -/
theorem coinsTie_of_facts (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok MsgT) (b : Nat)
    (weights : W₀ → Weights) (pile : PileOf Xi) (P : Where)
    (rd : Pp × S → VerifiableInference.Desc.Wit Cells Tok MsgT →
      Wit GE P.lin.matrixRows P.lin.kCol)
    {nR kC : ℕ} (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin kC → Bool) → GE)
    (hrd : ∀ a v, (rd a v).mask = (rwBook arr mat a v).mask)
    (M : List OracleShape) (Ld : VerifiableInference.Desc.K12.Door.Laid) (im k₀ free : ℕ)
    (sh : OracleShape) (q : ℕ × ℕ)
    (hsh : M[im]? = some sh) (hq : Ld.places[im]? = some q)
    (hSt : ∀ k s m En, Thr L.thread b k s m En →
      s.out.indexMasks = im ∧ msgShapesB M s.st = true ∧
        bookInOrderB 0 s.book s.roots = true ∧ seatsCarriedB Ld s.book = true ∧
        s.book.place.size = s.st.oracles.size ∧
        placesBelowB Ld s.book.place.size s.book.trees.size = true ∧ LedgerAt s.st im k₀ ∧
        free = Send.freeMaskEntries sh.maskRows (s.st.codes.mask.getD sh.maskCode default).ell
          sh.answers)
    {Vd : Local W₀ Rc Xi Tr → Prop} {N fx : ℕ}
    {txt : Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → ℕ → ℕ → Option GE}
    (hO : OwnMsgs L.Q Vd N (arr q.1 q.2) fx txt)
    (hV : ∀ k s m En, Thr L.thread b k s m En → Vd m.st.input ∧ N ≤ m.st.heard.length)
    {o : Addr} {d : Due} {rowOf : Cs d → ℕ → E} {own : Coins Bk → Cs d} {base : ℕ}
    (hTxt : ∀ k w (hd : List Fmt.Drawn) ν, Vd w → N ≤ hd.length → ν < free →
      txt k w (hd.take fx) true (ν % sh.maskRows) (ν / sh.maskRows) =
        some (ρg.val (rowOf (own k) ν)))
    (h2 : SenderLaysOwn rowOf base (· < free)) (ho : OwnIs Bk L.thread.chain o d own)
    (hin : ∀ ν, ν < free → base + ν < d.e)
    (hS : ∀ blk, L.thread.bs[b]? = some blk →
      oneStretch (rowEntries Bk blk.place 2 0) = some (o, base + k₀, 2 * P.lin.kCol + 1))
    (hfree : k₀ + (2 * P.lin.kCol + 1) ≤ free) :
    CoinsTie L b weights pile P rd := by
  refine (coinsTie_iff_spent L b weights pile P rd).2 fun blk hb => ?_
  -- the stretch lies inside what the look hands at the sender's address
  have hF : ∀ k : Coins Bk,
      base + k₀ + (2 * P.lin.kCol + 1) ≤ (k.look L.thread.chain o).1.e := by
    intro k
    have hd : 0 + d.e ≤ (k.look L.thread.chain o).1.e := by
      have e := ho k
      unfold Cs.cut at e
      split at e
      · rename_i hc
        exact hc.2
      · cases e
    have hi := hin (k₀ + 2 * P.lin.kCol) (by omega)
    omega
  -- the message's shape at a state under the thread
  have hshape : ∀ {k s m En}, Thr L.thread b k s m En → ∃ x : OnBytes.Oracle,
      s.st.oracles[im]? = some x ∧ x.shape = sh ∧ im < s.st.oracles.size ∧ 0 < sh.maskRows ∧
        1 ≤ sh.answers := by
    intro k s m En hT
    obtain ⟨_, h₁, _, _, _, _, hL, _⟩ := hSt k s m En hT
    obtain ⟨x, _, hx, _, hm, ha, _⟩ := id hL
    obtain ⟨hoo, _⟩ := Array.getElem?_eq_some_iff.1 hx
    have hxs : x.shape = sh := by
      have e := msgShape_at h₁ im hoo
      rw [hx, hsh] at e
      exact Option.some.inj e
    exact ⟨x, hx, hxs, hoo, hxs ▸ hm, hxs ▸ ha⟩
  -- the reader's sentence, at every take below the free count
  have h3 : ReaderReads L.thread (Thr L.thread b) (k13Opn P)
      (fun (_ : List Nat × St) s (w : Local W₀ Rc Xi Tr)
        (v : VerifiableInference.Desc.Wit Cells Tok MsgT) ν =>
        (rd (L.pubOf w.x, s) v).mask ⟨im, takenNo sh.maskRows ν⟩) ρg.val
      (fun k _ _ ν => rowOf (own k) ν) (· < free) := by
    intro k s m En hT a _ ds ν hν
    obtain ⟨_, h₁, h₂, h₃, hs, hbk, _, hf⟩ := hSt k s m En hT
    obtain ⟨_, _, _, hoo, hm, ha⟩ := hshape hT
    obtain ⟨hv, hN⟩ := hV k s m En hT
    show (rd (L.pubOf m.st.input.x, s) (L.Q.wit k m.st.input (m.st.heard ++ ds))).mask _ = _
    rw [hrd]
    exact reader_mask_own L.Q k m.st.input (m.st.heard ++ ds) arr mat M Ld _ s im ν sh q h₁ h₂ h₃
      hs hbk hoo hsh hq hm ha (hf ▸ hν) hO hv (by rw [List.length_append]; omega)
      (hTxt k _ _ ν hv (by rw [List.length_append]; omega) hν)
  have key := maskTieOn_whole_free (T := L.thread) (At := Thr L.thread b) (p := blk.place)
    (ps := (proverSideOfClaimCombination (Rc := Rc) (Tr := Tr) (X := X) weights pile P).parts) (slot := fun _ => k₀)
    h2 ho hin h3 (fun _ _ _ _ _ _ _ => rfl) (hS blk hb) hF hfree
  intro k s m En hT a c ha hc ds j hj
  have hj' : j < 2 * P.lin.kCol + 1 := hj
  have hlen : (spentOf _ c).length = 2 * P.lin.kCol + 1 := by
    rw [k13_spentOf, coinsE_length]
    exact k13_ownRun P.lin.kCol
  have e := key k s m En hT a c ha hc ds j (by rw [hlen]; exact hj')
  -- the entries taken are those of the takes k₀, k₀ + 1, …
  obtain ⟨hi, _, _, _, _, _, hL, _⟩ := hSt k s m En hT
  obtain ⟨x, hx, hxs, _, _, _⟩ := hshape hT
  have ht : takeMasksP (dOf s) im (Batt.masksOf P.lin.kCol) = some a := by
    rw [← hi]
    exact ha
  have en := takeMasksP_numbers (d := dOf s) hL hx ht
  have hg : (a.1.map fun i => (⟨s.out.indexMasks, i⟩ : Slot)).getD j default =
      ⟨im, takenNo sh.maskRows (k₀ + j)⟩ := by
    rw [en, hi, hxs, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by unfold Batt.masksOf; omega)]
    rfl
  show (rd (L.pubOf m.st.input.x, s) (L.Q.wit k m.st.input (m.st.heard ++ ds))).mask
    ((a.1.map fun i => (⟨s.out.indexMasks, i⟩ : Slot)).getD j default) = _
  rw [hg]
  exact e

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.coinsTie_of_facts
