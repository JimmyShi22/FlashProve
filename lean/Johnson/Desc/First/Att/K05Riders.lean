-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Riders.lean: THE KIND K5 IN THE CHAIN OF PROMISES: THE FIFTH TIE (what the kind's row does not
close rides back from the statement behind to the statement in front; Johnson/Desc/Sound/ChainOfPromises.lean: TiedAt,
t5), CUT DOWN TO FIVE FACTS ON THE FILLING OF THE TABLE's MEANING AND ONE TEST ON THE TABLE. Seated over the
guard (GuardN.lean); the facts have the promise in hand.

Why. The piece's extractor is the identity on the witness, and a yes of the block is "the record behind the lay; the
oracles below base unturned" (piece_yes_lay, Johnson/Desc/First/Att/K05T2Piece.lean). So the tie says: no open item that
rides reads what the lay turns (the open segment's ledger; what was heard at the kind's seat; the rows owed) or an oracle
from base on. WHICH ITEMS RIDE is a fact on the table: at its own walk: the pile · "constr" of OTHER segments · the index
masks' pin · the open segment's own classes of rows · formsT m 2 "objects".

Main names:
  `riderB m i`: the item is of one of these five sorts.
  `ridersB links ps k m`: A TEST ON THE TABLE: every member of the table's open list at border k is of the row's
    (closed, read, "no mark") or passes riderB.
  `K5FillRel Mg N links π Fr base m pl O Q own`: EIGHT FACTS ON THE FILLING: a sort of rider each (five), and the three
    items of the row's context (for the fourth tie): from the item at (the record behind the lay, y', w) to the item at
    (the record in front, y, w), WITH THE TABLE's PROMISE IN FRONT AND "NO MARK" IN HAND (asked at
    every record one of them at least could not hold at a filling that means the table's words), at every return of the
    hearing and every y' that holds what y holds below base. NONE IS SHOWN AT ANY FILLING.
  `k5_riders_sorted`: the table's three tests (readsOpen · rowsApart · ridersB) give: every item that the rule's open
    set holds at k and that the row does not close passes riderB.
  `k5_h5`: **the fifth tie at a piece that decides as the kind does**, from K5FillRel and that.
  `K05_tiedAt_riders`: K05_tiedAt_own (Johnson/Desc/First/Att/K05Tied.lean) with its h5 paid so: LEFT OF THE THREE TIES: h4.
  `riderB_bites`: controls: the row's own "formsT m 3 own" and the segment's own "constr" are no riders.
Limits. A RULE OVER LETTERS. That the piece's extractor (the identity) IS the table's one extractor at the kind's place
is asked elsewhere (EachExtQ, Johnson/Desc/Sound/BordersFill.lean) and is not shown here. By Lean's evaluator (a harness's print; no kernel
proof) the three tests say yes at the table's two lists of places at every attention segment's place of the kind.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Tied
import Johnson.Desc.Sound.SpineList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Tie.Pv.Att (recOf)
open OnBytes.Road.L5 (dimOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent attCaller attSg JAtt AttOK enMask lookAt)
open VerifiableInference.Desc.Sound (Frame Piece strsOf)
open VerifiableInference.Desc (Claim RoundAsG Place)
open VerifiableInference.Desc.First (Item Pub Meaning Numbers ModelPart onAt stepOpen pubStep rowOf pubRowOf
  pubRowM moreItem tiesOf)

open VerifiableInference.Desc.First (openSets pubSets start openSets_succ pubSets_succ segRow)
open VerifiableInference.Desc.Sound (TiedAt onQ relQ meansQ insQ outsQ rowQ relAt openAfter)
open VerifiableInference.Desc.Sound (openIsList openL insL outsL openL_iff_openSets rowsApart)
open VerifiableInference.Desc.First (readsOpen)

/-- The five sorts of items that ride past the kind's block. -/
def riderB (m : ℕ) : Item → Bool
  | .pile => true
  | .constr n _ => n != m
  | .pinI => true
  | .row n _ => n == m
  | .formsT n k r => n == m && k == 2 && r == "objects"
  | _ => false

/-- A TEST ON THE TABLE. -/
def ridersB (links : List ModelPart) (ps : List Place) (k m : ℕ) : Bool :=
  ((openSets links ps (start links))[k]?.getD []).all fun i => (insL links ps k).contains i || riderB m i

/-- A control. -/
theorem riderB_bites (m : ℕ) (p : First.Part) :
    riderB m (.formsT m 3 "own") = false ∧ riderB m (.constr m p) = false := by
  simp [riderB]

/-- **Eight facts on the filling**: five sorts of riders, and the three items of the row's context. EACH HAS THE TABLE's
PROMISE IN FRONT AND "NO MARK" IN HAND (the tie hands them). -/
structure K5FillRel {Pp W : Type} (Mg : Meaning Pp W) (N : Numbers) (links : List ModelPart) (π : Pp) (Fr : Frame)
    (base m : ℕ) (pl : Place) (O : List Item) (Q : List Pub) (own : Params.AttentionRounds) : Prop where
  pile : ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
    Mg.pile (π, behind s att hd G) (strsOf Fr y') w → Mg.pile (π, s) (strsOf Fr y) w
  constr : ∀ n p, n ≠ m → ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
    Mg.constr n p (π, behind s att hd G) (strsOf Fr y') w → Mg.constr n p (π, s) (strsOf Fr y) w
  pinI : ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
    Mg.pin N.index.1 N.index.2 (π, behind s att hd G) (strsOf Fr y') w → Mg.pin N.index.1 N.index.2 (π, s) (strsOf Fr y) w
  row : ∀ c, ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
    Mg.row m c (π, behind s att hd G) (strsOf Fr y') w → Mg.row m c (π, s) (strsOf Fr y) w
  objects : ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
    Mg.formsT m 2 "objects" (π, behind s att hd G) (strsOf Fr y') w → Mg.formsT m 2 "objects" (π, s) (strsOf Fr y) w
  ctxPin : ∀ t ∈ N.sent m 0, ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
    Mg.pin t.1 t.2 (π, behind s att hd G) (strsOf Fr y') w → Mg.pin t.1 t.2 (π, s) (strsOf Fr y) w
  ctxW : ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
    Mg.pinW (π, behind s att hd G) (strsOf Fr y') w → Mg.pinW (π, s) (strsOf Fr y) w
  ctxSmall : ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
    Mg.constr m .small (π, behind s att hd G) (strsOf Fr y') w → Mg.constr m .small (π, s) (strsOf Fr y) w

/-- **Which items ride**: from the table's three tests. -/
theorem k5_riders_sorted {links : List ModelPart} {ps : List Place} {k m : ℕ}
    (hr : readsOpen links ps (start links) = true) (ha : rowsApart links ps = true) (hk : k ≤ ps.length)
    (hB : ridersB links ps k m = true) (i : Item)
    (ho : openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i) (hn : ¬ insQ links ps k i) :
    riderB m i = true := by
  have hu : Item.unmarked ∈ start links := by simp [start]
  have h1 : i ∈ openL (insL links ps) (outsL links ps) (start links) k :=
    (openIsList Item (insL links ps) (outsL links ps) (start links) k i).1 ho
  have h2 := (openL_iff_openSets links ps (start links) hr ha hu k hk i).1 h1
  have h3 := List.all_eq_true.1 hB i h2
  rcases Bool.or_eq_true _ _ ▸ h3 with h | h
  · exact absurd (by simpa using h) hn
  · exact h

/-- **THE FIFTH TIE AT A PIECE THAT DECIDES AS THE KIND DOES.** -/
theorem k5_h5 {W Cl Pp : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (π : Pp) (k m : ℕ) (Pc : Piece (ckP .two) Fr First.S Cl W) (p : Par) (D : DecidesK5 Pc p)
    (hx : ∀ a τ w, Pc.ext a τ w = w) (pl : Place) (O : List Item) (Q : List Pub)
    (Rel : K5FillRel Mg N links π Fr Pc.base m pl O Q p.own)
    (hS : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      riderB m i = true)
    (a : First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) Pc.ds)) (b : First.S × Fr.E.Str) (w : W) (i : Item)
    (hon : onAt N Mg links (some pl) O Q (π, a.1) (strsOf Fr a.2)) (hm : a.1.failed = none)
    (hout : Pc.ior.red.out a τ = some b) (hall : relQ N Mg links ps (fun s => (π, s)) (k + 1) b w)
    (ho : openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i) (hn : ¬ insQ links ps k i) :
    meansQ N Mg (fun s => (π, s)) i a (Pc.ext a τ w) := by
  rw [hx]
  obtain ⟨att, hd, G, rs, e, hh, eb, hy⟩ := piece_yes_lay Pc p D a b τ hout
  have hb : meansQ N Mg (fun s => (π, s)) i b w := hall i (Or.inl ⟨ho, hn⟩)
  have hs := hS i ho hn
  unfold meansQ at hb ⊢
  rw [eb] at hb
  cases i with
  | pile => exact Rel.pile _ _ _ _ _ _ _ _ hon hm e hh hy hb
  | constr n q =>
    simp only [riderB, bne_iff_ne, ne_eq] at hs
    exact Rel.constr n q hs _ _ _ _ _ _ _ _ hon hm e hh hy hb
  | pinI => exact Rel.pinI _ _ _ _ _ _ _ _ hon hm e hh hy hb
  | row n c =>
    simp only [riderB, beq_iff_eq] at hs
    subst hs
    exact Rel.row c _ _ _ _ _ _ _ _ hon hm e hh hy hb
  | formsT n j r =>
    simp only [riderB, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
    exact Rel.objects _ _ _ _ _ _ _ _ hon hm e hh hy hb
  | _ => exact absurd hs (by simp [riderB])

open Classical in
/-- **THE KIND's BLOCK IN THE CHAIN OF PROMISES, THE FIFTH TIE PAID BY FIVE FACTS ON THE FILLING AND THREE TESTS ON THE
TABLE; the third is the identity; LEFT: the fourth.** -/
theorem K05_tiedAt_riders {W Cl Pp : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
    (hP : PlanIs Wv) (hp4 : Wv.p4 = true) (g m : ℕ) (hm : m = 2 * g + 1) (before : List (ℕ × ℕ))
    (blk : VerifiableInference.Desc.Block First.S Claim)
    (hblk : k5AtN Wv m g before = some blk) (hok : blk.planOk = true)
    (hG : k5GuardN Wv m g = true) {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    {x : VerifiableInference.Desc.First.Look.Place} (hx : lookAt Wv m false = some x) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns base : ℕ)
    (ds : List RDT) (hds : List.Forall₂ RoundAsG ds (rounds (parO Wv m a before)))
    (tj : OnBytes.K.Kc.Tape)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)))
    (yOf : First.S × Fr.E.Str → Ex.Str) (gOf : First.S × Fr.E.Str → Forest.Heard)
    (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
    (I : PinItemP Fr seatSO base W (attSg x D rad).Msg) (R' : First.S × Fr.E.Str → W → Prop)
    (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (π : Pp) (pl pl' : Place)
    (O : List Item) (Q : List Pub) (pC pD : Look.P) (hS : Forest.Shape) (arr : Array (ℕ × String))
    (first kr nsPlan : ℕ) (Ix : K5Place links m pl pl') (Bk : K5Book N pl pl')
    (Pn : K5Plan (parO Wv m a before).own m pC pD hS first kr nsPlan)
    (Fi : K5Fill Mg N π Fr base m O Q (parO Wv m a before).own pC pD arr first nsPlan)
    (hQ : ∀ q ∈ (pubRowOf links pl).asks, q ∈ Q)
    (keptForms : ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ i ∈ O, (rowOf links pl).ins.contains i = false → i ≠ .pinI → ∀ q ∈ tiesOf i,
        Mg.pub q (π, s) = true → Mg.pub q (π, behind s att hd G) = true)
    (madeForms : ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ q ∈ [Pub.formsInT m 3 "own", Pub.formsInT m 2 "planes", Pub.formsInT m 2 "join"],
        Mg.pub q (π, behind s att hd G) = true)
    (madeMore : ∀ (s : First.S) (y : Fr.E.Str) (att : First.AttOwn) (hd : Heard) (G : Fork)
      (rs : List Fmt.RoundView), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → hear (parO Wv m a before).own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ x ∈ (Mg.more.rows links pl).makes, Mg.pub (moreItem x) (π, behind s att hd G) = true ∧
        Mg.pubP (moreItem x) (π, behind s att hd G))
    (hleftIs : ∀ a' : First.S × Fr.E.Str, Mg.pubP (.left m) (π, a'.1) →
      K3LeftOutIs (VerifiableInference.Desc.K3.seatCalls claim).fork
        (VerifiableInference.Desc.K3.seatCalls claim).heard x.fs x.lm x.F.next
        (Cb.Fo.NumsEq.placeOf (enMask x.ns a.seam.tl) plJ)
        (fun F => Room F ns x.F.next
          (Forest.elems x.fs + (slotsOf (script (parO Wv m a before).own) + 0))) (x0 a') (gOf a') a'.1)
    (hokI : ∀ a', onT N Mg links π Fr pl O Q a' → I.ok (I.rc a'.1) a'.2)
    (Bh : K5Behind x a.seam.tl D rad Ex Wp α a (parO Wv m a before) ns base a.nW (plannedK a)
      (padOfO a.fs) tj gOf (onT N Mg links π Fr pl O Q) I R')
    (ps : List Place) (k : ℕ) (hk : ps[k]? = some pl) (hk' : ps[k + 1]? = some pl')
    (hO : O = (openSets links ps (start links))[k]?.getD [])
    (hQs : Q = (pubSets Mg.more links ps)[k]?.getD [])
    (hR' : R' = relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k))
    (h4 : ∀ (a' : First.S × Fr.E.Str) τ b w, onQ N Mg links ps (fun s => (π, s)) k a' → a'.1.failed = none →
      (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).ior.red.out a' τ = some b →
      onQ N Mg links ps (fun s => (π, s)) (k + 1) b → b.1.failed = none →
      relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k) b w →
      ((closedOf (attBase x a.S a.seam.tl D rad)
          (attLin x a.S a.seam.tl D rad Ex Wp α ns
            (numsPlan (parO Wv m a before).own (x.F.next + Forest.elems x.fs))) ns
          (numsPlan (parO Wv m a before).own (x.F.next + Forest.elems x.fs))).own
          (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a') (I.part w) →
      relAt (meansQ N Mg fun s => (π, s)) (insQ links ps k) a' w)
    (Rel : K5FillRel Mg N links π Fr base m pl O Q (parO Wv m a before).own)
    (hr : readsOpen links ps (start links) = true) (hap : rowsApart links ps = true)
    (hB : ridersB links ps k m = true) :
    TiedAt N Mg links ps (fun s => (π, s)) k
      (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W) := by
  have hD : DecidesK5 (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W) (parO Wv m a before) := by
    obtain ⟨a', ha', rfl⟩ := k5AtN_is Wv m g before blk hblk
    obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
    exact decides_k5_ok _ _ _ _ _ _
  have hkl : k ≤ ps.length := by
    have := (List.getElem?_eq_some_iff.1 hk).1
    omega
  exact K05_tiedAt_own claim hP hp4 g m hm before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj x0 yOf gOf plJ I R' N
    Mg links π pl pl' O Q pC pD hS arr first kr nsPlan Ix Bk Pn Fi hQ keptForms madeForms madeMore hleftIs hokI Bh
    ps k hk hk' hO hQs hR' h4
    (fun a' τ b w i hq hmk hout _ hall ho hn =>
      k5_h5 N Mg links ps π k m _ (parO Wv m a before) hD (fun _ _ _ => rfl) pl O Q Rel
        (k5_riders_sorted hr hap hkl hB) a' τ b w i (by
          unfold onQ at hq
          rw [hk, ← hO, ← hQs] at hq
          exact hq) hmk hout hall ho hn)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.riderB_bites
#print axioms VerifiableInference.Desc.First.Att.P.k5_riders_sorted
#print axioms VerifiableInference.Desc.First.Att.P.k5_h5
#print axioms VerifiableInference.Desc.First.Att.P.K05_tiedAt_riders
