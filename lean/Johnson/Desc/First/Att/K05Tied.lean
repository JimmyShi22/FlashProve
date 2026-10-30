-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Tied.lean: THE KIND K5 IN THE CHAIN OF PROMISES: what another file's rule
(Johnson/Desc/Sound/ChainOfPromises.lean: TiedAt k q: the kind's law in its own words and its five ties to the table
of joints) asks at the kind's block: WHICH OF IT IS HAD, AND WHICH IS LEFT, BY NAME.

WHAT IS SHOWN AND WHAT IS TAKEN. SHOWN: the law (K05_at_table, Johnson/Desc/First/Att/K05AtTable.lean, under its own
named premises) · t1 · t2 · the two facts on the block's text ("a mark stays"; "decodes rides"). TAKEN AS PREMISES, BY
NAME: h3, h4, h5: THE THREE TIES OF THE RELATION (what the row opens gives the kind's relation behind; the kind's
relation in front gives what the row closes; what the row does not close rides back). SO THIS IS NOT "TiedAt AT THE
KIND's BLOCK, PROVED": IT IS THE HALF OF IT THAT SPEAKS OF THE PROMISE, WITH THE OTHER HALF NAMED.

Main names:
  `tiedAt_of_table`: GENERAL IN THE PIECE: a law from "the table's promise at ps[k], no mark" to "the table's promise at
    ps[k + 1] at the stepped sets, no mark" (onT), with the two facts and the three ties, is a tie at k. The kind's
    words: o, o' := these two; so t1 and t2 are the unfolding of onQ and the two rules "one border on"
    (Johnson/Desc/First/BordersSucc.lean) and nothing else: t2's whole content sits in the law's "on' b".
  `K05_tiedAt`: that at the seated block k5AtN's piece.
  `K05_tiedAt_own`: at R' := what the row opens, in the table's own words: h3 is then the identity, and its debt
    stands in K5Behind at that R'.
  `k5_opens_iff`, `k5_closes_iff`: what the kind's row opens and closes, item by item.
Premises: K05_at_table's, at O and Q the table's own sets at k; ps[k]? = some pl; ps[k + 1]? = some pl'; h3 (not in
_own), h4, h5.
WHO WOULD PAY. h3: at _own nobody need; K5Behind.worth at that R' is "the three formsT give the forms' worth". h4: the
closed caller's Todo gives constr m idn and worth m 2 "planes" | "keys" | "rider": a fact on the filling of four
letters of the table's meaning. h5: no open item's meaning reads what the lay turns: facts on the filling. NEITHER IS
HELD BY ANYBODY.
Seated over the guard (Johnson/Desc/First/Att/GuardN.lean: seven tests): one letter m for the
block's link and the table's segment, hm : m = 2 * g + 1, hp4 : Wv.p4 = true (K05_at_table's binders).
Limits. A RULE OVER LETTERS. No filling is shown; no member. EMPTY AT: a promise that holds of nothing (every tie but "a
mark stays" is then free).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05AtTable
import Johnson.Desc.First.BordersSucc
import Johnson.Desc.Sound.ChainOfPromises

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

/-- **A law between the table's promises at two neighbouring places, with the two facts and the three ties of the
relation, is a tie.** -/
theorem tiedAt_of_table {W Cl Pp : Type} {C : _root_.Run.PQ.CK} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W)
    (links : List ModelPart) (ps : List Place) (π : Pp) (k : ℕ) (pl pl' : Place) (hk : ps[k]? = some pl)
    (hk' : ps[k + 1]? = some pl') (q : Piece C Fr First.S Cl W) (R R' : First.S × Fr.E.Str → W → Prop)
    (hlaw : q.GoodIn
      (onT N Mg links π Fr pl ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD []))
      (onT N Mg links π Fr pl' (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links pl))
        (pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links pl))) R R')
    (hMark : ∀ a τ b, q.ior.red.out a τ = some b → a.1.failed ≠ none → b.1.failed ≠ none)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (π, a.1) (strsOf Fr a.2) →
      Mg.decodes (π, b.1) (strsOf Fr b.2))
    (h3 : ∀ a τ b w, onQ N Mg links ps (fun s => (π, s)) k a → a.1.failed = none →
      q.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (π, s)) (k + 1) b → b.1.failed = none →
      relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k) b w → R' b w)
    (h4 : ∀ a τ b w, onQ N Mg links ps (fun s => (π, s)) k a → a.1.failed = none →
      q.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (π, s)) (k + 1) b → b.1.failed = none →
      relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k) b w → R a (q.ext a τ w) →
      relAt (meansQ N Mg fun s => (π, s)) (insQ links ps k) a (q.ext a τ w))
    (h5 : ∀ a τ b w i, onQ N Mg links ps (fun s => (π, s)) k a → a.1.failed = none →
      q.ior.red.out a τ = some b → onQ N Mg links ps (fun s => (π, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (π, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (π, s)) i a (q.ext a τ w)) :
    TiedAt N Mg links ps (fun s => (π, s)) k q := by
  have front : ∀ a : First.S × Fr.E.Str, onQ N Mg links ps (fun s => (π, s)) k a → a.1.failed = none →
      onT N Mg links π Fr pl ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD []) a := by
    intro a ha hm
    unfold onQ at ha
    rw [hk] at ha
    exact ⟨ha, hm⟩
  have behindQ : ∀ b : First.S × Fr.E.Str,
      onT N Mg links π Fr pl' (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links pl))
        (pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links pl)) b →
      onQ N Mg links ps (fun s => (π, s)) (k + 1) b := by
    intro b hb
    unfold onQ
    rw [hk', openSets_succ links ps _ k pl hk, pubSets_succ Mg.more links ps k pl hk]
    exact hb.1
  refine ⟨_, _, R, R', hlaw, fun a ha hm => front a ha (not_not.1 hm),
    fun a τ b _ _ _ hb => behindQ b hb,
    fun a τ b w ha hm ho hb hO => h3 a τ b w ha (not_not.1 hm) ho (behindQ b hb) hb.2 hO,
    fun a τ b w ha hm ho hb hO hR => h4 a τ b w ha (not_not.1 hm) ho (behindQ b hb) hb.2 hO hR,
    fun a τ b w i ha hm ho hon hall hi hin => h5 a τ b w i ha (not_not.1 hm) ho hon hall hi hin,
    fun a τ b ho hm => hMark a τ b ho hm, fun a τ b ho hd => hDec a τ b ho hd⟩

/-! ## What the kind's row opens and closes -/

section
variable {W Pp : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W) {links : List ModelPart} {ps : List Place} (π : Pp)
  {k m : ℕ} {pl pl' : Place}

/-- What the row opens, with what it reads, and "no mark": item by item. -/
theorem k5_opens_iff (Ix : K5Place links m pl pl') (hk : ps[k]? = some pl) (b : First.S × Fr.E.Str) (w : W) :
    relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k) b w ↔
      ∀ i ∈ [Item.formsT m 3 "own", .formsT m 2 "planes", .formsT m 2 "join", .pin m 0, .pinW,
        .constr m .small, .unmarked], meansQ N Mg (fun s => (π, s)) i b w := by
  unfold relAt outsQ rowQ
  rw [hk]
  simp only [Option.map_some, Option.getD_some, k5_row Ix]
  exact Iff.rfl

/-- What the row closes, with what it reads, and "no mark": item by item. -/
theorem k5_closes_iff (Ix : K5Place links m pl pl') (hk : ps[k]? = some pl) (a : First.S × Fr.E.Str) (w : W) :
    relAt (meansQ N Mg fun s => (π, s)) (insQ links ps k) a w ↔
      ∀ i ∈ [Item.constr m .idn, .worth m 2 "planes", .worth m 2 "keys", .worth m 2 "rider", .pin m 0, .pinW,
        .constr m .small, .unmarked], meansQ N Mg (fun s => (π, s)) i a w := by
  unfold relAt insQ rowQ
  rw [hk]
  simp only [Option.map_some, Option.getD_some, k5_row Ix]
  exact Iff.rfl

end

/-! ## At the seated block -/

open Classical in
/-- **THE KIND's BLOCK IN THE CHAIN OF PROMISES: the law, t1, t2 and the two facts on the text are had; the relation's
three ties are premises, by name.** -/
theorem K05_tiedAt {W Cl Pp : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
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
    (h3 : ∀ (a' : First.S × Fr.E.Str) τ b w, onQ N Mg links ps (fun s => (π, s)) k a' → a'.1.failed = none →
      (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).ior.red.out a' τ = some b →
      onQ N Mg links ps (fun s => (π, s)) (k + 1) b → b.1.failed = none →
      relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k) b w → R' b w)
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
    (h5 : ∀ (a' : First.S × Fr.E.Str) τ b w i, onQ N Mg links ps (fun s => (π, s)) k a' → a'.1.failed = none →
      (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).ior.red.out a' τ = some b →
      onQ N Mg links ps (fun s => (π, s)) (k + 1) b → relQ N Mg links ps (fun s => (π, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (π, s)) i a' w) :
    TiedAt N Mg links ps (fun s => (π, s)) k
      (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W) := by
  subst hO hQs
  have hD : DecidesK5 (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W) (parO Wv m a before) := by
    obtain ⟨a', ha', rfl⟩ := k5AtN_is Wv m g before blk hblk
    obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
    exact decides_k5_ok _ _ _ _ _ _
  exact tiedAt_of_table N Mg links ps π k pl pl' hk hk' _ _ R'
    (K05_at_table claim hP hp4 g m hm before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj x0 yOf gOf plJ I R' N Mg
      links π pl pl' _ _ pC pD hS arr first kr nsPlan Ix Bk Pn Fi hQ keptForms madeForms madeMore hleftIs hokI Bh)
    (fun a' τ b ho hm => k5_mark_stays _ _ hD a' b τ ho hm)
    (fun a' τ b ho hd => k5_decodes_rides N Mg π _ _ hD Fi a' b τ ho hd) h3 h4 h5

open Classical in
/-- **The same at R' := what the row opens, in the table's own words**: the third tie is the identity; its debt stands
in K5Behind at that R'. -/
theorem K05_tiedAt_own {W Cl Pp : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
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
    (h5 : ∀ (a' : First.S × Fr.E.Str) τ b w i, onQ N Mg links ps (fun s => (π, s)) k a' → a'.1.failed = none →
      (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W).ior.red.out a' τ = some b →
      onQ N Mg links ps (fun s => (π, s)) (k + 1) b → relQ N Mg links ps (fun s => (π, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (π, s)) i a' w) :
    TiedAt N Mg links ps (fun s => (π, s)) k
      (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W) :=
  K05_tiedAt claim hP hp4 g m hm before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj x0 yOf gOf plJ I R' N Mg
    links π pl pl' O Q pC pD hS arr first kr nsPlan Ix Bk Pn Fi hQ keptForms madeForms madeMore hleftIs hokI Bh
    ps k hk hk' hO hQs (fun _ _ _ _ _ _ _ _ _ hW => hR' ▸ hW) h4 h5

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.tiedAt_of_table
#print axioms VerifiableInference.Desc.First.Att.P.k5_opens_iff
#print axioms VerifiableInference.Desc.First.Att.P.k5_closes_iff
#print axioms VerifiableInference.Desc.First.Att.P.K05_tiedAt
#print axioms VerifiableInference.Desc.First.Att.P.K05_tiedAt_own
