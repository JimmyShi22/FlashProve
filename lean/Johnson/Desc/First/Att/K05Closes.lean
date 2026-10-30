-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Closes.lean: THE KIND K5 IN THE CHAIN OF PROMISES: THE FOURTH TIE (the kind's relation in front
gives what the kind's row closes; Johnson/Desc/Sound/ChainOfPromises.lean: TiedAt, t4): THREE QUARTERS OF IT ARE CUT DOWN TO
DICTIONARIES (from what the kind's relation says to three letters of the table's meaning); THE FOURTH QUARTER (worth m 2
"planes") STANDS, NAMED; AND THE TOP: TiedAt AT THE SEATED BLOCK's PIECE UNDER THESE NAMED PREMISES.

IT PROVES NO FILLING. The relation's ties are brought to NAMED PREMISES (K5FillRel: 5 + 3, Johnson/Desc/First/Att/K05Riders.lean;
K5FillIns: 4, here) and three tests on the table. ELEVEN OF THE TWELVE ARE FACTS ON THE FILLING (eight rides back over one return
of the hearing; three dictionaries). THE TWELFTH, K5FillIns.planes, IS NO FACT ON THE FILLING: IT IS THE FOURTH TIE ITSELF AT THAT
ITEM, WITH ALL THAT THE TIE HAS IN HAND BUT THE RELATION, UNDER A NAME (moved to the left is not cut down).
NONE OF THE TWELVE IS SHOWN AT ANY FILLING; the law's own premises (K05_at_table's) stand beside them. WHOEVER PAYS rider | keys
MUST HAVE hleftIs IN HAND: x0 a' is tied to the record by that premise of the top alone, not by K5FillIns.

What the row closes (k5_closes_iff): constr m idn · worth m 2 "planes" | "keys" | "rider" · its context pin m 0 · pinW ·
constr m small · "no mark". OF THESE EIGHT: "no mark" is in hand · the context's three stand among what the row opens at
(b, w) and ride back (K5FillRel.ctxPin | ctxW | ctxSmall) · THREE COME OF THE KIND's RELATION Todo, which says
(K05_means, K05_todo_is: Johnson/Desc/First/Att/K05Means.lean): the identities of the kind's own rounds hold at the cells
(OwnMeans.own1 | own2) · the caller's identity at the lookup's point is 0 (OwnMeans.rider) · the join at the rule values
is 0 (TodoJoin) · AND ONE DOES NOT: worth m 2 "planes" IS IN NONE OF Todo's CLAUSES: it comes of what the row opens.

Main names:
  `TodoJoin`: Todo's fourth clause, by name.
  `todo_at`: at a stored plan (PlanIs): Todo gives OwnMeans and TodoJoin, at the stored plan's own letters.
  `K5FillIns`: FOUR FACTS ON THE FILLING, each with the table's promise in front and "no mark" in hand:
    idn: own1 and own2 at the cells of I.part w, WITH THE CONTEXT's constr m small IN FRONT, give Mg.constr m idn · rider: the caller's identity at (x0 a')'s point
    gives Mg.worth m 2 "rider" · keys: TodoJoin gives Mg.worth m 2 "keys" · planes: ALL THAT THE ROW OPENS at the record
    behind the lay gives Mg.worth m 2 "planes" at the record in front.
  `k5_h4`: **the fourth tie at a piece that decides as the kind does.**
  `K05_tiedAt_all`: **TiedAt at the seated block's piece, from K5FillRel, K5FillIns and three tests on the table.**
WHO WOULD PAY (as reported): idn: whoever fills constr · rider, keys: whoever
fills worth (the lookup's files) · planes SPLITS IN THREE (as reported): "formsT m 2 planes is: the three
claims of the lookup's run planes are worth 0 in the later ledger's world" (the filling of formsT: nobody's yet) · "the
caller's readers read truly" (K3HostPlanes, Johnson/Meaning/PlanesLaw.lean: K5's FILES': had under named premises that hang on the
smallness test's tie: so constr m small, which is in hand there) · the lookups' own two lemmas from these to the worth.
K5FillIns.idn HAS THE PREMISE Mg.constr m .small at the state in front. WHY: a law on the messages says something of the model's integers only where the committed symbols are the packing of small integers, which
is what the part "small" says: without it the clause has no payer at the meaning that is meant. k5_h4 has it in hand (the row's context, carried back by K5FillRel.ctxSmall) and hands it on. THE FIELD IS WEAKER; NO CONCLUSION OF THIS FILE TURNS.
Limits. A RULE OVER LETTERS; no member. The letters x0 and I tie the filling to the law: the four facts name them.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Riders
import Johnson.Desc.First.Att.K05Means

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

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
open OnBytes.Road.L5 (callsOf)
open VerifiableInference.Desc.First.Look (attCells)

section
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

/-- Todo's fourth clause: the join at the rule values is 0. -/
def TodoJoin (ns : ℕ) (N : Nums) (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (m : (attSg x D rad).Msg) : Prop :=
  joinVal ((meantQ (attBase x S tl D rad) (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N)).q x0)
      (KF (scl := (meantQ (attBase x S tl D rad) (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N)).scl)
        (dimOf S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt)
        (rv (dimOf S) (callsOf x.fs) (pubOfZ Cb.Gl.E x0.2.1.pt) (attCells x S tl D rad m)))
      (((meantQ (attBase x S tl D rad) (attLin0 x S tl D rad) ns N (attQ0 x S tl D rad Ex Wp α ns N)).ce x0).val
        ((closedOf (attBase x S tl D rad) (attLin x S tl D rad Ex Wp α ns N) ns N).msg m)) = 0

end

/-- **What the kind's relation in front says, at a stored plan's own letters.** -/
theorem todo_at {Wv : Verify.Public} (hP : PlanIs Wv) {g : ℕ} {a : Attention.Plan} (ha : Wv.A[g]? = some a)
    (x : VerifiableInference.Desc.First.Look.Place) (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec)
    (Wp : Type) (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (ns : ℕ) (N : Nums)
    (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (m : (attSg x D rad).Msg)
    (h : ((closedOf (attBase x a.S a.seam.tl D rad) (attLin x a.S a.seam.tl D rad Ex Wp α ns N) ns N).own
      (theMeans Cb.Gl.E _ _ _)).ch.Todo x0 m) :
    OwnMeans x a.S a.seam.tl D rad x0.2.1.pt m ∧ TodoJoin x a.S a.seam.tl D rad Ex Wp α ns N x0 m := by
  obtain ⟨A0, pf, hA, e⟩ := hP g a ha
  subst e
  exact ⟨K05_means (A := A0) x _ D rad Ex Wp α hA ns N x0 m h,
    ((K05_todo_is (A := A0) x _ D rad Ex Wp α hA ns N x0 m).1 h).2.2.2⟩

/-- **Four facts on the filling**: what the kind's relation in front says gives three of the four items that the row
closes; all that the row opens gives the fourth. Each has the table's promise in front and "no mark" in hand. -/
structure K5FillIns {Pp W : Type} (Mg : Meaning Pp W) (N : Numbers) (links : List ModelPart) (π : Pp) (Fr : Frame)
    (base m : ℕ) (pl : Place) (O : List Item) (Q : List Pub) (own : Params.AttentionRounds)
    (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (Nn : Nums)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (part : W → (attSg x D rad).Msg) : Prop where
  idn : ∀ a' w, onT N Mg links π Fr pl O Q a' →
    (∀ j b g i, (Idn.at1 j b g i).Valid (dimOf S) →
      idnVal (dimOf S) (attCells x S tl D rad (part w)) (.at1 j b g i) = 0) →
    (∀ b g i, (Idn.at2 b g i).Valid (dimOf S) →
      idnVal (dimOf S) (attCells x S tl D rad (part w)) (.at2 b g i) = 0) →
    Mg.constr m .small (π, a'.1) (strsOf Fr a'.2) w →
    Mg.constr m .idn (π, a'.1) (strsOf Fr a'.2) w
  rider : ∀ a' w, onT N Mg links π Fr pl O Q a' →
    denOut (dimOf S) (callsOf x.fs) (x0 a').2.1.pt (attCells x S tl D rad (part w)) = 0 →
    Mg.worth m 2 "rider" (π, a'.1) (strsOf Fr a'.2) w
  keys : ∀ a' w, onT N Mg links π Fr pl O Q a' → TodoJoin x S tl D rad Ex Wp α ns Nn (x0 a') (part w) →
    Mg.worth m 2 "keys" (π, a'.1) (strsOf Fr a'.2) w
  planes : ∀ s att hd G rs y y' w, onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
    s.here = .att att → hear own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr base y y' →
    (∀ i ∈ [Item.formsT m 3 "own", .formsT m 2 "planes", .formsT m 2 "join", .pin m 0, .pinW, .constr m .small],
      i.holds N Mg (π, behind s att hd G) (strsOf Fr y') w) →
    Mg.worth m 2 "planes" (π, s) (strsOf Fr y) w

/-- **THE FOURTH TIE AT A PIECE THAT DECIDES AS THE KIND DOES**, from what the kind's relation says. -/
theorem k5_h4 {W Cl Pp : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (π : Pp) (k m : ℕ) (Pc : Piece (ckP .two) Fr First.S Cl W) (p : Par) (Dc : DecidesK5 Pc p) (pl pl' : Place)
    (O : List Item) (Q : List Pub) (Ix : K5Place links m pl pl') (hk : ps[k]? = some pl)
    (Rel : K5FillRel Mg N links π Fr Pc.base m pl O Q p.own)
    (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
    (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E) (ns : ℕ) (Nn : Nums)
    (x0 : First.S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)))
    (part : W → (attSg x D rad).Msg)
    (Ins : K5FillIns Mg N links π Fr Pc.base m pl O Q p.own x S tl D rad Ex Wp α ns Nn x0 part)
    (a : First.S × Fr.E.Str) (τ : Tr (uLT (ckP .two) Pc.ds)) (b : First.S × Fr.E.Str) (w : W)
    (hon : onAt N Mg links (some pl) O Q (π, a.1) (strsOf Fr a.2)) (hm : a.1.failed = none)
    (hout : Pc.ior.red.out a τ = some b)
    (hO : relAt (meansQ N Mg fun s => (π, s)) (outsQ links ps k) b w)
    (hOwn : OwnMeans x S tl D rad (x0 a).2.1.pt (part w))
    (hJ : TodoJoin x S tl D rad Ex Wp α ns Nn (x0 a) (part w)) :
    relAt (meansQ N Mg fun s => (π, s)) (insQ links ps k) a w := by
  obtain ⟨att, hd, G, rs, e, hh, eb, hy⟩ := piece_yes_lay Pc p Dc a b τ hout
  have hop := (k5_opens_iff N Mg π Ix hk b w).1 hO
  have at_b : ∀ i ∈ [Item.formsT m 3 "own", .formsT m 2 "planes", .formsT m 2 "join", .pin m 0, .pinW,
      .constr m .small, .unmarked], i.holds N Mg (π, behind a.1 att hd G) (strsOf Fr b.2) w := by
    intro i hi
    have := hop i hi
    unfold meansQ at this
    rw [eb] at this
    exact this
  refine (k5_closes_iff N Mg π Ix hk a w).2 fun i hi => ?_
  unfold meansQ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Ins.idn a w ⟨hon, hm⟩ hOwn.own1 hOwn.own2
      (Rel.ctxSmall _ _ _ _ _ _ _ w hon hm e hh hy (at_b (.constr m .small) (by simp)))
  · exact Ins.planes _ _ _ _ _ _ _ w hon hm e hh hy fun i hi => at_b i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      rcases hi with h | h | h | h | h | h <;> simp [h])
  · exact Ins.keys a w ⟨hon, hm⟩ hJ
  · exact Ins.rider a w ⟨hon, hm⟩ hOwn.rider
  · exact fun t ht => Rel.ctxPin t ht _ _ _ _ _ _ _ w hon hm e hh hy (at_b (.pin m 0) (by simp) t ht)
  · exact Rel.ctxW _ _ _ _ _ _ _ w hon hm e hh hy (at_b .pinW (by simp))
  · exact Rel.ctxSmall _ _ _ _ _ _ _ w hon hm e hh hy (at_b (.constr m .small) (by simp))
  · exact hm

open Classical in
/-- **THE KIND's BLOCK IN THE CHAIN OF PROMISES, UNDER NAMED PREMISES**: the third tie is the identity; of the fourth, three
quarters come by K5FillIns' dictionaries, the context by K5FillRel, and the quarter at "planes" stands as a named premise; the
fifth comes by K5FillRel and three tests on the table. IT PROVES NO FILLING. -/
theorem K05_tiedAt_all {W Cl Pp : Type} {Fr : Frame} (claim : Aff → Cl) {Wv : Verify.Public}
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
    (Rel : K5FillRel Mg N links π Fr base m pl O Q (parO Wv m a before).own)
    (hr : readsOpen links ps (start links) = true) (hap : rowsApart links ps = true)
    (hB : ridersB links ps k m = true)
    (Ins : K5FillIns Mg N links π Fr base m pl O Q (parO Wv m a before).own x a.S a.seam.tl D rad Ex Wp α ns
      (numsPlan (parO Wv m a before).own (x.F.next + Forest.elems x.fs)) x0 I.part) :
    TiedAt N Mg links ps (fun s => (π, s)) k
      (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W) := by
  have hD : DecidesK5 (⟨blk, base, ds, [], fun _ _ w => w, Err.cap 128 (uLT (ckP .two) ds)⟩ :
        Piece (ckP .two) Fr First.S Claim W) (parO Wv m a before) := by
    obtain ⟨a', ha', rfl⟩ := k5AtN_is Wv m g before blk hblk
    obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
    exact decides_k5_ok _ _ _ _ _ _
  exact K05_tiedAt_riders claim hP hp4 g m hm before blk hblk hok hG ha hx D rad Ex Wp α ns base ds hds tj x0 yOf gOf plJ
    I R' N Mg links π pl pl' O Q pC pD hS arr first kr nsPlan Ix Bk Pn Fi hQ keptForms madeForms madeMore hleftIs hokI Bh
    ps k hk hk' hO hQs hR'
    (fun a' τ b w hq hmk hout _ _ hW hT =>
      have hT' := todo_at hP ha x D rad Ex Wp α ns _ (x0 a') (I.part w) hT
      k5_h4 N Mg links ps π k m _ (parO Wv m a before) hD pl pl' O Q Ix hk Rel x a.S a.seam.tl D rad Ex Wp α ns _ x0
        I.part Ins a' τ b w (by
          unfold onQ at hq
          rw [hk, ← hO, ← hQs] at hq
          exact hq) hmk hout hW hT'.1 hT'.2)
    Rel hr hap hB

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.todo_at
#print axioms VerifiableInference.Desc.First.Att.P.k5_h4
#print axioms VerifiableInference.Desc.First.Att.P.K05_tiedAt_all
